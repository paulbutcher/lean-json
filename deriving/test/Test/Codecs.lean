/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import JsonDeriving
import Test.Runner

open Json
open Plausible (NamedBinder)

namespace Test.Codecs

structure Point where
  x : Nat
  y : Nat
deriving ToJson, FromJson, BEq, Repr

structure Person where
  name : String
  tags : Array String
  nickname? : Option String
  home : Point
deriving Json.ToJson, Json.FromJson, BEq, Repr

inductive Colour where
  | red
  | green
  | blue
deriving ToJson, FromJson, BEq, Repr

inductive Shape where
  | circle (radius : Nat)
  | rect (width : Nat) (height : Nat)
  | nothing
deriving ToJson, FromJson, BEq, Repr

inductive Positional where
  | pair : Nat → String → Positional
  | solo : Nat → Positional
deriving ToJson, FromJson, BEq, Repr

/-- Recursion through `Array`, which is where a derived decoder needs the count it carries. -/
inductive Tree where
  | leaf (value : Nat)
  | node (children : Array Tree)
deriving ToJson, FromJson, BEq, Repr

/-- Recursion through `List` and `Option`, the other two shapes the handler generates. -/
inductive Chain where
  | link (label : String) (next : Option Chain) (branches : List Chain)
deriving ToJson, FromJson, BEq, Repr

private def roundTrips [ToJson α] [FromJson α] [BEq α] [Repr α] (name : String) (v : α) :
    TestCase where
  name := name
  run :=
    match fromJson? (toJson v) with
    | .ok (w : α) => if w == v then pure () else throw (IO.userError s!"came back as {repr w}")
    | .error e => throw (IO.userError s!"failed to decode: {e}")

private def encodesTo [ToJson α] (name : String) (v : α) (expected : String) : TestCase where
  name := name
  run :=
    let got := compress (toJson v)
    if got == expected then pure () else throw (IO.userError s!"encoded as {got}")

def encoding : Array TestCase := #[
  encodesTo "a structure becomes an object of its fields" { x := 1, y := 2 : Point }
    "{\"x\":1,\"y\":2}",
  -- A name ending in `?` is optional: absent from the object rather than present as null.
  encodesTo "an absent optional field is left out"
    { name := "a", tags := #[], nickname? := none, home := { x := 0, y := 0 } : Person }
    "{\"name\":\"a\",\"tags\":[],\"home\":{\"x\":0,\"y\":0}}",
  encodesTo "a present optional field is written"
    { name := "a", tags := #["t"], nickname? := some "b", home := { x := 0, y := 0 } : Person }
    "{\"name\":\"a\",\"tags\":[\"t\"],\"nickname\":\"b\",\"home\":{\"x\":0,\"y\":0}}",
  encodesTo "a constructor with no fields is its name" Colour.green "\"green\"",
  -- A field with a name of its own keeps it, whether the constructor has one field or several.
  encodesTo "a single named field is written under its name" (Shape.circle 3)
    "{\"circle\":{\"radius\":3}}",
  encodesTo "a single unnamed field is written on its own" (Positional.solo 3) "{\"solo\":3}",
  encodesTo "named fields become an object" (Shape.rect 2 3)
    "{\"rect\":{\"width\":2,\"height\":3}}",
  encodesTo "unnamed fields become an array" (Positional.pair 1 "a")
    "{\"pair\":[1,\"a\"]}",
  encodesTo "recursion is written through the array" (Tree.node #[.leaf 1, .node #[.leaf 2]])
    ("{\"node\":{\"children\":[{\"leaf\":{\"value\":1}}," ++
      "{\"node\":{\"children\":[{\"leaf\":{\"value\":2}}]}}]}}")
]

private def deepTree : Nat → Tree
  | 0 => .leaf 0
  | n + 1 => .node #[deepTree n]

private def chain : Nat → Chain
  | 0 => .link "end" none []
  | n + 1 => .link s!"l{n}" (some (chain n)) [.link "side" none []]

def decoding : Array TestCase := #[
  roundTrips "a structure" { x := 1, y := 2 : Point },
  roundTrips "a structure with an optional field absent"
    { name := "a", tags := #["x", "y"], nickname? := none, home := { x := 1, y := 2 } : Person },
  roundTrips "a structure with an optional field present"
    { name := "a", tags := #[], nickname? := some "n", home := { x := 1, y := 2 } : Person },
  roundTrips "an enumeration" Colour.blue,
  roundTrips "a constructor with no fields" Shape.nothing,
  roundTrips "a constructor with named fields" (Shape.rect 4 5),
  roundTrips "a constructor with unnamed fields" (Positional.pair 7 "s"),
  roundTrips "a constructor with one unnamed field" (Positional.solo 7),
  roundTrips "a tree" (Tree.node #[.leaf 1, .node #[.leaf 2, .leaf 3]]),
  -- The count the decoder carries is the depth of what it was handed, so nesting costs it
  -- nothing until the value itself runs out.
  roundTrips "a tree two hundred deep" (deepTree 200),
  roundTrips "recursion through a list and an option" (chain 20),
  -- Everything above went through the printer and the parser, not just the two codecs.
  { name := "a value survives the text as well as the encoding"
    run :=
      let text := compress (toJson (Tree.node #[.leaf 1, .node #[.leaf 2]]))
      match Json.parse text with
      | .error e => throw (IO.userError s!"the text did not parse: {e}")
      | .ok j =>
        match fromJson? (α := Tree) j with
        | .ok t => if t == Tree.node #[.leaf 1, .node #[.leaf 2]] then pure ()
                   else throw (IO.userError s!"came back as {repr t}")
        | .error e => throw (IO.userError e) }
]

private def refuses (name : String) (α : Type) [FromJson α] (text : String) : TestCase where
  name := name
  run :=
    match Json.parse text with
    | .error e => throw (IO.userError s!"the text did not parse: {e}")
    | .ok j =>
      match fromJson? (α := α) j with
      | .error _ => pure ()
      | .ok _ => throw (IO.userError "accepted")

def refusal : Array TestCase := #[
  refuses "a missing field" Point "{\"x\":1}",
  refuses "a field of the wrong type" Point "{\"x\":1,\"y\":\"two\"}",
  refuses "an unknown constructor" Colour "\"purple\"",
  refuses "a constructor given the wrong shape" Shape "{\"rect\":[1,2]}",
  refuses "an array where an object belongs" Person "[]",
  { name := "the message names the field that was wrong"
    run :=
      match Json.parse "{\"x\":1,\"y\":\"two\"}" with
      | .error e => throw (IO.userError s!"the text did not parse: {e}")
      | .ok j =>
        match fromJson? (α := Point) j with
        | .error e =>
          if e.splitOn "y" |>.length |> (· > 1) then pure ()
          else throw (IO.userError s!"the message was {e}")
        | .ok _ => throw (IO.userError "accepted") }
]

/-! ## Properties -/

private def pointOf (n : Nat) : Point := { x := n % 97, y := n / 7 }

private def treeOf (n : Nat) : Tree :=
  match n % 4 with
  | 0 => .leaf n
  | 1 => .node #[.leaf n, .leaf (n + 1)]
  | 2 => .node #[.node #[.leaf n], .leaf 0]
  | _ => .node #[]

private def treeFrom (ns : List Nat) : Tree := .node ((ns.map treeOf).toArray)

abbrev pointsRoundTrip : Prop :=
  NamedBinder "n" <| ∀ n : Nat,
    ((fromJson? (toJson (pointOf n))).toOption == some (pointOf n)) = true

abbrev treesRoundTrip : Prop :=
  NamedBinder "ns" <| ∀ ns : List Nat,
    ((fromJson? (toJson (treeFrom ns))).toOption == some (treeFrom ns)) = true

abbrev treesSurviveTheText : Prop :=
  NamedBinder "ns" <| ∀ ns : List Nat,
    (match Json.parse (compress (toJson (treeFrom ns))) with
      | .ok j => (fromJson? (α := Tree) j).toOption == some (treeFrom ns)
      | .error _ => false) = true

def all : Array TestCase :=
  encoding ++ decoding ++ refusal ++ #[
    property "structures round trip" pointsRoundTrip,
    property "trees round trip" treesRoundTrip,
    property "trees survive the text" treesSurviveTheText
  ]

end Test.Codecs
