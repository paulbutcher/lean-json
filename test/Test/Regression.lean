/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json

namespace Test.Regression

/-!
Behaviours that another implementation gets wrong, gathered so that the list can be read in one
place. The ones that concern reading, deep nesting, a billion-place exponent, a lone surrogate
escape and a repeated name, are pinned beside the parser, and the float conversion beside the
codecs; what follows is everything else.
-/

/-- A chain of single-element arrays around `bottom`, iterated so the test's own depth is one. -/
private def deepFrom (n : Nat) (bottom : Json) : Json :=
  (List.range n).foldl (fun j _ => .arr #[j]) bottom

private def deep (n : Nat) : Json := deepFrom n .null

def printing : Array TestCase := #[
  -- Printing a deeply nested value is where a recursive printer overflows even though parsing
  -- survived. Comparing the text rather than the values keeps the check itself iterative.
  { name := "two hundred thousand deep is compressed and read back"
    run := do
      let text := compress (deep 200000)
      match Json.parse text { maxDepth := none } with
      | .error e => throw (IO.userError s!"failed with {repr e.kind} at {e.byteOffset}")
      | .ok j => if compress j != text then throw (IO.userError "the text changed") },
  -- Laying it out costs a line and an indent per level, so this one is bounded by its own
  -- output rather than by the printer.
  { name := "a thousand deep is laid out and read back"
    run := do
      let text := pretty (deep 1000)
      match Json.parse text { maxDepth := none } with
      | .error e => throw (IO.userError s!"failed with {repr e.kind} at {e.byteOffset}")
      | .ok j => if compress j != compress (deep 1000) then
          throw (IO.userError "the value changed") },
  -- The member order of an object is the order it was written in, and survives both directions.
  expectEq "the order of an object's members survives reading and writing"
    ((Json.parse "{\"b\":1,\"a\":2,\"c\":3}").toOption.map compress)
    (some "{\"b\":1,\"a\":2,\"c\":3}")
]

def values : Array TestCase := #[
  -- Setting a field of something that is not an object is an error, where a partial API panics.
  expect "setting a field of a number is refused"
    ((setObjVal? (.num 1) "a" .null).toOption.isNone),
  expect "setting a field of an array is refused"
    ((setObjVal? (.arr #[]) "a" .null).toOption.isNone),
  -- Two spellings of one number read as one value, which is what keeps `==` and `compare` from
  -- disagreeing: they part company only on values that are not canonical, and none are produced.
  { name := "spellings of one number cannot disagree about equality"
    run :=
      match Json.parse "150", Json.parse "1.5e2" with
      | .ok (.num a), .ok (.num b) =>
        if a == b && compare a b == .eq then pure ()
        else throw (IO.userError s!"{repr a} and {repr b}")
      | _, _ => throw (IO.userError "one of them did not parse") }
]

/--
Freeing a deeply nested value is a recursion the library does not control, and no theorem here
reaches it. Building and dropping one repeatedly is the only way to find out whether it bites.
-/
def teardown : Array TestCase := #[
  { name := "a million deep is torn down without taking the process with it"
    run := do
      let mut kept := 0
      for _ in [0:3] do
        let j := deep 1000000
        if (j.getArr?.toOption.map (·.size)) == some 1 then kept := kept + 1
      if kept != 3 then throw (IO.userError "the values were not built") }
]

/-!
Every traversal of a value is a traversal of whatever a caller built, and nothing bounds how deep
that is. These five walk the whole value, and each of them overflowed the stack before they were
paired with a fold.
-/
def traversal : Array TestCase := #[
  { name := "a million deep is hashed, compared, checked and measured"
    run := do
      let bottom := mkObj [("a", (1 : Json)), ("b", .str "x")]
      let j := deepFrom 1000000 bottom
      let k := deepFrom 1000000 bottom
      if Json.hash j != Json.hash k then throw (IO.userError "the hashes differ")
      if !(j == k) then throw (IO.userError "the values differ")
      if !Json.uniqueKeys j then throw (IO.userError "a repeated name was reported")
      if !Json.canonicalNumbers j then throw (IO.userError "a number was called uncanonical")
      if j.depth != 1000001 then throw (IO.userError s!"the depth came out as {j.depth}") }
]

def all : Array TestCase := printing ++ values ++ teardown ++ traversal

end Test.Regression
