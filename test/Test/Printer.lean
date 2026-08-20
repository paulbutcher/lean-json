/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json
open Plausible (NamedBinder)

namespace Test.Printer

/-! ## Numbers

The general theorem says only that the text denotes the same value; which of the two spellings
is chosen is a separate claim, and that is what these pin down. -/

private def renders (n : Number) (expected : String) : TestCase :=
  expectEq s!"renders {repr n} as {expected}" (toString n) expected

def numbers : Array TestCase := #[
  renders ⟨0, 0⟩ "0",
  renders ⟨1, 0⟩ "1",
  renders ⟨-1, 0⟩ "-1",
  renders ⟨-125, 2⟩ "-12500",
  renders ⟨123, -1⟩ "12.3",
  renders ⟨125, -2⟩ "1.25",
  renders ⟨1, -3⟩ "0.001",
  renders ⟨-1, -3⟩ "-0.001",
  -- Plain decimal while the padding stays within the limit, exponent notation beyond it.
  renders ⟨1, 20⟩ "100000000000000000000",
  renders ⟨1, 21⟩ "1e21",
  renders ⟨-1, 21⟩ "-1e21",
  renders ⟨1, -21⟩ "0.000000000000000000001",
  renders ⟨1, -22⟩ "1e-22",
  -- The input that hangs core: the exponent is written out, never applied.
  renders ⟨1, 1000000000⟩ "1e1000000000",
  renders ⟨1, -1000000000⟩ "1e-1000000000"
]

/-! ## Escaping -/

private def escapes (s expected : String) : TestCase :=
  expectEq s!"escapes {repr s}" (escape s) expected

def escaping : Array TestCase := #[
  escapes "" "",
  escapes "abc" "abc",
  escapes "a\"b" "a\\\"b",
  escapes "a\\b" "a\\\\b",
  escapes "\n\r\t" "\\n\\r\\t",
  escapes "\x08\x0c" "\\b\\f",
  -- Controls without a short form take the numeric escape.
  escapes "\x00\x01\x1f" "\\u0000\\u0001\\u001f",
  -- The solidus may be escaped but need not be, and non-ASCII is left as itself, the output
  -- being UTF-8.
  escapes "/" "/",
  escapes "é😀" "é😀",
  -- 0x7f is not a control character as far as the grammar is concerned.
  escapes "\x7f" "\x7f"
]

/-! ## Layout -/

private def sample : Json :=
  .obj #[("a", .num 1), ("b", .arr #[.num 2, .obj #[("c", .null)]]), ("d", .obj #[]),
    ("e", .arr #[])]

def layout : Array TestCase := #[
  expectEq "compresses to the shortest form the grammar allows"
    (compress sample) "{\"a\":1,\"b\":[2,{\"c\":null}],\"d\":{},\"e\":[]}",
  expectEq "prints one member or element per line, indented by depth" (pretty sample)
    "{\n  \"a\": 1,\n  \"b\": [\n    2,\n    {\n      \"c\": null\n    }\n  ],\n  \"d\": {},\n  \"e\": []\n}",
  expectEq "honours a different indent" (pretty (.arr #[.num 1]) 4) "[\n    1\n]",
  expectEq "prints empty containers without a break"
    (pretty (.arr #[.obj #[], .arr #[]])) "[\n  {},\n  []\n]",
  expectEq "the string form is the compressed one" (toString sample) (compress sample)
]

/-! ## Adversarial input -/

def adversarial : Array TestCase := #[
  -- Printing is a loop over an explicit stack, so nesting costs heap, not C stack. The value is
  -- built by the parser rather than by recursion here, so that only the printer is under test.
  { name := "100,000 deep nesting prints without a crash"
    run :=
      match Json.parse ("".pushn '[' 100000 ++ "".pushn ']' 100000) { maxDepth := none } with
      | .error e => throw (IO.userError s!"could not build the value: {repr e.kind}")
      | .ok j =>
        let n := (compress j).length
        if n == 200000 then pure () else throw (IO.userError s!"printed {n} characters") }
]

/-! ## Properties -/

-- Values are built from a list of numbers so that the generator covers every constructor, both
-- number forms, keys that stay distinct, and the string characters that need escaping.

private def charOf (i : Nat) : Char :=
  match i % 7 with
  | 0 => 'a'
  | 1 => '"'
  | 2 => '\\'
  | 3 => '\n'
  | 4 => '\x01'
  | 5 => '/'
  | _ => '😀'

private def stringOf (n : Nat) : String :=
  String.ofList ((List.range (n % 5)).map fun i => charOf (n + i))

-- The numbers here are shaped so that every rendering branch is reached: exponents inside and
-- outside the padding limit in both directions, and mantissas long enough that the decimal point
-- lands somewhere other than either end. Numbers drawn more naively leave the decimal-point
-- branch almost untouched, and a mutation that misplaced the point survived.
private def leaf (n : Nat) : Json :=
  match n % 10 with
  | 0 => .null
  | 1 => .bool (n % 2 == 0)
  | 2 => .num (Number.normalize n 0)
  | 3 => .num (Number.normalize (-(n : Int)) ((n % 7) * 5))
  | 4 => .num (Number.normalize (n * 1000 + 137) (-((n % 3 + 1 : Nat) : Int)))
  | 5 => .num (Number.normalize (n + 1) (-((n % 7 * 5 : Nat) : Int)))
  | 6 => .str (stringOf n)
  | 7 => .str ""
  | 8 => .arr #[]
  | _ => .obj #[]

private def treeOf : List Nat → Json
  | [] => .null
  | n :: rest =>
    match n % 3 with
    | 0 => leaf n
    | 1 => .arr #[leaf n, treeOf rest]
    | _ => .obj #[(stringOf n ++ "k", leaf n), ("nested", treeOf rest)]

/--
Whatever the compressed form of a value is, parsing it gives that value back. `parse_compress`
proves this for a configuration whose limits are off; what is left to a property is the default
reading, whose limits on nesting and on digits refuse some legal text by design.
-/
abbrev compressRoundTrips : Prop :=
  NamedBinder "ns" <| ∀ ns : List Nat,
    ((Json.parse (compress (treeOf ns))).toOption == some (treeOf ns)) = true

/--
The laid-out form denotes the same value, so the extra space is never significant. Proved as
`parse_pretty` for a configuration whose limits are off, and property-tested for the default.
-/
abbrev prettyRoundTrips : Prop :=
  NamedBinder "ns" <| ∀ ns : List Nat,
    ((Json.parse (pretty (treeOf ns))).toOption == some (treeOf ns)) = true

/-- Strings survive escaping, whatever they contain. -/
abbrev stringRoundTrips : Prop :=
  NamedBinder "ns" <| ∀ ns : List Nat,
    (let s := String.ofList (ns.map charOf)
     (Json.parse (renderString s)).toOption == some (.str s)) = true

def all : Array TestCase :=
  numbers ++ escaping ++ layout ++ adversarial ++ #[
    property "the compressed form round trips" compressRoundTrips,
    property "the laid-out form round trips" prettyRoundTrips,
    property "escaped strings round trip" stringRoundTrips
  ]

end Test.Printer
