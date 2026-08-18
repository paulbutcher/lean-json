/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json

namespace Test.Fuzz

/-!
Fuzzing answers the question no theorem here reaches: whether the process survives input nobody
designed. Every generator is seeded from a constant, so a failure is reproducible from the
iteration number printed beside it rather than only from a lucky rerun.
-/

private structure Rng where
  state : UInt64
deriving Inhabited

private def Rng.step (g : Rng) : UInt64 × Rng :=
  let s := g.state * 6364136223846793005 + 1442695040888963407
  (s >>> 33, ⟨s⟩)

private def Rng.upTo (g : Rng) (bound : Nat) : Nat × Rng :=
  let (v, g) := g.step
  (if bound = 0 then 0 else v.toNat % bound, g)

private def seeds : Array String := #[
  "null", "[]", "{}", "1e1000000000", "-12.50e3",
  "\"\\u00e9\\ud83d\\ude00\\t\\\\\\\"\"",
  "[1,2,[3,[4,{\"a\":null}]]]",
  "{\"a\":[true,false,null],\"b\":{\"c\":\"d\"},\"e\":-0.5e-7}",
  "[\"\", \"é😀\", \"\\u0000\"]",
  " \t\r\n [ 1 , { \"k\" : [ ] } ] \r\n "
]

/-- One edit at a random place: an insertion, a deletion, an overwrite, a truncation, or a repeat. -/
private def mutate (g : Rng) (bytes : List UInt8) : List UInt8 × Rng :=
  let (choice, g) := g.upTo 5
  let (i, g) := g.upTo (bytes.length + 1)
  let (b, g) := g.upTo 256
  let byte := UInt8.ofNat b
  match choice with
  | 0 => (bytes.take i ++ byte :: bytes.drop i, g)
  | 1 => (bytes.take i ++ bytes.drop (i + 1), g)
  | 2 => (bytes.take i ++ byte :: bytes.drop (i + 1), g)
  | 3 => (bytes.take i, g)
  | _ => (bytes ++ bytes.take i, g)

private def mutant (g : Rng) : ByteArray × Rng :=
  let (s, g) := g.upTo seeds.size
  let (edits, g) := g.upTo 3
  let start := (seeds[s]?.getD "null").toUTF8.toList
  let rec go (n : Nat) (bytes : List UInt8) (g : Rng) : List UInt8 × Rng :=
    match n with
    | 0 => (bytes, g)
    | n + 1 => let (bytes, g) := mutate g bytes; go n bytes g
  let (bytes, g) := go (edits + 1) start g
  (⟨bytes.toArray⟩, g)

/--
Bytes drawn mostly from the alphabet JSON is written in, and mostly short. Wholly random bytes
of any length almost never parse, so a sweep of them would exercise only the refusing path; one
byte in eight is arbitrary all the same, so that input which is not text at all still arrives.
-/
private def alphabet : ByteArray := "[]{},:\"\\/0123456789.-+eEturfalsn \t\r\n".toUTF8

private def noise (g : Rng) : ByteArray × Rng :=
  let (long, g) := g.upTo 4
  let (len, g) := g.upTo (if long == 0 then 48 else 12)
  let rec go (n : Nat) (bytes : List UInt8) (g : Rng) : List UInt8 × Rng :=
    match n with
    | 0 => (bytes, g)
    | n + 1 =>
      let (pick, g) := g.upTo 8
      let (v, g) := g.upTo (if pick == 0 then 256 else alphabet.size)
      let byte := if pick == 0 then UInt8.ofNat v else alphabet[v]?.getD 0x20
      go n (byte :: bytes) g
  let (bytes, g) := go len [] g
  (⟨bytes.toArray⟩, g)

/--
What must hold of anything the parser accepts, whatever the bytes were: the input was text, the
value obeys the invariants the rest of the library relies on, and both spellings of it read back
as the same value.
-/
private def acceptedIsSound (bytes : ByteArray) (j : Json) : Bool :=
  (String.fromUTF8? bytes).isSome && canonicalNumbers j && uniqueKeys j &&
    (Json.parse (compress j)).toOption == some j &&
    (Json.parse (pretty j)).toOption == some j

private def sweep (name : String) (rounds : Nat) (gen : Rng → ByteArray × Rng) : TestCase where
  name := name
  run := do
    let mut g : Rng := ⟨0x9E3779B97F4A7C15⟩
    let mut accepted := 0
    for iteration in [0:rounds] do
      let (bytes, g') := gen g
      g := g'
      match Json.parseBytes bytes with
      | .error _ => pure ()
      | .ok j =>
        accepted := accepted + 1
        if !acceptedIsSound bytes j then
          throw (IO.userError s!"iteration {iteration} accepted unsoundly: {repr j}")
    -- A run that accepts nothing has stopped testing the accepting path, and would pass silently.
    -- A generator that stopped reaching the accepting path would pass this sweep in silence,
    -- so the floor is part of the test rather than a diagnostic.
    if accepted * 200 < rounds then
      throw (IO.userError s!"only {accepted} of {rounds} were accepted, so little was checked")

def sweeps : Array TestCase := #[
  sweep "edited documents are read soundly or refused" 3000 mutant,
  sweep "byte soup is read soundly or refused" 3000 noise
]

/-! ## Shapes chosen to be awkward rather than drawn at random -/

private def nested (n : Nat) : String := "".pushn '[' n ++ "".pushn ']' n

private def wideObject (n : Nat) (duplicateLast : Bool) : String :=
  let member (i : Nat) := "\"k" ++ toString (if duplicateLast && i + 1 == n then 0 else i) ++ "\":1"
  "{" ++ String.intercalate "," ((List.range n).map member) ++ "}"

def stress : Array TestCase := #[
  expect "the depth limit falls exactly where it is set"
    ((Json.parse (nested 1024)).toOption.isSome &&
      (Json.parse (nested 1025)).toOption.isNone),
  expect "the digit limit falls exactly where it is set"
    ((Json.parse ("1".pushn '0' 999)).toOption.isSome &&
      (Json.parse ("1".pushn '0' 1000)).toOption.isNone),
  -- Duplicate detection is by hash set, so a wide object stays linear rather than quadratic.
  expect "twenty thousand distinct names are read"
    ((Json.parse (wideObject 20000 false)).toOption.isSome),
  expect "a repeat among twenty thousand names is found"
    ((Json.parse (wideObject 20000 true)).toOption.isNone),
  -- An exponent is carried, never applied, so its size costs nothing.
  expect "exponents at either extreme are read and round trip"
    (match Json.parse "[1e1000000000,1e-1000000000]" with
      | .ok j => (Json.parse (compress j)).toOption == some j
      | .error _ => false),
  { name := "no lone byte above the ASCII range is read as text"
    run := do
      let mut wrong := #[]
      for b in [0x80:0x100] do
        match Json.parseBytes ⟨#[0x22, UInt8.ofNat b, 0x22]⟩ with
        | .ok _ => wrong := wrong.push b
        | .error e => if e.kind != .invalidUtf8 then wrong := wrong.push b
      if !wrong.isEmpty then
        throw (IO.userError s!"{wrong.size} bytes were mishandled, starting with {wrong[0]?}") },
  { name := "a multi-byte sequence cut short is refused"
    run := do
      -- Each lead byte, given fewer continuation bytes than it announces.
      let leads : List (UInt8 × Nat) := [(0xC3, 1), (0xE2, 2), (0xF0, 3)]
      for (lead, needed) in leads do
        for short in [0:needed] do
          let body := ⟨#[0x22, lead] ++ Array.replicate short 0x80 ++ #[0x22]⟩
          match Json.parseBytes body with
          | .ok j => throw (IO.userError s!"lead {lead} with {short} accepted as {repr j}")
          | .error e =>
            if e.kind != .invalidUtf8 then
              throw (IO.userError s!"lead {lead} with {short} gave {repr e.kind}") }
]

def all : Array TestCase := sweeps ++ stress

end Test.Fuzz
