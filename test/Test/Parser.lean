/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json
open Plausible (NamedBinder)

namespace Test.Parser

/-! ## Behaviour -/

private def ok (s : String) (expected : Json) (cfg : Config := {}) : TestCase :=
  { name := s!"parses {s}"
    run :=
      match Json.parse s cfg with
      | .ok j =>
        if j == expected then pure ()
        else throw (IO.userError s!"parsed to {repr j}, expected {repr expected}")
      | .error e => throw (IO.userError s!"failed with {repr e.kind} at {e.position}") }

private def rejects (s : String) (kind : ErrorKind) (cfg : Config := {}) : TestCase :=
  { name := s!"rejects {s}"
    run :=
      match Json.parse s cfg with
      | .ok j => throw (IO.userError s!"accepted, giving {repr j}")
      | .error e =>
        if e.kind == kind then pure ()
        else throw (IO.userError s!"failed with {repr e.kind}, expected {repr kind}") }

private def num (m e : Int) : Json := .num ⟨m, e⟩

def accepted : Array TestCase := #[
  ok "null" .null,
  ok "true" (.bool true),
  ok "false" (.bool false),
  ok " \t\r\n null \t\r\n " .null,
  ok "0" (num 0 0),
  ok "-0" (num 0 0),
  ok "1" (num 1 0),
  ok "-12.50e3" (num (-125) 2),
  ok "1e1000000000" (num 1 1000000000),
  ok "1E+2" (num 1 2),
  ok "1e-2" (num 1 (-2)),
  ok "100" (num 1 2),
  ok "\"\"" (.str ""),
  ok "\"a\\nb\"" (.str "a\nb"),
  ok "\"\\u0041\"" (.str "A"),
  ok "\"\\ud83d\\ude00\"" (.str "😀"),
  ok "\"\\\"\\\\\\/\\b\\f\\r\\t\"" (.str "\"\\/\x08\x0c\x0d\t"),
  ok "[]" (.arr #[]),
  ok "{}" (.obj #[]),
  ok "[1,2,3]" (.arr #[num 1 0, num 2 0, num 3 0]),
  ok "[ 1 , [ ] , { } ]" (.arr #[num 1 0, .arr #[], .obj #[]]),
  ok "{\"a\":1}" (.obj #[("a", num 1 0)]),
  ok "{ \"a\" : { \"b\" : [ null ] } }" (.obj #[("a", .obj #[("b", .arr #[.null])])]),
  -- Field order is preserved, so this is not the same value as the reverse.
  ok "{\"b\":1,\"a\":2}" (.obj #[("b", num 1 0), ("a", num 2 0)]),
  -- Duplicate names are kept when the configuration allows them.
  ok "{\"a\":1,\"a\":2}" (.obj #[("a", num 1 0), ("a", num 2 0)])
    { duplicateKeys := .allow },
  -- A byte order mark is ignored by default.
  ok "﻿null" .null
]

def rejected : Array TestCase := #[
  rejects "" .unexpectedEnd,
  rejects "   " .unexpectedEnd,
  rejects "nul" (.unexpectedChar 'n'),
  rejects "trues" (.trailingText 's'),
  rejects "01" (.trailingText '1'),
  rejects "-" .expectedDigit,
  rejects "1." .expectedDigit,
  rejects ".1" (.unexpectedChar '.'),
  rejects "1e" .expectedDigit,
  rejects "1e+" .expectedDigit,
  rejects "+1" (.unexpectedChar '+'),
  rejects "[1,]" (.unexpectedChar ']'),
  rejects "[1 2]" (.unexpectedChar '2'),
  rejects "[" .unexpectedEnd,
  rejects "{\"a\"}" (.unexpectedChar '}'),
  rejects "{\"a\":}" (.unexpectedChar '}'),
  rejects "{a:1}" (.unexpectedChar 'a'),
  rejects "{\"a\":1,}" (.unexpectedChar '}'),
  rejects "\"unterminated" .unexpectedEnd,
  rejects "\"\t\"" (.controlCharInString '\t'),
  rejects "\"\\q\"" (.unknownEscape 'q'),
  rejects "\"\\u00g0\"" .badHexEscape,
  -- D8: a lone surrogate is an error, never a replacement character.
  rejects "\"\\ud800\"" .loneSurrogate,
  rejects "\"\\ud800a\"" .loneSurrogate,
  rejects "\"\\udc00\\ud800\"" .loneSurrogate,
  -- D6: duplicate names are rejected by default.
  rejects "{\"a\":1,\"a\":2}" (.duplicateKey "a"),
  rejects "nullnull" (.trailingText 'n'),
  rejects "[1][2]" (.trailingText '[')
]

/-! ## Adversarial input, from section 2 of the plan -/

private def nested (depth : Nat) : String :=
  "".pushn '[' depth ++ "".pushn ']' depth

/-! ## Error messages -/

def messages : Array TestCase := #[
  expectEq "an error says what and where"
    (toString { position := 3, kind := .unexpectedChar 'x' : Error })
    "unexpected character 'x' at character 3",
  expectEq "a depth failure names the limit rather than the input"
    (toString { position := 0, kind := .depthExceeded : Error })
    "nesting deeper than the configured limit at character 0",
  expectEq "a short duplicate name is quoted back"
    (toString { position := 7, kind := .duplicateKey "a" : Error })
    "the field name \"a\" appears twice at character 7",
  -- A field name comes from the input, so a long one is described rather than repeated.
  expectEq "a long duplicate name is not repeated back"
    (toString { position := 7, kind := .duplicateKey ("k".pushn 'x' 100) : Error })
    "a field name appears twice at character 7"
]

def adversarial : Array TestCase := #[
  -- Core aborts with a stack overflow on deep nesting. Here it is a plain error. Ten million
  -- deep behaves the same way but needs about 750MB, for the reason recorded in the plan's note
  -- on input representation, so the suite exercises a size that fits in a normal machine.
  { name := "1,000,000 deep nesting is an error, not a crash"
    run :=
      match Json.parse (nested 1000000) with
      | .error e =>
        if e.kind == .depthExceeded then pure ()
        else throw (IO.userError s!"failed with {repr e.kind}, expected depthExceeded")
      | .ok _ => throw (IO.userError "accepted, but the depth limit should have stopped it") },
  -- The same input with no limit set: bounded by memory alone, and it must still not crash.
  { name := "100,000 deep nesting parses with no depth limit"
    run :=
      match Json.parse (nested 100000) { maxDepth := none } with
      | .ok _ => pure ()
      | .error e => throw (IO.userError s!"failed with {repr e.kind} at {e.position}") },
  -- Core hangs on this input, computing ten to the billionth.
  { name := "a billion-place exponent is read, not applied"
    run :=
      match Json.parse "1e1000000000" with
      | .ok (.num n) =>
        if n == ⟨1, 1000000000⟩ then pure ()
        else throw (IO.userError s!"parsed to {repr n}")
      | .ok j => throw (IO.userError s!"parsed to {repr j}")
      | .error e => throw (IO.userError s!"failed with {repr e.kind}") },
  { name := "a long run of digits is refused rather than converted"
    run :=
      match Json.parse ("1".pushn '0' 5000) with
      | .error e =>
        if e.kind == .tooManyDigits then pure ()
        else throw (IO.userError s!"failed with {repr e.kind}, expected tooManyDigits")
      | .ok _ => throw (IO.userError "accepted, but the digit limit should have stopped it") },
  { name := "invalid UTF-8 bytes are refused"
    run :=
      match Json.parseBytes ⟨#[0x22, 0xFF, 0x22]⟩ with
      | .error e =>
        if e.kind == .invalidUtf8 then pure ()
        else throw (IO.userError s!"failed with {repr e.kind}, expected invalidUtf8")
      | .ok _ => throw (IO.userError "accepted invalid UTF-8") }
]

/-! ## Properties -/

-- Generators build text that is well formed by construction. Assembling input from random
-- characters, or even from random tokens, produces something parseable so rarely that the
-- properties pass without ever reaching the code they are meant to exercise: a token-based
-- version of the duplicate-name property below passed against a parser with its duplicate check
-- disabled.

/-- An object over a three-name alphabet, so that repeated names arise often. -/
private def objectText (ks : List Nat) : String :=
  "{" ++ String.intercalate "," (ks.map fun k => s!"\"k{k % 3}\":1") ++ "}"

private def hasDup : List Nat → Bool
  | [] => false
  | x :: rest => rest.contains x || hasDup rest

/-- Numerals of assorted shapes, including trailing zeros, so canonicalisation is exercised. -/
private def numberText (n : Nat) : String :=
  match n % 6 with
  | 0 => "0"
  | 1 => "-0"
  | 2 => s!"{n}"
  | 3 => s!"{n}.500"
  | 4 => s!"-{n}e{n % 5}"
  | _ => s!"{n}0"

private def arrayText (ns : List Nat) : String :=
  "[" ++ String.intercalate "," (ns.map numberText) ++ "]"

/-- Under the strict default, an object is accepted exactly when its names are distinct. -/
abbrev strictRejectsExactlyDuplicates : Prop :=
  NamedBinder "ks" <| ∀ ks : List Nat,
    (Json.parse (objectText ks)).toOption.isSome = !hasDup (ks.map (· % 3))

/-- Whatever strict parsing accepts has no repeated name anywhere, which is D6's purpose. -/
abbrev strictParseHasUniqueKeys : Prop :=
  NamedBinder "ks" <| ∀ ks : List Nat,
    (match Json.parse (objectText ks) with
      | .ok j => uniqueKeys j
      | .error _ => true) = true

/-- Permissive parsing keeps every member, in order, duplicates included. -/
abbrev allowKeepsEveryMember : Prop :=
  NamedBinder "ks" <| ∀ ks : List Nat,
    (match Json.parse (objectText ks) { duplicateKeys := .allow } with
      | .ok (.obj fields) => fields.size == ks.length
      | _ => false) = true

/-- Every number the parser produces is in canonical form, as D2 requires. -/
abbrev parsedNumbersAreCanonical : Prop :=
  NamedBinder "ns" <| ∀ ns : List Nat,
    (match Json.parse (arrayText ns) with
      | .ok j => canonicalNumbers j
      | .error _ => false) = true

def all : Array TestCase :=
  accepted ++ rejected ++ messages ++ adversarial ++ #[
    property "strict parsing accepts exactly the objects with distinct names"
      strictRejectsExactlyDuplicates,
    property "strict parsing yields unique keys" strictParseHasUniqueKeys,
    property "permissive parsing keeps every member" allowKeepsEveryMember,
    property "parsed numbers are canonical" parsedNumbersAreCanonical
  ]

end Test.Parser
