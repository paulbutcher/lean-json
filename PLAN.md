<!-- Copyright (c) 2026 Paul Butcher. All rights reserved.
     Released under Apache 2.0 license as described in the file LICENSE. -->

# Plan

A formally verified JSON library for Lean 4, providing the functionality of
`Lean.Data.Json` but built to be total and safe, verified against RFC 8259, resistant to
adversarial input, and incapable of emitting malformed output.

This document tracks decisions and progress. Decisions are append-only: when one changes,
supersede it rather than editing history. Check items off in the build order as they land.

## 1. Hard constraints

1. **Standalone.** The library may depend on `Init` and `Std`. It may not depend on
   anything in the `Lean` namespace.
2. **Nothing from the `Lean` package may be linked into a consumer's binary.** On Linux the
   frontend is not separable at link time, since `libleanshared.so` bundles `Init`, `Std`,
   and `Lean` together. The checkable form of this constraint is therefore: the non-`meta`
   import closure of the library contains no `Lean.*` module. Using `meta import` makes this
   machine-enforced, because declarations from a meta import may only be used in meta
   contexts. CI additionally lints for non-meta `import Lean`.
3. **Total and non-panicking.** No `partial`, no `sorry`, no functions that can panic.
   Warnings are errors.
4. **Stack safety by construction.** Every operation whose input can be deeply nested uses
   an explicit heap-allocated work stack, never recursion on the C stack.
5. **New module system.** Both packages use `module` with explicit `public import` /
   `meta import`. This is what gives constraint 2 its teeth.

Proof automation is unaffected by constraint 1: `omega`, `grind`, `simp`, and `decide` all
reach us from `Init` without any `Lean.*` import. There is no Mathlib, so numeric lemmas are
built from `Init`/`Std` plus automation.

## 2. Failure modes we are fixing

Measured against `Lean.Data.Json` on Lean v4.33.0. Each becomes a regression test.

| Input | Behaviour |
|---|---|
| `[` x 10,000,000 then `]` x 10,000,000 | `Stack overflow detected. Aborting.`, SIGABRT, exit 134. Uncatchable. 1,000,000 deep survives, so the cliff depends on available stack. |
| `1e1000000000` | Hangs. `JsonNumber.shiftl` evaluates `10 ^ 1000000000` into a bignum. |
| `"\ud800"` | Silently becomes `U+FFFD`. Data corruption with no error. |
| `{"a":1,"a":2}` | Silently last-wins, with no option to reject. |
| any object | Key order lost, since the payload is a `Std.TreeMap.Raw`. |
| deeply nested value | `render` and `pretty` are `partial` and recursive, so output overflows even when parsing survived. `compress` is already iterative. |
| `setObjVal!` on a non-object | Panics. |
| `⟨15,1⟩` vs `⟨150,2⟩` | `==` is `false` while `compare` is `.eq`, and the hashes differ. Incoherent `BEq`/`Ord` pair on one type. |

The duplicate-key case is not academic: a 2017 CouchDB RCE arose because JavaScript and
Erlang parsers resolved duplicate keys differently, so one saw `"roles": []` where the other
saw `"roles": ["_admin"]`.

## 3. Settled decisions

- **D1. Numbers are canonical decimals, `mantissa * 10 ^ exponent`, with `exponent : Int`
  never evaluated as a power.** Constant-time handling of `1e1000000000`, and the exponent
  bomb becomes unreachable. Powers of ten appear only in `Prop` (free, never computed) and in
  explicitly opt-in bounded conversions.
- **D2. Canonicity is carried by a predicate, not by a subtype.** `Number` stays a plain
  structure; `Canonical` is an ordinary `Prop`; the parser is proved to produce canonical
  values. Round-trip theorems take `Canonical` as a hypothesis, discharged from
  `Canonical (parse t)`.
- **D3. Structural equality is the only equality.** With D1 and D2, `=`, `==`, `compare`, and
  `hash` all coincide with numeric value, so `LawfulBEq` and `LawfulEqCmp` hold. Numeric
  equivalence is a separate `Prop`, `Eqv`, with `Canonical a → Canonical b → (Eqv a b ↔ a = b)`
  as the theorem that justifies the whole arrangement. An unlawful numeric `BEq` was rejected:
  it would make every theorem, which is stated with `=`, stop covering the `==` that callers use.
- **D4. No text-exact round tripping.** Value-level fidelity only. `-0` normalises to `0`,
  `1.50` to `1.5`, and `100` and `1e2` to the same value. Consequence to keep in view:
  `{"a":0,"a":-0}` becomes an exact same-key-same-value duplicate.
- **D5. Objects are `Array (String x Json)`,** order-preserving and duplicate-representable,
  so the AST is a faithful image of the text and the round-trip theorem is an identity.
- **D6. The parser rejects duplicate keys by default,** with `.allow` available in `Config`.
  This follows `encoding/json/v2` (rejects by default) and .NET 10's `Strict` preset, and it
  buys the theorem `UniqueKeys (parse .reject t)`. Lookup on hand-built or permissively parsed
  values is last-wins, matching ECMA-262 and every mainstream library.
- **D7. Duplicate detection compares bytes, never Unicode normal forms.** `{"é":1,"é":2}`
  with one key in NFC and one in NFD is two distinct keys.
- **D8. Unpaired surrogates are a parse error.** Lean's `String` cannot represent them, and
  silent replacement corrupts data. Keeping `String` as the string type also keeps the
  round-trip theorem unconditional.
- **D9. `String` is the primary input type, `ByteArray` a validating wrapper.** In v4.33
  `String` is a `ByteArray` plus an `IsValidUTF8` proof, so `parse (s : String)` needs no
  validation pass, and `parseBytes b` is `String.fromUTF8? b` followed by `parse`. RFC 8259
  section 8.1 is thereby enforced by a verified core component.
- **D10. We write no UTF-8 codec.** `Init/Data/String/Decode.lean` provides a verified one:
  `ByteArray.utf8DecodeChar?` and `ByteArray.validateUTF8` reject overlong encodings and
  surrogate code points explicitly, with round-trip, validation-agreement, and locality lemmas
  already proved. `ByteArray.IsValidUTF8` plus its append lemmas give us "output is always a
  valid `String`" by construction.
- **D11. Our own pretty-printing layout engine.** `Std.Format` is reachable without `Lean`,
  but `Format.be` is `partial` and recursive, so it is both unverified and a deep-nesting
  hazard. A `Std.ToFormat Json` instance may still be offered as interop.
- **D12. Derivation and `json%` live in a companion package.** Deriving handlers need
  `Lean.Elab.Deriving`, and core's `json%` needs `Lean.Syntax`. The companion uses
  `public meta import`, so nothing from the `Lean` package reaches a consumer's binary. The
  runtime helpers those handlers generate calls to (`parseTagged` and friends) stay here.
- **D13. `Name` and `NameMap` instances are out of scope,** their types being in the `Lean`
  namespace. `setObjVal!` is replaced by a total `setObjVal`.
- **D14. Completeness does not gate v1.** Soundness, round tripping, and well-formedness are
  proved for v1; the per-policy completeness theorems in section 8 are covered by the corpus
  for v1 and proved in v2.
- **D15. Whole-buffer parsing, plus `IO.FS.Stream` helpers.** No resumable or incremental
  parser, so the parser interface stays a single call over a complete input, with `readJson`
  and `writeJson` layered on top.
- **D16. The conformance corpus is vendored,** so tests need no network. It lives under
  `test/`, keeping it out of a consumer's dependency graph, with its licence and attribution
  recorded alongside it.
- **D17. Correctness first.** Benchmarks track regressions rather than gate releases, and
  nothing is written in an aggressive style if that makes it materially harder to prove.
- **D18. A leading `U+FEFF` byte order mark is ignored,** which RFC 8259 permits for
  non-networked text. This has a consequence for section 8: soundness is stated modulo BOM
  stripping, because `Spec.Value` transcribes the grammar and the grammar has no BOM
  production.
- **D19. The data model and its cheap total operations are `@[expose]`d,** so consumers can
  `simp` and `decide` on concrete `Json` and `Number` values. Parser and printer internals stay
  unexposed, so consumers work through the theorems and we stay free to rewrite.
- **D20. `maxDepth` defaults to `some 1024`, and `none` is permitted.** For comparison, .NET
  allows 64, serde_json 128, and Jackson 1000, but all three limits exist because those parsers
  recurse on the stack. Ours does not, so for us depth is a policy and memory guard rather than
  a crash guard, and we can offer genuinely unbounded depth where they cannot.
- **D21. `maxNumberDigits` defaults to `some 1000`,** matching Jackson's `maxNumberLength`, with
  `none` permitted at a documented quadratic cost, since building an `Int` digit by digit is
  O(n²). The limit applies to the significand only, the exponent being unbounded by D1. No
  string-length limit is needed, because string handling is linear.
- **D22. The companion package is `deriving/` in this repository,** package `jsonDeriving`,
  module `Json.Deriving`, consumed as
  `require jsonDeriving from git "..." @ "..." / "deriving"`, which Lake supports. One
  repository keeps the two versions in lockstep, mirroring the arrangement already used for
  `test/`.
- **D23. Pretty-printing defaults are a two-space indent, 80-column width, one space after
  `:`, and no spaces anywhere in `compress`.** Core's exact layout is not matched.

## 4. Data model

```lean
structure Number where
  mantissa : Int
  exponent : Int
deriving DecidableEq, Hashable, Repr, Inhabited

def Canonical : Number → Prop
  | ⟨0, e⟩ => e = 0            -- zero has exactly one spelling
  | ⟨m, _⟩ => m % 10 ≠ 0       -- mantissa carries no trailing zero

inductive Json where
  | null
  | bool (b : Bool)
  | num  (n : Number)
  | str  (s : String)
  | arr  (elems  : Array Json)
  | obj  (fields : Array (String × Json))
deriving DecidableEq
```

Normalisation happens on the digit text before the mantissa is built: one O(n) scan, no
bignum division and no exponentiation. `Ord` compares sign, then decimal scale, then aligned
mantissas, so the alignment factor is bounded by mantissa length and never by the exponent.

## 5. Module layout

```
Json/Basic.lean          Json, constructors, instances, UniqueKeys
Json/Number.lean         Number, Canonical, Eqv, Ord, bounded conversions
Json/Spec.lean           RFC 8259 grammar as an inductive Prop
Json/Parser.lean         iterative parser, Config, structured Error
Json/Parser/Lemmas.lean  soundness, completeness, UniqueKeys
Json/Printer.lean        compress, pretty, escaping
Json/Printer/Lemmas.lean well-formedness, round trip, UTF-8 validity
Json/Query.lean          total accessors, path lookup, merge, update
Json/FromTo.lean         ToJson / FromJson classes, instances, helpers
Json/Stream.lean         IO.FS.Stream helpers
test/                    own lakefile, requires root by path, plus plausible
deriving/                own lakefile, companion package, meta imports Lean
```

The companion holds only the deriving handlers and `json%`.

## 6. Parser

A state machine over a byte index with an explicit `Array Frame` stack, not a combinator
parser. Combinator recursion is what reaches SIGABRT in core, and it would also force a
well-founded recursion proof per combinator; one loop over remaining bytes gives termination
almost free and bounds depth by heap rather than stack.

`Config` carries `duplicateKeys := .reject`, `maxDepth := some 1024`,
`maxNumberDigits := some 1000`, and BOM handling, which ignores a leading `U+FEFF` per D18.
Both limits accept `none`, which is safe because the parser is stack-safe by construction, and
the quadratic cost of an unbounded significand is documented rather than hidden. Errors are
structured, `{ byteOffset : Nat, kind : ErrorKind }`, with line and column derived on demand.

Bounded-work guards: `maxNumberDigits`, because building an `Int` from a 100MB digit run is
quadratic; `maxDepth`, as a real error rather than a crash; and a `Std.HashSet String` above a
size threshold for duplicate detection, so adversarially wide objects stay linear.

## 7. Printer

`compress` and `pretty` share one explicit work-stack traversal. Output accumulates as bytes
with `IsValidUTF8` maintained alongside, so there is no unchecked construction step. Escaping
is table-driven over bytes.

Number rendering expands to plain decimal only while the digit count stays under a bound, and
otherwise emits exponent notation, so `⟨1,2⟩` renders as `100` while `⟨1,1000000000⟩` renders
as `1e1000000000`. Round tripping holds either way, since both spellings normalise back to the
same canonical value.

## 8. Specification and theorems

`Json/Spec.lean` transcribes the RFC 8259 ABNF as `Spec.Value : List UInt8 → Json → Prop`,
written to be read against the RFC rather than to suit the parser.

```lean
-- soundness: no false accepts, in every mode. Stated modulo the BOM, per D18,
-- since the grammar has no BOM production
parse cfg bs = .ok j → Spec.Value (stripBOM bs) j

-- completeness, per duplicate-key policy. v2, per D14
Spec.Value bs j → parse .allow bs = .ok j
Spec.Value bs j → UniqueKeys j  → parse .reject bs = .ok j
Spec.Value bs j → ¬UniqueKeys j → (parse .reject bs).isError

-- the grammar transcription is unambiguous, which validates the spec itself
Spec.Value bs j₁ → Spec.Value bs j₂ → j₁ = j₂

-- output is always well formed, and always a valid Lean String
Spec.Value (renderBytes j) j
(renderBytes j).IsValidUTF8

-- round trip, for both compress and pretty
Canonical j → parse cfg (render j) = .ok j

-- numbers
Canonical a → Canonical b → (Eqv a b ↔ a = b)
```

Note the per-policy split in completeness. RFC 8259 section 4 observes that implementations
may report an error on duplicate keys, while section 9 says a parser MUST accept all texts
conforming to the grammar, and `{"a":1,"a":2}` does conform. Strict mode is therefore
provably a restriction of the grammar rather than a defect, and unconditional completeness
belongs to `.allow`.

## 9. What we do not claim

- **Totality does not imply absence of stack overflow or OOM.** "Never crashes" is achieved by
  construction and evidenced by fuzzing, not proved. Reference-counted teardown of a deeply
  nested value is itself a runtime recursion risk and needs an empirical check.
- **`toFloat` is not verified against IEEE 754.**
- **Extern primitives are trusted at the usual level.** `String.toUTF8` is
  `@[extern "lean_string_to_utf8"]`, though proved equal to `toByteArray` by `rfl`. We
  introduce no new trust assumptions.
- **One conformance-corpus deviation by design.** `y_object_duplicated_key_and_value.json`
  (`{"a":"b","a":"b"}`) is a must-accept case that strict mode rejects. We run it in
  permissive mode and document the deviation.

## 10. Functionality parity

Tracked against `Lean.Data.Json` so that "same functionality" is checkable rather than
aspirational.

- [ ] `Number`: `toString`, `Ord`, `Neg`, `OfScientific`, `OfNat`, shifts, `toFloat`,
      `ofFloat?`, bounded `toInt?` / `toNat?`
- [ ] `Json`: `DecidableEq`, `Hashable`, `Inhabited`, `Repr`, coercions, `mkObj`, `isNull`
- [ ] Accessors: `getObj?`, `getArr?`, `getStr?`, `getNat?`, `getInt?`, `getBool?`, `getNum?`,
      `getObjVal?`, `getArrVal?`, `getObjValD`, `setObjVal`, `mergeObj`, `Structured`
- [ ] `parse`, `parseBytes`
- [ ] `compress`, `pretty`, `escape`, `renderString`, `ToString`
- [ ] `FromJson` / `ToJson` plus instances: `Json`, `Number`, `Unit`, `Empty`, `Bool`, `Nat`,
      `Int`, `String`, `String.Slice`, `FilePath`, `Array`, `List`, `Option`, `Prod`, `USize`,
      `UInt64`, `Float`, `Structured`, `Std.TreeMap String`
- [ ] Helpers: `getObjValAs?`, `setObjValAs`, `opt`, `getTag?`, `parseTagged`,
      `parseCtorFields`, `bignumFromJson?`, `bignumToJson`, `toStructured?`
- [ ] Stream helpers: `readJson`, `writeJson`
- [ ] Companion package: `deriving ToJson, FromJson`, `json%`

## 11. Testing

Tests live in `test/` with their own lakefile requiring the root by path, driven by a
`@[test_driver]` script in the root lakefile, so nothing test-only enters a consumer's
dependency graph. Strongest available form of each claim: theorem, then Plausible property,
then example. Theorems not needed by production code live in `test/`; compiling is passing.

Layers: the theorem set from section 8; properties for round tripping, parser and printer
agreement, and accessor laws; an accept/reject conformance corpus; fuzzing for the crash-freedom
claim that proofs cannot reach; and the regression cases from section 2.

## 12. Deferred

No open questions. Work deliberately postponed:

- **Completeness proofs**, per D14. Until they land, the claim "no false rejects" rests on the
  corpus rather than on proof, and the README must say so.
- **Subquadratic digit conversion.** A divide-and-conquer `Int`-from-digits conversion would
  let `maxNumberDigits := none` be the default rather than a documented hazard, retiring D21.
- **Reference-counted teardown of deeply nested values,** which is a runtime recursion risk
  that no theorem of ours covers. Phase 9 establishes empirically whether it bites.

## 13. Build order

**Phase 0. Scaffolding**
- [x] `LICENSE`, Apache 2.0
- [x] Root lakefile: module-system library, `@[test_driver]` script spawning `test/`
- [x] `test/` subproject lakefile requiring the root by path, plus `plausible` pinned at its
      `v4.33.0` tag
- [x] Minimal test harness: `TestCase`, `runAll`, `expect`, `expectEq`, and the `Test.all`
      array each test module contributes to
- [x] CI: `lake build` and `lake test`, warnings as errors, lint for `import Lean`

**Phase 1. Numbers**
- [ ] `Number`, `Canonical`, `Eqv`, normalisation from digit text
- [ ] `Canonical a → Canonical b → (Eqv a b ↔ a = b)`
- [ ] `Ord` in O(digits), `LawfulEqCmp`, `Hashable` coherence
- [ ] Bounded conversions and their guards

**Phase 2. Core type**
- [ ] `Json`, instances, coercions, `UniqueKeys`
- [ ] Total accessors and `mergeObj`, last-wins lookup with its agreement-with-dedup proof
- [ ] Stack-safe traversal primitive that later phases build on

**Phase 3. Specification**
- [ ] `Spec.Value` transcribed from the ABNF
- [ ] Unambiguity theorem

**Phase 4. Parser**
- [ ] `Config`, `Error`, the state machine, `parse` and `parseBytes`
- [ ] Soundness, `Canonical`, `UniqueKeys`
- [ ] Depth, digit-count, and duplicate-detection guards

**Phase 5. Printer**
- [ ] `compress`, `pretty`, escaping, number rendering
- [ ] Well-formedness, UTF-8 validity, round tripping for both forms

**Phase 6. Codecs**
- [ ] `FromJson` / `ToJson`, instances, helpers, `parseTagged` and friends

**Phase 7. Ergonomics**
- [ ] `Query`, path lookup, updates
- [ ] `IO.FS.Stream` helpers

**Phase 8. Assurance**
- [ ] Vendor the conformance corpus under `test/`, with licence and attribution, and record
      the documented strict-mode deviation
- [ ] Fuzzing, including nesting depth, wide objects, huge numbers, invalid UTF-8
- [ ] Regression cases from section 2, including the teardown check from section 9

**Phase 9. Companion package**
- [ ] `deriving/` subproject, `deriving ToJson, FromJson`
- [ ] `json%`
- [ ] Test that a consumer's binary links nothing from the `Lean` package

**Phase 10. Release**
- [ ] Benchmarks, as regression tracking rather than a gate
- [ ] README, including the duplicate-key default and its rationale, and the completeness
      caveat from section 12
- [ ] Doc strings across the public surface

**Post-v1**
- [ ] Completeness theorems, per D14

## 14. References

- RFC 8259, The JavaScript Object Notation (JSON) Data Interchange Format
- RFC 7493, The I-JSON Message Format, which forbids duplicate names outright
- Parsing JSON is a Minefield, <https://seriot.ch/security/parsing_json.html>
- JSONTestSuite, <https://github.com/nst/JSONTestSuite>
- Go `encoding/json/v2`, which rejects duplicate names by default,
  <https://pkg.go.dev/encoding/json/v2>
- `JsonSerializerOptions.AllowDuplicateProperties` and the .NET 10 `Strict` preset
- `Init/Data/String/Decode.lean` in the Lean toolchain, the verified UTF-8 codec
- Limit precedents for D20 and D21: Jackson `StreamReadConstraints`, with `maxNestingDepth`
  1000 and `maxNumberLength` 1000, <https://github.com/FasterXML/jackson-core/wiki/StreamReadConstraints>;
  `System.Text.Json` `MaxDepth` 64; serde_json's recursion limit of 128, with an
  `unbounded_depth` opt-out
