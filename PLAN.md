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

   As of Phase 2 this holds for the default path but not universally. `beq`, `hash` and
   `uniqueKeys` recurse, and what protects them is `maxDepth`: a value obtained from `parse`
   under the default configuration is depth-bounded, so recursing over it cannot overflow. A
   value built programmatically, or parsed with `maxDepth := none`, can be arbitrarily deep,
   and those three are then at risk. Replacing them with work-stack versions is tracked in
   section 12, and no downstream statement changes when they are, because every theorem is
   stated about `=` rather than about `beq`.
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
| `toJson (1e-300 : Float)` | Silently becomes `0`, as does every value below about `1e-7`. The encoder parses `Float.toString`, which is fixed point, so the digits are simply not there. The same path calls `panic!` if the parse ever fails. |
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
  `hash` all coincide with numeric value *on canonical values*, which is everything the parser
  produces. Numeric equivalence is a separate `Prop`, `Eqv`, with
  `Canonical a → Canonical b → (Eqv a b ↔ a = b)` as the theorem that justifies the whole
  arrangement. An unlawful numeric `BEq` was rejected: it would make every theorem, which is
  stated with `=`, stop covering the `==` that callers use.
  `LawfulBEq Number` holds unconditionally, since `==` comes from the derived `DecidableEq`.
  **`LawfulEqCmp` does not hold and no such instance is declared**: `Ord` compares numerically,
  so `⟨15,1⟩` and `⟨150,2⟩` compare equal while differing structurally. D2 makes non-canonical
  values representable, so no numeric-order `Ord` can be lawful, and claiming otherwise would
  reproduce exactly the incoherence found in `Lean.Data.Json`. What is proved instead is
  `cmp a b = .eq ↔ Eqv a b` unconditionally, plus the canonical corollary
  `Canonical a → Canonical b → (cmp a b = .eq ↔ a = b)`.
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
- **D24. The codec classes live in the `Json` namespace,** as `Json.ToJson` and
  `Json.FromJson`, rather than at the top level. `open Json` gives the familiar spelling, and
  a file that also uses core's classes can still name both.
- **D25. `toInt?` and `toNat?` bound the padding, not the digit count.** The cost worth
  refusing is the one a short text can inflict, `1e1000000000` being twelve characters and an
  integer of a billion digits; a mantissa that is long in itself has already been paid for by
  whoever holds it. The parameter is `maxPadding`, still defaulting to 1000, and the change is
  what lets `fromJson? (toJson n) = .ok n` be a theorem rather than a hope.
- **D26. `Float` is converted exactly, through its bits, not through its printed form.** A
  `Float` is `m * 2 ^ e`, and `2 ^ e = 5 ^ -e * 10 ^ e` for negative `e`, so every one of them
  has a finite decimal expansion that costs one bignum multiply to compute. Going through
  `Float.toString` instead is what makes core turn `1e-300` into `0`. The price is length,
  around fifty significant digits where a shortest spelling would use seventeen, and a few
  hundred for a subnormal. NaN and the infinities keep the customary `"NaN"`, `"Infinity"` and
  `"-Infinity"` strings, since JSON has no other way to carry them.
- **D27. Nothing in the codecs may panic, so `setObjValAs!` becomes `setObjValAs?`,** and the
  field names `parseTagged` and `parseCtorFields` take are `String`s rather than `Name`s, the
  latter being out of reach under constraint 3.

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
Json/Printer.lean        compress, pretty, escaping, number rendering
Json/FromTo.lean         ToJson / FromJson classes, instances, helpers
Json/Query.lean          total accessors, path lookup, merge, update
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

**Input representation, and a measured cost.** The machine scans a `List Char`, which mirrors
`Spec` exactly and so keeps the soundness proof within reach. It is paid for in memory: `parse`
converts the whole text up front, and a 20MB document was measured at 734MB peak resident, about
37 bytes per character. Throughput is 3.4x slower than `Lean.Data.Json` on the same 3.4MB document,
284ms against 83ms, and scales linearly. The behaviour on adversarial nesting is right, ten million
deep yielding `depthExceeded` in 619ms where core aborts, but the amplification is itself a denial
of service vector on large bodies and has to go before v1. The fix is to scan the `String` by
index rather than convert it, which changes no theorem statement, since every statement is written
against `Spec` rather than against the scanner.

`Config` carries `duplicateKeys := .reject`, `maxDepth := some 1024`,
`maxNumberDigits := some 1000`, and BOM handling, which ignores a leading `U+FEFF` per D18.
Both limits accept `none`, which is safe because the parser is stack-safe by construction, and
the quadratic cost of an unbounded significand is documented rather than hidden. Errors are
structured, `{ byteOffset : Nat, kind : ErrorKind }`, with line and column derived on demand.

Bounded-work guards: `maxNumberDigits`, because building an `Int` from a 100MB digit run is
quadratic; `maxDepth`, as a real error rather than a crash; and a `Std.HashSet String` above a
size threshold for duplicate detection, so adversarially wide objects stay linear.

## 7. Printer

`compress` and `pretty` share one explicit work-stack traversal, `render`, over a list of
`Item`s: literal text, a value at a depth, or the remaining elements or members of a container
that has been entered. Every step retires one item and pushes at most two smaller ones, so the
termination measure decreases locally and nesting costs heap rather than C stack. Output
accumulates in a `String`, which makes UTF-8 validity a property of the type rather than
something to maintain by hand.

Number rendering expands to plain decimal only while the padding stays within
`plainZeroLimit`, and otherwise emits exponent notation, so `⟨1,2⟩` renders as `100` while
`⟨1,1000000000⟩` renders as `1e1000000000`. Round tripping holds either way, since both
spellings normalise back to the same canonical value.

**Two descriptions of the same text.** The work stack is what keeps printing safe, but it
relates output to input only through a loop invariant. So the text is described a second time
by structural recursion on the value, `chars`, and the two are proved equal:
`(render st items acc).toList = acc.toList ++ itemsChars st items`. The grammar theorems are
then stated about `chars`, where induction follows the shape of the value. The reference
version is proof-only and never runs, which is just as well, since it is the C-stack recursion
the printer exists to avoid.

## 8. Specification and theorems

`Json/Spec.lean` transcribes the RFC 8259 ABNF, written to be read against the RFC rather than to
suit the parser. Two choices made when it was written:

**The alphabet is `Char`, not `UInt8`.** The RFC states the string productions in code points, and
D10 means the byte level is already covered by a verified decoder, so the spec stays at the level
the RFC is written in and the `ByteArray` entry point composes `String.fromUTF8?` in front of it.
A welcome consequence: D8 stops being a rule imposed on the grammar and becomes a property of the
alphabet, since no `Char` carries a surrogate code point, so a lone `\uD800` escape denotes
nothing. That is one of the two rejection proofs in the tests.

**Each relation threads a remainder**, as `Value : List Char → Json → List Char → Prop`, rather
than using existentially quantified concatenations. It makes both construction and inversion
tractable. It also means the relations are deliberately *not* deterministic in that remainder,
exactly as the ABNF is not: `12` derives as `1` with `2` left over. Determinism is a property of
`Text`, where the remainder must be empty, and proving it is the outstanding Phase 3 item.

```lean
-- soundness: no false accepts, in every mode. Stated modulo the BOM, per D18,
-- since the grammar has no BOM production
parse cfg s = .ok j → Spec.Text (stripBOM s).toList j

-- completeness, per duplicate-key policy. v2, per D14
Spec.Value bs j → parse .allow bs = .ok j
Spec.Value bs j → UniqueKeys j  → parse .reject bs = .ok j
Spec.Value bs j → ¬UniqueKeys j → (parse .reject bs).isError

-- the grammar transcription is unambiguous, which validates the spec itself
Spec.Value bs j₁ → Spec.Value bs j₂ → j₁ = j₂

-- output is always well formed, and always valid UTF-8. Proved
CanonicalNumbers j → Spec.TextOf (compress j) j
CanonicalNumbers j → Spec.TextOf (pretty j indent) j
s.toByteArray.IsValidUTF8

-- round trip, for both compress and pretty. Waits on completeness, so property-tested
CanonicalNumbers j → parse cfg (render j) = .ok j

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

- [x] `Number`: `toString`, `Ord`, `Neg`, `OfScientific`, `OfNat`, shifts, `toFloat`,
      `ofFloat?`, bounded `toInt?` / `toNat?`
- [x] `Json`: `DecidableEq`, `Hashable`, `Inhabited`, `Repr`, coercions, `mkObj`, `isNull`
- [ ] Accessors: `getObj?`, `getArr?`, `getStr?`, `getNat?`, `getInt?`, `getBool?`, `getNum?`,
      `getObjVal?`, `getArrVal?`, `getObjValD`, `setObjVal`, `mergeObj`, `Structured`
- [x] `parse`, `parseBytes`
- [x] `compress`, `pretty`, `escape`, `renderString`, `ToString`
- [x] `FromJson` / `ToJson` plus instances: `Json`, `Number`, `Unit`, `Empty`, `Bool`, `Nat`,
      `Int`, `String`, `String.Slice`, `FilePath`, `Array`, `List`, `Option`, `Prod`, `USize`,
      `UInt64`, `Float`, `Structured`, `Std.TreeMap String`
- [x] Helpers: `getObjValAs?`, `setObjValAs?`, `opt`, `getTag?`, `parseTagged`,
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

Two practical notes from Phase 1. `decide` cannot evaluate anything defined by well-founded
recursion, since such definitions do not reduce in the kernel, but `simp` with the generated
equation lemmas can, so concrete input and output claims still reach theorem strength rather
than falling back to runtime checks. And properties want their generators checked: the first
version of the `isLt` property passed against a deliberately broken mantissa alignment, because
independently drawn exponents almost never place two numbers at the same leading digit position.
Every property should be confronted with a mutation it ought to catch.

**No property is trusted until a mutation has failed it.** That rule has now caught three
useless properties. In Phase 1 the `isLt` property was blind to a broken alignment; in Phase 4
the first duplicate-name property was assembled from random tokens and passed against a parser
whose duplicate check had been deleted, because random tokens form parseable JSON far too rarely
to reach the check; in Phase 5 the round-trip properties survived a printer that put the decimal
point in the wrong place, because the generated numbers almost never had more digits than the
exponent asked for, so the branch that positions the point was hardly ever reached. The Phase 6
float property had the same shape of hole, caught before it could hide anything: a bit pattern
taken from a small natural has a zero exponent field, so every value drawn was subnormal and no
ordinary number was ever tested. Generators
must build well-formed input by construction, draw from an alphabet small enough that the
interesting collisions occur, and be shaped so that every branch of the code under test is
reachable. The mutation test is what demonstrates they are.

The rule extends to proofs, where it answers a different question: not whether the property has
teeth, but whether the theorem constrains the implementation that ships. Breaking `render` so
that `true` prints as `TRUE`, and `escapeCharTo` so that a backspace escapes as `\B`, each
fails a proof rather than a test, which is the evidence that the structural description the
grammar theorems talk about is tied to the traversal that actually runs.

## 12. Deferred

No open questions. Work deliberately postponed:

- **Completeness proofs**, per D14. Until they land, the claim "no false rejects" rests on the
  corpus rather than on proof, and the README must say so.
- **Subquadratic digit conversion.** A divide-and-conquer `Int`-from-digits conversion would
  let `maxNumberDigits := none` be the default rather than a documented hazard, retiring D21.
- **Reference-counted teardown of deeply nested values,** which is a runtime recursion risk
  that no theorem of ours covers. Phase 9 establishes empirically whether it bites.
- **Work-stack versions of `beq`, `hash` and `uniqueKeys`,** so that stack safety no longer
  depends on the parser's depth bound. See the note under constraint 4.
- **Proofs for `dedupKeys`,** which want a small library of `Array.foldl` characterisation
  lemmas that would also serve the parser and printer proofs.
- **Index-based scanning in the parser,** to remove the 37x memory amplification measured in
  section 6. This is a v1 blocker, not a nicety.

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
- [x] `Number`, `Canonical`, `Eqv`, `scaleTo`
- [x] `Canonical a → Canonical b → (Eqv a b ↔ a = b)`
- [x] `Eqv` is an equivalence relation, and decidable via `eqv_iff_normalize_eq`
- [x] `normalize`, with `Canonical (normalize m e)` and `Eqv (normalize m e) ⟨m, e⟩`
- [x] Constructors: `ofInt`, `ofNat`, `OfNat`, `OfScientific`, `Neg`, `mulPow10`, each with its
      canonicity lemma
- [x] `Ord` in O(digits), with the equality case proved exact and `LawfulBEq` confirmed. See the
      revision to D3: `LawfulEqCmp` is unattainable and is not claimed
- [x] Bounded conversions: `toInt?`, `toNat?`, `toFloat`, all guarded against exponent expansion
- [x] `toString`, landed in Phase 5 where the rendering rule belongs
- [x] `ofFloat?`, landed in Phase 6. It wants no parser after all: reading the IEEE fields is
      both exact and cheaper than reading back a printed decimal, per D26
- [ ] The scale comparison inside `isLt` is covered by two properties rather than proved. Closing
      it needs digit-count bounds, `10 ^ (digitCount m - 1) ≤ m.natAbs < 10 ^ digitCount m`

**Phase 2. Core type**
- [x] `Json`, coercions, `mkObj`, `isNull`
- [x] `beq` with `beq a b = true ↔ a = b` proved, giving `DecidableEq`, `BEq` and `LawfulBEq`.
      No deriving handler applies to either nested `Array` position, so equality, hashing and the
      key check are each a mutual group over `List`
- [x] `Hashable`
- [x] `uniqueKeys` and `UniqueKeys`, recursive through the whole value
- [x] Total accessors, `getObjVal?` resolving duplicates last-wins, `setObjVal?` replacing in
      place, `mergeObj` via `dedupKeys`
- [ ] `dedupKeys` correctness is covered by three properties, not proved. Both claims need a
      characterisation of `findLast?` over `Array.foldl` first, and there is no lemma library for
      array folds to build on yet
- [ ] Stack-safe traversal primitive. See the note on constraint 4 below; the termination lemma it
      needs, `(l.map sizeOf).sum < sizeOf l`, is proved out and ready to use

**Phase 3. Specification**
- [x] Every production of RFC 8259 section 2 transcribed: `Ws`, `Token`, `Digits`, `Int'`,
      `Frac`, `Exp`, `Sign`, `Num`, `Hex4`, `Ch`, `Chars`, `Str`, `Value`, `Arr`, `Elements`,
      `Object`, `Members`, `Member`, and `Text`
- [x] Eleven derivations built by hand as validation, covering whitespace, both number forms,
      escapes, a surrogate pair, empty and populated arrays and objects, and nesting
- [x] Two rejection proofs, that `"\ud800"` and `01` denote nothing, with the three inversion
      lemmas they need
- [ ] Unambiguity theorem. See the note below on why the relation is deliberately not
      deterministic in its remainder

**Phase 4. Parser**
- [x] `Config` (duplicate keys, `maxDepth`, `maxNumberDigits`, BOM), structured `Error` with a
      character offset, and `ErrorKind`
- [x] Leaf scanners: whitespace, strings with escapes and surrogate pairs, and numbers, each
      carrying its own consumption proof so termination needs no separate lemmas
- [x] The machine: `value`, `continueWith` and `member` over an explicit `Frame` stack, so nesting
      costs heap rather than C stack
- [x] `parse` and `parseBytes`, the latter enforcing RFC 8259 section 8.1 through
      `String.fromUTF8?`
- [x] Depth, digit-count and duplicate-name guards, each with a test
- [x] 68 behavioural tests: 26 accepted, 29 rejected, 5 adversarial, 4 properties, the last of
      these each confirmed by a mutation that ought to fail it
- [ ] Soundness against `Spec`. This needs an invariant relating a machine state, meaning the
      frame stack plus the remaining text, to a partial derivation. The leaf scanners can be
      proved sound first and independently, which is where to start
- [ ] `CanonicalNumbers` and `UniqueKeys` of parser output are property-tested, not proved. Both
      follow from the machine invariant above, so they are the same piece of work

**Phase 5. Printer**
- [x] `Number.toString`, `escape`, `renderString`, `compress`, `pretty`, `ToString` for both
      types, over one work-stack traversal
- [x] Agreement between that traversal and a structural description of the same text, so the
      grammar theorems can be proved by induction on the value
- [x] Well-formedness, proved: `CanonicalNumbers j → Spec.TextOf (compress j) j`, and the same
      for `pretty`, by way of `Spec.Num`, `Spec.Str` and the whitespace and token productions.
      The digit machinery goes through a `digitsValue` characterisation of a run of digit
      characters, which turns the fraction split into `digitsValue (l₁ ++ l₂)` arithmetic
- [x] UTF-8 validity, from `String.utf8Encode_toList`: the output is a `String`, so its bytes
      are the UTF-8 encoding of its characters and RFC 8259 section 8.1 holds by construction
- [x] 34 behavioural tests: number rendering by branch, escaping, layout for both forms, a
      100,000 deep value printed without a crash, and three round-trip properties, each
      confirmed by a mutation that ought to fail it
- [ ] Round tripping stays a property rather than a theorem, since `parse (render j) = .ok j`
      needs parser completeness, which is deferred per D14. Well-formedness is the half that
      does not depend on it

**Phase 6. Codecs**
- [x] `ToJson` / `FromJson` in the `Json` namespace, per D24, with instances for `Json`,
      `Number`, `Bool`, `String`, `String.Slice`, `Nat`, `Int`, `Unit`, `Empty`, `FilePath`,
      `Array`, `List`, `Option`, `Prod`, `USize`, `UInt64`, `Float`, `Structured` and
      `Std.TreeMap String`
- [x] `Number.ofFloat?`, exact by way of the IEEE fields, per D26, with `Canonical` proved of
      its result
- [x] Helpers: `getObjValAs?`, `setObjValAs?`, `opt`, `getTag?`, `parseTagged`,
      `parseCtorFields`, `bignumToJson`, `bignumFromJson?`, `decodeNat?`, `toStructured?`
- [x] Round trips proved for `Json`, `Number`, `Bool`, `String` and `Unit`, and for `Int` and
      `Nat` under the padding bound of D25. `Option` and `Prod` are proved from the round trips
      of what they contain, `Option` needing the value not to encode as `null`, which is what
      `Option (Option α)` violates
- [x] 54 tests: encodings, decoding failures, the helpers, the float edge cases that core loses,
      and five properties, each confirmed by a mutation that ought to fail it
- [ ] `Array` and `List` round trips are property-tested, not proved: the instances go through
      `Array.mapM`, and there is no characterisation of it to induct on yet

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
