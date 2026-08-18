# json

A JSON library for Lean 4, written to be safe on input it did not choose.

Nothing in it is `partial`, nothing in it can panic, and nothing in it walks a value on the C
stack: reading, writing, comparing, hashing and measuring all keep their work on the heap, so a
document that nests a million deep is an error or a long string rather than a crash. The grammar
of RFC 8259 is transcribed in `Json.Spec`, and both directions are proved against it: whatever
the printer emits, the grammar accepts; whatever the parser accepts, the grammar derives.

The library depends on `Init` and `Std` and on nothing in the `Lean` namespace, so a program that
reads and writes JSON does not carry the Lean frontend with it. `deriving ToJson, FromJson` and
the `json%` literal syntax need the frontend to elaborate, so they live in a companion package
that meta imports it, which keeps them out of what a program links.

## What it fixes

Measured against `Lean.Data.Json` on Lean v4.33.0. Each row is a regression test here.

| Input | There | Here |
|---|---|---|
| `[` a million times | `Stack overflow detected`, SIGABRT, uncatchable | an error, or a value if the limit is lifted |
| `1e1000000000` | hangs, computing ten to the billionth | read in constant time, the exponent never applied |
| `"\ud800"` | silently becomes `U+FFFD` | refused: no sequence of code points denotes it |
| `{"a":1,"a":2}` | silently last-wins, with no way to refuse | refused by default, permitted by configuration |
| any object | field order lost | field order preserved, duplicates representable |
| a deeply nested value, printed | overflows, both printers being recursive | printed iteratively |
| `setObjVal!` on a non-object | panics | `setObjVal?` returns an error |
| `toJson (1e-300 : Float)` | silently becomes `0` | exact, from the IEEE fields |
| `⟨15,1⟩` against `⟨150,2⟩` | `==` and `compare` disagree | one canonical spelling, so they cannot |

## Using it

```lean
require json from git "https://github.com/paulbutcher/lean-json.git" @ "main"
```

```lean
import Json
open Json

#eval parse "{\"a\": [1, 2.5e3], \"b\": null}"
-- Except.ok (Json.obj #[("a", ...), ("b", Json.null)])

#eval (parse "[1,2]").toOption.map compress   -- some "[1,2]"
#eval (parse "[1,2]").toOption.map pretty     -- some "[\n  1,\n  2\n]"
```

Failures say what was wrong and where, as a sentence:

```lean
#eval (parse "{\"a\":1,\"a\":2}").toOption.isNone
-- true

#eval match parse "[1,]" with | .error e => toString e | .ok _ => "accepted"
-- "unexpected character ']' at byte 3"
```

Values are read and written through `ToJson` and `FromJson`, reached along a `Path`, and moved
over `IO.FS.Stream`:

```lean
#eval fromJson? (α := Array Nat) (toJson #[1, 2, 3])          -- Except.ok #[1, 2, 3]
#eval (parse "{\"a\":{\"b\":[7]}}").toOption.bind
  (·.get? [.field "a", .field "b", .index 0])                 -- some (Json.num ⟨7, 0⟩)
```

`Json.readJson`, `Json.readJsonToEnd`, `Json.writeJson` and `Json.writeJsonPretty` are the stream
helpers; reading enforces UTF-8 where the bytes arrive, as RFC 8259 section 8.1 requires.

## Deriving, and literal syntax

```lean
require jsonDeriving from git "https://github.com/paulbutcher/lean-json.git" @ "main" / "deriving"
```

```lean
import JsonDeriving
open Json

structure Point where
  x : Nat
  y : Nat
  label? : Option String        -- a trailing `?` makes the field optional
deriving ToJson, FromJson

#eval compress (toJson { x := 1, y := 2, label? := none : Point })   -- {"x":1,"y":2}
#eval compress (json% {here: $(({ x := 1, y := 2, label? := none } : Point)), ok: true})
```

Recursive types are derived too, through the type itself or an `Array`, `List` or `Option` of it.
Neither direction is `partial`: an encoder recurses on the value, which is structural, and a
decoder is given a count, seeded with the depth of the value it was handed. A field that mentions
its own type in some other shape, and a group of mutually defined types, are refused at derive
time with a message saying so, rather than derived as something that might not terminate.

## Defaults

Reading is strict by default. `Json.Config` relaxes any of it.

| Setting | Default | Why |
|---|---|---|
| `duplicateKeys` | `.reject` | see below |
| `maxDepth` | `some 1024` | policy, not a crash guard: `none` is safe here |
| `maxNumberDigits` | `some 1000` | building an integer from a digit run is quadratic |
| `ignoreBOM` | `true` | RFC 8259 permits ignoring a leading `U+FEFF` |

**Duplicate names are refused by default.** RFC 8259 leaves the outcome to the implementation,
which means two programs reading the same bytes can disagree about what they say. That is not
academic: a 2017 CouchDB privilege escalation came of a JavaScript parser and an Erlang parser
resolving a repeated name differently, so one saw `"roles": []` where the other saw
`"roles": ["_admin"]`. Pass `{ duplicateKeys := .allow }` to accept them, in which case every
member is kept, in order, and lookup takes the last.

The refusal of a lone surrogate is not configurable. `"\ud800"` denotes no sequence of code
points, so there is nothing to build.

## What is proved, and what is not

Proved:

- One text names at most one value: `Spec.text_unique`. That is a claim about the transcription
  rather than about the code, and it is the one that would catch a grammar saying more than the
  RFC does, which no proof about the parser or the printer can. With it, `Parser.eq_of_textOf`
  says the value the parser returns is the value the RFC names, there being no other.
- Whatever the parser accepts, the grammar derives: `parse s cfg = .ok j` gives
  `Spec.TextOf s j`, so no text is ever read as a value the RFC does not say it denotes. Leaves
  and machine alike are covered, the machine by way of `Closes`, which says what the frames still
  on the stack demand of the text that follows. A byte order mark the configuration says to
  ignore is no part of a text of the grammar, so it is set aside first, and `text_parse` says so
  rather than passing over it.
- Whatever the printer emits, the grammar accepts: `CanonicalNumbers j → Spec.TextOf (compress j) j`,
  and the same for `pretty`. The work-stack traversal that runs is proved equal to a structural
  description of the same text, and the grammar theorems are proved about that.
- Output is always valid UTF-8, by construction, since it is a `String`.
- Every walk of a whole value agrees with one that keeps its pending work in a list rather than
  on the stack, and it is the second that runs: `Alg.fold_eq_run`, with `beq`, `hash`,
  `uniqueKeys`, `canonicalNumbers` and `depth` each tied to their folded form. A claim stated
  about the plain recursion is therefore a claim about what the program does, at any depth.
- What a parse returns holds canonical numbers throughout, so `==`, `compare` and `hash` agree
  on everything it produces; and under the strict default no object in it repeats a field name.
  The first is a property of the grammar, which records what digits denote rather than how they
  were written; the second is a property of the machine, which carries the names it has seen.
- Numeric equality and structural equality coincide on canonical numbers, which is what that
  agreement rests on.
- Every number the printer is asked to write, and every number `Number.ofFloat?` produces, is
  canonical.
- The path operations hold their laws: what `set?` puts at a path is what `get?` finds there,
  and putting back what is already at a path leaves the value alone.
- Deduplicating an object's field names leaves every lookup unchanged, repeats no name, and
  leaves an object that repeats none alone.
- Encoding then decoding gives back the value: for `Json`, `Number`, `Bool`, `String` and `Unit`
  outright, for `Int` and `Nat` within the padding bound, and for `Option`, `Prod`, `Array` and
  `List` from the round trip of whatever they hold.

Each of these ships as a theorem in the library rather than as a check beside the tests, so a
proof of your own can cite it: `Json.get?_set?`, `Json.findLast?_dedupKeys`,
`Json.Parser.textOf_parse`, `Json.Printer.textOf_compress` and the rest are importable with the
code they describe.

Not proved, and covered by tests instead:

- **Completeness, meaning no false rejects.** Soundness says nothing about what the parser turns
  away, so this is where 318 files of the JSONTestSuite conformance corpus, two 3,000 round fuzz
  sweeps and the behavioural tests earn their keep.
- **Round tripping through text**, `parse (render j) = .ok j`, which needs completeness, so it is
  property-tested and corpus-tested. `Float` is the one codec whose round trip is a property
  rather than a theorem, since it goes through the exact decimal expansion of a bit pattern.
- **Absence of stack overflow and out-of-memory.** No theorem says a program will not run out of
  either. What is proved is that what runs is the traversal holding its work in a list; that this
  costs heap rather than stack is by construction, and evidenced by fuzzing. Two recursions sit
  outside it: a codec the companion generates walks a value on the stack, and freeing a deeply
  nested value is a recursion the library does not perform and cannot control. The second was
  measured rather than argued: a million-deep value built and dropped repeatedly survives, with
  peak memory flat across rounds.
- `Number.toFloat` is not verified against IEEE 754.

## Speed

`bench/` times reading and writing beside `Lean.Data.Json` on the same text. Numbers from one
machine, best of three, so useful for tracking rather than for comparing machines:

| Document | Size | parse | compress | pretty | core parse |
|---|---|---|---|---|---|
| numbers | 311K | 10.3ms | 11.8ms | 13.6ms | 8.6ms |
| wide object | 915K | 18.8ms | 7.1ms | 9.4ms | 17.2ms |
| strings | 1063K | 13.6ms | 5.4ms | 6.4ms | 6.9ms |
| records | 1442K | 34.8ms | 23.4ms | 36.4ms | 18.4ms |
| nesting, 20,000 deep | 39K | 0.6ms | 1.8ms | - | 0.9ms |

Reading runs at 30 to 77 MB/s, between level with core and about twice its time, and the
difference is where the work is: duplicate names are checked, numbers are canonicalised, and depth
is counted. Encoding and decoding are timed too: 20,000 records go to JSON in 4.4ms and come back
in 3.2ms.

Memory is the number worth watching, and `bench/` reports it on two documents, because two
different things are being paid for. A document that is nearly all text and almost no value, a
single six megabyte string, costs about two bytes of peak resident memory per byte of text: that
is the scanner, which walks the string by position rather than converting it to a list of
characters first. A document that is nearly all value, 100,000 records, costs about six, and the
difference is the value itself, which no scanner can help with.

## Building

```
lake build          # the library
lake test           # both test suites, the library's and the companion's
./scripts/check-imports.sh    # no Lean package imports in the library
./scripts/check-runtime.sh    # and none reachable in what a consumer runs
cd bench && lake exe bench    # timings
```

`PLAN.md` carries the decisions, what is proved, what is deferred, and why.

## Licence

Apache 2.0, in `LICENSE`. The conformance corpus under `test/corpus` is
[JSONTestSuite](https://github.com/nst/JSONTestSuite), copyright (c) 2016 Nicolas Seriot, MIT
licence, vendored with its licence and provenance beside it.
