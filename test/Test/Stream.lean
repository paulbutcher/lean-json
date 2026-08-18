/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json

namespace Test.Stream

private def reading (contents : String) (f : IO.FS.Stream → IO α) : IO α := do
  let ref ← IO.mkRef { data := contents.toUTF8 : IO.FS.Stream.Buffer }
  f (IO.FS.Stream.ofBuffer ref)

private def writing (f : IO.FS.Stream → IO Unit) : IO String := do
  let ref ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  f (IO.FS.Stream.ofBuffer ref)
  let buffer ← ref.get
  match String.fromUTF8? buffer.data with
  | some s => pure s
  | none => throw (IO.userError "the stream did not hold valid UTF-8")

private def sample : Json := .obj #[("a", .num 1), ("b", .arr #[.null])]

def all : Array TestCase := #[
  { name := "readJson reads a value from a stream"
    run := do
      let text := "{\"a\":1,\"b\":[null]}"
      let j ← reading text fun h => readJson h text.utf8ByteSize
      if j == sample then pure () else throw (IO.userError s!"read {compress j}") },
  { name := "readJson reads only the bytes it was asked for"
    run := do
      let j ← reading "1 2 3" fun h => readJson h 1
      if j == .num 1 then pure () else throw (IO.userError s!"read {compress j}") },
  { name := "readJson reports a parse failure as an IO error"
    run := do
      match ← (reading "{" fun h => readJson h 1).toBaseIO with
      | .ok _ => throw (IO.userError "accepted")
      | .error _ => pure () },
  { name := "readJson refuses bytes that are not UTF-8"
    run := do
      let ref ← IO.mkRef { data := ⟨#[0x22, 0xFF, 0x22]⟩ : IO.FS.Stream.Buffer }
      match ← (readJson (IO.FS.Stream.ofBuffer ref) 3).toBaseIO with
      | .ok _ => throw (IO.userError "accepted")
      | .error _ => pure () },
  { name := "readJsonToEnd reads whatever is left"
    run := do
      let j ← reading "  {\"a\":1,\"b\":[null]}  " fun h => readJsonToEnd h
      if j == sample then pure () else throw (IO.userError s!"read {compress j}") },
  { name := "writeJson writes the compressed form"
    run := do
      let text ← writing fun h => writeJson h sample
      expectEq "" text "{\"a\":1,\"b\":[null]}" |>.run },
  { name := "writeJsonPretty writes the laid-out form"
    run := do
      let text ← writing fun h => writeJsonPretty h sample
      expectEq "" text "{\n  \"a\": 1,\n  \"b\": [\n    null\n  ]\n}" |>.run },
  -- What is written can be read back, which is the pair's reason to exist.
  { name := "a value written to a stream reads back"
    run := do
      let text ← writing fun h => writeJson h sample
      let j ← reading text fun h => readJsonToEnd h
      if j == sample then pure () else throw (IO.userError s!"read {compress j}") }
]

end Test.Stream
