/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json

namespace Test.Conformance

private def corpusDir : IO System.FilePath := do
  -- Depending on which directory `lake test` was started from, the corpus is either beside
  -- the test package or below it.
  for candidate in [("corpus" : System.FilePath), "test/corpus"] do
    let dir := candidate / "JSONTestSuite" / "test_parsing"
    if ← dir.pathExists then return dir
  throw (IO.userError "the JSONTestSuite corpus is missing")

private def filesStarting (pre : String) : IO (Array String) := do
  let entries ← (← corpusDir).readDir
  return (entries.map (·.fileName) |>.filter (·.startsWith pre)).qsort (· < ·)

private def parseFile (name : String) (cfg : Config := {}) : IO (Except Error Json) := do
  return Json.parseBytes (← IO.FS.readBinFile ((← corpusDir) / name)) cfg

/-- A failure names the files that misbehaved, since the interesting part is which ones. -/
private def report (what : String) (bad : Array String) : IO Unit := do
  if bad.isEmpty then return ()
  let shown := bad.toList.take 8
  throw (IO.userError s!"{bad.size} {what}: {String.intercalate ", " shown}")

/--
The sweeps below say nothing at all about a corpus that is not there, and `readDir` only catches
the case where none of it is. The census is what makes a partial copy fail loudly, and the
recorded outcomes are worth rerunning whenever these numbers change.
-/
def census : Array TestCase := #[
  { name := "the vendored corpus is all there"
    run := do
      let counts ← #["y_", "n_", "i_"].mapM fun pre => return (← filesStarting pre).size
      if counts != #[95, 188, 35] then
        throw (IO.userError s!"the corpus holds {counts}, where 95, 188 and 35 were expected") }
]

/--
`{"a":"b","a":"c"}` and `{"a":"b","a":"b"}` conform to the grammar, so section 9 of RFC 8259
makes them must-accept, and strict mode refuses them anyway. This is the library's one deviation
from the corpus, and it is a policy the caller can turn off rather than an inability to read the
text.
-/
private def duplicateKeyDeviations : Array String :=
  #["y_object_duplicated_key.json", "y_object_duplicated_key_and_value.json"]

def acceptance : Array TestCase := #[
  { name := "every y_ file is accepted, but for the two duplicate-name deviations"
    run := do
      let mut wrong := #[]
      for name in ← filesStarting "y_" do
        let expectedReject := duplicateKeyDeviations.contains name
        match ← parseFile name with
        | .ok _ => if expectedReject then wrong := wrong.push name
        | .error e =>
          if !expectedReject || e.kind != .duplicateKey "a" then wrong := wrong.push name
      report "must-accept files went the wrong way" wrong },
  { name := "the deviations are accepted once duplicate names are permitted"
    run := do
      let mut wrong := #[]
      for name in duplicateKeyDeviations do
        if (← parseFile name { duplicateKeys := .allow }).toOption.isNone then
          wrong := wrong.push name
      report "deviations still refused in permissive mode" wrong },
  { name := "every n_ file is rejected"
    run := do
      let mut wrong := #[]
      for name in ← filesStarting "n_" do
        if (← parseFile name).toOption.isSome then wrong := wrong.push name
      report "must-reject files were accepted" wrong }
]

/--
The corpus leaves the `i_` cases to the implementation, so the point of running them is to pin
the choice rather than to check it. Two rules decide every one of them: a number is read whatever
its magnitude, because an exponent is never evaluated; and text that no sequence of code points
denotes is refused, whether it arrives as invalid UTF-8 or as an escaped half of a surrogate
pair.
-/
def implementationDefined : Array TestCase := #[
  { name := "i_ numbers and structures are accepted whatever their magnitude or depth"
    run := do
      let mut wrong := #[]
      for name in ← filesStarting "i_" do
        let structural := name.startsWith "i_number_" || name.startsWith "i_structure_"
        if structural && (← parseFile name).toOption.isNone then wrong := wrong.push name
      report "files were refused" wrong },
  { name := "i_ strings that denote no code points are refused, and for that reason"
    run := do
      let mut wrong := #[]
      for name in ← filesStarting "i_" do
        if name.startsWith "i_number_" || name.startsWith "i_structure_" then continue
        match ← parseFile name with
        | .ok _ => wrong := wrong.push name
        | .error e =>
          if e.kind != .loneSurrogate && e.kind != .invalidUtf8 then wrong := wrong.push name
      report "files were read, or refused for an unrelated reason" wrong }
]

/--
Everything the corpus gets us to parse is then printed and read back, which puts documents nobody
here wrote through the printer.
-/
def roundTrip : Array TestCase := #[
  { name := "every accepted corpus document survives compress and re-parse"
    run := do
      let mut wrong := #[]
      for name in (← filesStarting "y_") ++ (← filesStarting "i_") do
        if let .ok j ← parseFile name { duplicateKeys := .allow } then
          if (Json.parse (compress j) { duplicateKeys := .allow }).toOption != some j then
            wrong := wrong.push name
      report "documents did not survive the round trip" wrong },
  { name := "every accepted corpus document survives pretty and re-parse"
    run := do
      let mut wrong := #[]
      for name in (← filesStarting "y_") ++ (← filesStarting "i_") do
        if let .ok j ← parseFile name { duplicateKeys := .allow } then
          if (Json.parse (pretty j) { duplicateKeys := .allow }).toOption != some j then
            wrong := wrong.push name
      report "documents did not survive the round trip" wrong }
]

def all : Array TestCase := census ++ acceptance ++ implementationDefined ++ roundTrip

end Test.Conformance
