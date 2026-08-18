/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import JsonDeriving
import Lean.Data.Json

/-!
Timings, kept as regression tracking rather than as a gate. Each case builds a document, reads
it and writes it back, and reads it again with `Lean.Data.Json` on the same text, so that the
cost of what this library does differently stays visible.

Peak resident memory is reported alongside, because the parser converts its input to a
`List Char` before scanning it, and the amplification that costs is itself a limit on what can
safely be read.
-/

namespace Bench

/--
The fastest of one run per input.

Two things have to be arranged for the number to mean anything, and both come of the work
being pure. Each round is handed its own copy of the input, because several rounds over one
input let the compiler do the work once and reuse it. And the result is looked at from inside
the timed region, by a branch deciding what to print, because a pure result that nothing
observes until later is computed later, which leaves the region measuring nothing at all.

`size` can be cheap: reaching the outermost constructor of a result forces the whole of the
call that produced it.
-/
private def best (inputs : Array α) (work : α → β) (size : β → Nat) (fallback : β) :
    IO (Nat × β) := do
  let mut fastest := none
  let mut last := fallback
  for input in inputs do
    let start ← IO.monoNanosNow
    let value := work input
    if size value == 0 then IO.println "nothing was computed, so the timing means nothing"
    let elapsed := (← IO.monoNanosNow) - start
    if fastest.all (elapsed < ·) then fastest := some elapsed
    last := value
  return (fastest.getD 0, last)

private def peakBytes : IO (Option Nat) := do
  let status : System.FilePath := "/proc/self/status"
  if !(← status.pathExists) then return none
  for line in (← IO.FS.readFile status).splitOn "\n" do
    if line.startsWith "VmHWM:" then
      return ((line.drop 6).trimAscii.takeWhile Char.isDigit |>.toNat?.map (· * 1024))
  return none

private def ms (nanos : Nat) : String :=
  let tenths := (nanos + 50000) / 100000
  s!"{tenths / 10}.{tenths % 10}"

private def perSecond (bytes nanos : Nat) : String :=
  if nanos == 0 then "-" else
    let tenths := bytes * 10000000000 / nanos / 1048576
    s!"{tenths / 10}.{tenths % 10}"

private def pad (s : String) (width : Nat) : String := s.pushn ' ' (width - min width s.length)

/-! ## Documents -/

private def numbers (n : Nat) : String :=
  "[" ++ String.intercalate "," ((List.range n).map fun i =>
    match i % 4 with
    | 0 => toString i
    | 1 => s!"-{i}.25"
    | 2 => s!"{i}e17"
    | _ => s!"0.{i}") ++ "]"

private def wideObject (n : Nat) : String :=
  "{" ++ String.intercalate "," ((List.range n).map fun i => s!"\"key{i}\":\"value{i}\"") ++ "}"

private def strings (n : Nat) : String :=
  "[" ++ String.intercalate "," ((List.range n).map fun i =>
    s!"\"a string with \\\"quotes\\\", a tab \\t and a café {i}\"") ++ "]"

private def records (n : Nat) : String :=
  "[" ++ String.intercalate "," ((List.range n).map fun i =>
    "{\"id\":" ++ toString i ++ ",\"name\":\"row " ++ toString i ++
      "\",\"tags\":[\"a\",\"b\"],\"ok\":" ++ (if i % 2 == 0 then "true" else "false") ++
      ",\"score\":" ++ toString i ++ ".5}") ++ "]"

private def nested (n : Nat) : String := "".pushn '[' n ++ "1" ++ "".pushn ']' n

/-! ## Codecs

Encoding and decoding are timed apart from the text, because a derived instance can do work that
neither parsing nor printing does and nothing else here would show it.
-/

structure Row where
  id : Nat
  name : String
  ok : Bool
deriving Json.ToJson, Json.FromJson

inductive Tree where
  | leaf (value : Nat)
  | node (children : Array Tree)
deriving Json.ToJson, Json.FromJson

private def rows (n : Nat) : Array Row :=
  (Array.range n).map fun i => { id := i, name := s!"row {i}", ok := i % 2 == 0 }

private def tree : Nat → Tree
  | 0 => .leaf 0
  | n + 1 => .node #[tree n, tree n]

private def codecs : IO Unit := do
  -- Each round is given its own value for the reason `best` explains, and they differ in size by
  -- one element so that no two rounds can share the work between them.
  let rowSets := (Array.range 3).map fun i => rows (20000 + i)
  let (rowsOut, encoded) ← best rowSets Json.toJson (fun j => Json.depth j) .null
  let (rowsIn, _) ← best ((Array.range 3).map fun i => Json.toJson (rows (20000 + i)))
    (fun j => Json.fromJson? (α := Array Row) j) (fun r => if r.toOption.isSome then 1 else 0)
    (.error "")
  let trees := (Array.range 3).map fun i => tree (13 + i % 2)
  let (treeOut, _) ← best trees Json.toJson (fun j => Json.depth j) .null
  let (treeIn, _) ← best (trees.map Json.toJson)
    (fun j => Json.fromJson? (α := Tree) j) (fun r => if r.toOption.isSome then 1 else 0)
    (.error "")
  IO.println s!"{pad "20,000 records" 20}toJson {pad (ms rowsOut ++ "ms") 10}\
fromJson? {pad (ms rowsIn ++ "ms") 10}as text {(Json.compress encoded).utf8ByteSize / 1024}K"
  IO.println s!"{pad "a tree of 8,191" 20}toJson {pad (ms treeOut ++ "ms") 10}\
fromJson? {pad (ms treeIn ++ "ms") 10}"

/-! ## The run -/

private structure Case where
  name : String
  text : String
  cfg : Json.Config := {}
  /--
  Laying out a deeply nested value costs an indent per level, so its text is quadratic in the
  depth and there is nothing to learn from timing it.
  -/
  layout : Bool := true

private def report (c : Case) : IO Unit := do
  let bytes := c.text.utf8ByteSize
  -- Trailing whitespace is text the grammar allows and the scanner skips, so these are the same
  -- document three times over, and three objects rather than one.
  let texts := (Array.range 3).map fun i => c.text.pushn ' ' i
  let (parseTime, parsed) ← best texts (fun t => Json.parse t c.cfg)
    (fun r => if r.toOption.isSome then 1 else 0) (.error ⟨0, .unexpectedEnd⟩)
  match parsed with
  | .error e => IO.println s!"{pad c.name 14} refused: {e}"
  | .ok _ =>
    let values := texts.filterMap fun t => (Json.parse t c.cfg).toOption
    let (compressTime, _) ← best values Json.compress String.utf8ByteSize ""
    let (prettyTime, _) ←
      if c.layout then best values (Json.pretty ·) String.utf8ByteSize ""
      else pure (0, "")
    let (coreTime, coreParsed) ← best texts Lean.Json.parse
      (fun r => if r.toOption.isSome then 1 else 0) (.error "")
    let core := if coreParsed.toOption.isSome then ms coreTime ++ "ms" else "refused"
    IO.println s!"{pad c.name 14}{pad s!"{bytes / 1024}K" 8}\
parse {pad (ms parseTime ++ "ms") 9}{pad (perSecond bytes parseTime ++ " MB/s") 14}\
compress {pad (ms compressTime ++ "ms") 9}\
pretty {pad (if c.layout then ms prettyTime ++ "ms" else "-") 9}\
core parse {core}"

/--
What one byte of text costs while it is being read.

Two documents, because there are two things being paid for. A long string is nearly all text and
almost no value, so its figure is the scanner's: this is the number that was about thirty when
the whole input was converted to a list of characters first, and the reason that had to change.
The records document is the other end, where most of what is held is the value, which no scanner
can do anything about.

They run first, because the figure is a rise in the high water mark, and a mark already raised by
everything else would hide it.
-/
private def amplification (name : String) (text : String) : IO Unit := do
  let bytes := text.utf8ByteSize
  -- Taken once the text exists, so that what it measures is the reading and not the building.
  let before := (← peakBytes).getD 0
  match Json.parse text with
  | .error e => IO.println s!"the {name} document was refused: {e}"
  | .ok value =>
    let after := (← peakBytes).getD 0
    if after ≤ before || bytes == 0 then
      IO.println s!"{pad name 16}reading it did not raise the high water mark"
    else
      IO.println s!"{pad name 16}{bytes / 1048576}M of text cost \
{(after - before) / 1048576}M of peak resident memory, about {(after - before) / bytes} bytes \
a character, at depth {Json.depth value}"

private def longString : String := "[\"" ++ "".pushn 'a' 7000000 ++ "\"]"

def main : IO Unit := do
  let cases : List Case := [
    { name := "numbers", text := numbers 40000 },
    { name := "wide object", text := wideObject 40000 },
    { name := "strings", text := strings 20000 },
    { name := "records", text := records 20000 },
    -- Past the default depth limit, so this one lifts it.
    { name := "nesting", text := nested 20000, cfg := { maxDepth := none }, layout := false }
  ]
  amplification "a long string" longString
  amplification "records" (records 100000)
  IO.println "best of three"
  for c in cases do
    report c
  IO.println "codecs, best of three"
  codecs
  match ← peakBytes with
  | some peak => IO.println s!"peak resident memory so far: {peak / 1048576}M"
  | none => pure ()

end Bench

def main : IO Unit := Bench.main
