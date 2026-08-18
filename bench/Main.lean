/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
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
What one byte of text costs while it is being read. The scanner works over a `List Char`, which
the whole input is converted to first, and this is the number that says why that has to change:
it is a limit on the size of document that can safely be read, whatever the timings say.

The document is the largest in the run and comes last, so that the high water mark it leaves is
its own.
-/
private def amplification : IO Unit := do
  let before := (← peakBytes).getD 0
  let text := records 100000
  let bytes := text.utf8ByteSize
  match Json.parse text with
  | .error e => IO.println s!"the document was refused: {e}"
  | .ok value =>
    let after := (← peakBytes).getD 0
    if after ≤ before || bytes == 0 then
      IO.println "peak resident memory did not rise, so there is nothing to report"
    else
      IO.println s!"reading {bytes / 1048576}M of text cost {(after - before) / 1048576}M of \
peak resident memory, about {(after - before) / bytes} bytes a character, at depth \
{Json.depth value}"

def main : IO Unit := do
  let cases : List Case := [
    { name := "numbers", text := numbers 40000 },
    { name := "wide object", text := wideObject 40000 },
    { name := "strings", text := strings 20000 },
    { name := "records", text := records 20000 },
    -- Past the default depth limit, so this one lifts it.
    { name := "nesting", text := nested 20000, cfg := { maxDepth := none }, layout := false }
  ]
  IO.println "best of three"
  for c in cases do
    report c
  match ← peakBytes with
  | some peak => IO.println s!"peak resident memory so far: {peak / 1048576}M"
  | none => pure ()
  amplification

end Bench

def main : IO Unit := Bench.main
