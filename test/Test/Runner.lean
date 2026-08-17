/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Plausible

namespace Test

structure TestCase where
  name : String
  run : IO Unit

def runAll (cases : Array TestCase) : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    match ← c.run.toBaseIO with
    | .ok _ => IO.println s!"ok   {c.name}"
    | .error e =>
      failures := failures + 1
      IO.println s!"FAIL {c.name}: {e}"
  IO.println s!"{cases.size - failures} passed, {failures} failed"
  return if failures = 0 then 0 else 1

def expect (name : String) (cond : Bool) : TestCase where
  name := name
  run := if cond then pure () else throw (IO.userError "expectation failed")

def expectEq [BEq α] [ToString α] (name : String) (actual expected : α) : TestCase where
  name := name
  run :=
    if actual == expected then pure ()
    else throw (IO.userError s!"expected {expected}, got {actual}")

/--
Randomised property check. Quantifiers must be wrapped in `Plausible.NamedBinder`, which is
what the `plausible` tactic's elaborator would otherwise add; the tactic itself is unusable
here because it reports through warnings, and warnings are errors.
-/
def property (name : String) (p : Prop) [Plausible.Testable p]
    (cfg : Plausible.Configuration := {}) : TestCase where
  name := name
  run := do
    match ← Plausible.Testable.checkIO p cfg with
    | .success _ => pure ()
    | .gaveUp n => throw (IO.userError s!"gave up after {n} attempts")
    | .failure _ counterexample _ =>
      throw (IO.userError s!"counterexample: {String.intercalate ", " counterexample}")

end Test
