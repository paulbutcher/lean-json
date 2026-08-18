/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser
public import Json.Printer

public section

namespace Json

@[expose] section

/--
Parses `nBytes` bytes read from `h` as one JSON text.

Bytes rather than characters, since RFC 8259 section 8.1 puts the encoding at this boundary and
`parseBytes` is where it is checked.
-/
def readJson (h : IO.FS.Stream) (nBytes : Nat) (cfg : Config := {}) : IO Json := do
  let bytes ← h.read (USize.ofNat nBytes)
  match parseBytes bytes cfg with
  | .ok j => pure j
  | .error e => throw (IO.userError (toString e))

/-- Parses everything left in `h` as one JSON text. -/
def readJsonToEnd (h : IO.FS.Stream) (cfg : Config := {}) : IO Json := do
  let bytes ← h.readBinToEnd
  match parseBytes bytes cfg with
  | .ok j => pure j
  | .error e => throw (IO.userError (toString e))

def writeJson (h : IO.FS.Stream) (j : Json) : IO Unit := do
  h.putStr (compress j)
  h.flush

/-- As `writeJson`, but laid out over several lines. -/
def writeJsonPretty (h : IO.FS.Stream) (j : Json) (indent : Nat := 2) : IO Unit := do
  h.putStr (pretty j indent)
  h.flush

end

end Json
