/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser.Completeness
public import Json.Printer.Soundness

public section

namespace Json

/-!
Reading what was written gives back what was written.

Both halves are already proved: what the printer emits is text the grammar derives, and text the
grammar derives is read as the value the grammar gives it. The round trip is their composition,
and it holds wherever the reading refuses nothing the grammar accepts: the digit limit off,
either repeated names allowed or a value that has none, and a value within the nesting limit.
-/

variable {cfg : Config} {j : Json}

theorem parse_compress (hdig : cfg.maxNumberDigits = none)
    (hkeys : cfg.duplicateKeys = .allow ∨ UniqueKeys j)
    (hdepth : ∀ limit, cfg.maxDepth = some limit → depth j ≤ limit) (h : CanonicalNumbers j) :
    parse (compress j) cfg = .ok j :=
  Parser.parse_complete hdig hkeys hdepth (Printer.textOf_compress h)

theorem parse_pretty (hdig : cfg.maxNumberDigits = none)
    (hkeys : cfg.duplicateKeys = .allow ∨ UniqueKeys j)
    (hdepth : ∀ limit, cfg.maxDepth = some limit → depth j ≤ limit) (h : CanonicalNumbers j)
    (indent : Nat) : parse (pretty j indent) cfg = .ok j :=
  Parser.parse_complete hdig hkeys hdepth (Printer.textOf_pretty h indent)

end Json
