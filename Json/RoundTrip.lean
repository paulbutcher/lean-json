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
and it holds for a configuration whose limits are off, since those refuse text the grammar
accepts by design.
-/

variable {cfg : Config} {j : Json}

theorem parse_compress (hmax : cfg.maxDepth = none) (hkeys : cfg.duplicateKeys = .allow)
    (hdig : cfg.maxNumberDigits = none) (h : CanonicalNumbers j) :
    parse (compress j) cfg = .ok j :=
  Parser.parse_complete hmax hkeys hdig (Printer.textOf_compress h)

theorem parse_pretty (hmax : cfg.maxDepth = none) (hkeys : cfg.duplicateKeys = .allow)
    (hdig : cfg.maxNumberDigits = none) (h : CanonicalNumbers j) (indent : Nat) :
    parse (pretty j indent) cfg = .ok j :=
  Parser.parse_complete hmax hkeys hdig (Printer.textOf_pretty h indent)

end Json
