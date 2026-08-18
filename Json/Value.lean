/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Number

public section

@[expose] section

/-!
The value alone, so that `Json.Fold` can sit between it and the rest of the data model.
-/

/--
A JSON value.

Object fields keep the order they appeared in, and duplicate names are representable, so a parsed
value is a faithful image of its text. Lookup resolves duplicates by taking the last, matching
ECMA-262 and the mainstream implementations.
-/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Json.Number)
  | str (s : String)
  | arr (elems : Array Json)
  | obj (fields : Array (String × Json))
deriving Inhabited, Repr
