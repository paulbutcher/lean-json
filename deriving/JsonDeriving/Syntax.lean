/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json
public meta import Lean.Syntax

public section

namespace Json

/-! A literal written the way JSON is written, with `$(e)` for a value computed in Lean. -/

declare_syntax_cat jsonLit (behavior := symbol)

syntax "null" : jsonLit
syntax "true" : jsonLit
syntax "false" : jsonLit
syntax str : jsonLit
syntax "-"? num : jsonLit
syntax "-"? scientific : jsonLit
syntax "[" jsonLit,* "]" : jsonLit
syntax jsonLitName := ident <|> str
syntax jsonLitField := jsonLitName ": " jsonLit
syntax "{" jsonLitField,* "}" : jsonLit

/-- A JSON value written out in place. -/
syntax "json% " jsonLit : term

macro_rules
  | `(json% null)           => `(Json.null)
  | `(json% true)           => `(Json.bool Bool.true)
  | `(json% false)          => `(Json.bool Bool.false)
  | `(json% $n:str)         => `(Json.str $n)
  | `(json% $n:num)         => `(Json.num $n)
  | `(json% $n:scientific)  => `(Json.num $n)
  | `(json% -$n:num)        => `(Json.num (-$n))
  | `(json% -$n:scientific) => `(Json.num (-$n))
  | `(json% [$[$xs],*])     => `(Json.arr #[$[json% $xs],*])
  | `(json% {$[$ks:jsonLitName : $vs:jsonLit],*}) => do
    let ks : Array (Lean.TSyntax `term) ← ks.mapM fun
      | `(jsonLitName| $k:ident) => pure (k.getId |> toString |> Lean.quote)
      | `(jsonLitName| $k:str)   => pure k
      | _                        => Lean.Macro.throwUnsupported
    `(Json.mkObj [$[($ks, json% $vs)],*])
  | `(json% $stx) =>
    -- An antiquotation is the escape hatch to a Lean term, encoded by its own instance.
    if stx.raw.isAntiquot then
      let stx := ⟨stx.raw.getAntiquotTerm⟩
      `(Json.toJson $stx)
    else
      Lean.Macro.throwUnsupported

end Json
