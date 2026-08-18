/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json Json.Spec

namespace Test.Spec

-- Derivations are written against character lists, with the text they spell alongside. Building
-- them by hand is what checks the transcription: a production stated wrongly cannot be derived.

attribute [local simp] Number.normalize Number.normalizeAux

/-- `null` -/
example : Text ['n', 'u', 'l', 'l'] .null :=
  ⟨_, _, .nil, .null, .nil⟩

/-- `  true ` , exercising `ws` on both sides -/
example : Text [' ', ' ', 't', 'r', 'u', 'e', ' '] (.bool true) :=
  ⟨_, _, .cons (by decide) (.cons (by decide) .nil), .true_, .cons (by decide) .nil⟩

/-- `1` -/
example : Text ['1'] (.num ⟨1, 0⟩) := by
  rw [show (⟨1, 0⟩ : Number) = Number.normalize 1 0 from by simp]
  exact ⟨_, _, .nil, .num (.mk .absent (.digits (by decide) (.last (by decide))) .absent .absent),
    .nil⟩

/-- `-12.50e3`, whose canonical value is `-125e2`, so the trailing zero is not a distinction -/
example : Text ['-', '1', '2', '.', '5', '0', 'e', '3'] (.num ⟨-125, 2⟩) := by
  rw [show (⟨-125, 2⟩ : Number) = Number.normalize (-1250) 1 from by simp]
  exact ⟨_, _, .nil,
    .num (.mk .minus
      (.digits (by decide) (.cons (by decide) (.last (by decide))))
      (.present (.cons (by decide) (.last (by decide))))
      (.bare (Or.inl rfl) (.last (by decide)))),
    .nil⟩

/-- `"a\nb"`, exercising an escape alongside unescaped characters -/
example : Text ['"', 'a', '\\', 'n', 'b', '"'] (.str "a\nb") := by
  rw [show "a\nb" = String.ofList ['a', '\n', 'b'] from by simp]
  exact ⟨_, _, .nil,
    .str (.mk (.cons (.unescaped (by decide)) (.cons .lineFeed (.cons (.unescaped (by decide))
      .nil)))),
    .nil⟩

/-- `"😀"`, where a surrogate pair denotes one code point above the BMP -/
example : Text ['"', '\\', 'u', 'd', '8', '3', 'd', '\\', 'u', 'd', 'e', '0', '0', '"']
    (.str "😀") := by
  rw [show "😀" = String.ofList ['😀'] from by simp]
  exact ⟨_, _, .nil,
    .str (.mk (.cons
      (.surrogatePair
        (.mk (show hexVal? 'd' = some 13 by decide) (show hexVal? '8' = some 8 by decide)
          (show hexVal? '3' = some 3 by decide) (show hexVal? 'd' = some 13 by decide))
        (.mk (show hexVal? 'd' = some 13 by decide) (show hexVal? 'e' = some 14 by decide)
          (show hexVal? '0' = some 0 by decide) (show hexVal? '0' = some 0 by decide))
        (by decide) (by decide) (by decide) (by decide) (by decide))
      .nil)),
    .nil⟩

/-- `[1,2]` -/
example : Text ['[', '1', ',', '2', ']'] (.arr #[.num ⟨1, 0⟩, .num ⟨2, 0⟩]) := by
  rw [show (⟨1, 0⟩ : Number) = Number.normalize 1 0 from by simp,
    show (⟨2, 0⟩ : Number) = Number.normalize 2 0 from by simp]
  exact ⟨_, _, .nil,
    .arr (.items (.mk .nil .nil)
      (.more (.num (.mk .absent (.digits (by decide) (.last (by decide))) .absent .absent))
        (.mk .nil .nil)
        (.one (.num (.mk .absent (.digits (by decide) (.last (by decide))) .absent .absent))))
      (.mk .nil .nil)),
    .nil⟩

/-- `[]`, the empty array, which takes the production's absent branch -/
example : Text ['[', ']'] (.arr #[]) :=
  ⟨_, _, .nil, .arr (.empty (.mk .nil .nil) (.mk .nil .nil)), .nil⟩

/-- `{ "a" : null }`, exercising whitespace inside the structural tokens -/
example : Text ['{', ' ', '"', 'a', '"', ' ', ':', ' ', 'n', 'u', 'l', 'l', ' ', '}']
    (.obj #[("a", .null)]) := by
  rw [show "a" = String.ofList ['a'] from by simp]
  exact ⟨_, _, .nil,
    .obj (.members (.mk .nil (.cons (by decide) .nil))
      (.one (.mk (.mk (.cons (.unescaped (by decide)) .nil))
        (.mk (.cons (by decide) .nil) (.cons (by decide) .nil))
        .null))
      (.mk (.cons (by decide) .nil) .nil)),
    .nil⟩

/-- `{"a":[{}]}`, nesting an object inside an array inside an object -/
example : Text ['{', '"', 'a', '"', ':', '[', '{', '}', ']', '}']
    (.obj #[("a", .arr #[.obj #[]])]) := by
  rw [show "a" = String.ofList ['a'] from by simp]
  exact ⟨_, _, .nil,
    .obj (.members (.mk .nil .nil)
      (.one (.mk (.mk (.cons (.unescaped (by decide)) .nil)) (.mk .nil .nil)
        (.arr (.items (.mk .nil .nil)
          (.one (.obj (.empty (.mk .nil .nil) (.mk .nil .nil))))
          (.mk .nil .nil)))))
      (.mk .nil .nil)),
    .nil⟩

/-! ## Rejection

The other half of validating a transcription. What these need beyond `cases` is the inversion
lemmas in `Json.Spec`, which say that whitespace never swallows a non-whitespace character and
that no character carries a surrogate code point.
-/

/-- `"\ud800"`, a lone surrogate escape, denotes nothing at all. -/
example : ¬ ∃ j, Text ['"', '\\', 'u', 'd', '8', '0', '0', '"'] j := by
  rintro ⟨j, s₁, s₂, hws, hv, -⟩
  obtain rfl := ws_eq_of_not_isWs (by decide) hws
  cases hv with
  | num hnum =>
    obtain ⟨hsign, hint, -, -⟩ := hnum
    cases hsign with
    | absent => cases hint with | digits hd _ => exact absurd hd (by decide)
  | arr harr =>
    cases harr with
    | empty hb _ => exact not_token_of_ne (by decide) (by decide) hb
    | items hb _ _ => exact not_token_of_ne (by decide) (by decide) hb
  | obj hobj =>
    cases hobj with
    | empty hb _ => exact not_token_of_ne (by decide) (by decide) hb
    | members hb _ _ => exact not_token_of_ne (by decide) (by decide) hb
  | str hstr =>
    cases hstr with
    | mk hchars =>
      cases hchars with
      | cons hch _ =>
        cases hch with
        | unescaped hu => exact absurd hu (by decide)
        | codePoint hhex hval =>
          cases hhex with
          | mk h1 h2 h3 h4 =>
            simp [hexVal?] at h1 h2 h3 h4
            have := escape_not_surrogate hval
            omega
        | surrogatePair hhi _ _ _ _ _ _ => cases hhi

/-- `01`, where `int` admits a leading zero only as the whole integer part. -/
example : ¬ ∃ j, Text ['0', '1'] j := by
  rintro ⟨j, s₁, s₂, hws, hv, hrest⟩
  obtain rfl := ws_eq_of_not_isWs (by decide) hws
  cases hv with
  | arr harr =>
    cases harr with
    | empty hb _ => exact not_token_of_ne (by decide) (by decide) hb
    | items hb _ _ => exact not_token_of_ne (by decide) (by decide) hb
  | obj hobj =>
    cases hobj with
    | empty hb _ => exact not_token_of_ne (by decide) (by decide) hb
    | members hb _ _ => exact not_token_of_ne (by decide) (by decide) hb
  | str hstr => cases hstr
  | num hnum =>
    obtain ⟨hsign, hint, hfrac, hexp⟩ := hnum
    cases hsign with
    | absent =>
      cases hint with
      | zero =>
        cases hfrac with
        | absent =>
          cases hexp with
          | absent => exact absurd (ws_eq_of_not_isWs (by decide) hrest) (by simp)
          | bare he _ => exact absurd he (by simp)
      | digits hd _ => exact absurd hd (by decide)

end Test.Spec
