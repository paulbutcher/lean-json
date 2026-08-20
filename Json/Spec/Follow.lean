/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec

public section

namespace Json.Spec

/-!
What a production can begin with, and what may follow one.

The relations are deliberately not deterministic in their remainder, exactly as the ABNF is not:
`12` derives as `1` with `2` left over as readily as it derives as `12`, and a run of whitespace
can be divided anywhere. Both proofs about the grammar need the same conditions to pin that down,
and both need to know which character each production starts with, so those live here rather than
in either of them.
-/

/-- A list that whitespace cannot be taken from, which is where a `Ws` derivation has to stop. -/
@[expose] def NoWs (l : List Char) : Prop := ∀ c t, l = c :: t → isWs c = false

/-- What may follow a value: the end of the text, whitespace, or a separator or closing bracket. -/
@[expose] def Follows (l : List Char) : Prop :=
  ∀ c t, l = c :: t → isWs c = true ∨ c = ',' ∨ c = ']' ∨ c = '}'

theorem Ws.trans {a b c : List Char} (h₁ : Ws a b) : Ws b c → Ws a c := by
  induction h₁ with
  | nil => exact fun h => h
  | cons hc _ ih => exact fun h => Ws.cons hc (ih h)

/-- Two runs of whitespace taken from the same text agree as far as the shorter one goes. -/
theorem Ws.confluent {s r₁ : List Char} (h₁ : Ws s r₁) :
    ∀ {r₂ : List Char}, Ws s r₂ → Ws r₁ r₂ ∨ Ws r₂ r₁ := by
  induction h₁ with
  | nil => exact fun h₂ => Or.inl h₂
  | @cons c s r hc h₁' ih =>
    intro r₂ h₂
    cases h₂ with
    | nil => exact Or.inr (Ws.cons hc h₁')
    | cons _ h₂' => exact ih h₂'

/-- Whitespace stops in one place only, once what follows it is not whitespace. -/
theorem Ws.eq_of_noWs {s r₁ r₂ : List Char} (h₁ : Ws s r₁) (h₂ : Ws s r₂)
    (n₁ : NoWs r₁) (n₂ : NoWs r₂) : r₁ = r₂ := by
  rcases h₁.confluent h₂ with h | h
  · cases h with
    | nil => rfl
    | cons hc _ => rw [n₁ _ _ rfl] at hc; exact absurd hc (by decide)
  · cases h with
    | nil => rfl
    | cons hc _ => rw [n₂ _ _ rfl] at hc; exact absurd hc (by decide)

/-- Whitespace cannot be taken from a text that begins with none. -/
theorem Ws.source_eq_of_noWs {l x : List Char} (h : Ws l x) (hn : NoWs l) : l = x := by
  cases h with
  | nil => rfl
  | cons hc _ => rw [hn _ _ rfl] at hc; exact absurd hc (by decide)

/-- Of two runs of whitespace from one text, the one that leaves none is the further on. -/
theorem Ws.to_noWs {x y z : List Char} (h₁ : Ws x y) (h₂ : Ws x z) (hn : NoWs z) : Ws y z := by
  rcases h₁.confluent h₂ with h | h
  · exact h
  · rw [← h.source_eq_of_noWs hn]
    exact Ws.nil

theorem noWs_cons {t : Char} {u : List Char} (h : isWs t = false) : NoWs (t :: u) := by
  intro c t' hc
  injection hc with hcc
  rw [← hcc]
  exact h

/-! ## Numbers

A number is where the grammar is genuinely ambiguous about its remainder, so each part of one
carries the condition that pins it down: a run of digits must not be followed by a digit, a
fraction not by a point, an exponent not by an `e`. Each of those follows from `Follows` at the
end of the number, and in between from the shape of the part that comes after.
-/

@[expose] def NoDigit (l : List Char) : Prop := ∀ c t, l = c :: t → isDigit c = false

@[expose] def NoFrac (l : List Char) : Prop :=
  ∀ c t, l = c :: t → isDigit c = false ∧ c ≠ '.'

@[expose] def NoExp (l : List Char) : Prop :=
  ∀ c t, l = c :: t → isDigit c = false ∧ c ≠ 'e' ∧ c ≠ 'E'

theorem eq_of_isWs {c : Char} (h : isWs c = true) :
    c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\x0d' := by simpa [isWs, or_assoc] using h

theorem noExp_of_follows {l : List Char} (h : Follows l) : NoExp l := by
  intro c t hl
  rcases h c t hl with hw | rfl | rfl | rfl
  · rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  all_goals exact ⟨by decide, by decide, by decide⟩

theorem noFrac_of_follows {l : List Char} (h : Follows l) : NoFrac l := by
  intro c t hl
  rcases h c t hl with hw | rfl | rfl | rfl
  · rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  all_goals exact ⟨by decide, by decide⟩

theorem noDigit_of_noFrac {l : List Char} (h : NoFrac l) : NoDigit l :=
  fun c t hl => (h c t hl).1

theorem noDigit_of_noExp {l : List Char} (h : NoExp l) : NoDigit l :=
  fun c t hl => (h c t hl).1

theorem digits_head {s : List Char} {v n : Nat} {r : List Char} (h : Digits s v n r) :
    ∃ c t, s = c :: t ∧ isDigit c = true := by
  cases h with
  | last hd => exact ⟨_, _, rfl, hd⟩
  | cons hd _ => exact ⟨_, _, rfl, hd⟩

theorem not_digits_cons {c : Char} (hc : isDigit c = false) {s : List Char} {v n : Nat}
    {r : List Char} : ¬ Digits (c :: s) v n r := by
  intro h
  obtain ⟨c', t', hct, hd⟩ := digits_head h
  injection hct with hcc
  subst hcc
  rw [hc] at hd
  exact absurd hd (by decide)

theorem int_head {s : List Char} {v : Nat} {r : List Char} (h : Int' s v r) :
    ∃ c t, s = c :: t ∧ isDigit c = true := by
  cases h with
  | zero => exact ⟨_, _, rfl, by decide⟩
  | digits hc _ =>
    refine ⟨_, _, rfl, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Char.le_trans (by decide) hc.1, hc.2⟩

/-- A sign is a leading minus or nothing at all. -/
theorem sign_head {l : List Char} {b : Bool} {r : List Char} (h : Sign l b r) :
    (b = false ∧ r = l) ∨ (b = true ∧ l = '-' :: r) := by
  cases h with
  | absent => exact .inl ⟨rfl, rfl⟩
  | minus => exact .inr ⟨rfl, rfl⟩

/-- The three shapes an exponent can take once its first character is an `e`. -/
theorem exp_head {c : Char} {l : List Char} {e : Int} {r : List Char} (h : Exp (c :: l) e r)
    (hn : NoExp r) (hc : c = 'e' ∨ c = 'E') :
    (∃ v n, Digits l v n r ∧ e = (v : Int)) ∨
      (∃ u v n, l = '+' :: u ∧ Digits u v n r ∧ e = (v : Int)) ∨
        (∃ u v n, l = '-' :: u ∧ Digits u v n r ∧ e = -(v : Int)) := by
  cases h with
  | absent =>
    obtain ⟨-, he, hE⟩ := hn c l rfl
    rcases hc with rfl | rfl
    · exact absurd rfl he
    · exact absurd rfl hE
  | bare _ hd => exact .inl ⟨_, _, hd, rfl⟩
  | plus _ hd => exact .inr (.inl ⟨_, _, _, rfl, hd, rfl⟩)
  | minus _ hd => exact .inr (.inr ⟨_, _, _, rfl, hd, rfl⟩)

/-- A fraction that does not begin with a decimal point is not there at all. -/
theorem frac_absent {l : List Char} {f n : Nat} {r : List Char} (h : Frac l f n r)
    (hne : ∀ u, l ≠ '.' :: u) : f = 0 ∧ n = 0 ∧ r = l := by
  cases h with
  | absent => exact ⟨rfl, rfl, rfl⟩
  | present _ => exact absurd rfl (hne _)

/-- An exponent that does not begin with `e` is not there at all. -/
theorem exp_absent {l : List Char} {e : Int} {r : List Char} (h : Exp l e r)
    (hne : ∀ c u, l = c :: u → c ≠ 'e' ∧ c ≠ 'E') : e = 0 ∧ r = l := by
  cases h with
  | absent => exact ⟨rfl, rfl⟩
  | bare hE _ | plus hE _ | minus hE _ =>
    rcases hE with rfl | rfl
    · exact absurd rfl (hne _ _ rfl).1
    · exact absurd rfl (hne _ _ rfl).2

theorem isWs_of_isDigit {c : Char} (h : isDigit c = true) : isWs c = false := by
  cases hw : isWs c with
  | false => rfl
  | true => rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact absurd h (by decide)

theorem digit_ne {c d : Char} (hc : isDigit c = true) (hd : isDigit d = false) : c ≠ d := by
  rintro rfl
  rw [hd] at hc
  exact absurd hc (by decide)

theorem num_head {s : List Char} {n : Number} {r : List Char} (h : Num s n r) :
    ∃ c t, s = c :: t ∧ (c = '-' ∨ isDigit c = true) := by
  cases h with
  | mk hs hi _ _ =>
    cases hs with
    | absent =>
      obtain ⟨c, t, hct, hd⟩ := int_head hi
      exact ⟨c, t, hct, Or.inr hd⟩
    | minus => exact ⟨_, _, rfl, Or.inl rfl⟩

theorem not_num_cons {c : Char} {t : List Char} {n : Number} {r : List Char}
    (h₁ : c ≠ '-') (h₂ : isDigit c = false) : ¬ Num (c :: t) n r := by
  intro h
  obtain ⟨c', t', hct, hc⟩ := num_head h
  injection hct with hcc
  subst hcc
  rcases hc with rfl | hd
  · exact h₁ rfl
  · rw [h₂] at hd
    exact absurd hd (by decide)

theorem noFrac_after_exp {c r : List Char} {e : Int} (he : Exp c e r) (hr : Follows r) :
    NoFrac c := by
  cases he with
  | absent => exact noFrac_of_follows hr
  | bare hE _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    rcases hE with rfl | rfl <;> exact ⟨by decide, by decide⟩
  | plus hE _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    rcases hE with rfl | rfl <;> exact ⟨by decide, by decide⟩
  | minus hE _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    rcases hE with rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem noDigit_after_int {b c r : List Char} {f nf : Nat} {e : Int}
    (hf : Frac b f nf c) (he : Exp c e r) (hr : Follows r) : NoDigit b := by
  cases hf with
  | present _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    decide
  | absent => exact noDigit_of_noFrac (noFrac_after_exp he hr)

/-! ## Strings

The closing quotation mark is a character no `Ch` can begin with, which is what ends a string
without any condition on what follows it.
-/

@[expose] def NoCh (l : List Char) : Prop := ∀ c r, ¬ Ch l c r

theorem noCh_quote {t : List Char} : NoCh ('"' :: t) := by
  intro c r h
  cases h with
  | unescaped hu => exact absurd hu (by decide)

theorem str_head {s : List Char} {v : String} {r : List Char} (h : Str s v r) :
    ∃ t, s = '"' :: t := by cases h with | mk _ => exact ⟨_, rfl⟩

theorem not_str_cons {c : Char} {t : List Char} {v : String} {r : List Char}
    (hne : c ≠ '"') : ¬ Str (c :: t) v r := by
  intro h
  cases h with
  | mk _ => exact hne rfl

/-! ## Values -/

theorem not_arr_cons {c : Char} {t : List Char} {e : Array Json} {r : List Char}
    (hw : isWs c = false) (hne : c ≠ '[') : ¬ Arr (c :: t) e r := by
  intro h
  cases h with
  | empty hb _ => exact not_token_of_ne hw hne hb
  | items hb _ _ => exact not_token_of_ne hw hne hb

theorem not_obj_cons {c : Char} {t : List Char} {f : Array (String × Json)}
    {r : List Char} (hw : isWs c = false) (hne : c ≠ '{') : ¬ Object (c :: t) f r := by
  intro h
  cases h with
  | empty hb _ => exact not_token_of_ne hw hne hb
  | members hb _ _ => exact not_token_of_ne hw hne hb

theorem not_value_cons {c : Char} {t : List Char} {j : Json} {r : List Char}
    (hw : isWs c = false) (hf : c ≠ 'f') (hn : c ≠ 'n') (ht : c ≠ 't') (hq : c ≠ '"')
    (hb : c ≠ '[') (hc : c ≠ '{') (hm : c ≠ '-') (hd : isDigit c = false) :
    ¬ Value (c :: t) j r := by
  intro h
  cases h with
  | false_ => exact hf rfl
  | null => exact hn rfl
  | true_ => exact ht rfl
  | str hs => cases hs with | mk _ => exact hq rfl
  | num hn' => exact not_num_cons hm hd hn'
  | arr ha => exact not_arr_cons hw hb ha
  | obj ho => exact not_obj_cons hw hc ho

theorem not_value_bracket {t : List Char} {j : Json} {r : List Char} :
    ¬ Value (']' :: t) j r :=
  not_value_cons (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem not_elements_bracket {t : List Char} {vs : List Json} {r : List Char} :
    ¬ Elements (']' :: t) vs r := by
  intro h
  cases h with
  | one hv => exact not_value_bracket hv
  | more hv _ _ => exact not_value_bracket hv

theorem not_members_brace {t : List Char} {ms : List (String × Json)} {r : List Char} :
    ¬ Members ('}' :: t) ms r := by
  intro h
  cases h with
  | one hm => cases hm with | mk hs _ _ => cases hs
  | more hm _ _ => cases hm with | mk hs _ _ => cases hs

theorem arr_begin {s : List Char} {e : Array Json} {r : List Char} (h : Arr s e r) :
    ∃ u, Ws s ('[' :: u) := by
  cases h with
  | empty hb _ => cases hb with | mk w _ => exact ⟨_, w⟩
  | items hb _ _ => cases hb with | mk w _ => exact ⟨_, w⟩

theorem obj_begin {s : List Char} {f : Array (String × Json)} {r : List Char}
    (h : Object s f r) : ∃ u, Ws s ('{' :: u) := by
  cases h with
  | empty hb _ => cases hb with | mk w _ => exact ⟨_, w⟩
  | members hb _ _ => cases hb with | mk w _ => exact ⟨_, w⟩

theorem follows_of_token {t : Char} {s r : List Char} (h : Token t s r)
    (ht : t = ',' ∨ t = ']' ∨ t = '}') : Follows s := by
  intro c t' hs
  subst hs
  cases h with
  | mk w _ =>
    cases w with
    | nil =>
      rcases ht with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    | cons hc _ => exact Or.inl hc

theorem follows_of_ws {l : List Char} (h : Ws l []) : Follows l := by
  intro c t hl
  subst hl
  cases h with
  | cons hc _ => exact Or.inl hc

end Json.Spec
