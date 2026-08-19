/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec
public import Json.Spec.Length

public section

namespace Json.Spec

/-!
The grammar names at most one value for a text.

This is a claim about the transcription rather than about the parser: a grammar that derived two
values for one text would make "the value the text denotes" meaningless, and no proof about the
parser could repair it.

The relations are deliberately not deterministic in their remainder, exactly as the ABNF is not:
`12` derives as `1` with `2` left over as readily as it derives as `12`. Two things pin that
down. A value is followed either by the end of the text or by one of the characters that
separates or closes, which is what `Follows` says, and that is enough to make the value unique.
Whitespace is the other: `ws` appears on both sides of every structural character, so two
derivations of the same text can divide one run of spaces differently, and the lemmas below say
that they still reach the same place whenever what comes next is not whitespace.
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



/-! ## Numbers

A number is where the grammar is genuinely ambiguous about its remainder, so each part of one
carries the condition that pins it down: a run of digits must not be followed by a digit, a
fraction not by a point, an exponent not by an `e`. Each of those follows from `Follows` at the
end of the number, and in between from the shape of the part that comes after.
-/

private def NoDigit (l : List Char) : Prop := ∀ c t, l = c :: t → isDigit c = false

private def NoFrac (l : List Char) : Prop :=
  ∀ c t, l = c :: t → isDigit c = false ∧ c ≠ '.'

private def NoExp (l : List Char) : Prop :=
  ∀ c t, l = c :: t → isDigit c = false ∧ c ≠ 'e' ∧ c ≠ 'E'

private theorem eq_of_isWs {c : Char} (h : isWs c = true) :
    c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\x0d' := by simpa [isWs, or_assoc] using h

private theorem noExp_of_follows {l : List Char} (h : Follows l) : NoExp l := by
  intro c t hl
  rcases h c t hl with hw | rfl | rfl | rfl
  · rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  all_goals exact ⟨by decide, by decide, by decide⟩

private theorem noFrac_of_follows {l : List Char} (h : Follows l) : NoFrac l := by
  intro c t hl
  rcases h c t hl with hw | rfl | rfl | rfl
  · rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  all_goals exact ⟨by decide, by decide⟩

private theorem noDigit_of_noFrac {l : List Char} (h : NoFrac l) : NoDigit l :=
  fun c t hl => (h c t hl).1

private theorem noDigit_of_noExp {l : List Char} (h : NoExp l) : NoDigit l :=
  fun c t hl => (h c t hl).1

private theorem digits_head {s : List Char} {v n : Nat} {r : List Char} (h : Digits s v n r) :
    ∃ c t, s = c :: t ∧ isDigit c = true := by
  cases h with
  | last hd => exact ⟨_, _, rfl, hd⟩
  | cons hd _ => exact ⟨_, _, rfl, hd⟩

private theorem not_digits_cons {c : Char} (hc : isDigit c = false) {s : List Char} {v n : Nat}
    {r : List Char} : ¬ Digits (c :: s) v n r := by
  intro h
  obtain ⟨c', t', hct, hd⟩ := digits_head h
  injection hct with hcc
  subst hcc
  rw [hc] at hd
  exact absurd hd (by decide)

private theorem int_head {s : List Char} {v : Nat} {r : List Char} (h : Int' s v r) :
    ∃ c t, s = c :: t ∧ isDigit c = true := by
  cases h with
  | zero => exact ⟨_, _, rfl, by decide⟩
  | digits hc _ =>
    refine ⟨_, _, rfl, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Char.le_trans (by decide) hc.1, hc.2⟩

private theorem digits_unique {s : List Char} {v₁ n₁ : Nat} {r₁ : List Char}
    (h₁ : Digits s v₁ n₁ r₁) : ∀ {v₂ n₂ : Nat} {r₂ : List Char}, Digits s v₂ n₂ r₂ →
      NoDigit r₁ → NoDigit r₂ → v₁ = v₂ ∧ n₁ = n₂ ∧ r₁ = r₂ := by
  induction h₁ with
  | @last c r hd =>
    intro v₂ n₂ r₂ h₂ hn₁ _
    cases h₂ with
    | last => exact ⟨rfl, rfl, rfl⟩
    | cons _ h₂' =>
      obtain ⟨c', t', hct, hd'⟩ := digits_head h₂'
      rw [hct] at hn₁
      rw [hn₁ c' t' rfl] at hd'
      exact absurd hd' (by decide)
  | @cons c s v n r hd h₁' ih =>
    intro v₂ n₂ r₂ h₂ hn₁ hn₂
    cases h₂ with
    | last =>
      obtain ⟨c', t', hct, hd'⟩ := digits_head h₁'
      rw [hct] at hn₂
      rw [hn₂ c' t' rfl] at hd'
      exact absurd hd' (by decide)
    | cons _ h₂' =>
      obtain ⟨hv, hn, hr⟩ := ih h₂' hn₁ hn₂
      exact ⟨by rw [hv, hn], by rw [hn], hr⟩

private theorem int_unique {s : List Char} {v₁ v₂ : Nat} {r₁ r₂ : List Char}
    (h₁ : Int' s v₁ r₁) (h₂ : Int' s v₂ r₂) (hn₁ : NoDigit r₁) (hn₂ : NoDigit r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | zero =>
    cases h₂ with
    | zero => exact ⟨rfl, rfl⟩
    | digits hc _ => exact absurd hc (by decide)
  | digits hc₁ hd₁ =>
    cases h₂ with
    | zero => exact absurd hc₁ (by decide)
    | digits _ hd₂ =>
      obtain ⟨hv, _, hr⟩ := digits_unique hd₁ hd₂ hn₁ hn₂
      exact ⟨hv, hr⟩

private theorem frac_unique {s : List Char} {f₁ n₁ f₂ n₂ : Nat} {r₁ r₂ : List Char}
    (h₁ : Frac s f₁ n₁ r₁) (h₂ : Frac s f₂ n₂ r₂) (hn₁ : NoFrac r₁) (hn₂ : NoFrac r₂) :
    f₁ = f₂ ∧ n₁ = n₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | absent =>
    cases h₂ with
    | absent => exact ⟨rfl, rfl, rfl⟩
    | present _ => exact absurd rfl (hn₁ _ _ rfl).2
  | present hd₁ =>
    cases h₂ with
    | absent => exact absurd rfl (hn₂ _ _ rfl).2
    | present hd₂ =>
      exact digits_unique hd₁ hd₂ (noDigit_of_noFrac hn₁) (noDigit_of_noFrac hn₂)

private theorem exp_unique {s : List Char} {e₁ e₂ : Int} {r₁ r₂ : List Char}
    (h₁ : Exp s e₁ r₁) (h₂ : Exp s e₂ r₂) (hn₁ : NoExp r₁) (hn₂ : NoExp r₂) :
    e₁ = e₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | absent =>
    cases h₂ with
    | absent => exact ⟨rfl, rfl⟩
    | bare he _ => rcases he with rfl | rfl
                   · exact absurd rfl (hn₁ _ _ rfl).2.1
                   · exact absurd rfl (hn₁ _ _ rfl).2.2
    | plus he _ => rcases he with rfl | rfl
                   · exact absurd rfl (hn₁ _ _ rfl).2.1
                   · exact absurd rfl (hn₁ _ _ rfl).2.2
    | minus he _ => rcases he with rfl | rfl
                    · exact absurd rfl (hn₁ _ _ rfl).2.1
                    · exact absurd rfl (hn₁ _ _ rfl).2.2
  | bare he₁ hd₁ =>
    cases h₂ with
    | absent => rcases he₁ with rfl | rfl
                · exact absurd rfl (hn₂ _ _ rfl).2.1
                · exact absurd rfl (hn₂ _ _ rfl).2.2
    | bare _ hd₂ =>
      obtain ⟨hv, _, hr⟩ :=
        digits_unique hd₁ hd₂ (noDigit_of_noExp hn₁) (noDigit_of_noExp hn₂)
      exact ⟨by rw [hv], hr⟩
    | plus _ _ => exact absurd hd₁ (not_digits_cons (by decide))
    | minus _ _ => exact absurd hd₁ (not_digits_cons (by decide))
  | plus he₁ hd₁ =>
    cases h₂ with
    | absent => rcases he₁ with rfl | rfl
                · exact absurd rfl (hn₂ _ _ rfl).2.1
                · exact absurd rfl (hn₂ _ _ rfl).2.2
    | bare _ hd₂ => exact absurd hd₂ (not_digits_cons (by decide))
    | plus _ hd₂ =>
      obtain ⟨hv, _, hr⟩ :=
        digits_unique hd₁ hd₂ (noDigit_of_noExp hn₁) (noDigit_of_noExp hn₂)
      exact ⟨by rw [hv], hr⟩
  | minus he₁ hd₁ =>
    cases h₂ with
    | absent => rcases he₁ with rfl | rfl
                · exact absurd rfl (hn₂ _ _ rfl).2.1
                · exact absurd rfl (hn₂ _ _ rfl).2.2
    | bare _ hd₂ => exact absurd hd₂ (not_digits_cons (by decide))
    | minus _ hd₂ =>
      obtain ⟨hv, _, hr⟩ :=
        digits_unique hd₁ hd₂ (noDigit_of_noExp hn₁) (noDigit_of_noExp hn₂)
      exact ⟨by rw [hv], hr⟩

private theorem sign_unique {s : List Char} {b₁ b₂ : Bool} {a₁ a₂ : List Char} {i₁ i₂ : Nat}
    {t₁ t₂ : List Char} (h₁ : Sign s b₁ a₁) (h₂ : Sign s b₂ a₂)
    (hi₁ : Int' a₁ i₁ t₁) (hi₂ : Int' a₂ i₂ t₂) : b₁ = b₂ ∧ a₁ = a₂ := by
  cases h₁ with
  | absent =>
    cases h₂ with
    | absent => exact ⟨rfl, rfl⟩
    | minus =>
      obtain ⟨c, t, hct, hd⟩ := int_head hi₁
      injection hct with hcc
      subst hcc
      exact absurd hd (by decide)
  | minus =>
    cases h₂ with
    | absent =>
      obtain ⟨c, t, hct, hd⟩ := int_head hi₂
      injection hct with hcc
      subst hcc
      exact absurd hd (by decide)
    | minus => exact ⟨rfl, rfl⟩

private theorem noFrac_after_exp {c r : List Char} {e : Int} (he : Exp c e r) (hr : Follows r) :
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

private theorem noDigit_after_int {b c r : List Char} {f nf : Nat} {e : Int}
    (hf : Frac b f nf c) (he : Exp c e r) (hr : Follows r) : NoDigit b := by
  cases hf with
  | present _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    decide
  | absent => exact noDigit_of_noFrac (noFrac_after_exp he hr)

/-- What may follow a number is enough to say which number it is. -/
theorem num_unique {s : List Char} {n₁ n₂ : Number} {r₁ r₂ : List Char}
    (h₁ : Num s n₁ r₁) (h₂ : Num s n₂ r₂) (f₁ : Follows r₁) (f₂ : Follows r₂) :
    n₁ = n₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | mk hs₁ hi₁ hfr₁ hex₁ =>
    cases h₂ with
    | mk hs₂ hi₂ hfr₂ hex₂ =>
      obtain ⟨hb, ha⟩ := sign_unique hs₁ hs₂ hi₁ hi₂
      subst ha
      obtain ⟨hiv, hbb⟩ :=
        int_unique hi₁ hi₂ (noDigit_after_int hfr₁ hex₁ f₁) (noDigit_after_int hfr₂ hex₂ f₂)
      subst hbb
      obtain ⟨hfv, hnf, hcc⟩ :=
        frac_unique hfr₁ hfr₂ (noFrac_after_exp hex₁ f₁) (noFrac_after_exp hex₂ f₂)
      subst hcc
      obtain ⟨hev, hr⟩ := exp_unique hex₁ hex₂ (noExp_of_follows f₁) (noExp_of_follows f₂)
      refine ⟨?_, hr⟩
      rw [hb, hiv, hfv, hnf, hev]


/-! ## Strings

A string needs no condition on what follows it, because the closing quotation mark is a character
no `Ch` can begin with. The one place two constructors could both apply is a `\u` escape, and
what separates them is that no character carries a surrogate code point: a four-digit escape in
the surrogate range denotes nothing on its own, so only the pair rule can derive it.
-/

private def NoCh (l : List Char) : Prop := ∀ c r, ¬ Ch l c r

private theorem noCh_quote {t : List Char} : NoCh ('"' :: t) := by
  intro c r h
  cases h with
  | unescaped hu => exact absurd hu (by decide)

private theorem hex4_unique {s : List Char} {v₁ v₂ : Nat} {r₁ r₂ : List Char}
    (h₁ : Hex4 s v₁ r₁) (h₂ : Hex4 s v₂ r₂) : v₁ = v₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | mk a₁ b₁ c₁ d₁ =>
    cases h₂ with
    | mk a₂ b₂ c₂ d₂ =>
      rw [a₁] at a₂
      rw [b₁] at b₂
      rw [c₁] at c₂
      rw [d₁] at d₂
      injection a₂ with a
      injection b₂ with b
      injection c₂ with c
      injection d₂ with d
      subst a
      subst b
      subst c
      subst d
      exact ⟨rfl, rfl⟩

private theorem ch_unique {s : List Char} {c₁ c₂ : Char} {r₁ r₂ : List Char}
    (h₁ : Ch s c₁ r₁) (h₂ : Ch s c₂ r₂) : c₁ = c₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | unescaped hu =>
    cases h₂ with
    | unescaped => exact ⟨rfl, rfl⟩
    | _ => exact absurd hu (by decide)
  | quote =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | quote => exact ⟨rfl, rfl⟩
  | backslash =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | backslash => exact ⟨rfl, rfl⟩
  | solidus =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | solidus => exact ⟨rfl, rfl⟩
  | backspace =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | backspace => exact ⟨rfl, rfl⟩
  | formFeed =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | formFeed => exact ⟨rfl, rfl⟩
  | lineFeed =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | lineFeed => exact ⟨rfl, rfl⟩
  | carriageReturn =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | carriageReturn => exact ⟨rfl, rfl⟩
  | tab =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | tab => exact ⟨rfl, rfl⟩
  | codePoint hx₁ hv₁ =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | codePoint hx₂ hv₂ =>
      obtain ⟨hv, hr⟩ := hex4_unique hx₁ hx₂
      exact ⟨Char.toNat_inj.mp (by rw [hv₁, hv₂, hv]), hr⟩
    | surrogatePair hx₂ _ hhi₁ hhi₂ _ _ _ =>
      obtain ⟨hv, _⟩ := hex4_unique hx₁ hx₂
      rcases char_not_surrogate c₁ with h | h <;> omega
  | surrogatePair hx₁ hlo₁ hhi₁ hhi₂ hlo₃ hlo₄ hc₁ =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | codePoint hx₂ hv₂ =>
      obtain ⟨hv, _⟩ := hex4_unique hx₁ hx₂
      rcases char_not_surrogate c₂ with h | h <;> omega
    | surrogatePair hx₂ hlo₂ _ _ _ _ hc₂ =>
      obtain ⟨hvhi, hrhi⟩ := hex4_unique hx₁ hx₂
      injection hrhi with _ hrhi'
      injection hrhi' with _ hrhi''
      subst hrhi''
      obtain ⟨hvlo, hr⟩ := hex4_unique hlo₁ hlo₂
      exact ⟨Char.toNat_inj.mp (by rw [hc₁, hc₂, hvhi, hvlo]), hr⟩

private theorem chars_unique {s : List Char} {cs₁ : List Char} {r₁ : List Char}
    (h₁ : Chars s cs₁ r₁) : ∀ {cs₂ r₂ : List Char}, Chars s cs₂ r₂ →
      NoCh r₁ → NoCh r₂ → cs₁ = cs₂ ∧ r₁ = r₂ := by
  induction h₁ with
  | nil =>
    intro cs₂ r₂ h₂ hn₁ _
    cases h₂ with
    | nil => exact ⟨rfl, rfl⟩
    | cons hch _ => exact absurd hch (hn₁ _ _)
  | @cons s s' cs c r hch _ ih =>
    intro cs₂ r₂ h₂ hn₁ hn₂
    cases h₂ with
    | nil => exact absurd hch (hn₂ _ _)
    | cons hch₂ h₂' =>
      obtain ⟨hc, hs⟩ := ch_unique hch hch₂
      subst hc
      subst hs
      obtain ⟨hcs, hr⟩ := ih h₂' hn₁ hn₂
      exact ⟨by rw [hcs], hr⟩

theorem str_unique {s : List Char} {v₁ v₂ : String} {r₁ r₂ : List Char}
    (h₁ : Str s v₁ r₁) (h₂ : Str s v₂ r₂) : v₁ = v₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | mk hcs₁ =>
    cases h₂ with
    | mk hcs₂ =>
      obtain ⟨hcs, hr⟩ := chars_unique hcs₁ hcs₂ noCh_quote noCh_quote
      injection hr with _ hr'
      exact ⟨by rw [hcs], hr'⟩


/-! ## Values

Two derivations of the same text can divide a run of whitespace differently, so the remainders
they reach need not be equal: `[] ` derives with a space left over or with nothing left over.
What holds is that one remainder is the other with some whitespace taken off, which is `WsEq`,
and that is enough, because the production that follows begins with a character that is not
whitespace and so starts in the same place either way.
-/

private def WsEq (a b : List Char) : Prop := Ws a b ∨ Ws b a

private theorem WsEq.refl (a : List Char) : WsEq a a := Or.inl Ws.nil

private theorem noWs_cons {t : Char} {u : List Char} (h : isWs t = false) : NoWs (t :: u) := by
  intro c t' hc
  injection hc with hcc
  rw [← hcc]
  exact h

/-- Whitespace either side of a structural character does not move the character. -/
private theorem wsEq_token_eq {a b : List Char} {t₁ t₂ : Char} {u₁ u₂ : List Char}
    (h : WsEq a b) (h₁ : Ws a (t₁ :: u₁)) (h₂ : Ws b (t₂ :: u₂))
    (n₁ : isWs t₁ = false) (n₂ : isWs t₂ = false) : t₁ = t₂ ∧ u₁ = u₂ := by
  have key : ∀ {s : List Char}, Ws s (t₁ :: u₁) → Ws s (t₂ :: u₂) → t₁ = t₂ ∧ u₁ = u₂ := by
    intro s k₁ k₂
    have he := Ws.eq_of_noWs k₁ k₂ (noWs_cons n₁) (noWs_cons n₂)
    injection he with ht hu
    exact ⟨ht, hu⟩
  rcases h with hab | hba
  · exact key h₁ (hab.trans h₂)
  · exact key (hba.trans h₁) h₂

private theorem token_ws {x y : List Char} {t : Char} {r : List Char} (hnw : isWs t = false)
    (hw : Ws x y) (h : Token t x r) : Token t y r := by
  cases h with
  | mk h₁ h₂ =>
    rcases hw.confluent h₁ with hc | hc
    · exact Token.mk hc h₂
    · exact Token.mk (by rw [ws_eq_of_not_isWs hnw hc]; exact Ws.nil) h₂

private theorem isWs_of_isDigit {c : Char} (h : isDigit c = true) : isWs c = false := by
  cases hw : isWs c with
  | false => rfl
  | true => rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact absurd h (by decide)

private theorem digit_ne {c d : Char} (hc : isDigit c = true) (hd : isDigit d = false) : c ≠ d := by
  rintro rfl
  rw [hd] at hc
  exact absurd hc (by decide)

private theorem num_head {s : List Char} {n : Number} {r : List Char} (h : Num s n r) :
    ∃ c t, s = c :: t ∧ (c = '-' ∨ isDigit c = true) := by
  cases h with
  | mk hs hi _ _ =>
    cases hs with
    | absent =>
      obtain ⟨c, t, hct, hd⟩ := int_head hi
      exact ⟨c, t, hct, Or.inr hd⟩
    | minus => exact ⟨_, _, rfl, Or.inl rfl⟩

private theorem not_num_cons {c : Char} {t : List Char} {n : Number} {r : List Char}
    (h₁ : c ≠ '-') (h₂ : isDigit c = false) : ¬ Num (c :: t) n r := by
  intro h
  obtain ⟨c', t', hct, hc⟩ := num_head h
  injection hct with hcc
  subst hcc
  rcases hc with rfl | hd
  · exact h₁ rfl
  · rw [h₂] at hd
    exact absurd hd (by decide)

private theorem not_arr_cons {c : Char} {t : List Char} {e : Array Json} {r : List Char}
    (hw : isWs c = false) (hne : c ≠ '[') : ¬ Arr (c :: t) e r := by
  intro h
  cases h with
  | empty hb _ => exact not_token_of_ne hw hne hb
  | items hb _ _ => exact not_token_of_ne hw hne hb

private theorem not_obj_cons {c : Char} {t : List Char} {f : Array (String × Json)}
    {r : List Char} (hw : isWs c = false) (hne : c ≠ '{') : ¬ Object (c :: t) f r := by
  intro h
  cases h with
  | empty hb _ => exact not_token_of_ne hw hne hb
  | members hb _ _ => exact not_token_of_ne hw hne hb

private theorem not_value_cons {c : Char} {t : List Char} {j : Json} {r : List Char}
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

private theorem arr_ws {x y : List Char} {e : Array Json} {r : List Char} (hw : Ws x y)
    (h : Arr x e r) : Arr y e r := by
  cases h with
  | empty hb he => exact Arr.empty (token_ws (by decide) hw hb) he
  | items hb hel he => exact Arr.items (token_ws (by decide) hw hb) hel he

private theorem obj_ws {x y : List Char} {f : Array (String × Json)} {r : List Char} (hw : Ws x y)
    (h : Object x f r) : Object y f r := by
  cases h with
  | empty hb he => exact Object.empty (token_ws (by decide) hw hb) he
  | members hb hms he => exact Object.members (token_ws (by decide) hw hb) hms he

private theorem value_ws {x y : List Char} {j : Json} {r : List Char} (hw : Ws x y)
    (h : Value x j r) : Value y j r := by
  cases h with
  | false_ => rw [ws_eq_of_not_isWs (by decide) hw]; exact Value.false_
  | null => rw [ws_eq_of_not_isWs (by decide) hw]; exact Value.null
  | true_ => rw [ws_eq_of_not_isWs (by decide) hw]; exact Value.true_
  | str hs =>
    cases hs with
    | mk hcs => rw [ws_eq_of_not_isWs (by decide) hw]; exact Value.str (Str.mk hcs)
  | num hn =>
    obtain ⟨c, t, hct, hc⟩ := num_head hn
    subst hct
    have : isWs c = false := by
      rcases hc with rfl | hd
      · decide
      · exact isWs_of_isDigit hd
    rw [ws_eq_of_not_isWs this hw]
    exact Value.num hn
  | arr ha => exact Value.arr (arr_ws hw ha)
  | obj ho => exact Value.obj (obj_ws hw ho)

private theorem elements_ws {x y : List Char} {vs : List Json} {r : List Char} (hw : Ws x y)
    (h : Elements x vs r) : Elements y vs r := by
  cases h with
  | one hv => exact Elements.one (value_ws hw hv)
  | more hv hs he => exact Elements.more (value_ws hw hv) hs he

private theorem member_ws {x y : List Char} {m : String × Json} {r : List Char} (hw : Ws x y)
    (h : Member x m r) : Member y m r := by
  cases h with
  | mk hstr hsep hval =>
    cases hstr with
    | mk hcs =>
      rw [ws_eq_of_not_isWs (by decide) hw]
      exact Member.mk (Str.mk hcs) hsep hval

private theorem members_ws {x y : List Char} {ms : List (String × Json)} {r : List Char}
    (hw : Ws x y) (h : Members x ms r) : Members y ms r := by
  cases h with
  | one hm => exact Members.one (member_ws hw hm)
  | more hm hs hms => exact Members.more (member_ws hw hm) hs hms


/-! ## The value family

`Value`, `Arr`, `Object`, `Elements`, `Members` and `Member` are one mutual definition, which the
`induction` tactic will not take apart. It does not have to: every derivation leaves less text
than it was given, so an induction on the length of the text carries all six, and within one
length they are proved in the order they depend on one another.

Each statement carries what pins its remainder down. A value needs only `Follows`, since what
can come after one is the end of the text or a separator or a closing bracket. A run of elements
or members needs the closing bracket itself, because `1` followed by `,2]` and `1,2` followed by
`]` are both derivations of the same text, and only the bracket tells them apart.
-/

private theorem wsEq_common {a b : List Char} (h : WsEq a b) : ∃ c, Ws a c ∧ Ws b c := by
  rcases h with hab | hba
  · exact ⟨b, hab, Ws.nil⟩
  · exact ⟨a, Ws.nil, hba⟩

private theorem ws_to_token {a b : List Char} {t : Char} {u : List Char} (h : WsEq a b)
    (hws : Ws a (t :: u)) (hnw : isWs t = false) : Ws b (t :: u) := by
  rcases h with hab | hba
  · rcases hab.confluent hws with hc | hc
    · exact hc
    · rw [ws_eq_of_not_isWs hnw hc]
      exact Ws.nil
  · exact hba.trans hws

private theorem follows_of_token {t : Char} {s r : List Char} (h : Token t s r)
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

private theorem follows_of_ws {l : List Char} (h : Ws l []) : Follows l := by
  intro c t hl
  subst hl
  cases h with
  | cons hc _ => exact Or.inl hc

private theorem arr_begin {s : List Char} {e : Array Json} {r : List Char} (h : Arr s e r) :
    ∃ u, Ws s ('[' :: u) := by
  cases h with
  | empty hb _ => cases hb with | mk w _ => exact ⟨_, w⟩
  | items hb _ _ => cases hb with | mk w _ => exact ⟨_, w⟩

private theorem obj_begin {s : List Char} {f : Array (String × Json)} {r : List Char}
    (h : Object s f r) : ∃ u, Ws s ('{' :: u) := by
  cases h with
  | empty hb _ => cases hb with | mk w _ => exact ⟨_, w⟩
  | members hb _ _ => cases hb with | mk w _ => exact ⟨_, w⟩

private theorem str_head {s : List Char} {v : String} {r : List Char} (h : Str s v r) :
    ∃ t, s = '"' :: t := by cases h with | mk _ => exact ⟨_, rfl⟩

private theorem not_str_cons {c : Char} {t : List Char} {v : String} {r : List Char}
    (hne : c ≠ '"') : ¬ Str (c :: t) v r := by
  intro h
  cases h with
  | mk _ => exact hne rfl

private theorem not_value_bracket {t : List Char} {j : Json} {r : List Char} :
    ¬ Value (']' :: t) j r :=
  not_value_cons (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

private theorem not_elements_bracket {t : List Char} {vs : List Json} {r : List Char} :
    ¬ Elements (']' :: t) vs r := by
  intro h
  cases h with
  | one hv => exact not_value_bracket hv
  | more hv _ _ => exact not_value_bracket hv

private theorem not_members_brace {t : List Char} {ms : List (String × Json)} {r : List Char} :
    ¬ Members ('}' :: t) ms r := by
  intro h
  cases h with
  | one hm => cases hm with | mk hs _ _ => cases hs
  | more hm _ _ => cases hm with | mk hs _ _ => cases hs

private def ArrUnique (s : List Char) : Prop :=
  ∀ {e₁ r₁ e₂ r₂}, Arr s e₁ r₁ → Arr s e₂ r₂ → e₁ = e₂ ∧ WsEq r₁ r₂

private def ObjectUnique (s : List Char) : Prop :=
  ∀ {f₁ r₁ f₂ r₂}, Object s f₁ r₁ → Object s f₂ r₂ → f₁ = f₂ ∧ WsEq r₁ r₂

private def ValueUnique (s : List Char) : Prop :=
  ∀ {j₁ r₁ j₂ r₂}, Value s j₁ r₁ → Value s j₂ r₂ → Follows r₁ → Follows r₂ →
    j₁ = j₂ ∧ WsEq r₁ r₂

private def ElementsUnique (s : List Char) : Prop :=
  ∀ {vs₁ r₁ vs₂ r₂ x₁ x₂}, Elements s vs₁ r₁ → Elements s vs₂ r₂ →
    EndArray r₁ x₁ → EndArray r₂ x₂ → vs₁ = vs₂ ∧ WsEq r₁ r₂

private def MemberUnique (s : List Char) : Prop :=
  ∀ {m₁ r₁ m₂ r₂}, Member s m₁ r₁ → Member s m₂ r₂ → Follows r₁ → Follows r₂ →
    m₁ = m₂ ∧ WsEq r₁ r₂

private def MembersUnique (s : List Char) : Prop :=
  ∀ {ms₁ r₁ ms₂ r₂ x₁ x₂}, Members s ms₁ r₁ → Members s ms₂ r₂ →
    EndObject r₁ x₁ → EndObject r₂ x₂ → ms₁ = ms₂ ∧ WsEq r₁ r₂

private theorem family_unique : ∀ (n : Nat) (s : List Char), s.length ≤ n →
    ArrUnique s ∧ ObjectUnique s ∧ ValueUnique s ∧ ElementsUnique s ∧ MemberUnique s ∧
      MembersUnique s := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs
    have harr : ArrUnique s := by
      intro e₁ r₁ e₂ r₂ h₁ h₂
      cases h₁ with
      | empty hb₁ he₁ =>
        cases h₂ with
        | empty hb₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₁'.confluent w₂'
          obtain ⟨v₁, v₁'⟩ := he₁
          obtain ⟨v₂, v₂'⟩ := he₂
          obtain ⟨-, hv⟩ := wsEq_token_eq hae v₁ v₂ (by decide) (by decide)
          subst hv
          exact ⟨rfl, v₁'.confluent v₂'⟩
        | items hb₂ hel₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₁'.confluent w₂'
          obtain ⟨v₁, -⟩ := he₁
          exact absurd (elements_ws (ws_to_token hae v₁ (by decide)) hel₂) not_elements_bracket
      | items hb₁ hel₁ he₁ =>
        cases h₂ with
        | empty hb₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₂'.confluent w₁'
          obtain ⟨v₂, -⟩ := he₂
          exact absurd (elements_ws (ws_to_token hae v₂ (by decide)) hel₁) not_elements_bracket
        | items hb₂ hel₂ he₂ =>
          have hlen := token_length hb₁
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hvs, hbe⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.2.1 (elements_ws hc₁ hel₁)
              (elements_ws hc₂ hel₂) he₁ he₂
          obtain ⟨v₁, v₁'⟩ := he₁
          obtain ⟨v₂, v₂'⟩ := he₂
          obtain ⟨-, hv⟩ := wsEq_token_eq hbe v₁ v₂ (by decide) (by decide)
          subst hv
          exact ⟨by rw [hvs], v₁'.confluent v₂'⟩
    have hobj : ObjectUnique s := by
      intro f₁ r₁ f₂ r₂ h₁ h₂
      cases h₁ with
      | empty hb₁ he₁ =>
        cases h₂ with
        | empty hb₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₁'.confluent w₂'
          obtain ⟨v₁, v₁'⟩ := he₁
          obtain ⟨v₂, v₂'⟩ := he₂
          obtain ⟨-, hv⟩ := wsEq_token_eq hae v₁ v₂ (by decide) (by decide)
          subst hv
          exact ⟨rfl, v₁'.confluent v₂'⟩
        | members hb₂ hms₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₁'.confluent w₂'
          obtain ⟨v₁, -⟩ := he₁
          exact absurd (members_ws (ws_to_token hae v₁ (by decide)) hms₂) not_members_brace
      | members hb₁ hms₁ he₁ =>
        cases h₂ with
        | empty hb₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₂'.confluent w₁'
          obtain ⟨v₂, -⟩ := he₂
          exact absurd (members_ws (ws_to_token hae v₂ (by decide)) hms₁) not_members_brace
        | members hb₂ hms₂ he₂ =>
          have hlen := token_length hb₁
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hms, hbe⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.2.2.2 (members_ws hc₁ hms₁)
              (members_ws hc₂ hms₂) he₁ he₂
          obtain ⟨v₁, v₁'⟩ := he₁
          obtain ⟨v₂, v₂'⟩ := he₂
          obtain ⟨-, hv⟩ := wsEq_token_eq hbe v₁ v₂ (by decide) (by decide)
          subst hv
          exact ⟨by rw [hms], v₁'.confluent v₂'⟩
    have hval : ValueUnique s := by
      intro j₁ r₁ j₂ r₂ h₁ h₂ f₁ f₂
      cases h₁ with
      | false_ =>
        cases h₂ with
        | false_ => exact ⟨rfl, WsEq.refl _⟩
        | str hst => exact absurd hst (not_str_cons (by decide))
        | num hn => exact absurd hn (not_num_cons (by decide) (by decide))
        | arr ha => exact absurd ha (not_arr_cons (by decide) (by decide))
        | obj ho => exact absurd ho (not_obj_cons (by decide) (by decide))
      | null =>
        cases h₂ with
        | null => exact ⟨rfl, WsEq.refl _⟩
        | str hst => exact absurd hst (not_str_cons (by decide))
        | num hn => exact absurd hn (not_num_cons (by decide) (by decide))
        | arr ha => exact absurd ha (not_arr_cons (by decide) (by decide))
        | obj ho => exact absurd ho (not_obj_cons (by decide) (by decide))
      | true_ =>
        cases h₂ with
        | true_ => exact ⟨rfl, WsEq.refl _⟩
        | str hst => exact absurd hst (not_str_cons (by decide))
        | num hn => exact absurd hn (not_num_cons (by decide) (by decide))
        | arr ha => exact absurd ha (not_arr_cons (by decide) (by decide))
        | obj ho => exact absurd ho (not_obj_cons (by decide) (by decide))
      | str hs₁ =>
        obtain ⟨t, hshape⟩ := str_head hs₁
        subst hshape
        cases h₂ with
        | str hs₂ =>
          obtain ⟨hv, hr⟩ := str_unique hs₁ hs₂
          exact ⟨by rw [hv], by rw [hr]; exact WsEq.refl _⟩
        | num hn => exact absurd hn (not_num_cons (by decide) (by decide))
        | arr ha => exact absurd ha (not_arr_cons (by decide) (by decide))
        | obj ho => exact absurd ho (not_obj_cons (by decide) (by decide))
      | num hn₁ =>
        cases h₂ with
        | false_ => exact absurd hn₁ (not_num_cons (by decide) (by decide))
        | null => exact absurd hn₁ (not_num_cons (by decide) (by decide))
        | true_ => exact absurd hn₁ (not_num_cons (by decide) (by decide))
        | str hst =>
          obtain ⟨t, hshape⟩ := str_head hst
          subst hshape
          exact absurd hn₁ (not_num_cons (by decide) (by decide))
        | num hn₂ =>
          obtain ⟨hv, hr⟩ := num_unique hn₁ hn₂ f₁ f₂
          exact ⟨by rw [hv], by rw [hr]; exact WsEq.refl _⟩
        | arr ha =>
          obtain ⟨c, t, hct, hc⟩ := num_head hn₁
          subst hct
          rcases hc with rfl | hd
          · exact absurd ha (not_arr_cons (by decide) (by decide))
          · exact absurd ha (not_arr_cons (isWs_of_isDigit hd) (digit_ne hd (by decide)))
        | obj ho =>
          obtain ⟨c, t, hct, hc⟩ := num_head hn₁
          subst hct
          rcases hc with rfl | hd
          · exact absurd ho (not_obj_cons (by decide) (by decide))
          · exact absurd ho (not_obj_cons (isWs_of_isDigit hd) (digit_ne hd (by decide)))
      | arr ha₁ =>
        cases h₂ with
        | false_ => exact absurd ha₁ (not_arr_cons (by decide) (by decide))
        | null => exact absurd ha₁ (not_arr_cons (by decide) (by decide))
        | true_ => exact absurd ha₁ (not_arr_cons (by decide) (by decide))
        | str hst =>
          obtain ⟨t, hshape⟩ := str_head hst
          subst hshape
          exact absurd ha₁ (not_arr_cons (by decide) (by decide))
        | num hn =>
          obtain ⟨c, t, hct, hc⟩ := num_head hn
          subst hct
          rcases hc with rfl | hd
          · exact absurd ha₁ (not_arr_cons (by decide) (by decide))
          · exact absurd ha₁ (not_arr_cons (isWs_of_isDigit hd) (digit_ne hd (by decide)))
        | arr ha₂ =>
          obtain ⟨he, hr⟩ := harr ha₁ ha₂
          exact ⟨by rw [he], hr⟩
        | obj ho =>
          obtain ⟨u₁, w₁⟩ := arr_begin ha₁
          obtain ⟨u₂, w₂⟩ := obj_begin ho
          obtain ⟨hc, -⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
      | obj ho₁ =>
        cases h₂ with
        | false_ => exact absurd ho₁ (not_obj_cons (by decide) (by decide))
        | null => exact absurd ho₁ (not_obj_cons (by decide) (by decide))
        | true_ => exact absurd ho₁ (not_obj_cons (by decide) (by decide))
        | str hst =>
          obtain ⟨t, hshape⟩ := str_head hst
          subst hshape
          exact absurd ho₁ (not_obj_cons (by decide) (by decide))
        | num hn =>
          obtain ⟨c, t, hct, hc⟩ := num_head hn
          subst hct
          rcases hc with rfl | hd
          · exact absurd ho₁ (not_obj_cons (by decide) (by decide))
          · exact absurd ho₁ (not_obj_cons (isWs_of_isDigit hd) (digit_ne hd (by decide)))
        | arr ha =>
          obtain ⟨u₁, w₁⟩ := obj_begin ho₁
          obtain ⟨u₂, w₂⟩ := arr_begin ha
          obtain ⟨hc, -⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
        | obj ho₂ =>
          obtain ⟨hf, hr⟩ := hobj ho₁ ho₂
          exact ⟨by rw [hf], hr⟩
    have hels : ElementsUnique s := by
      intro vs₁ r₁ vs₂ r₂ x₁ x₂ h₁ h₂ e₁ e₂
      cases h₁ with
      | one hv₁ =>
        cases h₂ with
        | one hv₂ =>
          obtain ⟨hv, hr⟩ :=
            hval hv₁ hv₂ (follows_of_token e₁ (by decide)) (follows_of_token e₂ (by decide))
          exact ⟨by rw [hv], hr⟩
        | more hv₂ hsep₂ _ =>
          obtain ⟨-, hwe⟩ :=
            hval hv₁ hv₂ (follows_of_token e₁ (by decide)) (follows_of_token hsep₂ (by decide))
          obtain ⟨w₁, -⟩ := e₁
          obtain ⟨w₂, -⟩ := hsep₂
          obtain ⟨hc, -⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
      | more hv₁ hsep₁ hel₁ =>
        cases h₂ with
        | one hv₂ =>
          obtain ⟨-, hwe⟩ :=
            hval hv₁ hv₂ (follows_of_token hsep₁ (by decide)) (follows_of_token e₂ (by decide))
          obtain ⟨w₁, -⟩ := hsep₁
          obtain ⟨w₂, -⟩ := e₂
          obtain ⟨hc, -⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
        | more hv₂ hsep₂ hel₂ =>
          obtain ⟨hveq, hwe⟩ :=
            hval hv₁ hv₂ (follows_of_token hsep₁ (by decide)) (follows_of_token hsep₂ (by decide))
          have hlen₁ := value_length hv₁
          have hlen₂ := token_length hsep₁
          obtain ⟨w₁, w₁'⟩ := hsep₁
          obtain ⟨w₂, w₂'⟩ := hsep₂
          obtain ⟨-, hu⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hvs, hr⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.2.1 (elements_ws hc₁ hel₁)
              (elements_ws hc₂ hel₂) e₁ e₂
          exact ⟨by rw [hveq, hvs], hr⟩
    have hmem : MemberUnique s := by
      intro m₁ r₁ m₂ r₂ h₁ h₂ f₁ f₂
      cases h₁ with
      | mk hs₁ hn₁ hv₁ =>
        cases h₂ with
        | mk hs₂ hn₂ hv₂ =>
          have hlen₁ := str_length hs₁
          have hlen₂ := token_length hn₁
          obtain ⟨hk, ha⟩ := str_unique hs₁ hs₂
          subst ha
          obtain ⟨w₁, w₁'⟩ := hn₁
          obtain ⟨w₂, w₂'⟩ := hn₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl _) w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hv, hr⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.1 (value_ws hc₁ hv₁) (value_ws hc₂ hv₂) f₁ f₂
          exact ⟨by rw [hk, hv], hr⟩
    have hmems : MembersUnique s := by
      intro ms₁ r₁ ms₂ r₂ x₁ x₂ h₁ h₂ e₁ e₂
      cases h₁ with
      | one hm₁ =>
        cases h₂ with
        | one hm₂ =>
          obtain ⟨hm, hr⟩ :=
            hmem hm₁ hm₂ (follows_of_token e₁ (by decide)) (follows_of_token e₂ (by decide))
          exact ⟨by rw [hm], hr⟩
        | more hm₂ hsep₂ _ =>
          obtain ⟨-, hwe⟩ :=
            hmem hm₁ hm₂ (follows_of_token e₁ (by decide)) (follows_of_token hsep₂ (by decide))
          obtain ⟨w₁, -⟩ := e₁
          obtain ⟨w₂, -⟩ := hsep₂
          obtain ⟨hc, -⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
      | more hm₁ hsep₁ hms₁ =>
        cases h₂ with
        | one hm₂ =>
          obtain ⟨-, hwe⟩ :=
            hmem hm₁ hm₂ (follows_of_token hsep₁ (by decide)) (follows_of_token e₂ (by decide))
          obtain ⟨w₁, -⟩ := hsep₁
          obtain ⟨w₂, -⟩ := e₂
          obtain ⟨hc, -⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
        | more hm₂ hsep₂ hms₂ =>
          obtain ⟨hmeq, hwe⟩ :=
            hmem hm₁ hm₂ (follows_of_token hsep₁ (by decide)) (follows_of_token hsep₂ (by decide))
          have hlen₁ := member_length hm₁
          have hlen₂ := token_length hsep₁
          obtain ⟨w₁, w₁'⟩ := hsep₁
          obtain ⟨w₂, w₂'⟩ := hsep₂
          obtain ⟨-, hu⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hms, hr⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.2.2.2 (members_ws hc₁ hms₁)
              (members_ws hc₂ hms₂) e₁ e₂
          exact ⟨by rw [hmeq, hms], hr⟩
    exact ⟨harr, hobj, hval, hels, hmem, hmems⟩


/-! ## Text -/

/--
A text names at most one value.

The two derivations need not divide the leading whitespace the same way, so they are brought to
a common starting point first; from there `Follows` holds of both remainders, because a text
ends in nothing but whitespace.
-/
theorem text_unique {s : List Char} {j₁ j₂ : Json} (h₁ : Text s j₁) (h₂ : Text s j₂) : j₁ = j₂ := by
  obtain ⟨a₁, b₁, hw₁, hv₁, he₁⟩ := h₁
  obtain ⟨a₂, b₂, hw₂, hv₂, he₂⟩ := h₂
  obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (hw₁.confluent hw₂)
  exact ((family_unique c.length c (Nat.le_refl _)).2.2.1 (value_ws hc₁ hv₁) (value_ws hc₂ hv₂)
    (follows_of_ws he₁) (follows_of_ws he₂)).1

/-- The same for a `String`, which is the form the parser's entry point takes. -/
theorem textOf_unique {s : String} {j₁ j₂ : Json} (h₁ : TextOf s j₁) (h₂ : TextOf s j₂) :
    j₁ = j₂ := text_unique h₁ h₂

end Json.Spec
