/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser
public import Json.Spec

public section

namespace Json.Parser

/-!
What the parser accepts, stated against the grammar.

The scanner walks the text by position, while `Json.Spec` is written over a list of characters, so
the two are related here first: `remaining p` is what is left of the text at `p`, and one step of
the scanner takes one character off the front of it. Everything else is proved in those terms.

Every leaf is here: whitespace, the literals, the parts of a number, and a string with its
escapes. The machine is not, and needs an invariant relating the frame stack and the remaining
text to a partial derivation.
-/

section
variable {s : String}

/-- What is left of the text at `p`. -/
def remaining (p : s.Pos) : List Char := (s.sliceFrom p).copy.toList

theorem remaining_startPos : remaining s.startPos = s.toList := by
  rw [remaining, String.Pos.Splits.eq_right s.startPos.splits (String.splits_startPos s)]

theorem remaining_endPos : remaining s.endPos = [] := by
  rw [remaining, String.Pos.Splits.eq_right s.endPos.splits (String.splits_endPos s)]
  rfl

theorem remaining_step {p q : s.Pos} {c : Char} (h : step? p = some (c, q)) :
    remaining p = c :: remaining q := by
  rw [step?] at h
  split at h
  · simp at h
  · next hp =>
    obtain ⟨hc, hq⟩ := Prod.mk.injEq .. ▸ Option.some.injEq .. ▸ h
    subst hc
    subst hq
    rw [remaining, String.Pos.Splits.eq_right p.splits (String.Pos.splits_next_right p hp),
      remaining]
    simp

theorem remaining_none {p : s.Pos} (h : step? p = none) : remaining p = [] := by
  rw [step?] at h
  split at h
  · next hp => exact hp ▸ remaining_endPos
  · simp at h


/-! ## Whitespace and literals -/

theorem ws_skipWs (start : s.Pos) :
    Spec.Ws (remaining start) (remaining (skipWs start).pos) := by
  have go : ∀ (p : s.Pos) (h : p.remainingBytes ≤ start.remainingBytes),
      Spec.Ws (remaining p) (remaining (skipWs.go start p h).pos) := by
    intro p h
    fun_induction skipWs.go start p h with
    | case1 p h c q hc hws ih =>
      rw [remaining_step hc]
      exact Spec.Ws.cons hws ih
    | case2 p h c q hc hws => exact Spec.Ws.nil
    | case3 p h hc => exact Spec.Ws.nil
  exact go start (Nat.le_refl _)

theorem expect?_eq {p : s.Pos} {l : List Char} {r : Consumed Unit p} (h : expect? p l = some r) :
    remaining p = l ++ remaining r.pos := by
  induction l generalizing p r with
  | nil =>
    rw [expect?] at h
    injection h with h
    simp [← h]
  | cons c rest ih =>
    rw [expect?] at h
    split at h
    · next c' q hc =>
      split at h
      · next hcc =>
        split at h
        · next t ht =>
          injection h with h
          rw [remaining_step hc, ← h, ih ht]
          simp [eq_of_beq hcc]
        · simp at h
      · simp at h
    · simp at h


/-! ## Numbers

The scanner reads digits left to right, accumulating as it goes, while `Spec.Digits` is built from
the first digit and the run that follows it. What bridges them is the invariant below: a run
either stops where it started or forms a `Digits` derivation whose value and length combine with
what the loop had already accumulated.
-/

private theorem digits_go_sound {start : s.Pos} :
    ∀ (p : s.Pos) (value count : Nat) (h : p.remainingBytes ≤ start.remainingBytes),
      ((digits.go start p value count h).pos = p ∧
          (digits.go start p value count h).value = (value, count)) ∨
        ∃ v n, Spec.Digits (remaining p) v n (remaining (digits.go start p value count h).pos) ∧
          (digits.go start p value count h).value = (value * 10 ^ n + v, count + n) := by
  intro p value count h
  fun_induction digits.go start p value count h with
  | case1 p value count h c q hc hd ih =>
    refine .inr ?_
    rcases ih with ⟨hpos, hval⟩ | ⟨v, n, hspec, hval⟩
    · refine ⟨Spec.digitVal c, 1, ?_, by rw [hval]⟩
      rw [remaining_step hc, hpos]
      exact Spec.Digits.last hd
    · refine ⟨Spec.digitVal c * 10 ^ n + v, n + 1, ?_, ?_⟩
      · rw [remaining_step hc]
        exact Spec.Digits.cons hd hspec
      · rw [hval, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ n)]
        simp only [Prod.mk.injEq]
        omega
  | case2 p value count h c q hc hd => exact .inl ⟨rfl, rfl⟩
  | case3 p value count h hc => exact .inl ⟨rfl, rfl⟩

/-- A digit and the run of digits after it are a `Digits` derivation. -/
theorem digits_sound {p q : s.Pos} {c : Char} (hc : step? p = some (c, q))
    (hd : Spec.isDigit c = true) :
    Spec.Digits (remaining p) (digits q (Spec.digitVal c) 1).value.1
      (digits q (Spec.digitVal c) 1).value.2 (remaining (digits q (Spec.digitVal c) 1).pos) := by
  rw [digits, remaining_step hc]
  rcases digits_go_sound (start := q) q (Spec.digitVal c) 1 (Nat.le_refl _) with
    ⟨hpos, hval⟩ | ⟨v, n, hspec, hval⟩
  · rw [hpos, hval]
    exact Spec.Digits.last hd
  · rw [hval, Nat.add_comm 1 n]
    exact Spec.Digits.cons hd hspec


private theorem one_le_of_isDigit {c : Char} (hd : Spec.isDigit c = true) (h0 : ¬ c = '0') :
    ('1' ≤ c && c ≤ '9') = true := by
  simp only [Spec.isDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def,
    UInt32.le_iff_toNat_le] at hd ⊢
  obtain ⟨hd1, hd2⟩ := hd
  have hne : c.val.toNat ≠ ('0' : Char).val.toNat := fun he => h0 (Char.toNat_inj.mp he)
  have h0' : ('0' : Char).val.toNat = 48 := rfl
  have h1' : ('1' : Char).val.toNat = 49 := rfl
  omega

theorem intPart_sound {p : s.Pos} {r : Scanned (Nat × Nat) p} (h : intPart p = .ok r) :
    Spec.Int' (remaining p) r.value.1 (remaining r.pos) := by
  rw [intPart] at h
  split at h
  · next q hc =>
    injection h with h
    rw [remaining_step hc, ← h]
    exact Spec.Int'.zero
  · next c q hne hc =>
    split at h
    · next hd =>
      injection h with h
      have hdig := digits_sound hc hd
      rw [remaining_step hc] at hdig
      rw [remaining_step hc, ← h]
      exact Spec.Int'.digits (one_le_of_isDigit hd hne) hdig
    · simp at h
  · simp at h


theorem fracPart_sound {p : s.Pos} {r : Consumed (Nat × Nat) p} (h : fracPart p = .ok r) :
    Spec.Frac (remaining p) r.value.1 r.value.2 (remaining r.pos) := by
  rw [fracPart] at h
  split at h
  · next q hc =>
    split at h
    · next c t hd =>
      split at h
      · next hdig =>
        injection h with h
        have hdigs := digits_sound hd hdig
        rw [remaining_step hc, ← h]
        exact Spec.Frac.present hdigs
      · simp at h
    · simp at h
  · injection h with h
    rw [← h]
    exact Spec.Frac.absent

private theorem expSign_sound (p : s.Pos) :
    ((expSign p).value = false ∧ (expSign p).pos = p) ∨
      ((expSign p).value = false ∧ remaining p = '+' :: remaining (expSign p).pos) ∨
      ((expSign p).value = true ∧ remaining p = '-' :: remaining (expSign p).pos) := by
  rw [expSign]
  split
  · next q hs => exact .inr (.inl ⟨rfl, remaining_step hs⟩)
  · next q hs => exact .inr (.inr ⟨rfl, remaining_step hs⟩)
  · exact .inl ⟨rfl, rfl⟩

theorem expPart_sound {p : s.Pos} {r : Consumed (Int × Nat) p} (h : expPart p = .ok r) :
    Spec.Exp (remaining p) r.value.1 (remaining r.pos) := by
  rw [expPart] at h
  split at h
  · next e q he =>
    split at h
    · next hcond =>
      have hE : e = 'e' ∨ e = 'E' := by
        rcases Bool.or_eq_true .. ▸ hcond with h' | h'
        · exact .inl (eq_of_beq h')
        · exact .inr (eq_of_beq h')
      split at h
      · next negative w hsign hs =>
        split at h
        · next c t hd =>
          split at h
          · next hdig =>
            injection h with h
            have hdigs := digits_sound hd hdig
            rw [remaining_step he, ← h]
            rcases expSign_sound q with ⟨hneg, hpos⟩ | ⟨hneg, hplus⟩ | ⟨hneg, hminus⟩
            · simp only [hs] at hneg hpos
              subst hneg
              subst hpos
              simpa using Spec.Exp.bare hE hdigs
            · simp only [hs] at hneg hplus
              subst hneg
              rw [hplus]
              simpa using Spec.Exp.plus hE hdigs
            · simp only [hs] at hneg hminus
              subst hneg
              rw [hminus]
              simpa using Spec.Exp.minus hE hdigs
          · simp at h
        · simp at h
    · injection h with h
      rw [← h]
      exact Spec.Exp.absent
  · injection h with h
    rw [← h]
    exact Spec.Exp.absent


private theorem unsignedNumber_sound {cfg : Config} {p : s.Pos} {neg : Bool} {t : List Char}
    {res : Scanned Number p} (hsign : Spec.Sign t neg (remaining p))
    (h : unsignedNumber cfg p neg = .ok res) : Spec.Num t res.value (remaining res.pos) := by
  rw [unsignedNumber] at h
  split at h
  · simp at h
  · next i hi =>
    split at h
    · simp at h
    · next f hf =>
      split at h
      · simp at h
      · next x hx =>
        split at h
        · simp at h
        · injection h with h
          rw [← h]
          exact Spec.Num.mk hsign (intPart_sound hi) (fracPart_sound hf) (expPart_sound hx)

/-- What `number` accepts is a number of the grammar, denoting the value it returns. -/
theorem number_sound {cfg : Config} {p : s.Pos} {res : Scanned Number p}
    (h : number cfg p = .ok res) : Spec.Num (remaining p) res.value (remaining res.pos) := by
  rw [number] at h
  split at h
  · next q hc =>
    split at h
    · simp at h
    · next r hr =>
      injection h with h
      have hs : Spec.Sign (remaining p) true (remaining q) := by
        rw [remaining_step hc]
        exact Spec.Sign.minus
      rw [← h]
      simpa using unsignedNumber_sound (t := remaining p) hs hr
  · exact unsignedNumber_sound Spec.Sign.absent h
  · simp at h


/-! ## Strings -/

private theorem hexDigit?_sound {p : s.Pos} {r : Scanned Nat p} (h : hexDigit? p = some r) :
    ∃ c, Spec.hexVal? c = some r.value ∧ remaining p = c :: remaining r.pos := by
  rw [hexDigit?] at h
  split at h
  · next c q hc =>
    split at h
    · next v hv =>
      injection h with h
      rw [← h]
      exact ⟨c, hv, remaining_step hc⟩
    · simp at h
  · simp at h

theorem hex4?_sound {p : s.Pos} {r : Scanned Nat p} (h : hex4? p = some r) :
    Spec.Hex4 (remaining p) r.value (remaining r.pos) := by
  rw [hex4?] at h
  split at h
  · simp at h
  · next r₁ h₁ =>
    split at h
    · simp at h
    · next r₂ h₂ =>
      split at h
      · simp at h
      · next r₃ h₃ =>
        split at h
        · simp at h
        · next r₄ h₄ =>
          injection h with h
          obtain ⟨c₁, hv₁, hr₁⟩ := hexDigit?_sound h₁
          obtain ⟨c₂, hv₂, hr₂⟩ := hexDigit?_sound h₂
          obtain ⟨c₃, hv₃, hr₃⟩ := hexDigit?_sound h₃
          obtain ⟨c₄, hv₄, hr₄⟩ := hexDigit?_sound h₄
          rw [← h, hr₁, hr₂, hr₃, hr₄]
          exact Spec.Hex4.mk hv₁ hv₂ hv₃ hv₄


private theorem escapeHex4?_sound {p : s.Pos} {r : Scanned Nat p} (h : escapeHex4? p = some r) :
    ∃ t, remaining p = '\\' :: 'u' :: t ∧ Spec.Hex4 t r.value (remaining r.pos) := by
  rw [escapeHex4?] at h
  split at h
  · next q hc =>
    split at h
    · next w hu =>
      split at h
      · next hh hx =>
        injection h with h
        refine ⟨remaining w, ?_, ?_⟩
        · rw [remaining_step hc, remaining_step hu]
        · rw [← h]
          exact hex4?_sound hx
      · simp at h
    · simp at h
  · simp at h

private theorem hexVal?_lt {c : Char} {v : Nat} (h : Spec.hexVal? c = some v) : v < 16 := by
  have h0 : ('0' : Char).toNat = 48 := rfl
  have h9 : ('9' : Char).toNat = 57 := rfl
  have ha : ('a' : Char).toNat = 97 := rfl
  have hf : ('f' : Char).toNat = 102 := rfl
  have hA : ('A' : Char).toNat = 65 := rfl
  have hF : ('F' : Char).toNat = 70 := rfl
  rw [Spec.hexVal?] at h
  split at h
  · next hc =>
    injection h with h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
      Char.toNat_val] at hc
    omega
  · split at h
    · next hc =>
      injection h with h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
        Char.toNat_val] at hc
      omega
    · split at h
      · next hc =>
        injection h with h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
          Char.toNat_val] at hc
        omega
      · simp at h

private theorem hex4_lt {t : List Char} {v : Nat} {r : List Char} (h : Spec.Hex4 t v r) :
    v < 65536 := by
  cases h with
  | mk h₁ h₂ h₃ h₄ =>
    have b₁ := hexVal?_lt h₁
    have b₂ := hexVal?_lt h₂
    have b₃ := hexVal?_lt h₃
    have b₄ := hexVal?_lt h₄
    omega

private theorem charOfCodePoint?_toNat {v : Nat} {c : Char} (hv : v < 1114112)
    (h : charOfCodePoint? v = some c) : c.toNat = v := by
  rw [charOfCodePoint?] at h
  split at h
  · injection h with h
    have hsize : v < UInt32.size := by
      have hs : UInt32.size = 4294967296 := rfl
      omega
    rw [← h, Char.toNat_mk, UInt32.toNat_ofNat_of_lt' hsize]
  · simp at h


private theorem escapeChar?_sound {c ch : Char} (h : escapeChar? c = some ch) (r : List Char) :
    Spec.Ch ('\\' :: c :: r) ch r := by
  rw [escapeChar?] at h
  split at h
  · next hc =>
    injection h with h
    rw [eq_of_beq hc, ← h]
    exact Spec.Ch.quote
  · split at h
    · next hc =>
      injection h with h
      rw [eq_of_beq hc, ← h]
      exact Spec.Ch.backslash
    · split at h
      · next hc =>
        injection h with h
        rw [eq_of_beq hc, ← h]
        exact Spec.Ch.solidus
      · split at h
        · next hc =>
          injection h with h
          rw [eq_of_beq hc, ← h]
          exact Spec.Ch.backspace
        · split at h
          · next hc =>
            injection h with h
            rw [eq_of_beq hc, ← h]
            exact Spec.Ch.formFeed
          · split at h
            · next hc =>
              injection h with h
              rw [eq_of_beq hc, ← h]
              exact Spec.Ch.lineFeed
            · split at h
              · next hc =>
                injection h with h
                rw [eq_of_beq hc, ← h]
                exact Spec.Ch.carriageReturn
              · split at h
                · next hc =>
                  injection h with h
                  rw [eq_of_beq hc, ← h]
                  exact Spec.Ch.tab
                · simp at h


private theorem codePoint_bound {v : Nat} (h : v < 65536) : v < 1114112 := by omega

private theorem combineSurrogates_bound {hi lo : Nat} (h₁ : hi ≤ 56319) (h₂ : lo ≤ 57343) :
    combineSurrogates hi lo < 1114112 := by
  have h : combineSurrogates hi lo = 65536 + (hi - 55296) * 1024 + (lo - 56320) := rfl
  omega

private theorem stringStep_done_sound (p : s.Pos) :
    ∀ q, stringStep p = .done q → remaining p = '"' :: remaining q := by
  fun_cases stringStep p with
  | case2 w hc =>
    intro q h
    injection h with h
    subst h
    exact remaining_step hc
  | _ => intro q h; simp at h

private theorem stringStep_char_sound (p : s.Pos) :
    ∀ c q, stringStep p = .char c q → Spec.Ch (remaining p) c (remaining q) := by
  fun_cases stringStep p with
  | case6 w hc r hu hex hx hrange ch hcp =>
    intro c q h
    injection h with hch hq
    subst hq
    have hhex := hex4?_sound hx
    have hlt := hex4_lt hhex
    have hbound := codePoint_bound (hex4_lt hhex)
    have hval : ch.toNat = hex.value := charOfCodePoint?_toNat hbound hcp
    rw [← hch, remaining_step hc, remaining_step hu]
    exact Spec.Ch.codePoint hhex hval
  | case9 w hc r hu hex hx hrange hhigh lo hlo hbounds ch hcp =>
    intro c q h
    injection h with hch hq
    subst hq
    have hhex := hex4?_sound hx
    obtain ⟨t, hpre, hhex2⟩ := escapeHex4?_sound hlo
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hrange
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbounds
    rw [hpre] at hhex
    have hbound := combineSurrogates_bound hhigh hbounds.2
    have hval : ch.toNat = combineSurrogates hex.value lo.value :=
      charOfCodePoint?_toNat hbound hcp
    rw [← hch, remaining_step hc, remaining_step hu]
    refine Spec.Ch.surrogatePair hhex hhex2 hrange.1 hhigh hbounds.1 hbounds.2 ?_
    rw [hval]
    rfl
  | case13 w hc e r hne hu ch he =>
    intro c q h
    injection h with hch hq
    subst hq
    rw [← hch, remaining_step hc, remaining_step hu]
    exact escapeChar?_sound he _
  | case14 e w hquote hesc hc hun =>
    intro c q h
    injection h with hch hq
    subst hq
    rw [← hch, remaining_step hc]
    exact Spec.Ch.unescaped hun
  | _ => intro c q h; simp at h


private theorem string_go_sound {start : s.Pos} :
    ∀ (p : s.Pos) (acc : String) (h : p.remainingBytes ≤ start.remainingBytes)
      (r : Scanned String start), string.go start p acc h = .ok r →
      ∃ cs, Spec.Chars (remaining p) cs ('"' :: remaining r.pos) ∧
        r.value.toList = acc.toList ++ cs := by
  intro p acc h
  fun_induction string.go start p acc h with
  | case1 p acc h e hs =>
    intro r hr
    simp at hr
  | case2 p acc h q hs =>
    intro r hr
    injection hr with hr
    refine ⟨[], ?_, ?_⟩
    · rw [← hr, stringStep_done_sound p q hs]
      exact Spec.Chars.nil
    · rw [← hr]
      simp
  | case3 p acc h c q hs ih =>
    intro r hr
    obtain ⟨cs, hchars, hval⟩ := ih r hr
    refine ⟨c :: cs, Spec.Chars.cons (stringStep_char_sound p c q hs) hchars, ?_⟩
    rw [hval, String.toList_push]
    simp

/-- What `string` accepts, after the opening quotation mark, is the characters of the grammar. -/
theorem string_sound {p : s.Pos} {acc : String} {r : Scanned String p}
    (h : string p acc = .ok r) :
    ∃ cs, Spec.Chars (remaining p) cs ('"' :: remaining r.pos) ∧
      r.value.toList = acc.toList ++ cs :=
  string_go_sound p acc (Nat.le_refl _) r h


/-- What the scanner reads between quotation marks is a string of the grammar. -/
theorem str_sound {p q : s.Pos} {r : Scanned String q} (hc : step? p = some ('"', q))
    (h : string q "" = .ok r) : Spec.Str (remaining p) r.value (remaining r.pos) := by
  obtain ⟨cs, hchars, hval⟩ := string_sound h
  have hstr : String.ofList cs = r.value := by
    have hcs : r.value.toList = cs := by simpa using hval
    rw [← hcs, String.ofList_toList]
  rw [remaining_step hc, ← hstr]
  exact Spec.Str.mk hchars

end

end Json.Parser

