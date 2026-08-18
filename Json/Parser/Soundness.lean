/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser
public import Json.Spec
public import Json.Spec.Unambiguity
public import Json.Spec.Canonical

public section

namespace Json.Parser

/-!
What the parser accepts, stated against the grammar.

The scanner walks the text by position, while `Json.Spec` is written over a list of characters, so
the two are related here first: `remaining p` is what is left of the text at `p`, and one step of
the scanner takes one character off the front of it. Everything else is proved in those terms.

The leaves come first: whitespace, the literals, the parts of a number, and a string with its
escapes. The machine follows, where what a stack of frames still demands of the text is written
down as `Closes` and every accepting run is shown to have a derivation behind it.
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


/-! ## The machine

A leaf scanner is a production of the grammar and nothing else, so its soundness is stated
directly. The machine is not: it holds what it has read so far in frames and closes them later,
so the text after a value has to finish every frame still on the stack before the parse is a
derivation at all.

Three relations say what that amounts to. `ElementsRest` and `MembersRest` describe the text
after a value or a member, which is the rest of the array or object around it and its closing
bracket. `Closes` describes the stack: each frame consumes its rest and hands the value it
completes to the frame outside it, and the empty stack is the whole value.
-/

/-- The elements after one already read, and the closing bracket. -/
private inductive ElementsRest : List Char → List Json → List Char → Prop where
  | close {t r} : Spec.EndArray t r → ElementsRest t [] r
  | more {t t₁ t₂ v vs r} : Spec.ValueSeparator t t₁ → Spec.Value t₁ v t₂ →
      ElementsRest t₂ vs r → ElementsRest t (v :: vs) r

/-- The members after one already read, and the closing brace. -/
private inductive MembersRest : List Char → List (String × Json) → List Char → Prop where
  | close {t r} : Spec.EndObject t r → MembersRest t [] r
  | more {t t₁ t₂ m ms r} : Spec.ValueSeparator t t₁ → Spec.Member t₁ m t₂ →
      MembersRest t₂ ms r → MembersRest t (m :: ms) r

private def ElementsEnd (t : List Char) (vs : List Json) (r : List Char) : Prop :=
  ∃ t', Spec.Elements t vs t' ∧ Spec.EndArray t' r

private def MembersEnd (t : List Char) (ms : List (String × Json)) (r : List Char) : Prop :=
  ∃ t', Spec.Members t ms t' ∧ Spec.EndObject t' r

private theorem elementsEnd_cons {t₂ r : List Char} {vs : List Json}
    (hrest : ElementsRest t₂ vs r) :
    ∀ {t₁ : List Char} {v : Json}, Spec.Value t₁ v t₂ → ElementsEnd t₁ (v :: vs) r := by
  induction hrest with
  | close hend => exact fun hv => ⟨_, Spec.Elements.one hv, hend⟩
  | more hsep hv₂ _ ih =>
    intro t₁ v hv
    obtain ⟨t', hels, hend⟩ := ih hv₂
    exact ⟨t', Spec.Elements.more hv hsep hels, hend⟩

private theorem membersEnd_cons {t₂ r : List Char} {ms : List (String × Json)}
    (hrest : MembersRest t₂ ms r) :
    ∀ {t₁ : List Char} {m : String × Json}, Spec.Member t₁ m t₂ → MembersEnd t₁ (m :: ms) r := by
  induction hrest with
  | close hend => exact fun hm => ⟨_, Spec.Members.one hm, hend⟩
  | more hsep hm₂ _ ih =>
    intro t₁ m hm
    obtain ⟨t', hms, hend⟩ := ih hm₂
    exact ⟨t', Spec.Members.more hm hsep hms, hend⟩

/-- What the frames still on the stack demand of the text after the value just read. -/
private def Closes : List Frame → Json → List Char → Json → List Char → Prop
  | [], v, t, j, r => j = v ∧ r = t
  | .arr elems :: outer, v, t, j, r =>
      ∃ vs t', ElementsRest t vs t' ∧ Closes outer (.arr (elems.push v ++ vs.toArray)) t' j r
  | .obj fields _ name :: outer, v, t, j, r =>
      ∃ ms t', MembersRest t ms t' ∧
        Closes outer (.obj (fields.push (name, v) ++ ms.toArray)) t' j r


/-!
Each of the machine's three functions calls the others, and every call is made at a position
strictly further on, so a single induction on how much text is left carries all three at once.
-/

private theorem ws_of_skipWs {q w : s.Pos} {u : Unit} {hw : w.remainingBytes ≤ q.remainingBytes}
    (h : skipWs q = ⟨u, w, hw⟩) : Spec.Ws (remaining q) (remaining w) := by
  have hws := ws_skipWs q
  rw [h] at hws
  exact hws

/-- A structural character, with whatever whitespace the scanner passed over either side of it. -/
private theorem token_of {t : Char} {p q r r' : s.Pos}
    (hlead : Spec.Ws (remaining p) (remaining q)) (hstep : step? q = some (t, r))
    (htrail : Spec.Ws (remaining r) (remaining r')) : Spec.Token t (remaining p) (remaining r') :=
  Spec.Token.mk (remaining_step hstep ▸ hlead) htrail

private def ValueSound (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (stack : List Frame) (j : Json) (rp : s.Pos),
    value cfg p depth stack = .ok (j, rp) →
      ∃ v t, Spec.Value (remaining p) v t ∧ Closes stack v t j (remaining rp)

private def ContinueSound (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (v : Json) (depth : Nat) (stack : List Frame) (j : Json) (rp : s.Pos),
    continueWith cfg v p depth stack = .ok (j, rp) →
      Closes stack v (remaining p) j (remaining rp)

private def MemberSound (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (fields : Array (String × Json)) (seen : Std.HashSet String)
      (stack : List Frame) (j : Json) (rp : s.Pos),
    member cfg p depth fields seen stack = .ok (j, rp) →
      ∃ m ms t₁ t, Spec.Member (remaining p) m t₁ ∧ MembersRest t₁ ms t ∧
        Closes stack (.obj (fields ++ (m :: ms).toArray)) t j (remaining rp)

private theorem machine_sound (cfg : Config) :
    ∀ (n : Nat) (p : s.Pos), p.remainingBytes ≤ n →
      ValueSound cfg p ∧ ContinueSound cfg p ∧ MemberSound cfg p := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · intro depth stack j rp
      fun_cases value cfg p depth stack with
      | case1 => intro h; simp at h
      | case2 q hc _ r hr hex =>
        intro h
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 .null depth stack j rp h
        have ht : remaining p = 'n' :: 'u' :: 'l' :: 'l' :: remaining r := by
          simp [remaining_step hc, expect?_eq hex]
        exact ⟨.null, remaining r, by rw [ht]; exact Spec.Value.null, hcont⟩
      | case3 => intro h; simp at h
      | case4 q hc _ r hr hex =>
        intro h
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 (.bool true) depth stack j rp h
        have ht : remaining p = 't' :: 'r' :: 'u' :: 'e' :: remaining r := by
          simp [remaining_step hc, expect?_eq hex]
        exact ⟨.bool true, remaining r, by rw [ht]; exact Spec.Value.true_, hcont⟩
      | case5 => intro h; simp at h
      | case6 q hc _ r hr hex =>
        intro h
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 (.bool false) depth stack j rp h
        have ht : remaining p = 'f' :: 'a' :: 'l' :: 's' :: 'e' :: remaining r := by
          simp [remaining_step hc, expect?_eq hex]
        exact ⟨.bool false, remaining r, by rw [ht]; exact Spec.Value.false_, hcont⟩
      | case7 => intro h; simp at h
      | case8 => intro h; simp at h
      | case9 q hc text r hr hstr =>
        intro h
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 (.str text) depth stack j rp h
        exact ⟨.str text, remaining r, Spec.Value.str (str_sound hc hstr), hcont⟩
      | case10 => intro h; simp at h
      | case11 q hc _ _ w hw hsw after hb =>
        intro h
        have hlt : after.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        have hcont := (ih _ hlt after (Nat.le_refl _)).2.1 (.arr #[]) depth stack j rp h
        exact ⟨.arr #[], remaining after,
          Spec.Value.arr (Spec.Arr.empty (token_of Spec.Ws.nil hc (ws_of_skipWs hsw))
            (token_of Spec.Ws.nil hb Spec.Ws.nil)), hcont⟩
      | case12 q hc _ _ w hw hsw _ =>
        intro h
        have hlt : w.remainingBytes < n := by have := step?_lt hc; omega
        obtain ⟨v, t, hv, hcl⟩ :=
          (ih _ hlt w (Nat.le_refl _)).1 (depth + 1) (.arr #[] :: stack) j rp h
        simp only [Closes] at hcl
        obtain ⟨vs, t', hrest, hcl⟩ := hcl
        obtain ⟨t'', hels, hend⟩ := elementsEnd_cons hrest hv
        refine ⟨.arr (v :: vs).toArray, t',
          Spec.Value.arr (Spec.Arr.items (token_of Spec.Ws.nil hc (ws_of_skipWs hsw)) hels hend),
          ?_⟩
        simpa using hcl
      | case13 => intro h; simp at h
      | case14 q hc _ _ w hw hsw after hb =>
        intro h
        have hlt : after.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        have hcont := (ih _ hlt after (Nat.le_refl _)).2.1 (.obj #[]) depth stack j rp h
        exact ⟨.obj #[], remaining after,
          Spec.Value.obj (Spec.Object.empty (token_of Spec.Ws.nil hc (ws_of_skipWs hsw))
            (token_of Spec.Ws.nil hb Spec.Ws.nil)), hcont⟩
      | case15 q hc _ _ w hw hsw _ =>
        intro h
        have hlt : w.remainingBytes < n := by have := step?_lt hc; omega
        obtain ⟨m, ms, t₁, t, hm, hrest, hcl⟩ :=
          (ih _ hlt w (Nat.le_refl _)).2.2 (depth + 1) #[] ∅ stack j rp h
        obtain ⟨t'', hms, hendo⟩ := membersEnd_cons hrest hm
        refine ⟨.obj (m :: ms).toArray, t,
          Spec.Value.obj (Spec.Object.members (token_of Spec.Ws.nil hc (ws_of_skipWs hsw)) hms
            hendo), ?_⟩
        simpa using hcl
      | case16 => intro h; simp at h
      | case17 _ _ _ _ _ _ _ _ hc _ m r hr hnum =>
        intro h
        have hlt : r.remainingBytes < n := by omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 (.num m) depth stack j rp h
        exact ⟨.num m, remaining r, Spec.Value.num (number_sound hnum), hcont⟩
      | case18 => intro h; simp at h
    · intro v depth stack j rp
      fun_cases continueWith cfg v p depth stack with
      | case1 =>
        intro h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, by rw [h.2]⟩
      | case2 elems outer _ w hw hsw after hb _ w₂ hw₂ hsw₂ =>
        intro h
        have hlt : w₂.remainingBytes < n := by have := step?_lt hb; omega
        obtain ⟨v₂, t, hv, hcl⟩ :=
          (ih _ hlt w₂ (Nat.le_refl _)).1 depth (.arr (elems.push v) :: outer) j rp h
        simp only [Closes] at hcl ⊢
        obtain ⟨vs, t', hrest, hcl⟩ := hcl
        refine ⟨v₂ :: vs, t',
          ElementsRest.more (token_of (ws_of_skipWs hsw) hb (ws_of_skipWs hsw₂)) hv hrest, ?_⟩
        simpa using hcl
      | case3 elems outer _ w hw hsw after hb =>
        intro h
        have hlt : after.remainingBytes < n := by have := step?_lt hb; omega
        have hcont :=
          (ih _ hlt after (Nat.le_refl _)).2.1 (.arr (elems.push v)) (depth - 1) outer j rp h
        simp only [Closes]
        exact ⟨[], remaining after,
          ElementsRest.close (token_of (ws_of_skipWs hsw) hb Spec.Ws.nil), by simpa using hcont⟩
      | case4 => intro h; simp at h
      | case5 => intro h; simp at h
      | case6 fields seen name outer _ w hw hsw after hb _ w₂ hw₂ hsw₂ =>
        intro h
        have hlt : w₂.remainingBytes < n := by have := step?_lt hb; omega
        obtain ⟨m, ms, t₁, t, hm, hrest, hcl⟩ :=
          (ih _ hlt w₂ (Nat.le_refl _)).2.2 depth (fields.push (name, v)) seen outer j rp h
        simp only [Closes]
        exact ⟨m :: ms, t,
          MembersRest.more (token_of (ws_of_skipWs hsw) hb (ws_of_skipWs hsw₂)) hm hrest, hcl⟩
      | case7 fields seen name outer _ w hw hsw after hb =>
        intro h
        have hlt : after.remainingBytes < n := by have := step?_lt hb; omega
        have hcont := (ih _ hlt after (Nat.le_refl _)).2.1 (.obj (fields.push (name, v)))
          (depth - 1) outer j rp h
        simp only [Closes]
        exact ⟨[], remaining after,
          MembersRest.close (token_of (ws_of_skipWs hsw) hb Spec.Ws.nil), by simpa using hcont⟩
      | case8 => intro h; simp at h
      | case9 => intro h; simp at h
    · intro depth fields seen stack j rp
      fun_cases member cfg p depth fields seen stack with
      | case1 => intro h; simp at h
      | case2 => intro h; simp at h
      | case3 q hc name k hk hstr _ _ w hw hsw after hb _ w₂ hw₂ hsw₂ =>
        intro h
        have hlt : w₂.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        obtain ⟨v, t, hv, hcl⟩ := (ih _ hlt w₂ (Nat.le_refl _)).1 depth
          (.obj fields (seen.insert name) name :: stack) j rp h
        simp only [Closes] at hcl
        obtain ⟨ms, t', hrest, hcl⟩ := hcl
        refine ⟨(name, v), ms, t, t',
          Spec.Member.mk (str_sound hc hstr)
            (token_of (ws_of_skipWs hsw) hb (ws_of_skipWs hsw₂)) hv, hrest, ?_⟩
        simpa using hcl
      | case4 => intro h; simp at h
      | case5 => intro h; simp at h
      | case6 => intro h; simp at h
      | case7 => intro h; simp at h


/-! ## Text

`Spec.Text` is one value with whitespace either side of it and nothing else, which is what the
entry points read.
-/

theorem text_parseFrom {cfg : Config} {start : s.Pos} {j : Json}
    (h : parseFrom cfg start = .ok j) : Spec.Text (remaining start) j := by
  simp only [parseFrom] at h
  split at h
  · simp at h
  · next j' p hv =>
    split at h
    · next hend =>
      obtain ⟨v, t, hval, hcl⟩ :=
        (machine_sound cfg _ (skipWs start).pos (Nat.le_refl _)).1 0 [] j' p hv
      simp only [Closes] at hcl
      obtain ⟨hj, ht⟩ := hcl
      injection h with hjj
      refine ⟨_, t, ws_skipWs start, ?_, ?_⟩
      · rw [← hjj, hj]
        exact hval
      · rw [← ht]
        exact remaining_none hend ▸ ws_skipWs p
    · simp at h

end

/--
What the parser accepts is a text of the grammar, save that a byte order mark it was configured
to ignore is no part of one.
-/
theorem text_parse {s : String} {cfg : Config} {j : Json} (h : parse s cfg = .ok j) :
    ∃ t, Spec.Text t j ∧ (s.toList = t ∨ s.toList = Char.ofNat 0xFEFF :: t) := by
  cases hc : step? s.startPos with
  | none =>
    simp only [parse, hc] at h
    exact ⟨_, text_parseFrom h, Or.inl remaining_startPos.symm⟩
  | some cq =>
    obtain ⟨c, q⟩ := cq
    simp only [parse, hc] at h
    split at h
    · next hbom =>
      refine ⟨_, text_parseFrom h, Or.inr ?_⟩
      have hval : c.toNat = 0xFEFF := by
        simp only [Bool.and_eq_true] at hbom
        exact eq_of_beq hbom.2
      have hbomChar : c = Char.ofNat 0xFEFF :=
        Char.toNat_inj.mp (by rw [hval]; rfl)
      rw [← remaining_startPos, remaining_step hc, hbomChar]
    · exact ⟨_, text_parseFrom h, Or.inl remaining_startPos.symm⟩

/-- With no byte order mark to set aside, what the parser accepts is a text of the grammar. -/
theorem textOf_parse {s : String} {cfg : Config} {j : Json} (hbom : cfg.ignoreBOM = false)
    (h : parse s cfg = .ok j) : Spec.TextOf s j := by
  cases hc : step? s.startPos with
  | none =>
    simp only [parse, hc] at h
    show Spec.Text s.toList j
    rw [← remaining_startPos]
    exact text_parseFrom h
  | some cq =>
    obtain ⟨c, q⟩ := cq
    simp only [parse, hc, hbom] at h
    show Spec.Text s.toList j
    rw [← remaining_startPos]
    exact text_parseFrom h


/--
The value the parser returns is the value the grammar names, there being no other: soundness says
the text derives it, and `Spec.textOf_unique` says the text derives nothing else.
-/
theorem eq_of_textOf {s : String} {cfg : Config} {j j' : Json} (hbom : cfg.ignoreBOM = false)
    (h : parse s cfg = .ok j) (ht : Spec.TextOf s j') : j = j' :=
  Spec.textOf_unique (textOf_parse hbom h) ht


/--
Every number the parser returns is canonical, whatever the text spelled, since the grammar
records what the digits denote rather than how they were written.
-/
theorem canonicalNumbers_parse {s : String} {cfg : Config} {j : Json} (h : parse s cfg = .ok j) :
    CanonicalNumbers j := by
  obtain ⟨t, ht, -⟩ := text_parse h
  exact Spec.canonicalNumbers_of_text ht

/-- Bytes the parser accepts are UTF-8 for a text of the grammar. -/
theorem textOf_parseBytes {b : ByteArray} {cfg : Config} {j : Json} (hbom : cfg.ignoreBOM = false)
    (h : parseBytes b cfg = .ok j) :
    ∃ text, String.fromUTF8? b = some text ∧ Spec.TextOf text j := by
  rw [parseBytes] at h
  split at h
  · next text hs => exact ⟨text, hs, textOf_parse hbom h⟩
  · simp at h

end Json.Parser
