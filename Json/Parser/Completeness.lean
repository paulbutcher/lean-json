/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser.Soundness
public import Json.Spec.Follow
public import Json.Spec.Unambiguity

public section

@[expose] section

namespace Json.Parser

variable {s : String}

/-!
The other direction: what the grammar derives, the parser accepts.

Three things shape the work. The value needs no tracking, since `parse_eq_of_isOk` gets it from
soundness and unambiguity together, which leaves only the obligation that a derivable text is
never refused. A scanner has to be shown maximal, which soundness never needed: `Ws` relates a
text to any of its whitespace-suffixes, while `skipWs` lands on exactly one of them, so the two
are tied together by what the scanner leaves rather than by what it consumes. And a derivation
can have taken whitespace the parser has not yet looked at, so what the machine concludes about
the position it stops at is stated with `Ws` rather than with equality.
-/

/--
On a text the grammar derives, returning anything at all is returning the right thing, there
being one value the text names and soundness saying the returned one is among them.
-/
theorem parse_eq_of_isOk {cfg : Config} {j : Json} (hbom : cfg.ignoreBOM = false)
    (ht : Spec.TextOf s j) (hok : (parse s cfg).isOk) : parse s cfg = .ok j := by
  cases h : parse s cfg with
  | error e => rw [h] at hok; exact absurd hok (by simp [Except.isOk, Except.toBool])
  | ok j' => rw [eq_of_textOf hbom h ht]

/-- The scanner stops at a character that is not whitespace, or at the end. -/
theorem noWs_skipWs (start : s.Pos) : Spec.NoWs (remaining (skipWs start).pos) := by
  have go : ∀ (p : s.Pos) (h : p.remainingBytes ≤ start.remainingBytes),
      Spec.NoWs (remaining (skipWs.go start p h).pos) := by
    intro p h
    fun_induction skipWs.go start p h with
    | case1 p h c q hc hws ih => exact ih
    | case2 p h c q hc hws =>
      intro c' t hct
      rw [remaining_step hc] at hct
      simp only [List.cons.injEq] at hct
      obtain ⟨rfl, -⟩ := hct
      simpa using hws
    | case3 p h hc =>
      intro c' t hct
      rw [remaining_none hc] at hct
      exact absurd hct (by simp)
  exact go start (Nat.le_refl _)

/-- Whatever whitespace a derivation passed over, the scanner passes over exactly that much. -/
theorem skipWs_complete {p : s.Pos} {t : List Char} (h : Spec.Ws (remaining p) t)
    (hn : Spec.NoWs t) : remaining (skipWs p).pos = t :=
  Spec.Ws.eq_of_noWs (ws_skipWs p) h (noWs_skipWs p) hn


/-- Reading a character is taking the head off what remains. -/
theorem step_of_remaining {p : s.Pos} {c : Char} {t : List Char} (h : remaining p = c :: t) :
    ∃ q, step? p = some (c, q) ∧ remaining q = t := by
  cases hs : step? p with
  | none => rw [remaining_none hs] at h; exact absurd h (by simp)
  | some cq =>
    obtain ⟨c', q⟩ := cq
    have he := remaining_step hs
    rw [h] at he
    simp only [List.cons.injEq] at he
    obtain ⟨hcc, htt⟩ := he
    subst hcc
    exact ⟨q, rfl, htt.symm⟩

/-! ## Numbers -/

/-- The loop stops at a character that is not a digit, or at the end. -/
theorem noDigit_digits (start : s.Pos) (value count : Nat) :
    Spec.NoDigit (remaining (digits start value count).pos) := by
  have go : ∀ (p : s.Pos) (v n : Nat) (h : p.remainingBytes ≤ start.remainingBytes),
      Spec.NoDigit (remaining (digits.go start p v n h).pos) := by
    intro p v n h
    fun_induction digits.go start p v n h with
    | case1 p v n h c q hc hd ih => exact ih
    | case2 p v n h c q hc hd =>
      intro c' t hct
      rw [remaining_step hc] at hct
      simp only [List.cons.injEq] at hct
      obtain ⟨rfl, -⟩ := hct
      simpa using hd
    | case3 p v n h hc =>
      intro c' t hct
      rw [remaining_none hc] at hct
      exact absurd hct (by simp)
  exact go start value count (Nat.le_refl _)

/-- Whatever run of digits a derivation took, the loop takes exactly that run. -/
theorem digits_complete {p q : s.Pos} {c : Char} (hc : step? p = some (c, q))
    (hd : Spec.isDigit c = true) {v n : Nat} {t : List Char}
    (h : Spec.Digits (remaining p) v n t) (hn : Spec.NoDigit t) :
    (digits q (Spec.digitVal c) 1).value = (v, n) ∧
      remaining (digits q (Spec.digitVal c) 1).pos = t := by
  obtain ⟨hv, hnn, hr⟩ :=
    Spec.digits_unique (digits_sound hc hd) h (noDigit_digits q (Spec.digitVal c) 1) hn
  exact ⟨by rw [Prod.ext_iff]; exact ⟨hv, hnn⟩, hr⟩

theorem intPart_complete {p : s.Pos} {v : Nat} {t : List Char}
    (h : Spec.Int' (remaining p) v t) (hn : Spec.NoDigit t) :
    ∃ r : Scanned (Nat × Nat) p, intPart p = .ok r ∧ r.value.1 = v ∧ remaining r.pos = t := by
  obtain ⟨c, u, hcu, hd⟩ := Spec.int_head h
  obtain ⟨q, hq, hqu⟩ := step_of_remaining hcu
  rw [hcu] at h
  rw [intPart]
  split
  · next q' hz =>
    have hqq := hq.symm.trans hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hqq
    obtain ⟨rfl, rfl⟩ := hqq
    cases h with
    | zero => exact ⟨_, rfl, rfl, hqu⟩
    | digits hc _ => exact absurd hc (by decide)
  · next c' q' hne hz =>
    have hqq := hq.symm.trans hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hqq
    obtain ⟨rfl, rfl⟩ := hqq
    split
    · next hdig =>
      cases h with
      | zero => exact absurd rfl hne
      | digits _ hdigs =>
        rw [← hcu] at hdigs
        obtain ⟨hval, hpos⟩ := digits_complete hq hdig hdigs hn
        exact ⟨_, rfl, by rw [hval], hpos⟩
    · next hdig => exact absurd hd hdig
  · next hz => rw [hq] at hz; exact absurd hz (by simp)

theorem fracPart_complete {p : s.Pos} {f n : Nat} {t : List Char}
    (h : Spec.Frac (remaining p) f n t) (hn : Spec.NoFrac t) :
    ∃ r : Consumed (Nat × Nat) p, fracPart p = .ok r ∧ r.value = (f, n) ∧ remaining r.pos = t := by
  rw [fracPart]
  split
  · next q hz =>
    rw [remaining_step hz] at h
    cases h with
    | absent => exact absurd rfl (hn _ _ rfl).2
    | present hdigs =>
      obtain ⟨c, w, hcw, hdg⟩ := Spec.digits_head hdigs
      obtain ⟨r', hr', hrw⟩ := step_of_remaining hcw
      split
      · next c' r'' hd2 =>
        have hqq := hr'.symm.trans hd2
        simp only [Option.some.injEq, Prod.mk.injEq] at hqq
        obtain ⟨rfl, rfl⟩ := hqq
        split
        · next hdig =>
          obtain ⟨hval, hpos⟩ := digits_complete hr' hdig hdigs (Spec.noDigit_of_noFrac hn)
          exact ⟨_, rfl, hval, hpos⟩
        · next hdig => exact absurd hdg hdig
      · next hd2 => rw [hr'] at hd2; exact absurd hd2 (by simp)
  · next hz =>
    have hne : ∀ u, remaining p ≠ '.' :: u := by
      intro u hu
      obtain ⟨q, hq, -⟩ := step_of_remaining hu
      exact hz q hq
    obtain ⟨rfl, rfl, rfl⟩ := Spec.frac_absent h hne
    exact ⟨_, rfl, rfl, rfl⟩
/-! ### The optional sign of an exponent -/

theorem expSign_absent {p q : s.Pos} {c : Char} (h : step? p = some (c, q)) (h₁ : c ≠ '+')
    (h₂ : c ≠ '-') : expSign p = ⟨false, p, Nat.le_refl _⟩ := by
  rw [expSign]
  split
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with hc _
    exact absurd hc h₁
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with hc _
    exact absurd hc h₂
  · rfl

theorem expSign_plus {p q : s.Pos} (h : step? p = some ('+', q)) :
    expSign p = ⟨false, q, Nat.le_of_lt (step?_lt h)⟩ := by
  rw [expSign]
  split
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with _ hq
    subst hq
    rfl
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with hc _
    exact absurd hc (by decide)
  · next h₁ _ => exact absurd h (h₁ q)

theorem expSign_minus {p q : s.Pos} (h : step? p = some ('-', q)) :
    expSign p = ⟨true, q, Nat.le_of_lt (step?_lt h)⟩ := by
  rw [expSign]
  split
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with hc _
    exact absurd hc (by decide)
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with _ hq
    subst hq
    rfl
  · next _ h₂ => exact absurd h (h₂ q)

theorem expPart_complete {p : s.Pos} {e : Int} {t : List Char}
    (h : Spec.Exp (remaining p) e t) (hn : Spec.NoExp t) :
    ∃ r : Consumed (Int × Nat) p, expPart p = .ok r ∧ r.value.1 = e ∧ remaining r.pos = t := by
  rw [expPart]
  split
  · next c q hz =>
    have hrp := remaining_step hz
    rw [hrp] at h
    split
    · next hcond =>
      have hE : c = 'e' ∨ c = 'E' := by
        rcases Bool.or_eq_true .. ▸ hcond with h' | h'
        · exact .inl (eq_of_beq h')
        · exact .inr (eq_of_beq h')
      obtain ⟨P, v, n, hpos, hdigs, he⟩ :
          ∃ (P : s.Pos) (v n : Nat), (expSign q).pos = P ∧ Spec.Digits (remaining P) v n t ∧
            e = (if (expSign q).value then -(v : Int) else (v : Int)) := by
        rcases Spec.exp_head h hn hE with ⟨v, n, hdigs, rfl⟩ | ⟨u, v, n, hu, hdigs, rfl⟩ |
            ⟨u, v, n, hu, hdigs, rfl⟩
        · obtain ⟨d, w, hdw, hdd⟩ := Spec.digits_head hdigs
          obtain ⟨q₂, hq₂, -⟩ := step_of_remaining hdw
          rw [expSign_absent hq₂ (Spec.digit_ne hdd (by decide)) (Spec.digit_ne hdd (by decide))]
          exact ⟨q, v, n, rfl, hdigs, rfl⟩
        · obtain ⟨q₂, hq₂, hq₂u⟩ := step_of_remaining hu
          rw [expSign_plus hq₂]
          exact ⟨q₂, v, n, rfl, by rw [hq₂u]; exact hdigs, rfl⟩
        · obtain ⟨q₂, hq₂, hq₂u⟩ := step_of_remaining hu
          rw [expSign_minus hq₂]
          exact ⟨q₂, v, n, rfl, by rw [hq₂u]; exact hdigs, rfl⟩
      split
      · next negative r hsign heq =>
        simp only [heq] at hpos he
        subst hpos
        obtain ⟨d, w, hdw, hdd⟩ := Spec.digits_head hdigs
        obtain ⟨q₃, hq₃, -⟩ := step_of_remaining hdw
        split
        · next d' r'' hd2 =>
          have hqq := hq₃.symm.trans hd2
          simp only [Option.some.injEq, Prod.mk.injEq] at hqq
          obtain ⟨rfl, rfl⟩ := hqq
          split
          · next hdig =>
            obtain ⟨hval, hrest⟩ := digits_complete hq₃ hdig hdigs (Spec.noDigit_of_noExp hn)
            refine ⟨_, rfl, ?_, hrest⟩
            simp only [hval, he]
          · next hdig => exact absurd hdd hdig
        · next hd2 => rw [hq₃] at hd2; exact absurd hd2 (by simp)
    · next hcond =>
      have hne : ∀ c' u, c :: remaining q = c' :: u → c' ≠ 'e' ∧ c' ≠ 'E' := by
        intro c' u hu
        injection hu with hcc
        subst hcc
        exact ⟨fun hE => hcond (by simp [hE]), fun hE => hcond (by simp [hE])⟩
      obtain ⟨rfl, rfl⟩ := Spec.exp_absent h hne
      exact ⟨_, rfl, rfl, hrp⟩
  · next hz =>
    rw [remaining_none hz] at h
    obtain ⟨rfl, rfl⟩ := Spec.exp_absent h (by intro c u hu; exact absurd hu (by simp))
    exact ⟨_, rfl, rfl, remaining_none hz⟩

theorem unsignedNumber_complete {cfg : Config} {p : s.Pos} {neg : Bool} {i f nf : Nat} {e : Int}
    {u₂ u₃ t : List Char} (hi : Spec.Int' (remaining p) i u₂) (hfr : Spec.Frac u₂ f nf u₃)
    (hex : Spec.Exp u₃ e t) (hft : Spec.Follows t) (hlim : cfg.maxNumberDigits = none) :
    ∃ r : Scanned Number p, unsignedNumber cfg p neg = .ok r ∧
      r.value = Number.normalize
        (if neg then -((i * 10 ^ nf + f : Nat) : Int) else ((i * 10 ^ nf + f : Nat) : Int))
        (e - nf) ∧ remaining r.pos = t := by
  obtain ⟨ri, hri, hriv, hrip⟩ := intPart_complete hi (Spec.noDigit_after_int hfr hex hft)
  rw [← hrip] at hfr
  obtain ⟨rf, hrf, hrfv, hrfp⟩ := fracPart_complete hfr (Spec.noFrac_after_exp hex hft)
  rw [← hrfp] at hex
  obtain ⟨rx, hrx, hrxv, hrxp⟩ := expPart_complete hex (Spec.noExp_of_follows hft)
  simp only [unsignedNumber, hri, hrf, hrx, tooManyDigits, hlim, Bool.or_self]
  refine ⟨_, rfl, ?_, hrxp⟩
  simp only [hriv, hrfv, hrxv]

theorem number_complete {cfg : Config} {p : s.Pos} {n : Number} {t : List Char}
    (h : Spec.Num (remaining p) n t) (hft : Spec.Follows t) (hlim : cfg.maxNumberDigits = none) :
    ∃ r : Scanned Number p, number cfg p = .ok r ∧ r.value = n ∧ remaining r.pos = t := by
  cases h with
  | mk hs hi hfr hex =>
    rw [number]
    split
    · next q hz =>
      rcases Spec.sign_head hs with ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
      · obtain ⟨c, u, hcu, hd⟩ := Spec.int_head hi
        rw [remaining_step hz] at hcu
        injection hcu with hcc
        subst hcc
        exact absurd hd (by decide)
      · rw [remaining_step hz] at hm
        injection hm with _ hst
        rw [← hst] at hi
        obtain ⟨ru, hru, hruv, hrup⟩ := unsignedNumber_complete hi hfr hex hft hlim
        rw [hru]
        exact ⟨_, rfl, hruv, hrup⟩
    · next q hne hz =>
      rcases Spec.sign_head hs with ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
      · obtain ⟨ru, hru, hruv, hrup⟩ := unsignedNumber_complete hi hfr hex hft hlim
        rw [hru]
        exact ⟨_, rfl, hruv, hrup⟩
      · rw [remaining_step hz] at hm
        injection hm with hcc
        exact absurd (by rw [← hcc] : q = ('-', q.snd)) (hne q.snd)
    · next hz =>
      obtain ⟨c, u, hcu, -⟩ := Spec.int_head hi
      rcases Spec.sign_head hs with ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
      · rw [remaining_none hz] at hcu
        exact absurd hcu (by simp)
      · rw [remaining_none hz] at hm
        exact absurd hm (by simp)

/-! ## Strings -/

theorem charOfCodePoint?_self (c : Char) : charOfCodePoint? c.toNat = some c := by
  have hv : UInt32.ofNat c.toNat = c.val := UInt32.ofNat_toNat
  rw [charOfCodePoint?, dif_pos (hv ▸ c.valid)]
  simp [hv]

theorem hexDigit?_complete {p : s.Pos} {c : Char} {v : Nat} {t : List Char}
    (hl : remaining p = c :: t) (hv : Spec.hexVal? c = some v) :
    ∃ r : Scanned Nat p, hexDigit? p = some r ∧ r.value = v ∧ remaining r.pos = t := by
  obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
  rw [hexDigit?]
  split
  · next c' q' hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with hcc hqq
    subst hcc
    subst hqq
    split
    · next v' hv' =>
      rw [hv] at hv'
      injection hv' with hvv
      exact ⟨_, rfl, hvv.symm, hqt⟩
    · next hv' => rw [hv] at hv'; exact absurd hv' (by simp)
  · next hc => rw [hq] at hc; exact absurd hc (by simp)

theorem hex4?_complete {p : s.Pos} {l : List Char} {v : Nat} {t : List Char}
    (hl : remaining p = l) (h : Spec.Hex4 l v t) :
    ∃ r : Scanned Nat p, hex4? p = some r ∧ r.value = v ∧ remaining r.pos = t := by
  cases h with
  | mk h₁ h₂ h₃ h₄ =>
    obtain ⟨r₁, hr₁, hv₁, hp₁⟩ := hexDigit?_complete hl h₁
    obtain ⟨r₂, hr₂, hv₂, hp₂⟩ := hexDigit?_complete hp₁ h₂
    obtain ⟨r₃, hr₃, hv₃, hp₃⟩ := hexDigit?_complete hp₂ h₃
    obtain ⟨r₄, hr₄, hv₄, hp₄⟩ := hexDigit?_complete hp₃ h₄
    simp only [hex4?, hr₁, hr₂, hr₃, hr₄]
    exact ⟨_, rfl, by rw [hv₁, hv₂, hv₃, hv₄], hp₄⟩

theorem escapeHex4?_complete {p : s.Pos} {l : List Char} {v : Nat} {t : List Char}
    (hl : remaining p = '\\' :: 'u' :: l) (h : Spec.Hex4 l v t) :
    ∃ r : Scanned Nat p, escapeHex4? p = some r ∧ r.value = v ∧ remaining r.pos = t := by
  obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
  obtain ⟨w, hw, hwt⟩ := step_of_remaining hqt
  obtain ⟨r, hr, hrv, hrp⟩ := hex4?_complete hwt h
  rw [escapeHex4?]
  split
  · next q' hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with _ hqq
    subst hqq
    split
    · next w' hu =>
      rw [hw] at hu
      injection hu with hu'
      injection hu' with _ hww
      subst hww
      rw [hr]
      exact ⟨_, rfl, hrv, hrp⟩
    · next hu => exact (hu w hw).elim
  · next hc => exact (hc q hq).elim

theorem stringStep_unescaped {p q : s.Pos} {c : Char} (hs : step? p = some (c, q))
    (hu : Spec.isUnescaped c = true) : stringStep p = .char c q := by
  rw [stringStep]
  split
  · next hc => rw [hs] at hc; exact absurd hc (by simp)
  · next w hc =>
    rw [hs] at hc
    injection hc with hc'
    injection hc' with hcc
    rw [hcc] at hu
    exact absurd hu (by decide)
  · next w hc =>
    rw [hs] at hc
    injection hc with hc'
    injection hc' with hcc
    rw [hcc] at hu
    exact absurd hu (by decide)
  · next c' w hc =>
    rw [hs] at hc
    injection hc with hc'
    injection hc' with hcc hww
    subst hcc
    subst hww
    rw [if_pos hu]

theorem stringStep_escape {p q r : s.Pos} {d ch : Char} (h₁ : step? p = some ('\\', q))
    (h₂ : step? q = some (d, r)) (he : escapeChar? d = some ch) : stringStep p = .char ch r := by
  have hu : d ≠ 'u' := by intro h; rw [h] at he; simp [escapeChar?] at he
  rw [stringStep]
  split
  · next hc => rw [h₁] at hc; exact absurd hc (by simp)
  · next w hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact absurd hcc (by decide)
  · next w hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with _ hww
    subst hww
    split
    · next hd => rw [h₂] at hd; exact absurd hd (by simp)
    · next w' hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with hdd
      exact absurd hdd hu
    · next d' w' hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with hdd hww'
      subst hdd
      subst hww'
      rw [he]
  · next _ _ _ _ hn2 hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact (hn2 hcc.symm).elim

theorem stringStep_codePoint {p q w : s.Pos} {v : Nat} {t : List Char} {c : Char}
    (h₁ : step? p = some ('\\', q)) (h₂ : step? q = some ('u', w))
    (hx : Spec.Hex4 (remaining w) v t) (hcv : c.toNat = v) :
    ∃ r : s.Pos, stringStep p = .char c r ∧ remaining r = t := by
  obtain ⟨h4, hh4, hh4v, hh4p⟩ := hex4?_complete rfl hx
  rw [stringStep]
  split
  · next hc => rw [h₁] at hc; exact absurd hc (by simp)
  · next w' hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact absurd hcc (by decide)
  · next w' hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with _ hww
    subst hww
    split
    · next hd => rw [h₂] at hd; exact absurd hd (by simp)
    · next w'' hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with _ hww2
      subst hww2
      simp only [hh4]
      have hcond : (decide (h4.value < 0xD800) || decide (0xDFFF < h4.value)) = true := by
        rw [hh4v, ← hcv]
        rcases Spec.char_not_surrogate c with hs | hs
        · simp [hs]
        · simp [hs]
      rw [if_pos hcond, hh4v, ← hcv, charOfCodePoint?_self]
      exact ⟨_, rfl, hh4p⟩
    · next _ _ _ hn hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with hdd
      exact (hn hdd.symm).elim
  · next _ _ _ _ hn2 hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact (hn2 hcc.symm).elim

theorem stringStep_surrogate {p q w : s.Pos} {s₂ t : List Char} {hi lo : Nat} {c : Char}
    (h₁ : step? p = some ('\\', q)) (h₂ : step? q = some ('u', w))
    (hx₁ : Spec.Hex4 (remaining w) hi ('\\' :: 'u' :: s₂)) (hx₂ : Spec.Hex4 s₂ lo t)
    (hhi₁ : 0xD800 ≤ hi) (hhi₂ : hi ≤ 0xDBFF) (hlo₁ : 0xDC00 ≤ lo) (hlo₂ : lo ≤ 0xDFFF)
    (hcv : c.toNat = 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) :
    ∃ r : s.Pos, stringStep p = .char c r ∧ remaining r = t := by
  obtain ⟨h4, hh4, hh4v, hh4p⟩ := hex4?_complete rfl hx₁
  obtain ⟨l4, hl4, hl4v, hl4p⟩ := escapeHex4?_complete hh4p hx₂
  rw [stringStep]
  split
  · next hc => rw [h₁] at hc; exact absurd hc (by simp)
  · next w' hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact absurd hcc (by decide)
  · next w' hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with _ hww
    subst hww
    split
    · next hd => rw [h₂] at hd; exact absurd hd (by simp)
    · next w'' hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with _ hww2
      subst hww2
      simp only [hh4]
      have hhigh : ¬((decide (h4.value < 0xD800) || decide (0xDFFF < h4.value)) = true) := by
        rw [hh4v]
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt]
        omega
      rw [if_neg hhigh, if_pos (show h4.value ≤ 0xDBFF by rw [hh4v]; omega)]
      simp only [hl4]
      rw [if_pos (show (decide (0xDC00 ≤ l4.value) && decide (l4.value ≤ 0xDFFF)) = true by
        rw [hl4v]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
      have hcomb : combineSurrogates h4.value l4.value = c.toNat := by
        rw [hh4v, hl4v, hcv]
        rfl
      rw [hcomb, charOfCodePoint?_self]
      exact ⟨_, rfl, hl4p⟩
    · next _ _ _ hn hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with hdd
      exact (hn hdd.symm).elim
  · next _ _ _ _ hn2 hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact (hn2 hcc.symm).elim

theorem stringStep_char_complete {p : s.Pos} {l : List Char} {c : Char} {t : List Char}
    (hl : remaining p = l) (h : Spec.Ch l c t) :
    ∃ q, stringStep p = .char c q ∧ remaining q = t := by
  cases h with
  | unescaped hu =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
    exact ⟨q, stringStep_unescaped hq hu, hqt⟩
  | quote | backslash | solidus | backspace | formFeed | lineFeed | carriageReturn | tab =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
    obtain ⟨r, hr, hrt⟩ := step_of_remaining hqt
    exact ⟨r, stringStep_escape hq hr (by decide), hrt⟩
  | codePoint hx hcv =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
    obtain ⟨w, hw, hwt⟩ := step_of_remaining hqt
    exact stringStep_codePoint hq hw (by rw [hwt]; exact hx) hcv
  | surrogatePair hx₁ hx₂ ha hb hc hd hcv =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
    obtain ⟨w, hw, hwt⟩ := step_of_remaining hqt
    exact stringStep_surrogate hq hw (by rw [hwt]; exact hx₁) hx₂ ha hb hc hd hcv

theorem stringStep_done_complete {p : s.Pos} {t : List Char} (hl : remaining p = '"' :: t) :
    ∃ q, stringStep p = .done q ∧ remaining q = t := by
  obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
  refine ⟨q, ?_, hqt⟩
  rw [stringStep]
  split
  · next hc => rw [hq] at hc; exact absurd hc (by simp)
  · next w hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with _ hww
    rw [hww]
  · next w hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with hcc
    exact absurd hcc (by decide)
  · next _ _ _ hn1 _ hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with hcc
    exact (hn1 hcc.symm).elim

private theorem string_go_complete {start : s.Pos} {l cs r : List Char} (h : Spec.Chars l cs r) :
    ∀ (p : s.Pos) (acc : String) (hp : p.remainingBytes ≤ start.remainingBytes) (t : List Char),
      remaining p = l → r = '"' :: t →
      ∃ res : Scanned String start, string.go start p acc hp = .ok res ∧
        res.value.toList = acc.toList ++ cs ∧ remaining res.pos = t := by
  induction h with
  | nil =>
    intro p acc hp t hpl hr
    obtain ⟨q, hq, hqt⟩ := stringStep_done_complete (by rw [hpl, hr])
    rw [string.go]
    split
    · next e hs => rw [hq] at hs; exact absurd hs (by simp)
    · next q' hs =>
      rw [hq] at hs
      injection hs with hqq
      subst hqq
      exact ⟨_, rfl, by simp, hqt⟩
    · next c q' hs => rw [hq] at hs; exact absurd hs (by simp)
  | @cons _ _ _ ch _ hch _ ih =>
    intro p acc hp t hpl hr
    obtain ⟨q, hq, hqt⟩ := stringStep_char_complete hpl hch
    rw [string.go]
    split
    · next e hs => rw [hq] at hs; exact absurd hs (by simp)
    · next q' hs => rw [hq] at hs; exact absurd hs (by simp)
    · next c' q' hs =>
      rw [hq] at hs
      injection hs with hcc hqq
      subst hcc
      subst hqq
      obtain ⟨res, hres, hval, hpos⟩ := ih q (acc.push ch) _ t hqt hr
      exact ⟨res, hres, by rw [hval, String.toList_push]; simp, hpos⟩

theorem string_complete {p : s.Pos} {acc : String} {cs t : List Char}
    (h : Spec.Chars (remaining p) cs ('"' :: t)) :
    ∃ res : Scanned String p, string p acc = .ok res ∧
      res.value.toList = acc.toList ++ cs ∧ remaining res.pos = t :=
  string_go_complete h p acc (Nat.le_refl _) t rfl rfl

/-- What the grammar reads between quotation marks, the scanner reads. -/
theorem str_complete {p : s.Pos} {l : List Char} {v : String} {t : List Char}
    (hl : remaining p = l) (h : Spec.Str l v t) :
    ∃ (q : s.Pos) (res : Scanned String q), step? p = some ('"', q) ∧ string q "" = .ok res ∧
      res.value = v ∧ remaining res.pos = t := by
  cases h with
  | @mk u cs r hchars =>
    obtain ⟨q, hq, hqu⟩ := step_of_remaining hl
    obtain ⟨res, hres, hval, hpos⟩ := string_complete (acc := "") (by rw [hqu]; exact hchars)
    refine ⟨q, res, hq, hres, ?_, hpos⟩
    have hcs : res.value.toList = cs := by simpa using hval
    rw [← hcs, String.ofList_toList]

/-! ## The machine -/

theorem expect?_complete {p : s.Pos} {l u : List Char} (h : remaining p = l ++ u) :
    ∃ r : Consumed Unit p, expect? p l = some r ∧ remaining r.pos = u := by
  induction l generalizing p with
  | nil => exact ⟨_, rfl, by simpa using h⟩
  | cons c rest ih =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining (by simpa using h)
    obtain ⟨r, hr, hrp⟩ := ih hqt
    rw [expect?]
    split
    · next c' q' hc =>
      rw [hq] at hc
      injection hc with hc'
      injection hc' with hcc hqq
      subst hcc
      subst hqq
      rw [if_pos (beq_self_eq_true c), hr]
      exact ⟨_, rfl, hrp⟩
    · next hc => rw [hq] at hc; exact absurd hc (by simp)

/-!
The elements and members of a container come apart into a first and a rest, which is the shape
the machine reads them in. The value family is one mutual definition, so the induction is on how
much text is left rather than on the derivation.
-/

private theorem elementsEnd_uncons_go : ∀ (n : Nat) (t : List Char), t.length ≤ n →
    ∀ {t' r : List Char} {vs : List Json}, Spec.Elements t vs t' → Spec.EndArray t' r →
      ∃ (v : Json) (vs' : List Json) (t₁ : List Char), vs = v :: vs' ∧ Spec.Value t v t₁ ∧
        ElementsRest t₁ vs' r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t ht t' r vs h hend
    cases h with
    | one hv => exact ⟨_, [], _, rfl, hv, ElementsRest.close hend⟩
    | @more _ _ s'' _ _ _ hv hsep hels =>
      have hlt : s''.length < n := by
        have h₁ := Spec.value_length hv
        have h₂ := Spec.token_length hsep
        omega
      obtain ⟨v₂, vs₂, t₂, rfl, hv₂, hrest⟩ := ih _ hlt _ (Nat.le_refl _) hels hend
      exact ⟨_, _, _, rfl, hv, ElementsRest.more hsep hv₂ hrest⟩

private theorem membersEnd_uncons_go : ∀ (n : Nat) (t : List Char), t.length ≤ n →
    ∀ {t' r : List Char} {ms : List (String × Json)}, Spec.Members t ms t' →
      Spec.EndObject t' r →
      ∃ (m : String × Json) (ms' : List (String × Json)) (t₁ : List Char), ms = m :: ms' ∧
        Spec.Member t m t₁ ∧ MembersRest t₁ ms' r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t ht t' r ms h hend
    cases h with
    | one hm => exact ⟨_, [], _, rfl, hm, MembersRest.close hend⟩
    | @more _ _ s'' _ _ _ hm hsep hms =>
      have hlt : s''.length < n := by
        have h₁ := Spec.member_length hm
        have h₂ := Spec.token_length hsep
        omega
      obtain ⟨m₂, ms₂, t₂, rfl, hm₂, hrest⟩ := ih _ hlt _ (Nat.le_refl _) hms hend
      exact ⟨_, _, _, rfl, hm, MembersRest.more hsep hm₂ hrest⟩

/-- An array's elements, split into the first and what has to follow it. -/
theorem elementsEnd_uncons {t t' r : List Char} {vs : List Json} (h : Spec.Elements t vs t')
    (hend : Spec.EndArray t' r) :
    ∃ (v : Json) (vs' : List Json) (t₁ : List Char), vs = v :: vs' ∧ Spec.Value t v t₁ ∧
      ElementsRest t₁ vs' r :=
  elementsEnd_uncons_go t.length t (Nat.le_refl _) h hend

/-- An object's members, split into the first and what has to follow it. -/
theorem membersEnd_uncons {t t' r : List Char} {ms : List (String × Json)}
    (h : Spec.Members t ms t') (hend : Spec.EndObject t' r) :
    ∃ (m : String × Json) (ms' : List (String × Json)) (t₁ : List Char), ms = m :: ms' ∧
      Spec.Member t m t₁ ∧ MembersRest t₁ ms' r :=
  membersEnd_uncons_go t.length t (Nat.le_refl _) h hend

/-!
The machine reads by looking at one character and dispatching on it. Each of the lemmas below
says what it does once that character is known, so that the induction can be driven by the
derivation rather than by the parser.
-/

variable {cfg : Config} {depth : Nat} {stack : List Frame}

private theorem value_null {p q : s.Pos} {e : Consumed Unit q} (hc : step? p = some ('n', q))
    (hex : expect? q ['u', 'l', 'l'] = some e) :
    value cfg p depth stack = continueWith cfg .null e.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    rw [hex]
  · rename_i hn _ _ _ _ _
    exact absurd heq.1.symm hn

private theorem value_true {p q : s.Pos} {e : Consumed Unit q} (hc : step? p = some ('t', q))
    (hex : expect? q ['r', 'u', 'e'] = some e) :
    value cfg p depth stack = continueWith cfg (.bool true) e.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    rw [hex]
  · rename_i _ hn _ _ _ _
    exact absurd heq.1.symm hn

private theorem value_false {p q : s.Pos} {e : Consumed Unit q} (hc : step? p = some ('f', q))
    (hex : expect? q ['a', 'l', 's', 'e'] = some e) :
    value cfg p depth stack = continueWith cfg (.bool false) e.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    rw [hex]
  · rename_i _ _ hn _ _ _
    exact absurd heq.1.symm hn

private theorem value_str {p q : s.Pos} {r : Scanned String q} (hc : step? p = some ('"', q))
    (hstr : string q "" = .ok r) :
    value cfg p depth stack = continueWith cfg (.str r.value) r.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    rw [hstr]
  · rename_i _ _ _ hn _ _
    exact absurd heq.1.symm hn

private theorem value_num {p q : s.Pos} {c : Char} {r : Scanned Number p}
    (hc : step? p = some (c, q)) (hd : (c == '-' || Spec.isDigit c) = true)
    (hnum : number cfg p = .ok r) :
    value cfg p depth stack = continueWith cfg (.num r.value) r.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    rw [if_pos hd, hnum]

private theorem value_arr_empty {p q after : s.Pos} (hc : step? p = some ('[', q))
    (hd : depthExceeded cfg depth = false) (hb : step? (skipWs q).pos = some (']', after)) :
    value cfg p depth stack = continueWith cfg (.arr #[]) after depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hd, Bool.false_eq_true, if_false]
    split <;> rename_i heq2 <;> rw [hb] at heq2 <;> simp at heq2
    · subst heq2
      rfl
  · rename_i _ _ _ _ hn _
    exact absurd heq.1.symm hn

private theorem value_arr_items {p q : s.Pos} (hc : step? p = some ('[', q))
    (hd : depthExceeded cfg depth = false)
    (hb : ∀ after, step? (skipWs q).pos ≠ some (']', after)) :
    value cfg p depth stack = value cfg (skipWs q).pos (depth + 1) (.arr #[] :: stack) := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hd, Bool.false_eq_true, if_false]
  · rename_i _ _ _ _ hn _
    exact absurd heq.1.symm hn

private theorem value_obj_empty {p q after : s.Pos} (hc : step? p = some ('{', q))
    (hd : depthExceeded cfg depth = false) (hb : step? (skipWs q).pos = some ('}', after)) :
    value cfg p depth stack = continueWith cfg (.obj #[]) after depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hd, Bool.false_eq_true, if_false]
    split <;> rename_i heq2 <;> rw [hb] at heq2 <;> simp at heq2
    · subst heq2
      rfl
  · rename_i _ _ _ _ _ hn
    exact absurd heq.1.symm hn

private theorem value_obj_members {p q : s.Pos} (hc : step? p = some ('{', q))
    (hd : depthExceeded cfg depth = false)
    (hb : ∀ after, step? (skipWs q).pos ≠ some ('}', after)) :
    value cfg p depth stack = member cfg (skipWs q).pos (depth + 1) #[] ∅ stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hd, Bool.false_eq_true, if_false]
  · rename_i _ _ _ _ _ hn
    exact absurd heq.1.symm hn

private theorem continueWith_nil {p : s.Pos} {v : Json} :
    continueWith cfg v p depth [] = .ok (v, p) := by rw [continueWith]

private theorem continueWith_arr_sep {p after : s.Pos} {v : Json} {elems : Array Json}
    {outer : List Frame} (hb : step? (skipWs p).pos = some (',', after)) :
    continueWith cfg v p depth (.arr elems :: outer) =
      value cfg (skipWs after).pos depth (.arr (elems.push v) :: outer) := by
  rw [continueWith]
  simp only []
  split <;> rename_i heq <;> rw [hb] at heq <;> simp at heq
  · subst heq
    rfl
  · obtain ⟨rfl, rfl⟩ := heq
    rename_i hn _
    exact (hn rfl).elim

private theorem continueWith_arr_close {p after : s.Pos} {v : Json} {elems : Array Json}
    {outer : List Frame} (hb : step? (skipWs p).pos = some (']', after)) :
    continueWith cfg v p depth (.arr elems :: outer) =
      continueWith cfg (.arr (elems.push v)) after (depth - 1) outer := by
  rw [continueWith]
  simp only []
  split <;> rename_i heq <;> rw [hb] at heq <;> simp at heq
  · subst heq
    rfl
  · obtain ⟨rfl, rfl⟩ := heq
    rename_i _ hn
    exact (hn rfl).elim

private theorem continueWith_obj_sep {p after : s.Pos} {v : Json}
    {fields : Array (String × Json)} {seen : Std.HashSet String} {name : String}
    {outer : List Frame} (hb : step? (skipWs p).pos = some (',', after)) :
    continueWith cfg v p depth (.obj fields seen name :: outer) =
      member cfg (skipWs after).pos depth (fields.push (name, v)) seen outer := by
  rw [continueWith]
  simp only []
  split <;> rename_i heq <;> rw [hb] at heq <;> simp at heq
  · subst heq
    rfl
  · obtain ⟨rfl, rfl⟩ := heq
    rename_i hn _
    exact (hn rfl).elim

private theorem continueWith_obj_close {p after : s.Pos} {v : Json}
    {fields : Array (String × Json)} {seen : Std.HashSet String} {name : String}
    {outer : List Frame} (hb : step? (skipWs p).pos = some ('}', after)) :
    continueWith cfg v p depth (.obj fields seen name :: outer) =
      continueWith cfg (.obj (fields.push (name, v))) after (depth - 1) outer := by
  rw [continueWith]
  simp only []
  split <;> rename_i heq <;> rw [hb] at heq <;> simp at heq
  · subst heq
    rfl
  · obtain ⟨rfl, rfl⟩ := heq
    rename_i _ hn
    exact (hn rfl).elim

private theorem member_value {p q after : s.Pos} {fields : Array (String × Json)}
    {seen : Std.HashSet String} {r : Scanned String q} (hc : step? p = some ('"', q))
    (hstr : string q "" = .ok r)
    (hdup : (cfg.duplicateKeys == .reject && seen.contains r.value) = false)
    (hb : step? (skipWs r.pos).pos = some (':', after)) :
    member cfg p depth fields seen stack =
      value cfg (skipWs after).pos depth (.obj fields (seen.insert r.value) r.value :: stack) := by
  rw [member]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hstr, hdup, Bool.false_eq_true, if_false]
    split <;> rename_i heq2 <;> rw [hb] at heq2 <;> simp at heq2
    · subst heq2
      rfl
    · obtain ⟨rfl, rfl⟩ := heq2
      rename_i hn
      exact (hn rfl).elim
  · obtain ⟨rfl, -⟩ := heq
    rename_i hn
    exact (hn rfl).elim

private theorem elementsRest_follows {t : List Char} {vs : List Json} {r : List Char}
    (h : ElementsRest t vs r) : Spec.Follows t := by
  cases h with
  | close hend => exact Spec.follows_of_token hend (.inr (.inl rfl))
  | more hsep _ _ => exact Spec.follows_of_token hsep (.inl rfl)

private theorem membersRest_follows {t : List Char} {ms : List (String × Json)} {r : List Char}
    (h : MembersRest t ms r) : Spec.Follows t := by
  cases h with
  | close hend => exact Spec.follows_of_token hend (.inr (.inr rfl))
  | more hsep _ _ => exact Spec.follows_of_token hsep (.inl rfl)

/-!
The machine, in the direction soundness does not go. What a derivation leaves is what the parser
leaves up to whitespace, since a token in the grammar carries the whitespace after it while the
scanner passes over that only when it next looks, so the conclusions are stated with `Ws` rather
than with equality.
-/

private def ValueComplete (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (stack : List Frame) (l : List Char) (v j : Json) (t r : List Char),
    remaining p = l → Spec.NoWs l → Spec.Value l v t → Spec.Follows t → Closes stack v t j r →
      ∃ rp, value cfg p depth stack = .ok (j, rp) ∧ Spec.Ws (remaining rp) r

private def ContinueComplete (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (v j : Json) (depth : Nat) (stack : List Frame) (t r : List Char),
    Spec.Ws (remaining p) t → Closes stack v t j r →
      ∃ rp, continueWith cfg v p depth stack = .ok (j, rp) ∧ Spec.Ws (remaining rp) r

private def MemberComplete (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (fields : Array (String × Json)) (seen : Std.HashSet String)
      (stack : List Frame) (l : List Char) (m : String × Json) (ms : List (String × Json))
      (t₁ t : List Char) (j : Json) (r : List Char),
    remaining p = l → Spec.NoWs l → Spec.Member l m t₁ → MembersRest t₁ ms t →
      Closes stack (.obj (fields ++ (m :: ms).toArray)) t j r →
        ∃ rp, member cfg p depth fields seen stack = .ok (j, rp) ∧ Spec.Ws (remaining rp) r

private theorem machine_complete {cfg : Config} (hmax : cfg.maxDepth = none)
    (hkeys : cfg.duplicateKeys = .allow) (hdig : cfg.maxNumberDigits = none) :
    ∀ (n : Nat) (p : s.Pos), p.remainingBytes ≤ n →
      ValueComplete cfg p ∧ ContinueComplete cfg p ∧ MemberComplete cfg p := by
  have hdepth : ∀ depth, depthExceeded cfg depth = false := by
    intro depth
    simp [depthExceeded, hmax]
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · intro depth stack l v j t r hl hnw hv hft hcl
      cases hv with
      | null =>
        obtain ⟨q, hc, hq⟩ := step_of_remaining hl
        obtain ⟨e, hex, hep⟩ :=
          expect?_complete (p := q) (l := ['u', 'l', 'l']) (u := t) (by simpa using hq)
        have hlt : e.pos.remainingBytes < n := by
          have := step?_lt hc
          have := e.notLonger
          omega
        obtain ⟨rp, hres, hws⟩ := (ih _ hlt e.pos (Nat.le_refl _)).2.1 .null j depth stack t r
          (by rw [hep]; exact Spec.Ws.nil) hcl
        exact ⟨rp, by rw [value_null hc hex]; exact hres, hws⟩
      | true_ =>
        obtain ⟨q, hc, hq⟩ := step_of_remaining hl
        obtain ⟨e, hex, hep⟩ :=
          expect?_complete (p := q) (l := ['r', 'u', 'e']) (u := t) (by simpa using hq)
        have hlt : e.pos.remainingBytes < n := by
          have := step?_lt hc
          have := e.notLonger
          omega
        obtain ⟨rp, hres, hws⟩ :=
          (ih _ hlt e.pos (Nat.le_refl _)).2.1 (.bool true) j depth stack t r
            (by rw [hep]; exact Spec.Ws.nil) hcl
        exact ⟨rp, by rw [value_true hc hex]; exact hres, hws⟩
      | false_ =>
        obtain ⟨q, hc, hq⟩ := step_of_remaining hl
        obtain ⟨e, hex, hep⟩ :=
          expect?_complete (p := q) (l := ['a', 'l', 's', 'e']) (u := t) (by simpa using hq)
        have hlt : e.pos.remainingBytes < n := by
          have := step?_lt hc
          have := e.notLonger
          omega
        obtain ⟨rp, hres, hws⟩ :=
          (ih _ hlt e.pos (Nat.le_refl _)).2.1 (.bool false) j depth stack t r
            (by rw [hep]; exact Spec.Ws.nil) hcl
        exact ⟨rp, by rw [value_false hc hex]; exact hres, hws⟩
      | str hs =>
        obtain ⟨q, res, hc, hstr, hval, hpos⟩ := str_complete hl hs
        have hlt : res.pos.remainingBytes < n := by
          have := step?_lt hc
          have := res.consumed
          omega
        obtain ⟨rp, hres, hws⟩ :=
          (ih _ hlt res.pos (Nat.le_refl _)).2.1 (.str res.value) j depth stack t r
            (by rw [hpos]; exact Spec.Ws.nil) (by rw [hval]; exact hcl)
        exact ⟨rp, by rw [value_str hc hstr]; exact hres, hws⟩
      | num hn =>
        obtain ⟨c, u, hcu, hcd⟩ := Spec.num_head hn
        obtain ⟨q, hc, -⟩ := step_of_remaining (hl.trans hcu)
        obtain ⟨rn, hnum, hnv, hnp⟩ := number_complete (by rw [hl]; exact hn) hft hdig
        have hlt : rn.pos.remainingBytes < n := by
          have := rn.consumed
          omega
        obtain ⟨rp, hres, hws⟩ :=
          (ih _ hlt rn.pos (Nat.le_refl _)).2.1 (.num rn.value) j depth stack t r
            (by rw [hnp]; exact Spec.Ws.nil) (by rw [hnv]; exact hcl)
        refine ⟨rp, ?_, hws⟩
        rw [value_num hc ?_ hnum]
        · exact hres
        · rcases hcd with rfl | hd
          · decide
          · simp [hd]
      | arr ha =>
        cases ha with
        | @empty _ s₂ _ hb hend =>
          cases hb with
          | @mk s₁ _ hlead htrail =>
            cases hend with
            | @mk u _ hlead₂ htrail₂ =>
              obtain ⟨q, hc, hq⟩ := step_of_remaining (hl.trans (hlead.source_eq_of_noWs hnw))
              have hstep : remaining (skipWs q).pos = ']' :: u :=
                skipWs_complete (by rw [hq]; exact htrail.trans hlead₂)
                  (Spec.noWs_cons (by decide))
              obtain ⟨after, hb₂, hafter⟩ := step_of_remaining hstep
              have hlt : after.remainingBytes < n := by
                have := step?_lt hc
                have := (skipWs q).notLonger
                have := step?_lt hb₂
                omega
              obtain ⟨rp, hres, hws⟩ :=
                (ih _ hlt after (Nat.le_refl _)).2.1 (.arr #[]) j depth stack t r
                  (by rw [hafter]; exact htrail₂) hcl
              exact ⟨rp, by rw [value_arr_empty hc (hdepth depth) hb₂]; exact hres, hws⟩
        | @items _ s₂ s₃ vs _ hb hels hend =>
          cases hb with
          | @mk s₁ _ hlead htrail =>
            obtain ⟨q, hc, hq⟩ := step_of_remaining (hl.trans (hlead.source_eq_of_noWs hnw))
            have hshift : Spec.Ws s₂ (remaining (skipWs q).pos) :=
              Spec.Ws.to_noWs htrail (by rw [← hq]; exact ws_skipWs q) (noWs_skipWs q)
            obtain ⟨v₁, vs', t₁, rfl, hv₁, hrest⟩ :=
              elementsEnd_uncons (Spec.elements_ws hshift hels) hend
            have hnb : ∀ after, step? (skipWs q).pos ≠ some (']', after) := by
              intro after hb₂
              exact Spec.not_value_bracket (remaining_step hb₂ ▸ hv₁)
            have hlt : (skipWs q).pos.remainingBytes < n := by
              have := step?_lt hc
              have := (skipWs q).notLonger
              omega
            obtain ⟨rp, hres, hws⟩ :=
              (ih _ hlt (skipWs q).pos (Nat.le_refl _)).1 (depth + 1) (.arr #[] :: stack)
                (remaining (skipWs q).pos) v₁ j t₁ r rfl (noWs_skipWs q) hv₁
                (elementsRest_follows hrest) (by simp only [Closes]; exact ⟨vs', t, hrest,
                  by simpa using hcl⟩)
            exact ⟨rp, by rw [value_arr_items hc (hdepth depth) hnb]; exact hres, hws⟩
      | obj ho =>
        cases ho with
        | @empty _ s₂ _ hb hend =>
          cases hb with
          | @mk s₁ _ hlead htrail =>
            cases hend with
            | @mk u _ hlead₂ htrail₂ =>
              obtain ⟨q, hc, hq⟩ := step_of_remaining (hl.trans (hlead.source_eq_of_noWs hnw))
              have hstep : remaining (skipWs q).pos = '}' :: u :=
                skipWs_complete (by rw [hq]; exact htrail.trans hlead₂)
                  (Spec.noWs_cons (by decide))
              obtain ⟨after, hb₂, hafter⟩ := step_of_remaining hstep
              have hlt : after.remainingBytes < n := by
                have := step?_lt hc
                have := (skipWs q).notLonger
                have := step?_lt hb₂
                omega
              obtain ⟨rp, hres, hws⟩ :=
                (ih _ hlt after (Nat.le_refl _)).2.1 (.obj #[]) j depth stack t r
                  (by rw [hafter]; exact htrail₂) hcl
              exact ⟨rp, by rw [value_obj_empty hc (hdepth depth) hb₂]; exact hres, hws⟩
        | @members _ s₂ s₃ ms _ hb hms hend =>
          cases hb with
          | @mk s₁ _ hlead htrail =>
            obtain ⟨q, hc, hq⟩ := step_of_remaining (hl.trans (hlead.source_eq_of_noWs hnw))
            have hshift : Spec.Ws s₂ (remaining (skipWs q).pos) :=
              Spec.Ws.to_noWs htrail (by rw [← hq]; exact ws_skipWs q) (noWs_skipWs q)
            obtain ⟨m₁, ms', t₁, rfl, hm₁, hrest⟩ :=
              membersEnd_uncons (Spec.members_ws hshift hms) hend
            have hnb : ∀ after, step? (skipWs q).pos ≠ some ('}', after) := by
              intro after hb₂
              exact Spec.not_members_brace (remaining_step hb₂ ▸ Spec.Members.one hm₁)
            have hlt : (skipWs q).pos.remainingBytes < n := by
              have := step?_lt hc
              have := (skipWs q).notLonger
              omega
            obtain ⟨rp, hres, hws⟩ :=
              (ih _ hlt (skipWs q).pos (Nat.le_refl _)).2.2 (depth + 1) #[] ∅ stack
                (remaining (skipWs q).pos) m₁ ms' t₁ t j r rfl (noWs_skipWs q) hm₁ hrest
                (by simpa using hcl)
            exact ⟨rp, by rw [value_obj_members hc (hdepth depth) hnb]; exact hres, hws⟩
    · intro v j depth stack t r hws hcl
      cases stack with
      | nil =>
        simp only [Closes] at hcl
        obtain ⟨rfl, rfl⟩ := hcl
        exact ⟨p, continueWith_nil, hws⟩
      | cons f outer =>
        cases f with
        | arr elems =>
          simp only [Closes] at hcl
          obtain ⟨vs, t', hrest, hcl₂⟩ := hcl
          cases hrest with
          | @close _ _ hend =>
            cases hend with
            | @mk u _ hlead htrail =>
              have hstep : remaining (skipWs p).pos = ']' :: u :=
                skipWs_complete (hws.trans hlead) (Spec.noWs_cons (by decide))
              obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
              have hlt : after.remainingBytes < n := by
                have := (skipWs p).notLonger
                have := step?_lt hb
                omega
              obtain ⟨rp, hres, hwsr⟩ :=
                (ih _ hlt after (Nat.le_refl _)).2.1 (.arr (elems.push v)) j (depth - 1) outer t' r
                  (by rw [hafter]; exact htrail) (by simpa using hcl₂)
              exact ⟨rp, by rw [continueWith_arr_close hb]; exact hres, hwsr⟩
          | @more _ t₁ t₂ v₂ vs' _ hsep hv hrest₂ =>
            cases hsep with
            | @mk u _ hlead htrail =>
              have hstep : remaining (skipWs p).pos = ',' :: u :=
                skipWs_complete (hws.trans hlead) (Spec.noWs_cons (by decide))
              obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
              have hshift : Spec.Ws t₁ (remaining (skipWs after).pos) :=
                Spec.Ws.to_noWs htrail (by rw [← hafter]; exact ws_skipWs after)
                  (noWs_skipWs after)
              have hlt : (skipWs after).pos.remainingBytes < n := by
                have := (skipWs p).notLonger
                have := step?_lt hb
                have := (skipWs after).notLonger
                omega
              obtain ⟨rp, hres, hwsr⟩ :=
                (ih _ hlt (skipWs after).pos (Nat.le_refl _)).1 depth
                  (.arr (elems.push v) :: outer) (remaining (skipWs after).pos) v₂ j t₂ r rfl
                  (noWs_skipWs after) (Spec.value_ws hshift hv) (elementsRest_follows hrest₂)
                  (by simp only [Closes]; exact ⟨vs', t', hrest₂, by simpa using hcl₂⟩)
              exact ⟨rp, by rw [continueWith_arr_sep hb]; exact hres, hwsr⟩
        | obj fields seen name =>
          simp only [Closes] at hcl
          obtain ⟨ms, t', hrest, hcl₂⟩ := hcl
          cases hrest with
          | @close _ _ hend =>
            cases hend with
            | @mk u _ hlead htrail =>
              have hstep : remaining (skipWs p).pos = '}' :: u :=
                skipWs_complete (hws.trans hlead) (Spec.noWs_cons (by decide))
              obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
              have hlt : after.remainingBytes < n := by
                have := (skipWs p).notLonger
                have := step?_lt hb
                omega
              obtain ⟨rp, hres, hwsr⟩ :=
                (ih _ hlt after (Nat.le_refl _)).2.1 (.obj (fields.push (name, v))) j (depth - 1)
                  outer t' r (by rw [hafter]; exact htrail) (by simpa using hcl₂)
              exact ⟨rp, by rw [continueWith_obj_close hb]; exact hres, hwsr⟩
          | @more _ t₁ t₂ m₂ ms' _ hsep hm hrest₂ =>
            cases hsep with
            | @mk u _ hlead htrail =>
              have hstep : remaining (skipWs p).pos = ',' :: u :=
                skipWs_complete (hws.trans hlead) (Spec.noWs_cons (by decide))
              obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
              have hshift : Spec.Ws t₁ (remaining (skipWs after).pos) :=
                Spec.Ws.to_noWs htrail (by rw [← hafter]; exact ws_skipWs after)
                  (noWs_skipWs after)
              have hlt : (skipWs after).pos.remainingBytes < n := by
                have := (skipWs p).notLonger
                have := step?_lt hb
                have := (skipWs after).notLonger
                omega
              obtain ⟨rp, hres, hwsr⟩ :=
                (ih _ hlt (skipWs after).pos (Nat.le_refl _)).2.2 depth (fields.push (name, v))
                  seen outer (remaining (skipWs after).pos) m₂ ms' t₂ t' j r rfl
                  (noWs_skipWs after) (Spec.member_ws hshift hm) hrest₂ (by simpa using hcl₂)
              exact ⟨rp, by rw [continueWith_obj_sep hb]; exact hres, hwsr⟩
    · intro depth fields seen stack l m ms t₁ t j r hl hnw hm hrest hcl
      cases hm with
      | @mk _ s₂ s₃ k v _ hstr hsep hv =>
        obtain ⟨q, res, hc, hs, hval, hpos⟩ := str_complete hl hstr
        cases hsep with
        | @mk u _ hlead htrail =>
          have hstep : remaining (skipWs res.pos).pos = ':' :: u :=
            skipWs_complete (by rw [hpos]; exact hlead) (Spec.noWs_cons (by decide))
          obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
          have hshift : Spec.Ws s₃ (remaining (skipWs after).pos) :=
            Spec.Ws.to_noWs htrail (by rw [← hafter]; exact ws_skipWs after) (noWs_skipWs after)
          have hlt : (skipWs after).pos.remainingBytes < n := by
            have := step?_lt hc
            have := res.consumed
            have := (skipWs res.pos).notLonger
            have := step?_lt hb
            have := (skipWs after).notLonger
            omega
          obtain ⟨rp, hres, hwsr⟩ :=
            (ih _ hlt (skipWs after).pos (Nat.le_refl _)).1 depth
              (.obj fields (seen.insert res.value) res.value :: stack)
              (remaining (skipWs after).pos) v j t₁ r rfl (noWs_skipWs after)
              (Spec.value_ws hshift hv) (membersRest_follows hrest)
              (by simp only [Closes]; exact ⟨ms, t, hrest, by rw [hval]; simpa using hcl⟩)
          refine ⟨rp, ?_, hwsr⟩
          rw [member_value hc hs (by simp [hkeys]) hb]
          exact hres

/-! ## Text -/

/--
No derivable text begins with a byte order mark, so the parser's leave to ignore one is never
exercised on text the grammar accepts and the reading does not depend on `ignoreBOM`.
-/
private theorem head_ne_bom {l : List Char} {j : Json} (h : Spec.Text l j) {c : Char}
    {u : List Char} (hl : l = c :: u) : c.toNat ≠ 0xFEFF := by
  intro hbom
  obtain ⟨s₁, s₂, hws, hv, -⟩ := h
  have hne : ∀ d : Char, d.toNat ≠ 0xFEFF → c ≠ d := fun d hd hcd => hd (hcd ▸ hbom)
  have hnw : Spec.isWs c = false := by
    cases hw : Spec.isWs c with
    | false => rfl
    | true =>
      rcases Spec.eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact absurd hbom (by decide)
  have hd : Spec.isDigit c = false := by
    simp only [Spec.isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not, Char.le_def,
      UInt32.le_iff_toNat_le, Nat.not_le]
    have h9 : ('9' : Char).val.toNat = 57 := rfl
    have hcv : c.val.toNat = 65279 := hbom
    omega
  rw [hl] at hws
  rw [Spec.ws_eq_of_not_isWs hnw hws] at hv
  exact Spec.not_value_cons hnw (hne 'f' (by decide)) (hne 'n' (by decide)) (hne 't' (by decide))
    (hne '"' (by decide)) (hne '[' (by decide)) (hne '{' (by decide)) (hne '-' (by decide)) hd hv

/-- Whatever the grammar derives from the text at `start`, the machine reads. -/
theorem parseFrom_complete {cfg : Config} (hmax : cfg.maxDepth = none)
    (hkeys : cfg.duplicateKeys = .allow) (hdig : cfg.maxNumberDigits = none) {start : s.Pos}
    {j : Json} (h : Spec.Text (remaining start) j) : parseFrom cfg start = .ok j := by
  obtain ⟨s₁, s₂, hws, hv, hend⟩ := h
  have hshift : Spec.Ws s₁ (remaining (skipWs start).pos) :=
    Spec.Ws.to_noWs hws (ws_skipWs start) (noWs_skipWs start)
  obtain ⟨rp, hres, hwsr⟩ :=
    (machine_complete hmax hkeys hdig (skipWs start).pos.remainingBytes (skipWs start).pos
        (Nat.le_refl _)).1 0 [] (remaining (skipWs start).pos) j j s₂ s₂ rfl (noWs_skipWs start)
      (Spec.value_ws hshift hv) (Spec.follows_of_ws hend) (by simp [Closes])
  have hnil : remaining (skipWs rp).pos = [] :=
    skipWs_complete (hwsr.trans hend) (fun c t hct => absurd hct (by simp))
  have hstep : step? (skipWs rp).pos = none := by
    cases hs : step? (skipWs rp).pos with
    | none => rfl
    | some cq =>
      obtain ⟨c, q⟩ := cq
      rw [remaining_step hs] at hnil
      exact absurd hnil (by simp)
  simp only [parseFrom, hres, hstep]

/--
No false rejects: text the grammar derives is read, and read as the value the grammar gives it.
The knobs that refuse legal text are off, which is what the three hypotheses say.
-/
theorem parse_complete {s : String} {cfg : Config} {j : Json} (hmax : cfg.maxDepth = none)
    (hkeys : cfg.duplicateKeys = .allow) (hdig : cfg.maxNumberDigits = none)
    (h : Spec.TextOf s j) : parse s cfg = .ok j := by
  have h' : Spec.Text (remaining s.startPos) j := by rw [remaining_startPos]; exact h
  cases hc : step? s.startPos with
  | none =>
    simp only [parse, hc]
    exact parseFrom_complete hmax hkeys hdig h'
  | some cq =>
    obtain ⟨c, q⟩ := cq
    have hbom := head_ne_bom h' (remaining_step hc)
    simp only [parse, hc, if_neg (by simp [hbom] : ¬(cfg.ignoreBOM && c.toNat == 0xFEFF) = true)]
    exact parseFrom_complete hmax hkeys hdig h'

end Json.Parser
