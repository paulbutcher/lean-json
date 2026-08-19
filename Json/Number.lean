/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

namespace Json

@[expose] section

/-!
Numbers as JSON writes them, `mantissa * 10 ^ exponent`, with the exponent carried rather than
applied: `1e1000000000` is a pair of small integers here, where expanding it is a denial of
service.

`Canonical` picks one spelling of each value and the parser produces only canonical numbers, so
structural equality agrees with numeric equality on everything that came from text. `Ord`
compares numerically and so parts company with `=` on values that are not canonical; `Eqv` is
numeric equality as a proposition, and `eqv_iff_eq` ties the two together where it matters.

Every conversion out of a `Number` is bounded and says so in its type. `toInt?` and `toNat?`
refuse a number whose padding would run past `maxPadding` digits, which is what makes a
twelve-character text unable to ask for an integer of a billion digits.
-/

/-- A decimal number denoting `mantissa * 10 ^ exponent`. -/
structure Number where
  mantissa : Int
  exponent : Int
deriving DecidableEq, Hashable, Repr, Inhabited

namespace Number

@[simp] theorem mk_mantissa (m e : Int) : (Number.mk m e).mantissa = m := rfl

@[simp] theorem mk_exponent (m e : Int) : (Number.mk m e).exponent = e := rfl

/--
`n` is the unique representation of its value: either a mantissa with no trailing zero, or
zero paired with a zero exponent.

The exponent is never evaluated as a power of ten, so a number such as `1e1000000000` costs
nothing to represent.
-/
def Canonical (n : Number) : Prop :=
  n.mantissa % 10 ≠ 0 ∨ (n.mantissa = 0 ∧ n.exponent = 0)

instance : DecidablePred Canonical := fun n =>
  inferInstanceAs (Decidable (n.mantissa % 10 ≠ 0 ∨ (n.mantissa = 0 ∧ n.exponent = 0)))

/-- `n`'s mantissa rescaled to the exponent `k`, meaningful when `k ≤ n.exponent`. -/
def scaleTo (n : Number) (k : Int) : Int :=
  n.mantissa * 10 ^ (n.exponent - k).toNat

/--
`a` and `b` denote the same value, whatever their representations. Powers of ten appear here
only inside a proposition, where they are never computed.
-/
def Eqv (a b : Number) : Prop :=
  a.scaleTo (min a.exponent b.exponent) = b.scaleTo (min a.exponent b.exponent)

theorem pow_ten_pos (d : Nat) : (0 : Int) < 10 ^ d :=
  Int.pow_pos (by decide)

theorem pow_ten_ne_zero (d : Nat) : (10 : Int) ^ d ≠ 0 :=
  Int.ne_of_gt (pow_ten_pos d)

theorem Eqv.refl (a : Number) : Eqv a a := rfl

theorem scaleTo_lower {n : Number} {k k' : Int} (hk : k ≤ k') (hk' : k' ≤ n.exponent) :
    n.scaleTo k = n.scaleTo k' * 10 ^ (k' - k).toNat := by
  have hsplit : (n.exponent - k).toNat = (n.exponent - k').toNat + (k' - k).toNat := by omega
  simp only [scaleTo, hsplit, Int.pow_add, Int.mul_assoc]

theorem scaleTo_eq_of_eqv {a b : Number} {k : Int} (hka : k ≤ a.exponent) (hkb : k ≤ b.exponent)
    (h : Eqv a b) : a.scaleTo k = b.scaleTo k := by
  rw [scaleTo_lower (n := a) (k := k) (k' := min a.exponent b.exponent) (by omega) (by omega),
    scaleTo_lower (n := b) (k := k) (k' := min a.exponent b.exponent) (by omega) (by omega), h]

theorem eqv_of_scaleTo {a b : Number} {k : Int} (hka : k ≤ a.exponent) (hkb : k ≤ b.exponent)
    (h : a.scaleTo k = b.scaleTo k) : Eqv a b := by
  refine Int.eq_of_mul_eq_mul_right (pow_ten_ne_zero (min a.exponent b.exponent - k).toNat) ?_
  rw [← scaleTo_lower (n := a) (by omega) (by omega),
    ← scaleTo_lower (n := b) (by omega) (by omega)]
  exact h

theorem Eqv.symm {a b : Number} (h : Eqv a b) : Eqv b a :=
  eqv_of_scaleTo (k := min a.exponent b.exponent) (by omega) (by omega)
    (scaleTo_eq_of_eqv (by omega) (by omega) h).symm

theorem Eqv.trans {a b c : Number} (hab : Eqv a b) (hbc : Eqv b c) : Eqv a c :=
  eqv_of_scaleTo (k := min (min a.exponent b.exponent) c.exponent) (by omega) (by omega)
    ((scaleTo_eq_of_eqv (by omega) (by omega) hab).trans
      (scaleTo_eq_of_eqv (by omega) (by omega) hbc))

private theorem exponent_eq_zero_of_emod_ne {m : Int} {d : Nat}
    (h : (m * 10 ^ d) % 10 ≠ 0) : d = 0 := by
  match d with
  | 0 => rfl
  | d + 1 =>
    exact absurd (by rw [Int.pow_succ, ← Int.mul_assoc]; exact Int.mul_emod_left _ _) h

@[simp] theorem canonical_mk {m e : Int} :
    Canonical ⟨m, e⟩ ↔ (m % 10 ≠ 0 ∨ (m = 0 ∧ e = 0)) := Iff.rfl

private theorem eq_of_scaled {ma mb ea eb : Int} (hle : ea ≤ eb)
    (ha : ma % 10 ≠ 0 ∨ (ma = 0 ∧ ea = 0)) (hb : mb % 10 ≠ 0 ∨ (mb = 0 ∧ eb = 0))
    (h : ma = mb * 10 ^ (eb - ea).toNat) : ma = mb ∧ ea = eb := by
  rcases ha with hma | ⟨hma, hea⟩
  · have hd : (eb - ea).toNat = 0 := exponent_eq_zero_of_emod_ne (h ▸ hma)
    rw [hd] at h
    exact ⟨by simpa using h, by omega⟩
  · subst hma
    have hmb : mb = 0 := by
      rcases Int.mul_eq_zero.mp h.symm with h' | h'
      · exact h'
      · exact absurd h' (Int.ne_of_gt (pow_ten_pos _))
    rcases hb with hmb' | ⟨_, heb⟩
    · exact absurd (by simp [hmb]) hmb'
    · exact ⟨hmb.symm, by omega⟩

theorem eqv_iff_eq {a b : Number} (ha : Canonical a) (hb : Canonical b) :
    Eqv a b ↔ a = b := by
  obtain ⟨ma, ea⟩ := a
  obtain ⟨mb, eb⟩ := b
  constructor
  · intro h
    simp only [Eqv, scaleTo] at h
    rcases Int.le_total ea eb with hle | hle
    · have h₁ : (ea - min ea eb).toNat = 0 := by omega
      have h₂ : (eb - min ea eb).toNat = (eb - ea).toNat := by omega
      rw [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := eq_of_scaled hle ha hb (by simpa using h)
      rfl
    · have h₁ : (eb - min ea eb).toNat = 0 := by omega
      have h₂ : (ea - min ea eb).toNat = (ea - eb).toNat := by omega
      rw [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := eq_of_scaled hle hb ha (by simpa using h.symm)
      rfl
  · intro h
    injection h with hm he
    subst hm
    subst he
    rfl

def normalizeAux (m e : Int) : Number :=
  if h : m % 10 = 0 ∧ m ≠ 0 then normalizeAux (m / 10) (e + 1) else ⟨m, e⟩
termination_by m.natAbs
decreasing_by
  obtain ⟨h1, h2⟩ := h
  omega

/-- The canonical representation of `mantissa * 10 ^ exponent`. -/
def normalize (mantissa exponent : Int) : Number :=
  if mantissa = 0 then ⟨0, 0⟩ else normalizeAux mantissa exponent

theorem canonical_normalizeAux : ∀ (m e : Int), m ≠ 0 → Canonical (normalizeAux m e) := by
  intro m e
  fun_induction normalizeAux m e with
  | case1 m e h ih =>
    intro _
    exact ih (by obtain ⟨h1, h2⟩ := h; omega)
  | case2 m e h =>
    intro hm
    exact Or.inl fun hc => h ⟨hc, hm⟩

theorem canonical_normalize (m e : Int) : Canonical (normalize m e) := by
  unfold normalize
  split
  next => exact Or.inr ⟨rfl, rfl⟩
  next hm => exact canonical_normalizeAux _ _ hm

theorem eqv_div_ten {m e : Int} (h : m % 10 = 0) : Eqv ⟨m / 10, e + 1⟩ ⟨m, e⟩ := by
  refine eqv_of_scaleTo (k := e) (show (e : Int) ≤ e + 1 by omega) (Int.le_refl e) ?_
  have h1 : ((e + 1) - e).toNat = 1 := by omega
  have h2 : (e - e).toNat = 0 := by omega
  have hdm := Int.mul_ediv_add_emod m 10
  simp only [scaleTo, h1, h2, Int.pow_one, Int.pow_zero, Int.mul_one]
  omega

private theorem eqv_normalizeAux (m e : Int) : Eqv (normalizeAux m e) ⟨m, e⟩ := by
  fun_induction normalizeAux m e with
  | case1 m e h ih => exact ih.trans (eqv_div_ten h.1)
  | case2 m e h => exact Eqv.refl _

theorem eqv_normalize (m e : Int) : Eqv (normalize m e) ⟨m, e⟩ := by
  unfold normalize
  split
  next hm => subst hm; simp [Eqv, scaleTo]
  next => exact eqv_normalizeAux _ _

/-- Canonicity turns numeric equivalence into a decidable equality of canonical forms. -/
theorem eqv_iff_normalize_eq {a b : Number} :
    Eqv a b ↔ normalize a.mantissa a.exponent = normalize b.mantissa b.exponent := by
  constructor
  · intro h
    refine (eqv_iff_eq (canonical_normalize _ _) (canonical_normalize _ _)).mp ?_
    exact ((eqv_normalize a.mantissa a.exponent).trans h).trans
      (eqv_normalize b.mantissa b.exponent).symm
  · intro h
    exact ((eqv_normalize a.mantissa a.exponent).symm.trans
      (h ▸ Eqv.refl _)).trans (eqv_normalize b.mantissa b.exponent)

instance (a b : Number) : Decidable (Eqv a b) :=
  decidable_of_iff _ eqv_iff_normalize_eq.symm

/-- A canonical number is its own normal form. -/
theorem normalize_eq_self {n : Number} (h : Canonical n) :
    normalize n.mantissa n.exponent = n :=
  (eqv_iff_eq (canonical_normalize _ _) h).mp (eqv_normalize _ _)

/-- `mantissa * 10 ^ exponent` for an integer, in canonical form. -/
def ofInt (m : Int) : Number := normalize m 0

def ofNat (n : Nat) : Number := ofInt n

instance : OfNat Number n := ⟨ofNat n⟩

instance : Neg Number := ⟨fun n => ⟨-n.mantissa, n.exponent⟩⟩

/-- Multiply by a power of ten, which only ever adjusts the exponent. -/
def mulPow10 (n : Number) (k : Int) : Number :=
  if n.mantissa = 0 then n else ⟨n.mantissa, n.exponent + k⟩

instance : OfScientific Number where
  ofScientific m sign e := normalize m (if sign then -(e : Int) else (e : Int))

theorem canonical_ofInt (m : Int) : Canonical (ofInt m) := canonical_normalize m 0

@[simp] theorem neg_mantissa (n : Number) : (-n).mantissa = -n.mantissa := rfl

@[simp] theorem neg_exponent (n : Number) : (-n).exponent = n.exponent := rfl

theorem canonical_neg {n : Number} (h : Canonical n) : Canonical (-n) := by
  rcases h with h | ⟨h₁, h₂⟩
  · exact Or.inl (by simp only [neg_mantissa]; omega)
  · exact Or.inr ⟨by simp [h₁], h₂⟩

theorem canonical_mulPow10 {n : Number} (h : Canonical n) (k : Int) :
    Canonical (n.mulPow10 k) := by
  unfold mulPow10
  split
  next => exact h
  next hm =>
    rcases h with h | ⟨h₁, _⟩
    · exact Or.inl h
    · exact absurd h₁ hm

/-- Decimal digits in `m`, counting `0` as one digit. -/
def digitCount (m : Int) : Nat :=
  go m.natAbs 1
where
  go (n acc : Nat) : Nat :=
    if n ≤ 9 then acc else go (n / 10) (acc + 1)
  termination_by n
  decreasing_by omega

private theorem digitCountGo_bounds : ∀ (n acc : Nat), 1 ≤ n →
    ∃ e, digitCount.go n acc = acc + e ∧ 10 ^ e ≤ n ∧ n < 10 ^ (e + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro acc hn
    rw [digitCount.go]
    split
    next h => exact ⟨0, by simp, by simpa using hn, by simp; omega⟩
    next h =>
      obtain ⟨e, he, hle, hlt⟩ := ih (n / 10) (by omega) (acc + 1) (by omega)
      have hs : (10 : Nat) ^ (e + 1) = 10 ^ e * 10 := Nat.pow_succ ..
      have hs' : (10 : Nat) ^ (e + 1 + 1) = 10 ^ (e + 1) * 10 := Nat.pow_succ ..
      exact ⟨e + 1, by omega, by omega, by omega⟩
theorem one_le_digitCount (m : Int) : 1 ≤ digitCount m := by
  rcases Nat.eq_zero_or_pos m.natAbs with h | h
  · simp [digitCount, h, digitCount.go]
  · obtain ⟨e, he, _, _⟩ := digitCountGo_bounds m.natAbs 1 h
    simp only [digitCount, he]
    omega

theorem natAbs_lt_pow_digitCount (m : Int) : m.natAbs < 10 ^ digitCount m := by
  rcases Nat.eq_zero_or_pos m.natAbs with h | h
  · simp [digitCount, h, digitCount.go]
  · obtain ⟨e, he, _, hlt⟩ := digitCountGo_bounds m.natAbs 1 h
    simp only [digitCount, he]
    have : (1 : Nat) + e = e + 1 := by omega
    rw [this]
    exact hlt

theorem pow_digitCount_le {m : Int} (h : m ≠ 0) : 10 ^ (digitCount m - 1) ≤ m.natAbs := by
  have hpos : 0 < m.natAbs := Int.natAbs_pos.mpr h
  obtain ⟨e, he, hle, _⟩ := digitCountGo_bounds m.natAbs 1 hpos
  simp only [digitCount, he]
  have : 1 + e - 1 = e := by omega
  rw [this]
  exact hle

/--
Whether `a` denotes a smaller value than `b`. Only the sign, the position of the leading digit,
and mantissas aligned to a common digit count are ever computed, so the exponent's magnitude
never costs anything.
-/
def isLt (a b : Number) : Bool :=
  if a.mantissa < 0 && 0 ≤ b.mantissa then true
  else if 0 ≤ a.mantissa && b.mantissa < 0 then false
  else if a.mantissa = 0 then 0 < b.mantissa
  else if b.mantissa = 0 then a.mantissa < 0
  else
    let dA : Int := digitCount a.mantissa
    let dB : Int := digitCount b.mantissa
    let sA := dA + a.exponent
    let sB := dB + b.exponent
    if sA ≠ sB then
      if 0 < a.mantissa then sA < sB else sB < sA
    else if dA < dB then
      a.mantissa * 10 ^ (dB - dA).toNat < b.mantissa
    else
      a.mantissa < b.mantissa * 10 ^ (dA - dB).toNat

private theorem natAbs_scaleTo (n : Number) (k : Int) :
    (n.scaleTo k).natAbs = n.mantissa.natAbs * 10 ^ (n.exponent - k).toNat := by
  simp [scaleTo, Int.natAbs_mul, Int.natAbs_pow]
private theorem scaleTo_pos_iff (n : Number) (k : Int) : 0 < n.scaleTo k ↔ 0 < n.mantissa := by
  constructor
  · intro h
    exact Int.lt_of_mul_lt_mul_right (by simpa [scaleTo] using h) (Int.le_of_lt (pow_ten_pos _))
  · intro h
    exact Int.mul_pos h (pow_ten_pos _)

private theorem scaleTo_neg_iff (n : Number) (k : Int) : n.scaleTo k < 0 ↔ n.mantissa < 0 := by
  constructor
  · intro h
    exact Int.lt_of_mul_lt_mul_right (by simpa [scaleTo] using h) (Int.le_of_lt (pow_ten_pos _))
  · intro h
    exact Int.mul_neg_of_neg_of_pos h (pow_ten_pos _)

private theorem scaleTo_eq_zero_iff (n : Number) (k : Int) :
    n.scaleTo k = 0 ↔ n.mantissa = 0 := by
  simp [scaleTo, Int.mul_eq_zero, pow_ten_ne_zero]
private theorem scaleTo_lt_pow (n : Number) (k : Int) :
    (n.scaleTo k).natAbs < 10 ^ (digitCount n.mantissa + (n.exponent - k).toNat) := by
  rw [natAbs_scaleTo, Nat.pow_add]
  exact (Nat.mul_lt_mul_right (Nat.pow_pos (by omega))).mpr (natAbs_lt_pow_digitCount _)

private theorem pow_le_scaleTo {n : Number} (h : n.mantissa ≠ 0) (k : Int) :
    10 ^ (digitCount n.mantissa - 1 + (n.exponent - k).toNat) ≤ (n.scaleTo k).natAbs := by
  rw [natAbs_scaleTo, Nat.pow_add]
  exact Nat.mul_le_mul_right _ (pow_digitCount_le h)

private theorem natAbs_scaleTo_lt {a b : Number} {k : Int} (hb : b.mantissa ≠ 0)
    (h : digitCount a.mantissa + (a.exponent - k).toNat
       < digitCount b.mantissa + (b.exponent - k).toNat) :
    (a.scaleTo k).natAbs < (b.scaleTo k).natAbs := by
  have h1 := scaleTo_lt_pow a k
  have h2 := pow_le_scaleTo hb k
  have hd : 1 ≤ digitCount b.mantissa := one_le_digitCount _
  have hmono : (10:Nat) ^ (digitCount a.mantissa + (a.exponent - k).toNat)
      ≤ 10 ^ (digitCount b.mantissa - 1 + (b.exponent - k).toNat) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

private theorem scaleTo_nonneg_iff (n : Number) (k : Int) :
    0 ≤ n.scaleTo k ↔ 0 ≤ n.mantissa := by
  have h1 := scaleTo_pos_iff n k
  have h2 := scaleTo_eq_zero_iff n k
  omega

private theorem scaleTo_split {n : Number} {k : Int} {d c : Nat}
    (h : (n.exponent - k).toNat = d + c) :
    n.scaleTo k = (n.mantissa * 10 ^ d) * 10 ^ c := by
  simp only [scaleTo, h, Int.pow_add, Int.mul_assoc]

private theorem aligned_left {a b : Number} {k : Int} (hkb : k ≤ b.exponent)
    (hd : digitCount a.mantissa < digitCount b.mantissa)
    (hs : (digitCount a.mantissa : Int) + a.exponent
        = (digitCount b.mantissa : Int) + b.exponent) :
    (a.mantissa * 10 ^ ((digitCount b.mantissa : Int) - (digitCount a.mantissa : Int)).toNat
        < b.mantissa) ↔ a.scaleTo k < b.scaleTo k := by
  have hA : a.scaleTo k =
      (a.mantissa * 10 ^ ((digitCount b.mantissa : Int) - (digitCount a.mantissa : Int)).toNat)
        * 10 ^ (b.exponent - k).toNat :=
    scaleTo_split (by omega)
  have hB : b.scaleTo k = b.mantissa * 10 ^ (b.exponent - k).toNat := by
    simp [scaleTo]
  rw [hA, hB]
  exact (Int.mul_lt_mul_right (pow_ten_pos _)).symm

private theorem aligned_right {a b : Number} {k : Int} (hka : k ≤ a.exponent)
    (hd : digitCount b.mantissa ≤ digitCount a.mantissa)
    (hs : (digitCount a.mantissa : Int) + a.exponent
        = (digitCount b.mantissa : Int) + b.exponent) :
    (a.mantissa
        < b.mantissa * 10 ^ ((digitCount a.mantissa : Int) - (digitCount b.mantissa : Int)).toNat)
      ↔ a.scaleTo k < b.scaleTo k := by
  have hB : b.scaleTo k =
      (b.mantissa * 10 ^ ((digitCount a.mantissa : Int) - (digitCount b.mantissa : Int)).toNat)
        * 10 ^ (a.exponent - k).toNat :=
    scaleTo_split (by omega)
  have hA : a.scaleTo k = a.mantissa * 10 ^ (a.exponent - k).toNat := by
    simp [scaleTo]
  rw [hA, hB]
  exact (Int.mul_lt_mul_right (pow_ten_pos _)).symm

/--
The efficient comparison agrees with the obvious one, which rescales both mantissas to a common
exponent. Any `k` at or below both exponents will do, a factor of ten shared by the two sides
leaving the comparison alone.
-/
theorem isLt_iff {a b : Number} {k : Int} (hka : k ≤ a.exponent) (hkb : k ≤ b.exponent) :
    isLt a b = true ↔ a.scaleTo k < b.scaleTo k := by
  have hpa := scaleTo_pos_iff a k
  have hna := scaleTo_neg_iff a k
  have hza := scaleTo_eq_zero_iff a k
  have hqa := scaleTo_nonneg_iff a k
  have hpb := scaleTo_pos_iff b k
  have hnb := scaleTo_neg_iff b k
  have hzb := scaleTo_eq_zero_iff b k
  have hqb := scaleTo_nonneg_iff b k
  have hp : ((a.exponent - k).toNat : Int) = a.exponent - k := Int.toNat_of_nonneg (by omega)
  have hq : ((b.exponent - k).toNat : Int) = b.exponent - k := Int.toNat_of_nonneg (by omega)
  unfold isLt
  split
  next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [true_iff]
    omega
  split
  next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine iff_of_false (by simp) ?_
    omega
  split
  next h =>
    simp only [decide_eq_true_eq]
    omega
  split
  next h =>
    simp only [decide_eq_true_eq]
    omega
  rename_i h₁ h₂ ha0 hb0
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h₁ h₂
  split
  next hposa =>
    have hposb : 0 < b.mantissa := by omega
    have hAv : ((a.scaleTo k).natAbs : Int) = a.scaleTo k := Int.natAbs_of_nonneg (by omega)
    have hBv : ((b.scaleTo k).natAbs : Int) = b.scaleTo k := Int.natAbs_of_nonneg (by omega)
    simp only []
    split
    next hne =>
      simp only [decide_eq_true_eq]
      rcases Int.lt_trichotomy (digitCount a.mantissa + a.exponent : Int)
          (digitCount b.mantissa + b.exponent : Int) with hs | hs | hs
      · have := natAbs_scaleTo_lt (a := a) (b := b) (k := k) hb0 (by omega)
        exact iff_of_true hs (by omega)
      · exact absurd hs hne
      · have := natAbs_scaleTo_lt (a := b) (b := a) (k := k) ha0 (by omega)
        exact iff_of_false (by omega) (by omega)
    next hne =>
      split
      next hd =>
        simpa only [decide_eq_true_eq] using
          aligned_left (a := a) (b := b) hkb (by omega) (by omega)
      next hd =>
        simpa only [decide_eq_true_eq] using
          aligned_right (a := a) (b := b) hka (by omega) (by omega)
  next hposa =>
    have hnega : a.mantissa < 0 := by omega
    have hnegb : b.mantissa < 0 := by omega
    have hAv : ((a.scaleTo k).natAbs : Int) = -a.scaleTo k :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hBv : ((b.scaleTo k).natAbs : Int) = -b.scaleTo k :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    simp only []
    split
    next hne =>
      simp only [decide_eq_true_eq]
      rcases Int.lt_trichotomy (digitCount a.mantissa + a.exponent : Int)
          (digitCount b.mantissa + b.exponent : Int) with hs | hs | hs
      · have := natAbs_scaleTo_lt (a := a) (b := b) (k := k) hb0 (by omega)
        exact iff_of_false (by omega) (by omega)
      · exact absurd hs hne
      · have := natAbs_scaleTo_lt (a := b) (b := a) (k := k) ha0 (by omega)
        exact iff_of_true (by omega) (by omega)
    next hne =>
      split
      next hd =>
        simpa only [decide_eq_true_eq] using
          aligned_left (a := a) (b := b) hkb (by omega) (by omega)
      next hd =>
        simpa only [decide_eq_true_eq] using
          aligned_right (a := a) (b := b) hka (by omega) (by omega)

/--
The equality case is decided by canonical form, so it is exact; the remaining branch only has to
choose between `lt` and `gt`, and can never report `eq`.
-/
def cmp (a b : Number) : Ordering :=
  if normalize a.mantissa a.exponent = normalize b.mantissa b.exponent then .eq
  else if isLt a b then .lt else .gt

instance : Ord Number := ⟨cmp⟩

theorem cmp_eq_eq_iff_eqv {a b : Number} : cmp a b = .eq ↔ Eqv a b := by
  unfold cmp
  split
  next h => exact iff_of_true rfl (eqv_iff_normalize_eq.mpr h)
  next h =>
    refine iff_of_false ?_ (fun he => h (eqv_iff_normalize_eq.mp he))
    split <;> simp

theorem cmp_eq_eq_iff_eq {a b : Number} (ha : Canonical a) (hb : Canonical b) :
    cmp a b = .eq ↔ a = b :=
  cmp_eq_eq_iff_eqv.trans (eqv_iff_eq ha hb)

/-- Comparison agrees with rescaling both to a common exponent and comparing the integers. -/
theorem cmp_eq_compare_scaleTo {a b : Number} {k : Int} (hka : k ≤ a.exponent)
    (hkb : k ≤ b.exponent) : cmp a b = compare (a.scaleTo k) (b.scaleTo k) := by
  unfold cmp
  split
  next h =>
    have heq : a.scaleTo k = b.scaleTo k :=
      scaleTo_eq_of_eqv hka hkb (eqv_iff_normalize_eq.mpr h)
    simp [heq]
  next h =>
    have hne : a.scaleTo k ≠ b.scaleTo k := fun he =>
      h (eqv_iff_normalize_eq.mp (eqv_of_scaleTo hka hkb he))
    split
    next hlt => exact (Int.compare_eq_lt.mpr ((isLt_iff hka hkb).mp hlt)).symm
    next hlt =>
      have hge : ¬ a.scaleTo k < b.scaleTo k := fun hc => hlt ((isLt_iff hka hkb).mpr hc)
      exact (Int.compare_eq_gt.mpr (by omega)).symm



/--
The integer `n` denotes, when it denotes one and writing it out costs at most `maxPadding`
zeros beyond the digits already present in the mantissa.

The bound is on the padding rather than on the result, because the cost that has to be
refused is the one a short text can inflict: `1e1000000000` is twelve characters and an
integer of a billion digits. A mantissa that is itself long has already been paid for by
whoever holds it, so it passes.
-/
def toInt? (n : Number) (maxPadding : Nat := 1000) : Option Int :=
  if n.mantissa = 0 then
    some 0
  else if 0 ≤ n.exponent then
    if n.exponent ≤ (maxPadding : Int) then
      some (n.mantissa * 10 ^ n.exponent.toNat)
    else
      none
  else
    -- Below one in magnitude unless the mantissa's own trailing zeros absorb the exponent, so
    -- the power of ten computed here is bounded by the mantissa's length.
    let k := (-n.exponent).toNat
    if k ≤ digitCount n.mantissa then
      let p : Int := 10 ^ k
      if n.mantissa % p = 0 then some (n.mantissa / p) else none
    else
      none

/-- As `toInt?`, refusing a negative value as well as an over-padded one. -/
def toNat? (n : Number) (maxPadding : Nat := 1000) : Option Nat :=
  match n.toInt? maxPadding with
  | some i => if 0 ≤ i then some i.toNat else none
  | none => none

/--
The nearest `Float`, saturating to zero or an infinity outside the double range and truncating
mantissas far longer than a double can represent. Not verified against IEEE 754.
-/
def toFloat (n : Number) : Float :=
  if n.mantissa = 0 then
    0.0
  else
    let sign : Float := if n.mantissa < 0 then -1.0 else 1.0
    let d := digitCount n.mantissa
    let (m, e) :=
      if d ≤ 40 then (n.mantissa.natAbs, n.exponent)
      else (n.mantissa.natAbs / 10 ^ (d - 40), n.exponent + ((d - 40 : Nat) : Int))
    if e < -400 then sign * 0.0
    else if 400 < e then sign * (1.0 / 0.0)
    else if e < 0 then sign * OfScientific.ofScientific m true (-e).toNat
    else sign * OfScientific.ofScientific m false e.toNat

/--
The exact value of `x`, or `none` for a NaN or an infinity, neither of which JSON can express.

A `Float` is `m * 2 ^ e` for integers `m` and `e`, and every such value has a finite decimal
expansion, because `2 ^ e = 5 ^ -e * 10 ^ e` when `e` is negative. So the conversion is exact,
at the cost of being long: fifty significant digits is ordinary and a subnormal reaches several
hundred. The alternative, converting through the shortest decimal spelling a `Float` prints,
loses the value outright for small magnitudes.
-/
def ofFloat? (x : Float) : Option Number :=
  let bits := x.toBits.toNat
  let frac := bits % 0x10000000000000
  let biased := bits / 0x10000000000000 % 0x800
  -- A subnormal has no implicit leading bit, and takes the exponent of the smallest normal.
  let m : Nat := if biased = 0 then frac else frac + 0x10000000000000
  let e : Int := if biased = 0 then -1074 else (biased : Int) - 1075
  let signed : Int := if 0x8000000000000000 ≤ bits then -(m : Int) else (m : Int)
  if biased = 0x7FF then none
  else if 0 ≤ e then some (normalize (signed * 2 ^ e.toNat) 0)
  else some (normalize (signed * 5 ^ (-e).toNat) e)

theorem canonical_ofFloat {x : Float} {n : Number} (h : ofFloat? x = some n) : Canonical n := by
  simp only [ofFloat?] at h
  repeat' split at h
  all_goals first
    | (injection h with h; exact h ▸ canonical_normalize _ _)
    | simp at h


/-- Normalisation only ever moves the exponent up, one trailing zero at a time. -/
theorem le_exponent_normalizeAux (m e : Int) : e ≤ (normalizeAux m e).exponent := by
  fun_induction normalizeAux m e with
  | case1 m e h ih => omega
  | case2 m e h => simp

/--
An integer read back out of the number it was written to is the integer, whenever writing it out
again stays within the padding bound.
-/
theorem toInt?_ofInt {i : Int} {maxPadding : Nat}
    (h : (ofInt i).exponent ≤ (maxPadding : Int)) :
    (ofInt i).toInt? maxPadding = some i := by
  have hexp : 0 ≤ (normalize i 0).exponent := by
    unfold normalize
    split
    · simp
    · exact le_exponent_normalizeAux i 0
  have hval : (normalize i 0).mantissa * 10 ^ (normalize i 0).exponent.toNat = i := by
    have heqv := eqv_normalize i 0
    simp only [Eqv, scaleTo, show min (normalize i 0).exponent 0 = 0 by omega] at heqv
    simpa using heqv
  have h' : (normalize i 0).exponent ≤ (maxPadding : Int) := h
  by_cases hm : (normalize i 0).mantissa = 0
  · have hi : i = 0 := by simpa [hm] using hval.symm
    simp [ofInt, toInt?, normalize, hi]
  · simp [ofInt, toInt?, hm, hexp, h', hval]

theorem toNat?_ofNat {n : Nat} {maxPadding : Nat}
    (h : (ofNat n).exponent ≤ (maxPadding : Int)) :
    (ofNat n).toNat? maxPadding = some n := by
  simp [toNat?, ofNat, toInt?_ofInt h]

end Number

end

end Json
