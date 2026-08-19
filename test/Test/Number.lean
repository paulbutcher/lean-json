/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json

open Json Json.Number

namespace Test.Number

-- `decide` cannot evaluate these definitions, since well-founded recursion does not reduce in
-- the kernel, but their equation lemmas let `simp` do it.
attribute [local simp] normalize normalizeAux digitCount digitCount.go Number.ofInt cmp isLt
  toInt? toNat?

example : LawfulBEq Json.Number := inferInstance

example : normalize 150 (-2) = ⟨15, -1⟩ := by simp

example : normalize 100 0 = ⟨1, 2⟩ := by simp

example : normalize (-1500) 3 = ⟨-15, 5⟩ := by simp

example : normalize 0 7 = ⟨0, 0⟩ := by simp

-- `-0` and `0` denote the same value, as do `100` and `1e2`.
example : Number.ofInt (-0) = Number.ofInt 0 := by simp

example : cmp ⟨1, 2⟩ ⟨100, 0⟩ = .eq := by simp

example : cmp ⟨15, -1⟩ ⟨150, -2⟩ = .eq := by simp

-- Ordering across scales, including a tie in leading digit position, where the mantissas have
-- to be aligned before they can be compared.
example : cmp ⟨1, 2⟩ ⟨999, -1⟩ = .gt := by simp

example : cmp ⟨-1, 2⟩ ⟨-999, -1⟩ = .lt := by simp

example : cmp ⟨-5, 0⟩ ⟨1, -3⟩ = .lt := by simp

example : cmp ⟨0, 0⟩ ⟨-1, -5⟩ = .gt := by simp

-- Equal leading digit positions with unequal digit counts: 90 against 85, then 85 against 90,
-- which is the case that only the mantissa alignment can decide.
example : cmp ⟨9, 1⟩ ⟨85, 0⟩ = .gt := by simp

example : cmp ⟨85, 0⟩ ⟨9, 1⟩ = .lt := by simp

example : cmp ⟨-9, 1⟩ ⟨-85, 0⟩ = .lt := by simp

example : cmp ⟨-85, 0⟩ ⟨-9, 1⟩ = .gt := by simp

-- An exponent that could never be expanded still compares and converts in no time, which is
-- what makes the exponent bomb unreachable.
example : cmp ⟨1, 1000000000⟩ ⟨2, 1000000000⟩ = .lt := by simp

example : toInt? ⟨1, 1000000000⟩ = none := by simp

example : toInt? ⟨1, 3⟩ = some 1000 := by simp

example : toInt? ⟨15, -1⟩ = none := by simp

example : toNat? ⟨-1, 3⟩ = none := by simp

example : digitCount 1000 = 4 := by simp

example : digitCount (-99) = 2 := by simp

/--
The efficient comparison agrees with the obvious but bomb-prone one, which rescales both
mantissas to a common exponent and compares those. It holds at every exponent, the digit-count
bounds the scale comparison turns on being proved rather than sampled.
-/
example (ma ea mb eb : Int) :
    cmp ⟨ma, ea⟩ ⟨mb, eb⟩ =
      compare (scaleTo ⟨ma, ea⟩ (min ea eb)) (scaleTo ⟨mb, eb⟩ (min ea eb)) :=
  cmp_eq_compare_scaleTo (Int.min_le_left _ _) (Int.min_le_right _ _)

end Test.Number
