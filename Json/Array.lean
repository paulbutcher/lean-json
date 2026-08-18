/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

/-!
Facts about arrays that Lean's own library does not carry, kept apart from the JSON they serve
because there is nothing about JSON in them.

`pushInduction` is the shape every claim about a fold takes: `Array.foldl_push` turns one step of
a fold into one step of the induction, so a lemma about `Array.foldl` is proved by saying what
one more element does to the result.
-/

namespace Array

theorem pushInduction {α : Type u} {motive : Array α → Prop} (empty : motive #[])
    (push : ∀ (a : Array α) (x : α), motive a → motive (a.push x)) (a : Array α) : motive a := by
  have rev : ∀ l : List α, motive l.reverse.toArray := by
    intro l
    induction l with
    | nil => exact empty
    | cons x t ih =>
      have h : (x :: t).reverse.toArray = t.reverse.toArray.push x := by simp
      exact h ▸ push _ x ih
  simpa using rev a.toList.reverse

theorem setIfInBounds_push_lt {a : Array α} {i : Nat} (h : i < a.size) (x y : α) :
    (a.push x).setIfInBounds i y = (a.setIfInBounds i y).push x := by
  rw [← Array.toList_inj]
  simp [Array.toList_setIfInBounds,
    List.set_append_left _ _ (by rw [Array.length_toList]; exact h)]

theorem setIfInBounds_push_size {a : Array α} (x y : α) :
    (a.push x).setIfInBounds a.size y = a.push y := by
  rw [← Array.toList_inj]
  simp [Array.toList_setIfInBounds, List.set_append_right]

/-- Putting an element back where it already was, unchanged. -/
theorem setIfInBounds_getElem {a : Array α} {i : Nat} (h : i < a.size) :
    a.setIfInBounds i a[i] = a := by
  have h' : i < a.toList.length := by simpa using h
  rw [← Array.toList_inj, Array.toList_setIfInBounds, ← Array.getElem_toList h',
    List.set_getElem_self]

end Array
