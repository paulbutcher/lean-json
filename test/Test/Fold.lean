/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json

/-!
An object's fields, described one `push` at a time.

`findLast?`, `findLastIdx?` and `dedupKeys` are each a left fold over the field array, so a claim
about any of them is a claim about what a fold accumulates. `pushInduction` is the induction that
fits: `Array.foldl_push` turns one step of a fold into one step of the induction, and each of the
folds then has a single lemma saying what pushing a field does to it. `distinctNames` is a loop
rather than a fold, so it is first related to `Nodup` and then given a lemma of the same shape.

Everything else in the test suite that reasons about objects, deduplication and the path
operations among them, is stated in terms of these.
-/

open Json

namespace Test.Fold

universe u
variable {α : Type u}

theorem pushInduction {motive : Array α → Prop} (empty : motive #[])
    (push : ∀ (a : Array α) (x : α), motive a → motive (a.push x)) (a : Array α) : motive a := by
  have rev : ∀ l : List α, motive l.reverse.toArray := by
    intro l
    induction l with
    | nil => exact empty
    | cons x t ih =>
      have h : (x :: t).reverse.toArray = t.reverse.toArray.push x := by simp
      exact h ▸ push _ x ih
  simpa using rev a.toList.reverse

/-- The names an object gives its fields, in the order they appear. -/
def names (a : Array (String × α)) : List String := a.toList.map (·.1)

@[simp] theorem names_push (a : Array (String × α)) (x : String × α) :
    names (a.push x) = names a ++ [x.1] := by simp [names]

private theorem names_length (a : Array (String × α)) : (names a).length = a.size := by
  simp [names]

/-! ## Lookup -/

theorem findLast?_push (a : Array (String × α)) (key : String) (v : α) (k : String) :
    findLast? (a.push (key, v)) k = if key == k then some v else findLast? a k := by
  simp [findLast?]

private theorem findLastIdxCount (a : Array (String × α)) (k : String) :
    (a.foldl (init := ((none : Option Nat), 0)) (fun (found, i) (key, _) =>
      (if key == k then some i else found, i + 1))).2 = a.size := by
  induction a using pushInduction with
  | empty => rfl
  | push a x ih => rw [Array.foldl_push]; simpa using ih

theorem findLastIdx?_push (a : Array (String × α)) (key : String) (v : α) (k : String) :
    findLastIdx? (a.push (key, v)) k = if key == k then some a.size else findLastIdx? a k := by
  have h := findLastIdxCount a k
  simp only [findLastIdx?, Array.foldl_push] at *
  split <;> simp_all

theorem findLast?_eq_none_iff (a : Array (String × α)) (k : String) :
    findLast? a k = none ↔ k ∉ names a := by
  induction a using pushInduction with
  | empty => simp [findLast?, names]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    by_cases h : key = k
    · subst h; simp [findLast?_push]
    · simp [findLast?_push, h, ih, Ne.symm h]

theorem findLastIdx?_eq_none_iff (a : Array (String × α)) (k : String) :
    findLastIdx? a k = none ↔ k ∉ names a := by
  induction a using pushInduction with
  | empty => simp [findLastIdx?, names]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    by_cases h : key = k
    · subst h; simp [findLastIdx?_push]
    · simp [findLastIdx?_push, h, ih, Ne.symm h]

theorem findLastIdx?_eq_some {a : Array (String × α)} {k : String} {i : Nat}
    (h : findLastIdx? a k = some i) :
    ∃ hi : i < a.size, a[i].1 = k ∧ findLast? a k = some a[i].2 := by
  induction a using pushInduction with
  | empty => simp [findLastIdx?] at h
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    rw [findLastIdx?_push] at h
    by_cases hk : key = k
    · subst hk
      simp at h
      subst h
      refine ⟨by simp, ?_⟩
      simp [Array.getElem_push, findLast?_push]
    · simp [hk] at h
      obtain ⟨hi, hkey, hval⟩ := ih h
      refine ⟨by simp; omega, ?_⟩
      simp [Array.getElem_push, hi, findLast?_push, hk, hkey, hval]

theorem findLastIdx?_lt {a : Array (String × α)} {k : String} {i : Nat}
    (h : findLastIdx? a k = some i) : i < a.size := (findLastIdx?_eq_some h).1

/-- A name that lookup finds has a position, which is what an in-place update needs. -/
theorem findLastIdx?_isSome {a : Array (String × α)} {k : String} {v : α}
    (h : findLast? a k = some v) : ∃ i, findLastIdx? a k = some i := by
  cases hi : findLastIdx? a k with
  | some i => exact ⟨i, rfl⟩
  | none =>
    rw [(findLast?_eq_none_iff a k).2 ((findLastIdx?_eq_none_iff a k).1 hi)] at h
    exact absurd h (by simp)

/-! ## Updating in place -/

private theorem setIfInBounds_push_lt {a : Array α} {i : Nat} (h : i < a.size) (x y : α) :
    (a.push x).setIfInBounds i y = (a.setIfInBounds i y).push x := by
  rw [← Array.toList_inj]
  simp [Array.toList_setIfInBounds,
    List.set_append_left _ _ (by rw [Array.length_toList]; exact h)]

private theorem setIfInBounds_push_size {a : Array α} (x y : α) :
    (a.push x).setIfInBounds a.size y = a.push y := by
  rw [← Array.toList_inj]
  simp [Array.toList_setIfInBounds, List.set_append_right]

/--
Replacing the last field named `k` is what lookup sees: that name yields the new value, and
every other name is unaffected.
-/
theorem findLast?_setIfInBounds {a : Array (String × α)} {k k' : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) :
    findLast? (a.setIfInBounds i (k, v)) k' = if k == k' then some v else findLast? a k' := by
  induction a using pushInduction with
  | empty => simp [findLastIdx?] at h
  | push a x ih =>
    obtain ⟨key, w⟩ := x
    rw [findLastIdx?_push] at h
    by_cases hk : key = k
    · subst hk
      simp at h
      subst h
      rw [setIfInBounds_push_size, findLast?_push, findLast?_push]
      by_cases hk' : key = k' <;> simp [hk']
    · simp [hk] at h
      rw [setIfInBounds_push_lt (findLastIdx?_lt h), findLast?_push, findLast?_push, ih h]
      by_cases hk' : key = k' <;> by_cases hkk' : k = k' <;> simp_all

/-- Putting an element back where it already was, unchanged. -/
theorem setIfInBounds_getElem {a : Array α} {i : Nat} (h : i < a.size) :
    a.setIfInBounds i a[i] = a := by
  have h' : i < a.toList.length := by simpa using h
  rw [← Array.toList_inj, Array.toList_setIfInBounds, ← Array.getElem_toList h',
    List.set_getElem_self]

/-- Putting a field back where it already was, unchanged. -/
theorem setIfInBounds_self {a : Array (String × α)} {k : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) (hv : findLast? a k = some v) :
    a.setIfInBounds i (k, v) = a := by
  obtain ⟨hi, hkey, hval⟩ := findLastIdx?_eq_some h
  rw [hv] at hval
  have hfield : (k, v) = a[i] := Prod.ext hkey.symm (Option.some.inj hval)
  rw [hfield, setIfInBounds_getElem hi]

/-! ## Distinct names -/

private theorem names_drop (a : Array (String × α)) {i : Nat} (h : i < a.size) :
    (names a).drop i = a[i].1 :: (names a).drop (i + 1) := by
  have hi : i < (names a).length := by simpa [names_length] using h
  rw [List.drop_eq_getElem_cons hi]
  simp [names]

private theorem distinctNamesGo (a : Array (String × α)) (i : Nat) (seen : Std.HashSet String) :
    distinctNames.go a i seen = true ↔
      ((names a).drop i).Nodup ∧ ∀ x ∈ (names a).drop i, seen.contains x = false := by
  induction i, seen using distinctNames.go.induct (fields := a) with
  | case1 i seen h k hc =>
    rw [distinctNames.go, dif_pos h, if_pos hc, names_drop a h]
    have hmem : a[i].1 ∈ seen := by simpa using hc
    simp [hmem]
  | case2 i seen h k hc ih =>
    rw [distinctNames.go, dif_pos h, if_neg hc, ih, names_drop a h]
    simp only [Std.HashSet.contains_insert]
    grind
  | case3 i seen h =>
    have hnil : (names a).drop i = [] := by
      apply List.drop_eq_nil_of_le
      rw [names_length]
      omega
    rw [distinctNames.go, dif_neg h]
    simp [hnil]

theorem distinctNames_iff (a : Array (String × α)) :
    distinctNames a = true ↔ (names a).Nodup := by
  rw [distinctNames, distinctNamesGo]
  simp

theorem distinctNames_push (a : Array (String × α)) (x : String × α) :
    distinctNames (a.push x) = true ↔ distinctNames a = true ∧ findLast? a x.1 = none := by
  rw [distinctNames_iff, distinctNames_iff, findLast?_eq_none_iff, names_push]
  simp only [List.nodup_append]
  grind

theorem names_setIfInBounds {a : Array (String × α)} {k : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) : names (a.setIfInBounds i (k, v)) = names a := by
  obtain ⟨hi, hkey, _⟩ := findLastIdx?_eq_some h
  have hi' : i < (names a).length := by rw [names_length]; exact hi
  have hget : (names a)[i]'hi' = k := by simp [names, hkey]
  have hset : names (a.setIfInBounds i (k, v)) = (names a).set i k := by
    simp [names, Array.toList_setIfInBounds, List.map_set]
  rw [hset, ← hget, List.set_getElem_self]

/-! ## Deduplication -/

theorem dedupKeys_push_none {a : Array (String × α)} {key : String} {v : α}
    (h : findLastIdx? (dedupKeys a) key = none) :
    dedupKeys (a.push (key, v)) = (dedupKeys a).push (key, v) := by
  simp only [dedupKeys, Array.foldl_push] at h ⊢
  rw [h]

theorem dedupKeys_push_some {a : Array (String × α)} {key : String} {v : α} {i : Nat}
    (h : findLastIdx? (dedupKeys a) key = some i) :
    dedupKeys (a.push (key, v)) = (dedupKeys a).setIfInBounds i (key, v) := by
  simp only [dedupKeys, Array.foldl_push] at h ⊢
  rw [h]

/--
Deduplication leaves every lookup unchanged, which is what makes it safe to apply to an object
whose names a caller may already have read.
-/
theorem findLast?_dedupKeys (a : Array (String × α)) (k : String) :
    findLast? (dedupKeys a) k = findLast? a k := by
  induction a using pushInduction with
  | empty => rfl
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    rw [findLast?_push]
    cases h : findLastIdx? (dedupKeys a) key with
    | none => rw [dedupKeys_push_none h, findLast?_push, ih]
    | some i => rw [dedupKeys_push_some h, findLast?_setIfInBounds h, ih]

theorem distinctNames_dedupKeys (a : Array (String × α)) : distinctNames (dedupKeys a) = true := by
  induction a using pushInduction with
  | empty => rw [distinctNames_iff]; simp [dedupKeys, names]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    cases h : findLastIdx? (dedupKeys a) key with
    | none =>
      rw [dedupKeys_push_none h, distinctNames_push]
      exact ⟨ih, (findLast?_eq_none_iff _ _).2 ((findLastIdx?_eq_none_iff _ _).1 h)⟩
    | some i =>
      rw [dedupKeys_push_some h, distinctNames_iff, names_setIfInBounds h, ← distinctNames_iff]
      exact ih

/-- An object that repeats no name is left alone. -/
theorem dedupKeys_eq_self :
    ∀ a : Array (String × α), distinctNames a = true → dedupKeys a = a := by
  intro a
  induction a using pushInduction with
  | empty => intro _; rfl
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    intro h
    rw [distinctNames_push] at h
    have hnone : findLastIdx? (dedupKeys a) key = none := by
      rw [ih h.1]
      exact (findLastIdx?_eq_none_iff a key).2 ((findLast?_eq_none_iff a key).1 h.2)
    rw [dedupKeys_push_none hnone, ih h.1]

theorem dedupKeys_dedupKeys (a : Array (String × α)) : dedupKeys (dedupKeys a) = dedupKeys a :=
  dedupKeys_eq_self _ (distinctNames_dedupKeys a)

end Test.Fold
