/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Value

public section

@[expose] section

namespace Json

/-!
Walking a whole value without the C stack.

`Alg` says what to do at each kind of node, `run` applies it by recursion, and `fold` applies it
with the containers part way through held in a list. `fold_eq_run` is what lets the second stand
in for the first, so that a claim can be made against a plain recursion and still describe what
runs: `Json.Basic` ties each traversal it defines to its folded form with `csimp`.

`beqPairs` is the same idea for a comparison, which has two values to walk rather than one and so
keeps a work list of pairs rather than a stack of part-built containers.

The measures the termination arguments turn on are `noncomputable`, `sizeOf` of a `Json` being
so, and appear nowhere but in `termination_by`.
-/

/-- What a traversal does at each kind of node. -/
structure Alg (α : Type u) where
  null : α
  bool : Bool → α
  num : Number → α
  str : String → α
  arr : Array α → α
  obj : Array (String × α) → α

namespace Alg

variable {α : Type u}

mutual

/-- The algebra applied by recursion, which is the form every proof is stated against. -/
def run (a : Alg α) : Json → α
  | .null => a.null
  | .bool b => a.bool b
  | .num n => a.num n
  | .str s => a.str s
  | .arr elems => a.arr (a.runList elems.toList).toArray
  | .obj fields => a.obj (a.runFields fields.toList).toArray

def runList (a : Alg α) : List Json → List α
  | [] => []
  | j :: rest => a.run j :: a.runList rest

def runFields (a : Alg α) : List (String × Json) → List (String × α)
  | [] => []
  | (k, v) :: rest => (k, a.run v) :: a.runFields rest

end

/-- A container part way through: what has been folded already, and what is still to fold. -/
inductive Frame (α : Type u) where
  | arr (done : Array α) (rest : List Json)
  | obj (done : Array (String × α)) (name : String) (rest : List (String × Json))

noncomputable def pendingList : List Json → Nat
  | [] => 1
  | j :: rest => sizeOf j + pendingList rest + 1

noncomputable def pendingFields : List (String × Json) → Nat
  | [] => 1
  | (_, v) :: rest => sizeOf v + pendingFields rest + 1

private theorem pendingList_le : ∀ l : List Json, pendingList l ≤ sizeOf l
  | [] => by simp [pendingList]
  | j :: rest => by
    have := pendingList_le rest
    simp only [pendingList, List.cons.sizeOf_spec]
    omega

private theorem pendingFields_le : ∀ l : List (String × Json), pendingFields l ≤ sizeOf l
  | [] => by simp [pendingFields]
  | (k, v) :: rest => by
    have := pendingFields_le rest
    simp only [pendingFields, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    omega

private theorem sizeOf_pos (j : Json) : 0 < sizeOf j := by cases j <;> simp <;> omega

private theorem arr_pending_lt {elems : Array Json} {j : Json} {rest : List Json}
    (h : elems.toList = j :: rest) : sizeOf j + pendingList rest < sizeOf (Json.arr elems) := by
  have := pendingList_le rest
  cases elems with
  | mk l => simp_all; omega

private theorem obj_pending_lt {fields : Array (String × Json)} {name : String} {v : Json}
    {rest : List (String × Json)} (h : fields.toList = (name, v) :: rest) :
    sizeOf v + pendingFields rest < sizeOf (Json.obj fields) := by
  have := pendingFields_le rest
  cases fields with
  | mk l => simp_all; omega

noncomputable def Frame.pending : Frame α → Nat
  | .arr _ rest => pendingList rest
  | .obj _ _ rest => pendingFields rest

noncomputable def pending : List (Frame α) → Nat
  | [] => 0
  | f :: k => f.pending + pending k

mutual

/-- Fold `j`, then give the answer to the frames waiting for it. -/
def step (a : Alg α) (j : Json) (k : List (Frame α)) : α :=
  match j with
  | .null => resume a a.null k
  | .bool b => resume a (a.bool b) k
  | .num n => resume a (a.num n) k
  | .str s => resume a (a.str s) k
  | .arr elems =>
    match _h : elems.toList with
    | [] => resume a (a.arr #[]) k
    | j' :: rest => step a j' (.arr #[] rest :: k)
  | .obj fields =>
    match _h : fields.toList with
    | [] => resume a (a.obj #[]) k
    | (name, v) :: rest => step a v (.obj #[] name rest :: k)
termination_by sizeOf j + pending k
decreasing_by
  · have := sizeOf_pos Json.null; omega
  · have := sizeOf_pos (Json.bool b); omega
  · have := sizeOf_pos (Json.num n); omega
  · have := sizeOf_pos (Json.str s); omega
  · have := sizeOf_pos (Json.arr elems); omega
  · have := arr_pending_lt _h; simp only [pending, Frame.pending]; omega
  · have := sizeOf_pos (Json.obj fields); omega
  · have := obj_pending_lt _h; simp only [pending, Frame.pending]; omega

/-- Give a folded value to the innermost frame, and go on to whatever that frame wants next. -/
def resume (a : Alg α) (v : α) (k : List (Frame α)) : α :=
  match k with
  | [] => v
  | .arr done rest :: k' =>
    match rest with
    | [] => resume a (a.arr (done.push v)) k'
    | j :: rest' => step a j (.arr (done.push v) rest' :: k')
  | .obj done name rest :: k' =>
    match rest with
    | [] => resume a (a.obj (done.push (name, v))) k'
    | (name', v') :: rest' => step a v' (.obj (done.push (name, v)) name' rest' :: k')
termination_by pending k
decreasing_by
  · simp only [pending, Frame.pending, pendingList]; omega
  · simp only [pending, Frame.pending, pendingList]; omega
  · simp only [pending, Frame.pending, pendingFields]; omega
  · simp only [pending, Frame.pending, pendingFields]; omega

end

/-- What the frames still owe a folded value, said by recursion. -/
private def close (a : Alg α) : α → List (Frame α) → α
  | v, [] => v
  | v, .arr done rest :: k => close a (a.arr (done.push v ++ (a.runList rest).toArray)) k
  | v, .obj done name rest :: k =>
    close a (a.obj (done.push (name, v) ++ (a.runFields rest).toArray)) k

private theorem machine (a : Alg α) : ∀ n : Nat,
    (∀ (j : Json) (k : List (Frame α)), sizeOf j + pending k ≤ n →
        step a j k = close a (run a j) k) ∧
      (∀ (v : α) (k : List (Frame α)), pending k ≤ n → resume a v k = close a v k) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have H1 : ∀ (j : Json) (k : List (Frame α)), sizeOf j + pending k < n →
        step a j k = close a (run a j) k :=
      fun j k h => (ih _ h).1 j k (Nat.le_refl _)
    have H2 : ∀ (v : α) (k : List (Frame α)), pending k < n → resume a v k = close a v k :=
      fun v k h => (ih _ h).2 v k (Nat.le_refl _)
    refine ⟨?_, ?_⟩
    · intro j k hn
      have hpos := sizeOf_pos j
      cases j with
      | null => rw [step, run]; exact H2 _ _ (by omega)
      | bool b => rw [step, run]; exact H2 _ _ (by omega)
      | num x => rw [step, run]; exact H2 _ _ (by omega)
      | str s => rw [step, run]; exact H2 _ _ (by omega)
      | arr elems =>
        rw [step]
        split
        · next hl => rw [run, hl]; simp only [runList]; exact H2 _ _ (by omega)
        · next j' rest hl =>
          have hlt := arr_pending_lt hl
          rw [H1 j' _ (by simp only [pending, Frame.pending]; omega), run, hl]
          simp [close, runList]
      | obj fields =>
        rw [step]
        split
        · next hl => rw [run, hl]; simp only [runFields]; exact H2 _ _ (by omega)
        · next name v rest hl =>
          have hlt := obj_pending_lt hl
          rw [H1 v _ (by simp only [pending, Frame.pending]; omega), run, hl]
          simp [close, runFields]
    · intro v k hn
      cases k with
      | nil => rw [resume, close]
      | cons f k' =>
        cases f with
        | arr done rest =>
          cases rest with
          | nil =>
            rw [resume, close]
            refine H2 _ _ ?_
            simp only [pending, Frame.pending, pendingList] at hn ⊢
            omega
          | cons j rest' =>
            rw [resume, H1 j _ (by simp only [pending, Frame.pending, pendingList] at hn ⊢; omega),
              close]
            simp [close, runList]
        | obj done name rest =>
          cases rest with
          | nil =>
            rw [resume, close]
            refine H2 _ _ ?_
            simp only [pending, Frame.pending, pendingFields] at hn ⊢
            omega
          | cons p rest' =>
            obtain ⟨name', v'⟩ := p
            rw [resume,
              H1 v' _ (by simp only [pending, Frame.pending, pendingFields] at hn ⊢; omega), close]
            simp [close, runFields]

/-- The traversal, with its pending work in a list rather than on the stack. -/
def fold (a : Alg α) (j : Json) : α := step a j []

/-- The two ways of applying an algebra agree, which is what makes one usable for the other. -/
theorem fold_eq_run (a : Alg α) (j : Json) : fold a j = run a j :=
  (machine a (sizeOf j + pending ([] : List (Frame α)))).1 j [] (Nat.le_refl _)

theorem runFields_names (a : Alg α) : ∀ l : List (String × Json),
    (runFields a l).map (·.1) = l.map (·.1)
  | [] => rfl
  | (k, v) :: rest => by simp [runFields, runFields_names a rest]

end Alg

/-! ## Equality by work list

Comparing two values walks both at once, so there is no part-built result to keep: a list of the
pairs still to compare is the whole state.
-/

noncomputable def weight : List (Json × Json) → Nat
  | [] => 0
  | (a, _) :: rest => sizeOf a + weight rest

/-- The values of two objects, paired up by position. -/
def valuePairs (x y : Array (String × Json)) : List (Json × Json) :=
  (x.toList.map Prod.snd).zip (y.toList.map Prod.snd)

private theorem weight_lt_cons (a b : Json) (rest : List (Json × Json)) :
    weight rest < weight ((a, b) :: rest) := by
  have := Alg.sizeOf_pos a
  simp only [weight]
  omega

private theorem weight_append : ∀ l₁ l₂ : List (Json × Json),
    weight (l₁ ++ l₂) = weight l₁ + weight l₂
  | [], _ => by simp [weight]
  | (a, b) :: rest, l₂ => by
    simp only [List.cons_append, weight, weight_append rest l₂]
    omega

private theorem weight_zip_lt : ∀ (xs ys : List Json), weight (xs.zip ys) < Alg.pendingList xs
  | [], _ => by simp [weight, Alg.pendingList]
  | _ :: _, [] => by simp [weight, Alg.pendingList]
  | x :: xs, y :: ys => by
    have := weight_zip_lt xs ys
    simp only [List.zip_cons_cons, weight, Alg.pendingList]
    omega

private theorem weight_zip_fields_lt : ∀ (xs ys : List (String × Json)),
    weight ((xs.map Prod.snd).zip (ys.map Prod.snd)) < Alg.pendingFields xs
  | [], _ => by simp [weight, Alg.pendingFields]
  | _ :: _, [] => by simp [weight, Alg.pendingFields]
  | (k, v) :: xs, (k', v') :: ys => by
    have := weight_zip_fields_lt xs ys
    simp only [List.map_cons, List.zip_cons_cons, weight, Alg.pendingFields]
    omega

private theorem weight_valuePairs_lt (x y : Array (String × Json)) :
    weight (valuePairs x y) < Alg.pendingFields x.toList :=
  weight_zip_fields_lt x.toList y.toList

private theorem pendingList_arr_lt (elems : Array Json) :
    Alg.pendingList elems.toList < sizeOf (Json.arr elems) := by
  have := Alg.pendingList_le elems.toList
  cases elems with
  | mk l => simp_all; omega

private theorem pendingFields_obj_lt (fields : Array (String × Json)) :
    Alg.pendingFields fields.toList < sizeOf (Json.obj fields) := by
  have := Alg.pendingFields_le fields.toList
  cases fields with
  | mk l => simp_all; omega

/-- Whether every pair in the list is equal, the members of a container joining the list. -/
def beqPairs : List (Json × Json) → Bool
  | [] => true
  | (a, b) :: rest =>
    match a, b with
    | .null, .null => beqPairs rest
    | .bool x, .bool y => x == y && beqPairs rest
    | .num x, .num y => x == y && beqPairs rest
    | .str x, .str y => x == y && beqPairs rest
    | .arr x, .arr y => x.size == y.size && beqPairs (x.toList.zip y.toList ++ rest)
    | .obj x, .obj y =>
      x.toList.map Prod.fst == y.toList.map Prod.fst && beqPairs (valuePairs x y ++ rest)
    | _, _ => false
termination_by l => weight l
decreasing_by
  all_goals
    first
      | exact weight_lt_cons _ _ _
      | (rw [weight_append]
         have := weight_zip_lt x.toList y.toList
         have := pendingList_arr_lt x
         simp only [weight]
         omega)
      | (rw [weight_append]
         have := weight_valuePairs_lt x y
         have := pendingFields_obj_lt x
         simp only [weight]
         omega)


end Json
