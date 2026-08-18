/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Fold
import Test.Runner

open Json
open Plausible (NamedBinder)

namespace Test.Query

private def sample : Json :=
  .obj #[("name", .str "a"),
         ("items", .arr #[.num 1, .obj #[("deep", .bool true)]]),
         ("empty", .obj #[])]

private def gets (name : String) (p : Path) (expected : Option Json) : TestCase :=
  { name := name
    run :=
      let got := sample.get? p
      if got == expected then pure ()
      else throw (IO.userError s!"got {repr got}") }

def lookup : Array TestCase := #[
  gets "the empty path is the value itself" [] (some sample),
  gets "a field" [.field "name"] (some (.str "a")),
  gets "an element" [.field "items", .index 0] (some (.num 1)),
  gets "a field of an element" [.field "items", .index 1, .field "deep"] (some (.bool true)),
  gets "a missing field" [.field "absent"] none,
  gets "an index past the end" [.field "items", .index 9] none,
  gets "a field of a number" [.field "name", .field "more"] none,
  gets "an index into an object" [.index 0] none,
  expect "has agrees with get?" (sample.has [.field "items", .index 0] &&
    !sample.has [.field "items", .index 2]),
  expect "getD falls back" (sample.getD [.field "absent"] (.num 7) == .num 7),
  -- Duplicate names resolve to the last, as everywhere else in the library.
  expect "a duplicate name resolves to the last"
    ((Json.obj #[("a", .num 1), ("a", .num 2)]).get? [.field "a"] == some (.num 2))
]

private def sets (name : String) (p : Path) (v : Json) (expected : String) : TestCase :=
  { name := name
    run :=
      match sample.set? p v with
      | .ok j => if compress j == expected then pure ()
                 else throw (IO.userError s!"got {compress j}")
      | .error e => throw (IO.userError s!"failed: {e}") }

private def setFails (name : String) (p : Path) : TestCase :=
  { name := name
    run :=
      match sample.set? p (.num 0) with
      | .ok j => throw (IO.userError s!"accepted, giving {compress j}")
      | .error _ => pure () }

def update : Array TestCase := #[
  sets "replaces a field in place" [.field "name"] (.num 1)
    "{\"name\":1,\"items\":[1,{\"deep\":true}],\"empty\":{}}",
  sets "replaces an element" [.field "items", .index 0] (.null)
    "{\"name\":\"a\",\"items\":[null,{\"deep\":true}],\"empty\":{}}",
  sets "replaces deep inside" [.field "items", .index 1, .field "deep"] (.num 2)
    "{\"name\":\"a\",\"items\":[1,{\"deep\":2}],\"empty\":{}}",
  -- A new name at the end of the path is added, since that is how an object gets built.
  sets "adds a field the object lacks" [.field "extra"] (.num 3)
    "{\"name\":\"a\",\"items\":[1,{\"deep\":true}],\"empty\":{},\"extra\":3}",
  sets "adds a field to a nested object" [.field "empty", .field "k"] (.num 4)
    "{\"name\":\"a\",\"items\":[1,{\"deep\":true}],\"empty\":{\"k\":4}}",
  -- Anything else missing along the way is refused rather than invented.
  setFails "will not invent an intermediate object" [.field "absent", .field "k"],
  setFails "will not grow an array" [.field "items", .index 5],
  setFails "will not index an object" [.index 0],
  setFails "will not name a field of an array" [.field "items", .field "k"],
  { name := "the whole value can be replaced"
    run :=
      match sample.set? [] (.num 1) with
      | .ok j => if j == .num 1 then pure () else throw (IO.userError "wrong value")
      | .error e => throw (IO.userError e) },
  { name := "modify? applies a function where the value is"
    run :=
      match sample.modify? [.field "items", .index 0] (fun _ => .str "x") with
      | .ok j => if j.get? [.field "items", .index 0] == some (.str "x") then pure ()
                 else throw (IO.userError s!"got {compress j}")
      | .error e => throw (IO.userError e) },
  { name := "modify? reports a path that is not there"
    run :=
      match sample.modify? [.field "absent"] id with
      | .ok _ => throw (IO.userError "accepted")
      | .error _ => pure () }
]

private def removes (name : String) (p : Path) (expected : String) : TestCase :=
  { name := name
    run :=
      match sample.remove? p with
      | .ok j => if compress j == expected then pure ()
                 else throw (IO.userError s!"got {compress j}")
      | .error e => throw (IO.userError s!"failed: {e}") }

def removal : Array TestCase := #[
  removes "a field" [.field "name"] "{\"items\":[1,{\"deep\":true}],\"empty\":{}}",
  removes "an element, closing the gap" [.field "items", .index 0]
    "{\"name\":\"a\",\"items\":[{\"deep\":true}],\"empty\":{}}",
  removes "a field deep inside" [.field "items", .index 1, .field "deep"]
    "{\"name\":\"a\",\"items\":[1,{}],\"empty\":{}}",
  { name := "the whole value cannot be removed"
    run :=
      match sample.remove? [] with
      | .ok _ => throw (IO.userError "accepted")
      | .error _ => pure () },
  { name := "an index past the end cannot be removed"
    run :=
      match sample.remove? [.field "items", .index 9] with
      | .ok _ => throw (IO.userError "accepted")
      | .error _ => pure () }
]

def typed : Array TestCase := #[
  { name := "getAs? decodes at a path"
    run :=
      match sample.getAs? String [.field "name"] with
      | .ok v => if v == "a" then pure () else throw (IO.userError s!"got {v}")
      | .error e => throw (IO.userError e) },
  { name := "getAs? reports the wrong type"
    run :=
      match sample.getAs? Nat [.field "name"] with
      | .ok _ => throw (IO.userError "accepted")
      | .error _ => pure () },
  { name := "setAs? encodes at a path"
    run :=
      match sample.setAs? [.field "name"] (5 : Nat) with
      | .ok j => if j.get? [.field "name"] == some (.num 5) then pure ()
                 else throw (IO.userError s!"got {compress j}")
      | .error e => throw (IO.userError e) }
]

/-! ## Properties

Paths are drawn from the ones `sample` actually has, so that the operations under test are
reached rather than refused. -/

private def paths : Array Path :=
  #[[], [.field "name"], [.field "items"], [.field "items", .index 0],
    [.field "items", .index 1], [.field "items", .index 1, .field "deep"], [.field "empty"]]

private def pathOf (n : Nat) : Path := (paths[n % paths.size]?).getD []

private def arrayLength? (j : Json) (p : Path) : Option Nat :=
  match j.get? p with
  | some (.arr elems) => some elems.size
  | _ => none

/--
What is removed is gone: a field simply disappears, while an element leaves the array one
shorter, those after it closing the gap rather than the index falling empty.
-/
abbrev removeThenMiss : Prop :=
  NamedBinder "n" <| ∀ n : Nat,
    (match sample.remove? (pathOf n), (pathOf n).getLast? with
      | .ok j, some (.field _) => !j.has (pathOf n)
      | .ok j, some (.index _) =>
        arrayLength? j (pathOf n).dropLast ==
          (arrayLength? sample (pathOf n).dropLast).map (· - 1)
      | .ok _, none => false
      | .error _, _ => (pathOf n).isEmpty) = true

/-! ## Laws

Two claims about a path, proved rather than sampled. Both come down, once the recursion over the
path is peeled away, to what a fold over an object's fields does, which `Test.Fold` says.
-/

open Test.Fold

/-- Whatever is put at a path is what is found there. -/
theorem get?_set? : ∀ (p : Path) (j v j' : Json), j.set? p v = .ok j' → j'.get? p = some v := by
  intro p
  induction p with
  | nil =>
    intro j v j' h
    replace h : v = j' := by injection h
    subst h
    rfl
  | cons s rest ih =>
    intro j v j' h
    cases s with
    | field k =>
      cases j with
      | obj fields =>
        unfold Json.set? at h
        cases hf : findLast? fields k with
        | none =>
          cases rest with
          | cons _ _ =>
            simp only [hf] at h
            replace h : (Except.error s!"no such field: {k}" : Except String Json) = .ok j' := h
            simp at h
          | nil =>
            simp only [hf] at h
            replace h : Json.obj (fields.push (k, v)) = j' := by injection h
            subst h
            rw [Json.get?, findLast?_push]
            simp [Json.get?]
        | some child =>
          simp only [hf] at h
          cases hc : child.set? rest v with
          | error e =>
            rw [hc] at h
            replace h : (Except.error e : Except String Json) = .ok j' := h
            simp at h
          | ok child' =>
            obtain ⟨i, hi⟩ := findLastIdx?_isSome hf
            rw [hc] at h
            replace h : (Json.obj fields).setObjVal? k child' = .ok j' := h
            rw [Json.setObjVal?] at h
            simp only [hi] at h
            replace h : Json.obj (fields.setIfInBounds i (k, child')) = j' := by injection h
            subst h
            rw [Json.get?, findLast?_setIfInBounds hi]
            simpa using ih child v child' hc
      | null | bool _ | num _ | str _ | arr _ => simp [Json.set?] at h
    | index i =>
      cases j with
      | arr elems =>
        unfold Json.set? at h
        cases he : elems[i]? with
        | none =>
          simp only [he] at h
          replace h : (Except.error s!"index out of bounds: {i}" : Except String Json) = .ok j' := h
          simp at h
        | some child =>
          simp only [he] at h
          cases hc : child.set? rest v with
          | error e =>
            rw [hc] at h
            replace h : (Except.error e : Except String Json) = .ok j' := h
            simp at h
          | ok child' =>
            rw [hc] at h
            replace h : Json.arr (elems.setIfInBounds i child') = j' := by injection h
            subst h
            have hlt : i < elems.size := (Array.getElem?_eq_some_iff.mp he).1
            rw [Json.get?, Array.getElem?_setIfInBounds]
            simp only [hlt, if_true]
            simpa using ih child v child' hc
      | null | bool _ | num _ | str _ | obj _ => simp [Json.set?] at h

/-- Putting back what is already at a path changes nothing. -/
theorem set?_get? : ∀ (p : Path) (j v : Json), j.get? p = some v → j.set? p v = .ok j := by
  intro p
  induction p with
  | nil =>
    intro j v h
    replace h : j = v := by injection h
    subst h
    rfl
  | cons s rest ih =>
    intro j v h
    cases s with
    | field k =>
      cases j with
      | obj fields =>
        rw [Json.get?] at h
        cases hf : findLast? fields k with
        | none => simp only [hf] at h; simp at h
        | some child =>
          simp only [hf] at h
          obtain ⟨i, hi⟩ := findLastIdx?_isSome hf
          unfold Json.set?
          simp only [hf]
          rw [ih child v h]
          show (Json.obj fields).setObjVal? k child = .ok (Json.obj fields)
          rw [Json.setObjVal?]
          simp only [hi, setIfInBounds_self hi hf]
      | null | bool _ | num _ | str _ | arr _ => simp [Json.get?] at h
    | index i =>
      cases j with
      | arr elems =>
        rw [Json.get?] at h
        cases he : elems[i]? with
        | none => simp only [he] at h; simp at h
        | some child =>
          simp only [he] at h
          obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp he
          unfold Json.set?
          simp only [he]
          rw [ih child v h]
          show Except.ok (Json.arr (elems.setIfInBounds i child)) = .ok (Json.arr elems)
          rw [← hget, setIfInBounds_getElem hlt]
      | null | bool _ | num _ | str _ | obj _ => simp [Json.get?] at h

def all : Array TestCase :=
  lookup ++ update ++ removal ++ typed ++ #[
    property "what is removed is gone" removeThenMiss
  ]

end Test.Query
