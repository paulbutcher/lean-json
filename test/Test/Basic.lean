/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json
open Plausible (NamedBinder)

namespace Test.Basic

attribute [local simp] beq beqList beqFields findLast? findLastIdx? dedupKeys distinctNames
  distinctNames.go uniqueKeys uniqueKeysList uniqueKeysFields getObjVal? getArrVal? setObjVal?
  mergeObj Number.normalize Number.normalizeAux Except.toOption

example : LawfulBEq Json := inferInstance

-- Equality reaches through both nested positions, and distinguishes field order.
example : (Json.arr #[.num 1, .str "a"] == Json.arr #[.num 1, .str "a"]) = true := by simp

example : (Json.arr #[.num 1] == Json.arr #[.num 1, .num 1]) = false := by simp

example : (Json.obj #[("a", .null)] == Json.obj #[("a", .null)]) = true := by simp

example : (Json.obj #[("a", .null), ("b", .null)] == Json.obj #[("b", .null), ("a", .null)])
    = false := by simp

-- Numbers inside a value compare by value, since `Number` is canonical.
example : (Json.num (Number.normalize 150 (-2)) == Json.num ⟨15, -1⟩) = true := by simp

-- Duplicate names survive parsing into the value, and lookup takes the last.
example : getObjVal? (.obj #[("a", .num 1), ("a", .num 2)]) "a" = .ok (.num 2) := by simp

example : (getObjVal? (.obj #[("a", .num 1)]) "b").toOption = none := by simp

example : (getObjVal? (.num 1) "a").toOption = none := by simp

example : (getArrVal? (.arr #[.null]) 1).toOption = none := by simp

-- Replacing a field leaves the others in place, and adds one when the name is absent.
example : setObjVal? (.obj #[("a", .num 1), ("b", .num 2)]) "a" .null
    = .ok (.obj #[("a", .null), ("b", .num 2)]) := by simp

example : setObjVal? (.obj #[("a", .num 1)]) "b" .null
    = .ok (.obj #[("a", .num 1), ("b", .null)]) := by simp

-- Deduplication keeps the last value at the first position the name held.
example : dedupKeys #[("a", 1), ("b", 2), ("a", 3)] = #[("a", 3), ("b", 2)] := by simp

example : distinctNames #[("a", 1), ("a", 2)] = false := by simp

example : uniqueKeys (.obj #[("a", .num 1), ("a", .num 2)]) = false := by simp

-- The check is recursive: a repeat nested inside an array still fails it.
example : uniqueKeys (.arr #[.obj #[("a", .null), ("a", .null)]]) = false := by simp

example : uniqueKeys (.arr #[.obj #[("a", .null)], .obj #[("a", .null)]]) = true := by simp

example : mergeObj (.obj #[("a", .num 1), ("b", .num 2)]) (.obj #[("a", .num 3)])
    = .obj #[("a", .num 3), ("b", .num 2)] := by simp
/-! ## Depth

A derived decoder is handed the depth of the value it is to read, and spends one of it per
level. What makes that enough is that every member is strictly shallower than the container it
came out of, which is what these say.
-/

theorem depth_le_depthList {j : Json} : ∀ {l : List Json}, j ∈ l → depth j ≤ depthList l
  | _ :: _, .head _ => by simp [depthList, Nat.le_max_left]
  | _ :: rest, .tail _ h => by
    have := depth_le_depthList (l := rest) h
    simp only [depthList]
    omega

theorem depth_le_depthFields {k : String} {v : Json} :
    ∀ {l : List (String × Json)}, (k, v) ∈ l → depth v ≤ depthFields l
  | _ :: _, .head _ => by simp [depthFields, Nat.le_max_left]
  | _ :: rest, .tail _ h => by
    have := depth_le_depthFields (l := rest) h
    simp only [depthFields]
    omega

theorem depth_arr_lt {j : Json} {elems : Array Json} (h : j ∈ elems) :
    depth j < depth (.arr elems) := by
  have hmem : j ∈ elems.toList := by simpa using h
  have := depth_le_depthList hmem
  simp only [depth]
  omega

theorem depth_obj_lt {k : String} {v : Json} {fields : Array (String × Json)}
    (h : (k, v) ∈ fields) : depth v < depth (.obj fields) := by
  have hmem : (k, v) ∈ fields.toList := by simpa using h
  have := depth_le_depthFields hmem
  simp only [depth]
  omega

example : depth .null = 0 := by simp [depth]

example : depth (.arr #[]) = 1 := by simp [depth, depthList]

example : depth (.obj #[("a", .arr #[.num 1])]) = 2 := by
  simp [depth, depthList, depthFields]

/--
Deduplication leaves every lookup unchanged. Stated at `Nat` values, where generators exist;
nothing in the field helpers depends on the value type.

This is a property rather than a theorem because the fold that implements `dedupKeys` needs a
characterisation of `findLast?` over `Array.foldl` before either claim can be proved, and there
is no such lemma library to build on yet.
-/
abbrev dedupPreservesLookup : Prop :=
  NamedBinder "fields" <| ∀ fields : Array (String × Nat), NamedBinder "k" <| ∀ k : String,
    findLast? (dedupKeys fields) k = findLast? fields k

abbrev dedupGivesDistinctNames : Prop :=
  NamedBinder "fields" <| ∀ fields : Array (String × Nat),
    distinctNames (dedupKeys fields) = true

abbrev dedupIsIdempotent : Prop :=
  NamedBinder "fields" <| ∀ fields : Array (String × Nat),
    dedupKeys (dedupKeys fields) = dedupKeys fields

def all : Array TestCase := #[
  property "dedupKeys preserves every lookup" dedupPreservesLookup,
  property "dedupKeys yields distinct names" dedupGivesDistinctNames,
  property "dedupKeys is idempotent" dedupIsIdempotent
]

end Test.Basic
