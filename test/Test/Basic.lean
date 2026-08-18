/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json

open Json

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

/-! ## Depth -/

example : depth .null = 0 := by simp [depth]

example : depth (.arr #[]) = 1 := by simp [depth, depthList]

example : depth (.obj #[("a", .arr #[.num 1])]) = 2 := by
  simp [depth, depthList, depthFields]

end Test.Basic
