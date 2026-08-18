/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Array
public import Json.Number
public import Std.Data.HashSet

public section

@[expose] section

/-!
The data model, and what can be done with it alone.

An object holds its fields in the order they were written and can hold one name twice, so that a
parsed value is a faithful image of its text. Lookup takes the last of a repeated name, as
ECMA-262 and the mainstream implementations do. Equality and hashing are structural, which is
safe here because `Json.Number` keeps one spelling of each number.

Nothing here panics: an accessor returns `Except String`, or a default where the name says so.
`beq`, `hash`, `uniqueKeys` and `depth` recurse on the stack rather than on the heap, which is
safe for anything `parse` produced under the default depth limit, and worth remembering for a
value built by hand or read with `maxDepth := none`.
-/

/--
A JSON value.

Object fields keep the order they appeared in, and duplicate names are representable, so a parsed
value is a faithful image of its text. Lookup resolves duplicates by taking the last, matching
ECMA-262 and the mainstream implementations.
-/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Json.Number)
  | str (s : String)
  | arr (elems : Array Json)
  | obj (fields : Array (String × Json))
deriving Inhabited, Repr

namespace Json

-- Equality, hashing and the key check all recurse through the two nested `Array` positions, for
-- which no deriving handler applies. Splitting each into a mutual group over `List` keeps the
-- termination argument and the correctness proof straightforward.
mutual

def beq : Json → Json → Bool
  | null, null => true
  | bool a, bool b => a == b
  | num a, num b => a == b
  | str a, str b => a == b
  | arr a, arr b => beqList a.toList b.toList
  | obj a, obj b => beqFields a.toList b.toList
  | _, _ => false

def beqList : List Json → List Json → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false

def beqFields : List (String × Json) → List (String × Json) → Bool
  | [], [] => true
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys => k₁ == k₂ && beq v₁ v₂ && beqFields xs ys
  | _, _ => false

end

mutual

theorem beq_iff_eq : ∀ a b : Json, beq a b = true ↔ a = b
  | null, null => by simp [beq]
  | bool _, bool _ => by simp [beq]
  | num _, num _ => by simp [beq]
  | str _, str _ => by simp [beq]
  | arr x, arr y => by simp [beq, beqList_iff_eq x.toList y.toList, Array.toList_inj]
  | obj x, obj y => by simp [beq, beqFields_iff_eq x.toList y.toList, Array.toList_inj]
  | null, bool _ | null, num _ | null, str _ | null, arr _ | null, obj _
  | bool _, null | bool _, num _ | bool _, str _ | bool _, arr _ | bool _, obj _
  | num _, null | num _, bool _ | num _, str _ | num _, arr _ | num _, obj _
  | str _, null | str _, bool _ | str _, num _ | str _, arr _ | str _, obj _
  | arr _, null | arr _, bool _ | arr _, num _ | arr _, str _ | arr _, obj _
  | obj _, null | obj _, bool _ | obj _, num _ | obj _, str _ | obj _, arr _ => by simp [beq]

theorem beqList_iff_eq : ∀ xs ys : List Json, beqList xs ys = true ↔ xs = ys
  | [], [] => by simp [beqList]
  | x :: xs, y :: ys => by simp [beqList, beq_iff_eq x y, beqList_iff_eq xs ys]
  | [], _ :: _ => by simp [beqList]
  | _ :: _, [] => by simp [beqList]

theorem beqFields_iff_eq : ∀ xs ys : List (String × Json), beqFields xs ys = true ↔ xs = ys
  | [], [] => by simp [beqFields]
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys => by
    simp [beqFields, beq_iff_eq v₁ v₂, beqFields_iff_eq xs ys, and_assoc]
  | [], _ :: _ => by simp [beqFields]
  | _ :: _, [] => by simp [beqFields]

end

instance : DecidableEq Json := fun a b => decidable_of_iff _ (beq_iff_eq a b)

instance : BEq Json := ⟨beq⟩

instance : LawfulBEq Json where
  eq_of_beq h := (beq_iff_eq _ _).mp h
  rfl := (beq_iff_eq _ _).mpr rfl

mutual

def hash : Json → UInt64
  | null => 11
  | bool b => mixHash 13 (Hashable.hash b)
  | num n => mixHash 17 (Hashable.hash n)
  | str s => mixHash 19 (Hashable.hash s)
  | arr elems => mixHash 23 (hashList elems.toList)
  | obj fields => mixHash 29 (hashFields fields.toList)

def hashList : List Json → UInt64
  | [] => 7
  | j :: rest => mixHash (hash j) (hashList rest)

def hashFields : List (String × Json) → UInt64
  | [] => 7
  | (k, v) :: rest => mixHash (mixHash (Hashable.hash k) (hash v)) (hashFields rest)

end

instance : Hashable Json := ⟨hash⟩

instance : Coe Bool Json := ⟨bool⟩
instance : Coe String Json := ⟨str⟩
instance : Coe Number Json := ⟨num⟩
instance : OfNat Json n := ⟨num (Number.ofNat n)⟩

def ofInt (i : Int) : Json := num (Number.ofInt i)

def ofNat (n : Nat) : Json := num (Number.ofNat n)

def mkObj (fields : List (String × Json)) : Json := obj fields.toArray

def isNull : Json → Bool
  | null => true
  | _ => false

-- The field helpers are polymorphic in the value type. Nothing about resolving duplicate names
-- depends on the values, and it lets them be tested at a type that has generators.

/-- The value of the last field named `k`, which is the one lookup resolves to. -/
def findLast? (fields : Array (String × α)) (k : String) : Option α :=
  fields.foldl (init := none) fun found (key, v) => if key == k then some v else found

/-- The position of the last field named `k`. -/
def findLastIdx? (fields : Array (String × α)) (k : String) : Option Nat :=
  (fields.foldl (init := ((none : Option Nat), 0)) fun (found, i) (key, _) =>
    (if key == k then some i else found, i + 1)).1

/--
Keeps one field per name, the last value at the first position that name occupied, so that
lookup is unaffected and field order is preserved as far as it can be.
-/
def dedupKeys (fields : Array (String × α)) : Array (String × α) :=
  fields.foldl (init := #[]) fun acc (k, v) =>
    match findLastIdx? acc k with
    | some i => acc.setIfInBounds i (k, v)
    | none => acc.push (k, v)

/-- Whether the field names of one object are pairwise distinct. -/
def distinctNames (fields : Array (String × α)) : Bool :=
  go 0 ∅
where
  go (i : Nat) (seen : Std.HashSet String) : Bool :=
    if h : i < fields.size then
      let k := fields[i].1
      if seen.contains k then false else go (i + 1) (seen.insert k)
    else
      true

mutual

/-- No object anywhere in the value has a repeated field name. -/
def uniqueKeys : Json → Bool
  | arr elems => uniqueKeysList elems.toList
  | obj fields => distinctNames fields && uniqueKeysFields fields.toList
  | _ => true

def uniqueKeysList : List Json → Bool
  | [] => true
  | j :: rest => uniqueKeys j && uniqueKeysList rest

def uniqueKeysFields : List (String × Json) → Bool
  | [] => true
  | (_, v) :: rest => uniqueKeys v && uniqueKeysFields rest

end

/-- `uniqueKeys` as a proposition, decidable by construction. -/
abbrev UniqueKeys (j : Json) : Prop := uniqueKeys j = true

mutual

/-- Every number in the value is in canonical form, which is what the parser guarantees. -/
def canonicalNumbers : Json → Bool
  | num n => decide n.Canonical
  | arr elems => canonicalNumbersList elems.toList
  | obj fields => canonicalNumbersFields fields.toList
  | _ => true

def canonicalNumbersList : List Json → Bool
  | [] => true
  | j :: rest => canonicalNumbers j && canonicalNumbersList rest

def canonicalNumbersFields : List (String × Json) → Bool
  | [] => true
  | (_, v) :: rest => canonicalNumbers v && canonicalNumbersFields rest

end

abbrev CanonicalNumbers (j : Json) : Prop := canonicalNumbers j = true

mutual

/--
How deeply the value nests: zero for a scalar, and one more than its deepest member for a
container. An empty container is one, entering it being what costs.
-/
def depth : Json → Nat
  | arr elems => depthList elems.toList + 1
  | obj fields => depthFields fields.toList + 1
  | _ => 0

def depthList : List Json → Nat
  | [] => 0
  | j :: rest => max (depth j) (depthList rest)

def depthFields : List (String × Json) → Nat
  | [] => 0
  | (_, v) :: rest => max (depth v) (depthFields rest)

end

/--
Every member of a container is strictly shallower than the container itself, which is what makes
a recursion over a value that spends one unit of depth per level terminate.
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

/-! ## Accessors

Each reads one thing and says in `Except String` why it could not, so that a wrong shape is a
value to handle rather than a panic. Where an object names a field twice, the last one wins.
-/

def getBool? : Json → Except String Bool
  | bool b => .ok b
  | _ => .error "expected a boolean"

def getNum? : Json → Except String Number
  | num n => .ok n
  | _ => .error "expected a number"

def getStr? : Json → Except String String
  | str s => .ok s
  | _ => .error "expected a string"

def getArr? : Json → Except String (Array Json)
  | arr elems => .ok elems
  | _ => .error "expected an array"

def getObj? : Json → Except String (Array (String × Json))
  | obj fields => .ok fields
  | _ => .error "expected an object"

def getInt? : Json → Except String Int
  | num n =>
    match n.toInt? with
    | some i => .ok i
    | none => .error "number is not an integer of a workable size"
  | _ => .error "expected a number"

def getNat? : Json → Except String Nat
  | num n =>
    match n.toNat? with
    | some i => .ok i
    | none => .error "number is not a natural number of a workable size"
  | _ => .error "expected a number"

def getObjVal? : Json → String → Except String Json
  | obj fields, k =>
    match findLast? fields k with
    | some v => .ok v
    | none => .error s!"no such field: {k}"
  | _, _ => .error "expected an object"

def getArrVal? : Json → Nat → Except String Json
  | arr elems, i =>
    match elems[i]? with
    | some v => .ok v
    | none => .error s!"index out of bounds: {i}"
  | _, _ => .error "expected an array"

def getObjValD (j : Json) (k : String) : Json :=
  (j.getObjVal? k).toOption.getD null

/-- Replaces the last field named `k`, or appends one, leaving other fields where they are. -/
def setObjVal? : Json → String → Json → Except String Json
  | obj fields, k, v =>
    match findLastIdx? fields k with
    | some i => .ok (obj (fields.setIfInBounds i (k, v)))
    | none => .ok (obj (fields.push (k, v)))
  | _, _, _ => .error "expected an object"

/-- `{...a, ...b}`, with `b`'s fields winning. Yields `b` when `a` is not an object. -/
def mergeObj : Json → Json → Json
  | obj a, obj b => obj (dedupKeys (a ++ b))
  | _, b => b

/-! ## Field arrays, one `push` at a time

`findLast?`, `findLastIdx?` and `dedupKeys` are each a left fold over the field array, so a claim
about any of them is a claim about what a fold accumulates, and `Array.pushInduction` is the
induction that fits: each fold has a single lemma saying what pushing a field does to it, and the
rest follows from those. `distinctNames` is a loop rather than a fold, so it is first related to
`Nodup` and then given a lemma of the same shape.
-/

/-- The names an object gives its fields, in the order they appear. -/
def fieldNames (a : Array (String × α)) : List String := a.toList.map (·.1)

@[simp] theorem fieldNames_push (a : Array (String × α)) (x : String × α) :
    fieldNames (a.push x) = fieldNames a ++ [x.1] := by simp [fieldNames]

private theorem fieldNames_length (a : Array (String × α)) : (fieldNames a).length = a.size := by
  simp [fieldNames]

theorem findLast?_push (a : Array (String × α)) (key : String) (v : α) (k : String) :
    findLast? (a.push (key, v)) k = if key == k then some v else findLast? a k := by
  simp [findLast?]

private theorem findLastIdxCount (a : Array (String × α)) (k : String) :
    (a.foldl (init := ((none : Option Nat), 0)) (fun (found, i) (key, _) =>
      (if key == k then some i else found, i + 1))).2 = a.size := by
  induction a using Array.pushInduction with
  | empty => rfl
  | push a x ih => rw [Array.foldl_push]; simpa using ih

theorem findLastIdx?_push (a : Array (String × α)) (key : String) (v : α) (k : String) :
    findLastIdx? (a.push (key, v)) k = if key == k then some a.size else findLastIdx? a k := by
  have h := findLastIdxCount a k
  simp only [findLastIdx?, Array.foldl_push] at *
  split <;> simp_all

theorem findLast?_eq_none_iff (a : Array (String × α)) (k : String) :
    findLast? a k = none ↔ k ∉ fieldNames a := by
  induction a using Array.pushInduction with
  | empty => simp [findLast?, fieldNames]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    by_cases h : key = k
    · subst h; simp [findLast?_push]
    · simp [findLast?_push, h, ih, Ne.symm h]

theorem findLastIdx?_eq_none_iff (a : Array (String × α)) (k : String) :
    findLastIdx? a k = none ↔ k ∉ fieldNames a := by
  induction a using Array.pushInduction with
  | empty => simp [findLastIdx?, fieldNames]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    by_cases h : key = k
    · subst h; simp [findLastIdx?_push]
    · simp [findLastIdx?_push, h, ih, Ne.symm h]

theorem findLastIdx?_eq_some {a : Array (String × α)} {k : String} {i : Nat}
    (h : findLastIdx? a k = some i) :
    ∃ hi : i < a.size, a[i].1 = k ∧ findLast? a k = some a[i].2 := by
  induction a using Array.pushInduction with
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

/--
Replacing the last field named `k` is what lookup sees: that name yields the new value, and
every other name is unaffected.
-/
theorem findLast?_setIfInBounds {a : Array (String × α)} {k k' : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) :
    findLast? (a.setIfInBounds i (k, v)) k' = if k == k' then some v else findLast? a k' := by
  induction a using Array.pushInduction with
  | empty => simp [findLastIdx?] at h
  | push a x ih =>
    obtain ⟨key, w⟩ := x
    rw [findLastIdx?_push] at h
    by_cases hk : key = k
    · subst hk
      simp at h
      subst h
      rw [Array.setIfInBounds_push_size, findLast?_push, findLast?_push]
      by_cases hk' : key = k' <;> simp [hk']
    · simp [hk] at h
      rw [Array.setIfInBounds_push_lt (findLastIdx?_lt h), findLast?_push, findLast?_push, ih h]
      by_cases hk' : key = k' <;> by_cases hkk' : k = k' <;> simp_all

/-- Putting a field back where it already was, unchanged. -/
theorem setIfInBounds_self {a : Array (String × α)} {k : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) (hv : findLast? a k = some v) :
    a.setIfInBounds i (k, v) = a := by
  obtain ⟨hi, hkey, hval⟩ := findLastIdx?_eq_some h
  rw [hv] at hval
  have hfield : (k, v) = a[i] := Prod.ext hkey.symm (Option.some.inj hval)
  rw [hfield, Array.setIfInBounds_getElem hi]

private theorem fieldNames_drop (a : Array (String × α)) {i : Nat} (h : i < a.size) :
    (fieldNames a).drop i = a[i].1 :: (fieldNames a).drop (i + 1) := by
  have hi : i < (fieldNames a).length := by simpa [fieldNames_length] using h
  rw [List.drop_eq_getElem_cons hi]
  simp [fieldNames]

private theorem distinctNamesGo (a : Array (String × α)) (i : Nat) (seen : Std.HashSet String) :
    distinctNames.go a i seen = true ↔
      ((fieldNames a).drop i).Nodup ∧ ∀ x ∈ (fieldNames a).drop i, seen.contains x = false := by
  induction i, seen using distinctNames.go.induct (fields := a) with
  | case1 i seen h k hc =>
    rw [distinctNames.go, dif_pos h, if_pos hc, fieldNames_drop a h]
    have hmem : a[i].1 ∈ seen := by simpa using hc
    simp [hmem]
  | case2 i seen h k hc ih =>
    rw [distinctNames.go, dif_pos h, if_neg hc, ih, fieldNames_drop a h]
    simp only [Std.HashSet.contains_insert]
    grind
  | case3 i seen h =>
    have hnil : (fieldNames a).drop i = [] := by
      apply List.drop_eq_nil_of_le
      rw [fieldNames_length]
      omega
    rw [distinctNames.go, dif_neg h]
    simp [hnil]

theorem distinctNames_iff (a : Array (String × α)) :
    distinctNames a = true ↔ (fieldNames a).Nodup := by
  rw [distinctNames, distinctNamesGo]
  simp

theorem distinctNames_push (a : Array (String × α)) (x : String × α) :
    distinctNames (a.push x) = true ↔ distinctNames a = true ∧ findLast? a x.1 = none := by
  rw [distinctNames_iff, distinctNames_iff, findLast?_eq_none_iff, fieldNames_push]
  simp only [List.nodup_append]
  grind

theorem fieldNames_setIfInBounds {a : Array (String × α)} {k : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) : fieldNames (a.setIfInBounds i (k, v)) = fieldNames a := by
  obtain ⟨hi, hkey, _⟩ := findLastIdx?_eq_some h
  have hi' : i < (fieldNames a).length := by rw [fieldNames_length]; exact hi
  have hget : (fieldNames a)[i]'hi' = k := by simp [fieldNames, hkey]
  have hset : fieldNames (a.setIfInBounds i (k, v)) = (fieldNames a).set i k := by
    simp [fieldNames, Array.toList_setIfInBounds, List.map_set]
  rw [hset, ← hget, List.set_getElem_self]

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
  induction a using Array.pushInduction with
  | empty => rfl
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    rw [findLast?_push]
    cases h : findLastIdx? (dedupKeys a) key with
    | none => rw [dedupKeys_push_none h, findLast?_push, ih]
    | some i => rw [dedupKeys_push_some h, findLast?_setIfInBounds h, ih]

theorem distinctNames_dedupKeys (a : Array (String × α)) : distinctNames (dedupKeys a) = true := by
  induction a using Array.pushInduction with
  | empty => rw [distinctNames_iff]; simp [dedupKeys, fieldNames]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    cases h : findLastIdx? (dedupKeys a) key with
    | none =>
      rw [dedupKeys_push_none h, distinctNames_push]
      exact ⟨ih, (findLast?_eq_none_iff _ _).2 ((findLastIdx?_eq_none_iff _ _).1 h)⟩
    | some i =>
      rw [dedupKeys_push_some h, distinctNames_iff, fieldNames_setIfInBounds h,
        ← distinctNames_iff]
      exact ih

/-- An object that repeats no name is left alone. -/
theorem dedupKeys_eq_self :
    ∀ a : Array (String × α), distinctNames a = true → dedupKeys a = a := by
  intro a
  induction a using Array.pushInduction with
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

end Json
