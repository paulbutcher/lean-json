/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Number
public import Std.Data.HashSet

public section

@[expose] section

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

end Json
