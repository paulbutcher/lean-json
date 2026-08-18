/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Basic
public import Std.Data.TreeMap

public section

namespace Json

@[expose] section

universe u v

/-- Types that can be encoded as JSON. -/
class ToJson (α : Type u) where
  toJson : α → Json

/-- Types that can be decoded from JSON. -/
class FromJson (α : Type u) where
  fromJson? : Json → Except String α

export ToJson (toJson)
export FromJson (fromJson?)

/-! ## Values that carry structure -/

/-- The two shapes a codec can descend into. -/
inductive Structured where
  | arr (elems : Array Json)
  | obj (fields : Array (String × Json))
deriving Inhabited, Repr, BEq

def Structured.toJson : Structured → Json
  | .arr elems => .arr elems
  | .obj fields => .obj fields

def Structured.fromJson? : Json → Except String Structured
  | .arr elems => .ok (.arr elems)
  | .obj fields => .ok (.obj fields)
  | _ => .error "expected an array or an object"

instance : ToJson Structured := ⟨Structured.toJson⟩
instance : FromJson Structured := ⟨Structured.fromJson?⟩

/-! ## Instances -/

instance : ToJson Json := ⟨id⟩
instance : FromJson Json := ⟨Except.ok⟩

instance : ToJson Number := ⟨num⟩
instance : FromJson Number := ⟨getNum?⟩

instance : ToJson Bool := ⟨bool⟩
instance : FromJson Bool := ⟨getBool?⟩

instance : ToJson String := ⟨str⟩
instance : FromJson String := ⟨getStr?⟩

instance : ToJson Nat := ⟨fun n => num (Number.ofNat n)⟩
instance : FromJson Nat := ⟨getNat?⟩

instance : ToJson Int := ⟨fun i => num (Number.ofInt i)⟩
instance : FromJson Int := ⟨getInt?⟩

instance : ToJson Unit := ⟨fun _ => obj #[]⟩
instance : FromJson Unit := ⟨fun j =>
  match j with
  | obj #[] => .ok ()
  | _ => .error "expected an empty object"⟩

instance : ToJson Empty := ⟨nofun⟩
instance : FromJson Empty := ⟨fun _ => .error "Empty has no values to decode into"⟩

instance : ToJson String.Slice := ⟨fun s => str s.copy⟩
instance : FromJson String.Slice := ⟨fun j => String.toSlice <$> getStr? j⟩

instance : ToJson System.FilePath := ⟨fun p => str p.toString⟩
instance : FromJson System.FilePath := ⟨fun j => System.FilePath.mk <$> getStr? j⟩

def arrayToJson [ToJson α] (a : Array α) : Json := arr (a.map toJson)

def arrayFromJson? [FromJson α] : Json → Except String (Array α)
  | arr elems => elems.mapM fromJson?
  | _ => .error "expected an array"

instance [ToJson α] : ToJson (Array α) := ⟨arrayToJson⟩
instance [FromJson α] : FromJson (Array α) := ⟨arrayFromJson?⟩

instance [ToJson α] : ToJson (List α) := ⟨fun l => arrayToJson l.toArray⟩
instance [FromJson α] : FromJson (List α) := ⟨fun j => Array.toList <$> arrayFromJson? j⟩

/--
`none` is `null`, and `some a` is whatever `a` is. As in every library that makes this choice,
`Option (Option α)` therefore does not round trip, `none` and `some none` sharing an encoding.
-/
def optionToJson [ToJson α] : Option α → Json
  | none => null
  | some a => toJson a

def optionFromJson? [FromJson α] : Json → Except String (Option α)
  | null => .ok none
  | j => some <$> fromJson? j

instance [ToJson α] : ToJson (Option α) := ⟨optionToJson⟩
instance [FromJson α] : FromJson (Option α) := ⟨optionFromJson?⟩

instance [ToJson α] [ToJson β] : ToJson (α × β) :=
  ⟨fun (a, b) => arr #[toJson a, toJson b]⟩

-- Matching a list rather than an array literal, so that the equation lemmas a proof needs are
-- generated: `#[ja, jb]` as a pattern defeats them.
def prodFromJson? {α : Type u} {β : Type v} [FromJson α] [FromJson β] :
    Json → Except String (α × β)
  | arr elems =>
    match elems.toList with
    | [ja, jb] => do
      let ⟨a⟩ : ULift.{v} α := ← (fromJson? ja).map ULift.up
      let ⟨b⟩ : ULift.{u} β := ← (fromJson? jb).map ULift.up
      return (a, b)
    | _ => .error "expected an array of two elements"
  | _ => .error "expected an array of two elements"

instance {α : Type u} {β : Type v} [FromJson α] [FromJson β] : FromJson (α × β) :=
  ⟨prodFromJson?⟩

/--
A natural number written as a decimal string rather than as a JSON number.

`USize` and `UInt64` are encoded this way, following the same reasoning as every other library
that talks to JavaScript: JSON numbers have no range limit, but a JavaScript `Number` holds
integers exactly only up to `2 ^ 53 - 1`, so a value near the top of a 64-bit range would not
survive the trip.
-/
def bignumToJson (n : Nat) : Json := str (toString n)

/-- A decimal numeral of at most `maxDigits` digits, refusing anything longer unread. -/
def decodeNat? (s : String) (maxDigits : Nat := 1000) : Option Nat :=
  if s.isEmpty || maxDigits < s.length then
    none
  else
    s.foldl (init := some 0) fun acc c =>
      match acc with
      | none => none
      | some v => if '0' ≤ c && c ≤ '9' then some (v * 10 + (c.toNat - '0'.toNat)) else none

def bignumFromJson? (j : Json) (maxDigits : Nat := 1000) : Except String Nat := do
  let s ← getStr? j
  match decodeNat? s maxDigits with
  | some v => .ok v
  | none => .error "expected a string holding a decimal numeral"

instance : ToJson USize := ⟨fun v => bignumToJson v.toNat⟩
instance : FromJson USize := ⟨fun j => do
  let n ← bignumFromJson? j
  if h : n < USize.size then .ok (USize.ofNatLT n h) else .error "value is too large for USize"⟩

instance : ToJson UInt64 := ⟨fun v => bignumToJson v.toNat⟩
instance : FromJson UInt64 := ⟨fun j => do
  let n ← bignumFromJson? j
  if h : n < UInt64.size then .ok (UInt64.ofNatLT n h) else .error "value is too large for UInt64"⟩

/--
A finite `Float` is a number, exactly; the three values IEEE 754 has and JSON does not are the
strings `"NaN"`, `"Infinity"` and `"-Infinity"`, which is the encoding the other implementations
use.
-/
def floatToJson (x : Float) : Json :=
  match Number.ofFloat? x with
  | some n => num n
  | none => str (if x.isNaN then "NaN" else if x < 0.0 then "-Infinity" else "Infinity")

def floatFromJson? : Json → Except String Float
  | num n => .ok n.toFloat
  | str "NaN" => .ok (0.0 / 0.0)
  | str "Infinity" => .ok (1.0 / 0.0)
  | str "-Infinity" => .ok (-1.0 / 0.0)
  | _ => .error "expected a number, or \"NaN\", \"Infinity\" or \"-Infinity\""

instance : ToJson Float := ⟨floatToJson⟩
instance : FromJson Float := ⟨floatFromJson?⟩

instance {cmp} [ToJson α] : ToJson (Std.TreeMap String α cmp) :=
  ⟨fun m => obj (m.foldl (init := #[]) fun acc k v => acc.push (k, toJson v))⟩

instance {cmp} [FromJson α] : FromJson (Std.TreeMap String α cmp) := ⟨fun j => do
  let fields ← getObj? j
  fields.foldlM (init := ∅) fun m (k, v) => return m.insert k (← fromJson? v)⟩

/-! ## Helpers -/

def toStructured? [ToJson α] (v : α) : Except String Structured := fromJson? (toJson v)

/-- The field named `k`, decoded. A missing field decodes `null`, which an `Option` accepts. -/
def getObjValAs? (j : Json) (α : Type u) [FromJson α] (k : String) : Except String α :=
  fromJson? (j.getObjValD k)

def setObjValAs? (j : Json) {α : Type u} [ToJson α] (k : String) (v : α) : Except String Json :=
  j.setObjVal? k (toJson v)

/-- A field to include only when it has a value, for building objects out of optional parts. -/
def opt [ToJson α] (k : String) : Option α → List (String × Json)
  | none => []
  | some v => [(k, toJson v)]

/-- The string value, or the single field name, if there is exactly one. -/
def getTag? : Json → Option String
  | str tag => some tag
  | obj fields => if fields.size == 1 then fields[0]?.map Prod.fst else none
  | _ => none

/--
The fields of an encoded constructor whose tag is already known, which is what a derived
decoder needs once it has dispatched on the tag.
-/
def parseCtorFields (j : Json) (tag : String) (nFields : Nat)
    (fieldNames? : Option (Array String)) : Except String (Array Json) := do
  let payload ← j.getObjVal? tag
  match fieldNames? with
  | some names => names.mapM payload.getObjVal?
  | none =>
    if nFields == 1 then
      .ok #[payload]
    else
      let fields ← payload.getArr?
      if fields.size == nFields then .ok fields
      else .error s!"expected {nFields} fields, got {fields.size}"

/-- As `parseCtorFields`, but also handling a constructor with no arguments, encoded as its name. -/
def parseTagged (j : Json) (tag : String) (nFields : Nat)
    (fieldNames? : Option (Array String)) : Except String (Array Json) :=
  if nFields == 0 then do
    let s ← j.getStr?
    if s == tag then .ok #[] else .error s!"expected the tag {tag}, got {s}"
  else
    parseCtorFields j tag nFields fieldNames?

end

end Json
