/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.FromTo

public section

namespace Json

@[expose] section

/-!
Reaching into a value along a path.

Every operation here recurses along the path rather than through the value, so what it costs is
the length of the path, and a deeply nested document is no more dangerous than a flat one.

`set?` adds a field named by the last step of a path, since that is how an object gets built up,
but refuses a missing intermediate rather than inventing one: guessing whether a gap should
become an object or an array is how a typo turns into a new field. `remove?` closes the gap it
leaves in an array, so the index removed is occupied again by its successor.
-/

/-- One step into a value: a field of an object, or a position in an array. -/
inductive Step where
  | field (name : String)
  | index (i : Nat)
deriving DecidableEq, Repr, Inhabited

/--
Where a value sits inside another. Every operation here recurses along the path rather than
through the value, so the depth reached is the length of the path the caller wrote, whatever
the value it is applied to.
-/
abbrev Path := List Step

instance : Coe String Step := ⟨.field⟩
instance : Coe Nat Step := ⟨.index⟩

/-- The value at `p`, if there is one. Duplicate field names resolve to the last, as elsewhere. -/
def get? (j : Json) (p : Path) : Option Json :=
  match p, j with
  | [], _ => some j
  | .field k :: rest, obj fields =>
    match findLast? fields k with
    | some child => get? child rest
    | none => none
  | .index i :: rest, arr elems =>
    match elems[i]? with
    | some child => get? child rest
    | none => none
  | _, _ => none

def getD (j : Json) (p : Path) (fallback : Json) : Json := (j.get? p).getD fallback

def has (j : Json) (p : Path) : Bool := (j.get? p).isSome

/-- The value at `p`, decoded. -/
def getAs? (j : Json) (α : Type u) [FromJson α] (p : Path) : Except String α :=
  match j.get? p with
  | some v => fromJson? v
  | none => .error s!"no value at {repr p}"

/--
`j` with `v` at `p`.

A field named by the last step of the path is added when it is missing, so building an object up
one field at a time works; anything else missing along the way is an error rather than a silent
creation, since guessing whether a gap should become an object or an array is how a typo turns
into a new field.
-/
def set? (j : Json) (p : Path) (v : Json) : Except String Json :=
  match p, j with
  | [], _ => .ok v
  | .field k :: rest, obj fields =>
    match findLast? fields k with
    | some child => do
      let child ← set? child rest v
      (obj fields).setObjVal? k child
    | none =>
      match rest with
      | [] => .ok (obj (fields.push (k, v)))
      | _ => .error s!"no such field: {k}"
  | .index i :: rest, arr elems =>
    match elems[i]? with
    | some child => do
      let child ← set? child rest v
      .ok (arr (elems.setIfInBounds i child))
    | none => .error s!"index out of bounds: {i}"
  | .field _ :: _, _ => .error "expected an object"
  | .index _ :: _, _ => .error "expected an array"

def setAs? (j : Json) {α : Type u} [ToJson α] (p : Path) (v : α) : Except String Json :=
  j.set? p (toJson v)

/-- `j` with the value at `p` replaced by `f` applied to it. -/
def modify? (j : Json) (p : Path) (f : Json → Json) : Except String Json :=
  match j.get? p with
  | some v => j.set? p (f v)
  | none => .error s!"no value at {repr p}"

/--
`j` without whatever is at `p`. Every field of that name goes, which matters only for a value
that was parsed with duplicates allowed.
-/
def remove? (j : Json) (p : Path) : Except String Json :=
  match p, j with
  | [], _ => .error "the empty path names the whole value, which cannot be removed"
  | [.field k], obj fields => .ok (obj (fields.filter fun (name, _) => name != k))
  | [.index i], arr elems =>
    if i < elems.size then .ok (arr (elems.eraseIdxIfInBounds i))
    else .error s!"index out of bounds: {i}"
  | .field k :: rest, obj fields =>
    match findLast? fields k with
    | some child => do
      let child ← remove? child rest
      (obj fields).setObjVal? k child
    | none => .error s!"no such field: {k}"
  | .index i :: rest, arr elems =>
    match elems[i]? with
    | some child => do
      let child ← remove? child rest
      .ok (arr (elems.setIfInBounds i child))
    | none => .error s!"index out of bounds: {i}"
  | .field _ :: _, _ => .error "expected an object"
  | .index _ :: _, _ => .error "expected an array"

end

end Json
