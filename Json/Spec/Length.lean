/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec

public section

namespace Json.Spec

/-!
How much of the text each production consumes.

Every production leaves less text than it was given, and a value leaves strictly less. That is
what lets a proof about the grammar run by induction on the length of the text: the six relations
of the value family are one mutual definition, which the `induction` tactic will not take apart,
but each of them shortens what it is given, so an induction on the length reaches all six.
-/

theorem Ws.length_le {s r : List Char} (h : Ws s r) : r.length ≤ s.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => exact Nat.le_succ_of_le ih

theorem token_length {t : Char} {s r : List Char} (h : Token t s r) :
    r.length < s.length := by
  cases h with
  | mk h₁ h₂ =>
    have l₁ := h₁.length_le
    have l₂ := h₂.length_le
    simp only [List.length_cons] at l₁
    omega

theorem digits_length {s : List Char} {v n : Nat} {r : List Char} (h : Digits s v n r) :
    r.length < s.length := by
  induction h with
  | last => simp
  | cons _ _ ih => simp only [List.length_cons]; omega

theorem int_length {s : List Char} {v : Nat} {r : List Char} (h : Int' s v r) :
    r.length < s.length := by
  cases h with
  | zero => simp
  | digits _ hd => exact digits_length hd

theorem frac_length {s : List Char} {f n : Nat} {r : List Char} (h : Frac s f n r) :
    r.length ≤ s.length := by
  cases h with
  | absent => exact Nat.le_refl _
  | present hd => have := digits_length hd; simp only [List.length_cons]; omega

theorem exp_length {s : List Char} {e : Int} {r : List Char} (h : Exp s e r) :
    r.length ≤ s.length := by
  cases h with
  | absent => exact Nat.le_refl _
  | bare _ hd => have := digits_length hd; simp only [List.length_cons]; omega
  | plus _ hd => have := digits_length hd; simp only [List.length_cons]; omega
  | minus _ hd => have := digits_length hd; simp only [List.length_cons]; omega

theorem sign_length {s : List Char} {b : Bool} {r : List Char} (h : Sign s b r) :
    r.length ≤ s.length := by
  cases h with
  | absent => exact Nat.le_refl _
  | minus => simp

theorem num_length {s : List Char} {n : Number} {r : List Char} (h : Num s n r) :
    r.length < s.length := by
  cases h with
  | mk hs hi hf he =>
    have l₁ := sign_length hs
    have l₂ := int_length hi
    have l₃ := frac_length hf
    have l₄ := exp_length he
    omega

theorem hex4_length {s : List Char} {v : Nat} {r : List Char} (h : Hex4 s v r) :
    r.length + 4 = s.length := by
  cases h with
  | mk => simp

theorem ch_length {s : List Char} {c : Char} {r : List Char} (h : Ch s c r) :
    r.length < s.length := by
  cases h with
  | codePoint hx _ => have := hex4_length hx; simp only [List.length_cons]; omega
  | surrogatePair hx₁ hx₂ _ _ _ _ _ =>
    have := hex4_length hx₁
    have := hex4_length hx₂
    simp only [List.length_cons] at *
    omega
  | _ => simp only [List.length_cons]; omega

theorem chars_length {s : List Char} {cs r : List Char} (h : Chars s cs r) :
    r.length ≤ s.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hch _ ih => have := ch_length hch; omega

theorem str_length {s : List Char} {v : String} {r : List Char} (h : Str s v r) :
    r.length < s.length := by
  cases h with
  | mk hcs =>
    have := chars_length hcs
    simp only [List.length_cons] at *
    omega

private theorem family_length : ∀ (n : Nat) (s : List Char), s.length ≤ n →
    (∀ {e r}, Arr s e r → r.length < s.length) ∧
    (∀ {f r}, Object s f r → r.length < s.length) ∧
    (∀ {j r}, Value s j r → r.length < s.length) ∧
    (∀ {vs r}, Elements s vs r → r.length ≤ s.length) ∧
    (∀ {m r}, Member s m r → r.length ≤ s.length) ∧
    (∀ {ms r}, Members s ms r → r.length ≤ s.length) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs
    have harr : ∀ {e r}, Arr s e r → r.length < s.length := by
      intro e r h
      cases h with
      | empty hb he => have := token_length hb; have := token_length he; omega
      | items hb hel he =>
        have l₁ := token_length hb
        have l₂ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.1 hel
        have l₃ := token_length he
        omega
    have hobj : ∀ {f r}, Object s f r → r.length < s.length := by
      intro f r h
      cases h with
      | empty hb he => have := token_length hb; have := token_length he; omega
      | members hb hms he =>
        have l₁ := token_length hb
        have l₂ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.2.2 hms
        have l₃ := token_length he
        omega
    have hval : ∀ {j r}, Value s j r → r.length < s.length := by
      intro j r h
      cases h with
      | false_ => simp only [List.length_cons]; omega
      | null => simp only [List.length_cons]; omega
      | true_ => simp only [List.length_cons]; omega
      | num hn => exact num_length hn
      | str hst => exact str_length hst
      | arr ha => exact harr ha
      | obj ho => exact hobj ho
    have hels : ∀ {vs r}, Elements s vs r → r.length ≤ s.length := by
      intro vs r h
      cases h with
      | one hv => exact Nat.le_of_lt (hval hv)
      | more hv hsep hel =>
        have l₁ := hval hv
        have l₂ := token_length hsep
        have l₃ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.1 hel
        omega
    have hmem : ∀ {m r}, Member s m r → r.length ≤ s.length := by
      intro m r h
      cases h with
      | mk hst hsep hv =>
        have l₁ := str_length hst
        have l₂ := token_length hsep
        have l₃ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.1 hv
        omega
    have hmems : ∀ {ms r}, Members s ms r → r.length ≤ s.length := by
      intro ms r h
      cases h with
      | one hm => exact hmem hm
      | more hm hsep hms =>
        have l₁ := hmem hm
        have l₂ := token_length hsep
        have l₃ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.2.2 hms
        omega
    exact ⟨harr, hobj, hval, hels, hmem, hmems⟩

theorem arr_length {s : List Char} {e : Array Json} {r : List Char} (h : Arr s e r) :
    r.length < s.length := (family_length s.length s (Nat.le_refl _)).1 h

theorem object_length {s : List Char} {f : Array (String × Json)} {r : List Char}
    (h : Object s f r) : r.length < s.length :=
  (family_length s.length s (Nat.le_refl _)).2.1 h

theorem members_length {s : List Char} {ms : List (String × Json)} {r : List Char}
    (h : Members s ms r) : r.length ≤ s.length :=
  (family_length s.length s (Nat.le_refl _)).2.2.2.2.2 h

theorem value_length {s : List Char} {j : Json} {r : List Char} (h : Value s j r) :
    r.length < s.length := (family_length s.length s (Nat.le_refl _)).2.2.1 h

theorem elements_length {s : List Char} {vs : List Json} {r : List Char}
    (h : Elements s vs r) : r.length ≤ s.length :=
  (family_length s.length s (Nat.le_refl _)).2.2.2.1 h

theorem member_length {s : List Char} {m : String × Json} {r : List Char}
    (h : Member s m r) : r.length ≤ s.length :=
  (family_length s.length s (Nat.le_refl _)).2.2.2.2.1 h

end Json.Spec
