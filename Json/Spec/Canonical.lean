/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec
public import Json.Spec.Length

public section

namespace Json.Spec

/-!
Every number in a value the grammar derives is canonical.

`number` in the ABNF is a spelling rather than a value, and one value has many spellings: `1`,
`1.0` and `1e0` are the same number. The grammar records what the digits denote, in the one
canonical form, so a value derived from a text carries no other. That is what makes `==`,
`compare` and `hash` agree on everything a parse produces, since agreement is what
`Number.eqv_iff_eq` gives for canonical numbers and nothing weaker.
-/

theorem canonical_of_num {s : List Char} {n : Number} {r : List Char} (h : Num s n r) :
    n.Canonical := by
  cases h with
  | mk => exact Number.canonical_normalize _ _

private theorem family_canonical : ∀ (n : Nat) (s : List Char), s.length ≤ n →
    (∀ {e r}, Arr s e r → canonicalNumbersList e.toList = true) ∧
    (∀ {f r}, Object s f r → canonicalNumbersFields f.toList = true) ∧
    (∀ {j r}, Value s j r → canonicalNumbers j = true) ∧
    (∀ {vs r}, Elements s vs r → canonicalNumbersList vs = true) ∧
    (∀ {m r}, Member s m r → canonicalNumbers m.2 = true) ∧
    (∀ {ms r}, Members s ms r → canonicalNumbersFields ms = true) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs
    have harr : ∀ {e r}, Arr s e r → canonicalNumbersList e.toList = true := by
      intro e r h
      cases h with
      | empty => rfl
      | items hb hel _ =>
        have := token_length hb
        simpa using (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.1 hel
    have hobj : ∀ {f r}, Object s f r → canonicalNumbersFields f.toList = true := by
      intro f r h
      cases h with
      | empty => rfl
      | members hb hms _ =>
        have := token_length hb
        simpa using (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.2.2 hms
    have hval : ∀ {j r}, Value s j r → canonicalNumbers j = true := by
      intro j r h
      cases h with
      | false_ => rfl
      | null => rfl
      | true_ => rfl
      | str _ => rfl
      | num hn => exact decide_eq_true (canonical_of_num hn)
      | arr ha => exact harr ha
      | obj ho => exact hobj ho
    have hels : ∀ {vs r}, Elements s vs r → canonicalNumbersList vs = true := by
      intro vs r h
      cases h with
      | one hv => simp [canonicalNumbersList, hval hv]
      | more hv hsep hel =>
        have := value_length hv
        have := token_length hsep
        have htail := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.1 hel
        simp [canonicalNumbersList, hval hv, htail]
    have hmem : ∀ {m r}, Member s m r → canonicalNumbers m.2 = true := by
      intro m r h
      cases h with
      | mk hst hsep hv =>
        have := str_length hst
        have := token_length hsep
        exact (ih _ (by omega) _ (Nat.le_refl _)).2.2.1 hv
    have hmems : ∀ {ms r}, Members s ms r → canonicalNumbersFields ms = true := by
      intro ms r h
      cases h with
      | one hm => simp [canonicalNumbersFields, hmem hm]
      | more hm hsep hms =>
        have := member_length hm
        have := token_length hsep
        have htail := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.2.2 hms
        simp [canonicalNumbersFields, hmem hm, htail]
    exact ⟨harr, hobj, hval, hels, hmem, hmems⟩

/-- A value the grammar derives holds canonical numbers and nothing else. -/
theorem canonicalNumbers_of_value {s : List Char} {j : Json} {r : List Char} (h : Value s j r) :
    CanonicalNumbers j := (family_canonical s.length s (Nat.le_refl _)).2.2.1 h

theorem canonicalNumbers_of_text {s : List Char} {j : Json} (h : Text s j) :
    CanonicalNumbers j := by
  obtain ⟨a, b, hws, hv, hend⟩ := h
  exact canonicalNumbers_of_value hv

end Json.Spec
