/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser.Soundness
public import Json.Spec.Unambiguity

public section

@[expose] section

namespace Json.Parser

variable {s : String}

/-!
The other direction: what the grammar derives, the parser accepts.

Two things shape the work. The value needs no tracking, since `parse_eq_of_isOk` gets it from
soundness and unambiguity together, which leaves only the obligation that a derivable text is
never refused. And a scanner has to be shown maximal, which soundness never needed: `Ws` relates
a text to any of its whitespace-suffixes, while `skipWs` lands on exactly one of them, so the
two are tied together by what the scanner leaves rather than by what it consumes.
-/

/--
On a text the grammar derives, returning anything at all is returning the right thing, there
being one value the text names and soundness saying the returned one is among them.
-/
theorem parse_eq_of_isOk {cfg : Config} {j : Json} (hbom : cfg.ignoreBOM = false)
    (ht : Spec.TextOf s j) (hok : (parse s cfg).isOk) : parse s cfg = .ok j := by
  cases h : parse s cfg with
  | error e => rw [h] at hok; exact absurd hok (by simp [Except.isOk, Except.toBool])
  | ok j' => rw [eq_of_textOf hbom h ht]

/-- The scanner stops at a character that is not whitespace, or at the end. -/
theorem noWs_skipWs (start : s.Pos) : Spec.NoWs (remaining (skipWs start).pos) := by
  have go : ∀ (p : s.Pos) (h : p.remainingBytes ≤ start.remainingBytes),
      Spec.NoWs (remaining (skipWs.go start p h).pos) := by
    intro p h
    fun_induction skipWs.go start p h with
    | case1 p h c q hc hws ih => exact ih
    | case2 p h c q hc hws =>
      intro c' t hct
      rw [remaining_step hc] at hct
      simp only [List.cons.injEq] at hct
      obtain ⟨rfl, -⟩ := hct
      simpa using hws
    | case3 p h hc =>
      intro c' t hct
      rw [remaining_none hc] at hct
      exact absurd hct (by simp)
  exact go start (Nat.le_refl _)

/-- Whatever whitespace a derivation passed over, the scanner passes over exactly that much. -/
theorem skipWs_complete {p : s.Pos} {t : List Char} (h : Spec.Ws (remaining p) t)
    (hn : Spec.NoWs t) : remaining (skipWs p).pos = t :=
  Spec.Ws.eq_of_noWs (ws_skipWs p) h (noWs_skipWs p) hn

end Json.Parser
