-- Dr1nds/Forbid/Singleton.lean
import Mathlib.Tactic

import Dr1nds.SetFamily.CoreDefs      -- Up, Hole, NDS, NDS_corr
import Dr1nds.Forbid.Basic     -- singleton lemmas for Up/Hole

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-!
# Forbid singleton (A = {a})

This file contains family-level identities for singleton forbids only.
-/


/-- Rewrites `NDS_corr n C {a}` into filter form. Currently unused outside this file. -/
private lemma NDS_corr_singleton_rewrite
  (n : Nat) (C : Finset (Finset α)) (a : α) :
  NDS_corr (α := α) n C ({a} : Finset α)
    =
    NDS (α := α) n (C.filter (fun X => a ∉ X))
      + (C.filter (fun X => a ∈ X)).card := by
  classical
  -- unfold + rewrite Up/Hole using `Forbid/Basic.lean`
  simp [NDS_corr,
    Dr1nds.Hole_singleton_eq_filter_notmem (α := α),
    Dr1nds.Up_singleton_eq_filter_mem (α := α)]

omit [DecidableEq α] in
/-- `NDS` changes by exactly `|C|` when the ambient size increases by 1.

This is the basic accounting identity used when shifting between `n` and `n-1`.
Currently unused outside this file.
-/
private lemma NDS_succ_eq_sub_card
  (n : Nat) (C : Finset (Finset α)) :
  NDS (α := α) (n + 1) C = NDS (α := α) n C - (C.card : Int) := by
  classical
  simp [Dr1nds.NDS, w]
  ring


omit [DecidableEq α] in
/-- Local helper for filter-card partition. -/
private lemma card_filter_add_card_filter_not
  (s : Finset α) (p : α → Prop) [DecidablePred p] :
  (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  classical
  simpa using (Finset.filter_card_add_filter_neg_card_eq_card (s := s) (p := p))


/-- Local helper: `Up` and `Hole` partition the family for singleton forbids. -/
private lemma card_up_add_card_hole_singleton
  (C : Finset (Finset α)) (a : α) :
  (Up (α := α) C ({a} : Finset α)).card
    + (Hole (α := α) C ({a} : Finset α)).card
    = C.card := by
  classical
  simpa [
    Dr1nds.Up_singleton_eq_filter_mem (α := α),
    Dr1nds.Hole_singleton_eq_filter_notmem (α := α)
  ] using (card_filter_add_card_filter_not (α := Finset α)
        (s := C) (p := fun X : Finset α => a ∈ X))

/-- A rearranged form of `card_up_add_card_hole_singleton`.
Currently unused outside this file.
-/
private lemma card_up_singleton_eq
  (C : Finset (Finset α)) (a : α) :
  (Up (α := α) C ({a} : Finset α)).card
    = C.card - (Hole (α := α) C ({a} : Finset α)).card := by
  classical
  have hpart :
      (Up (α := α) C ({a} : Finset α)).card
        + (Hole (α := α) C ({a} : Finset α)).card
        = C.card :=
    card_up_add_card_hole_singleton (α := α) (C := C) (a := a)
  exact Nat.eq_sub_of_add_eq hpart

/--- `Int.ofNat` compatibility for subtraction when the RHS is known to be ≤ LHS.

This lemma is often what remains after rewriting cardinalities and switching between
`Nat` and `Int` in NDS/NDSCorr calculations.
Currently unused outside this file.
-/

private lemma int_ofNat_sub_of_le (a b : Nat) (h : b ≤ a) :
  (↑a : Int) - (↑b : Int) = (↑(a - b) : Int) := by
  simp [Int.ofNat_sub h]

end Dr1nds
