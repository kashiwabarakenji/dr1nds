-- Dr1nds/Forbid/Basic.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import LeanCopilot

import Dr1nds.S0_CoreDefs  -- Up / Hole / NDS / NDS_corr がここにある想定

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-!
# Forbid.Basic

`Up C A = {X∈C | A ⊆ X}` と `Hole C A = {X∈C | ¬ A ⊆ X}` に関する
Finset レベルの一般補題（Horn/closure を一切使わない）。

特に `A = {a}` のとき
`Up C {a} = {X∈C | a∈X}`、`Hole C {a} = {X∈C | a∉X}`
まで落とすのが目的。
-/

/- ------------------------------------------------------------
  membership rewriting
------------------------------------------------------------ -/

@[simp] lemma mem_Up_iff (C : Finset (Finset α)) (A X : Finset α) :
  X ∈ Up (α := α) C A ↔ X ∈ C ∧ A ⊆ X := by
  classical
  simp [Up]

@[simp] lemma mem_Hole_iff (C : Finset (Finset α)) (A X : Finset α) :
  X ∈ Hole (α := α) C A ↔ X ∈ C ∧ ¬ A ⊆ X := by
  classical
  simp [Hole]

/- ------------------------------------------------------------
  Up/Hole partition of C
------------------------------------------------------------ -/

lemma Up_union_Hole (C : Finset (Finset α)) (A : Finset α) :
  Up (α := α) C A ∪ Hole (α := α) C A = C := by
  classical
  ext X
  by_cases hXC : X ∈ C
  · have : (A ⊆ X) ∨ ¬ (A ⊆ X) := em (A ⊆ X)
    cases this with
    | inl hAX =>
        simp [mem_Up_iff, mem_Hole_iff, hXC, hAX]
    | inr hAX =>
        simp [mem_Up_iff, mem_Hole_iff, hXC, hAX]
  · -- X ∉ C
    simp [mem_Up_iff, mem_Hole_iff, hXC]

lemma Up_inter_Hole_empty (C : Finset (Finset α)) (A : Finset α) :
  Up (α := α) C A ∩ Hole (α := α) C A = ∅ := by
  classical
  ext X
  by_cases hXC : X ∈ C
  · by_cases hAX : A ⊆ X
    · simp [mem_Up_iff, mem_Hole_iff, hXC, hAX]
    · simp [mem_Up_iff, mem_Hole_iff, hXC, hAX]
  · simp [mem_Up_iff, mem_Hole_iff, hXC]

lemma Up_disjoint_Hole (C : Finset (Finset α)) (A : Finset α) :
  Disjoint (Up (α := α) C A) (Hole (α := α) C A) := by
  classical
  -- Finset.disjoint_left: ∀ ⦃a⦄, a ∈ s → a ∈ t → False
  refine Finset.disjoint_left.2 ?_
  intro X hXUp hXHole
  have h1 := (mem_Up_iff (α := α) C A X).1 hXUp
  have h2 := (mem_Hole_iff (α := α) C A X).1 hXHole
  exact h2.2 h1.2

lemma card_Up_add_card_Hole (C : Finset (Finset α)) (A : Finset α) :
  (Up (α := α) C A).card + (Hole (α := α) C A).card = C.card := by
  classical
  -- disjoint union + union = C
  have hdis : Disjoint (Up (α := α) C A) (Hole (α := α) C A) :=
    Up_disjoint_Hole (α := α) C A
  -- `card_union_of_disjoint` gives:
  -- card (s ∪ t) = card s + card t
  have hcard :
      (Up (α := α) C A ∪ Hole (α := α) C A).card
        = (Up (α := α) C A).card + (Hole (α := α) C A).card := by
    let fc := (Finset.card_union_of_disjoint hdis).symm
    simp [Finset.card_union_of_disjoint hdis]

  -- rewrite union = C
  have hunion : Up (α := α) C A ∪ Hole (α := α) C A = C :=
    Up_union_Hole (α := α) C A
  -- finish
  -- from hcard: card(union)=sum, so sum = card(union) = card C
  -- rearrange:
  -- sum = C.card
  -- We can just simp using hunion.
  -- (We already have hcard with reversed direction; easiest do:)
  have : (Up (α := α) C A).card + (Hole (α := α) C A).card
        = (Up (α := α) C A ∪ Hole (α := α) C A).card := by
    simp [Finset.card_union_of_disjoint hdis]
  simpa [hunion] using this

/- ------------------------------------------------------------
  Singleton forbid: A = {a}
------------------------------------------------------------ -/

omit [DecidableEq α] in
@[simp] lemma singleton_subset_iff {a : α} (X : Finset α) :
  ({a} : Finset α) ⊆ X ↔ a ∈ X := by
  classical
  constructor
  · intro h
    exact h (by simp)
  · intro ha
    intro x hx
    -- x = a
    have : a=x:=by simp_all only [Finset.mem_singleton]
    rw [this] at ha
    exact ha

@[simp] lemma Up_singleton_eq_filter_mem (C : Finset (Finset α)) (a : α) :
  Up (α := α) C ({a} : Finset α)
    = C.filter (fun X => a ∈ X) := by
  classical
  ext X
  -- unfold membership
  simp [Up]

@[simp] lemma Hole_singleton_eq_filter_notmem (C : Finset (Finset α)) (a : α) :
  Hole (α := α) C ({a} : Finset α)
    = C.filter (fun X => a ∉ X) := by
  classical
  ext X
  simp [Hole]

/- ------------------------------------------------------------
  NDS_corr: trivial helper lemma (no Horn)
------------------------------------------------------------ -/

lemma Up_card_nonneg (C : Finset (Finset α)) (A : Finset α) :
  (0 : Int) ≤ (Up (α := α) C A).card := by
  simpa using Int.ofNat_nonneg (Up (α := α) C A).card

/-- `NDS_corr ≤ 0` から `NDS(Hole) ≤ 0` を取り出す一般補題（Up≥0 を落とす）。 -/
lemma corr_implies_hole_bound
  (n : Nat) (C : Finset (Finset α)) (A : Finset α)
  (h : NDS_corr (α := α) n C A ≤ 0) :
  NDS (α := α) n (Hole (α := α) C A) ≤ 0 := by
  classical
  have h' :
      NDS (α := α) n (Hole (α := α) C A)
        + (Up (α := α) C A).card ≤ 0 := by
    simpa [NDS_corr] using h
  have hup : (0 : Int) ≤ (Up (α := α) C A).card :=
    Up_card_nonneg (α := α) C A
  linarith

end Dr1nds
