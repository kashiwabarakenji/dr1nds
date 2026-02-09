import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanCopilot

import Dr1nds.Accounting

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
Forbid1: 「穴あき族」(holey family) と補正付き NDS

Up(C;A)   := { X∈C | A ⊆ X }
Hole(C;A) := { X∈C | ¬ A ⊆ X }   (= C \ Up だが、定義は filter)
F(C;A)    := Hole(C;A) （旧名互換）

NDS_corr_n(C;A) := Σ_{X∈Hole(C;A)} w_n(X) + |Up(C;A)|
-/

/-- Up(C;A) = { X∈C | A ⊆ X } -/
def Up (C : Finset (Finset α)) (A : Finset α) : Finset (Finset α) :=
  C.filter (fun X => A ⊆ X)

/-- Hole(C;A) = { X∈C | ¬ A ⊆ X } (= C \ Up(C;A)) -/
def Hole (C : Finset (Finset α)) (A : Finset α) : Finset (Finset α) :=
  C.filter (fun X => ¬ (A ⊆ X))

/-- 互換用：F(C;A) は Hole(C;A) と同義（旧コード救済） -/
abbrev F (C : Finset (Finset α)) (A : Finset α) : Finset (Finset α) :=
  Hole (α := α) C A

/--
Corrected NDS for forbid1:
  NDS_corr_n(C;A) = Σ_{X∈Hole(C;A)} w_n(X) + |Up(C;A)|
-/
def NDS_corr (n : Nat) (C : Finset (Finset α)) (A : Finset α) : Int :=
  (∑ X ∈ Hole (α := α) C A, w (α := α) n X) + (Up (α := α) C A).card

/-- Membership unfolding for Up. -/
@[simp] theorem mem_Up_iff (C : Finset (Finset α)) (A X : Finset α) :
    X ∈ Up (α := α) C A ↔ (X ∈ C ∧ A ⊆ X) := by
  unfold Up
  simp [Finset.mem_filter]

/-- Membership unfolding for Hole. -/
@[simp] theorem mem_Hole_iff (C : Finset (Finset α)) (A X : Finset α) :
    X ∈ Hole (α := α) C A ↔ (X ∈ C ∧ ¬ (A ⊆ X)) := by
  unfold Hole
  simp [Finset.mem_filter]

/- ------------------------------------------------------------
  Simple subset facts (named; useful for later rewrites)
------------------------------------------------------------ -/

/-- Up(C;A) ⊆ C -/
@[simp] lemma Up_subset_C (C : Finset (Finset α)) (A : Finset α) :
    Up (α := α) C A ⊆ C := by
  intro X hX
  exact (mem_Up_iff (α := α) C A X).1 hX |>.1

/-- Hole(C;A) ⊆ C -/
@[simp] lemma Hole_subset_C (C : Finset (Finset α)) (A : Finset α) :
    Hole (α := α) C A ⊆ C := by
  intro X hX
  exact (mem_Hole_iff (α := α) C A X).1 hX |>.1

/- ------------------------------------------------------------
  Partition facts: C splits into Up and Hole
------------------------------------------------------------ -/

/-- Up(C;A) and Hole(C;A) are disjoint. -/
theorem disjoint_Up_Hole (C : Finset (Finset α)) (A : Finset α) :
    Disjoint (Up (α := α) C A) (Hole (α := α) C A) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro X hXUp hXHole
  have hUp : X ∈ C ∧ A ⊆ X := (mem_Up_iff (α := α) C A X).1 hXUp
  have hHo : X ∈ C ∧ ¬ A ⊆ X := (mem_Hole_iff (α := α) C A X).1 hXHole
  exact hHo.2 hUp.2

/-- Every element of C is in Up(C;A) or in Hole(C;A). -/
theorem mem_C_iff_mem_Up_or_mem_Hole (C : Finset (Finset α)) (A X : Finset α) :
    X ∈ C ↔ X ∈ Up (α := α) C A ∨ X ∈ Hole (α := α) C A := by
  classical
  constructor
  · intro hXC
    by_cases hAX : A ⊆ X
    · left
      exact (mem_Up_iff (α := α) C A X).2 ⟨hXC, hAX⟩
    · right
      exact (mem_Hole_iff (α := α) C A X).2 ⟨hXC, hAX⟩
  · intro h
    cases h with
    | inl hUp =>
        exact (mem_Up_iff (α := α) C A X).1 hUp |>.1
    | inr hHo =>
        exact (mem_Hole_iff (α := α) C A X).1 hHo |>.1

/-- As finsets: C = Up(C;A) ∪ Hole(C;A). -/
theorem union_Up_Hole_eq (C : Finset (Finset α)) (A : Finset α) :
    Up (α := α) C A ∪ Hole (α := α) C A = C := by
  classical
  ext X
  constructor
  · intro h
    rcases Finset.mem_union.1 h with hUp | hHo
    · exact (mem_Up_iff (α := α) C A X).1 hUp |>.1
    · exact (mem_Hole_iff (α := α) C A X).1 hHo |>.1
  · intro hXC
    have : X ∈ Up (α := α) C A ∨ X ∈ Hole (α := α) C A :=
      (mem_C_iff_mem_Up_or_mem_Hole (α := α) C A X).1 hXC
    exact Finset.mem_union.2 this

/-- Card decomposition: |C| = |Up| + |Hole|. (stable proof) -/
theorem card_eq_card_Up_add_card_Hole (C : Finset (Finset α)) (A : Finset α) :
    C.card = (Up (α := α) C A).card + (Hole (α := α) C A).card := by
  classical
  have hdisj : Disjoint (Up (α := α) C A) (Hole (α := α) C A) :=
    disjoint_Up_Hole (α := α) C A
  have hcard :
      (Up (α := α) C A ∪ Hole (α := α) C A).card
        =
      (Up (α := α) C A).card + (Hole (α := α) C A).card :=
    Finset.card_union_of_disjoint hdisj
  -- union = C に置換して終わり
  let uuh := union_Up_Hole_eq (α := α) C A
  simp_all

/- ------------------------------------------------------------
  Optional: "Hole = C \\ Up" as a Finset equality (ext lemma)
------------------------------------------------------------ -/

/--
`Hole(C;A)` は `C \ Up(C;A)` と同値（Finset の等式として固定）

※定義上は filter vs sdiff なので、ext で示す。
-/
theorem Hole_eq_sdiff_Up (C : Finset (Finset α)) (A : Finset α) :
    Hole (α := α) C A = C \ Up (α := α) C A := by
  classical
  ext X
  constructor
  · intro hX
    have hC : X ∈ C := (mem_Hole_iff (α := α) C A X).1 hX |>.1
    have hnotUp : X ∉ Up (α := α) C A := by
      intro hUp
      have hAX : A ⊆ X := (mem_Up_iff (α := α) C A X).1 hUp |>.2
      exact (mem_Hole_iff (α := α) C A X).1 hX |>.2 hAX
    exact Finset.mem_sdiff.2 ⟨hC, hnotUp⟩
  · intro hX
    rcases Finset.mem_sdiff.1 hX with ⟨hC, hnotUp⟩
    have hnotAX : ¬ (A ⊆ X) := by
      intro hAX
      have : X ∈ Up (α := α) C A := (mem_Up_iff (α := α) C A X).2 ⟨hC, hAX⟩
      exact hnotUp this
    exact (mem_Hole_iff (α := α) C A X).2 ⟨hC, hnotAX⟩

/- ------------------------------------------------------------
  Forbid1: emptiness facts
------------------------------------------------------------ -/

omit [DecidableEq α] in
/-- If A is nonempty, then A ⊄ ∅. -/
lemma not_subset_empty_of_nonempty
  (A : Finset α) (hA : A.Nonempty) : ¬ A ⊆ (∅ : Finset α) := by
  rcases hA with ⟨a, ha⟩
  intro hsub
  have : a ∈ (∅ : Finset α) := hsub ha
  simpa using this

/-- If A is nonempty, then ∅ ∉ Up(C;A). -/
lemma empty_not_mem_Up_of_nonempty
  (C : Finset (Finset α)) (A : Finset α) (hA : A.Nonempty) :
  (∅ : Finset α) ∉ Up (α := α) C A := by
  intro h
  have h' : (∅ : Finset α) ∈ C ∧ A ⊆ (∅ : Finset α) :=
    (mem_Up_iff (α := α) C A (∅ : Finset α)).1 h
  exact (not_subset_empty_of_nonempty (α := α) A hA) h'.2

/--
If A is nonempty, then membership of ∅ in Hole(C;A) is equivalent to membership in C.
(= forbid does not delete ∅)
-/
lemma empty_mem_Hole_iff_mem_C_of_nonempty
  (C : Finset (Finset α)) (A : Finset α) (hA : A.Nonempty) :
  ((∅ : Finset α) ∈ Hole (α := α) C A) ↔ ((∅ : Finset α) ∈ C) := by
  have hnot : ¬ (A ⊆ (∅ : Finset α)) :=
    not_subset_empty_of_nonempty (α := α) A hA
  constructor
  · intro hHo
    exact (mem_Hole_iff (α := α) C A (∅ : Finset α)).1 hHo |>.1
  · intro hC
    exact (mem_Hole_iff (α := α) C A (∅ : Finset α)).2 ⟨hC, hnot⟩

/-- 旧名互換：F = Hole なので同じ事実として使える。 -/
lemma empty_mem_F_iff_mem_C_of_nonempty
  (C : Finset (Finset α)) (A : Finset α) (hA : A.Nonempty) :
  ((∅ : Finset α) ∈ F (α := α) C A) ↔ ((∅ : Finset α) ∈ C) := by
  simpa [F] using empty_mem_Hole_iff_mem_C_of_nonempty (α := α) C A hA

end Dr1nds
