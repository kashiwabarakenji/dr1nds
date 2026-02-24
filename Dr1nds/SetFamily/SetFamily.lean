import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanCopilot

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
S1_Families.lean

目的（凍結）：
- 有限集合族 C : Finset (Finset α) を「会計の母体」として扱うための
  最小限の定義・補題を与える。
- Horn / forbid / con / trace には立ち入らない。
- 交わり・最小閉集合は **論理的定義のみ** を使う。
- 以後の S2–S11 は、このファイルの定義を前提に構成される。
-/

/- ============================================================
  1. 基本：集合族と台
============================================================ -/

/--
有限集合族 C と、その台集合 U。
※ U ∈ C を仮定しない（Hole / Del 用）。
-/
structure SetFamily (α : Type) [DecidableEq α] where
  U : Finset α
  C : Finset (Finset α)
  subset_univ : ∀ {X : Finset α}, X ∈ C → X ⊆ U

namespace SetFamily

@[simp] lemma subset_univ_of_mem
  (F : SetFamily α) {X : Finset α} (hX : X ∈ F.C) : X ⊆ F.U :=
F.subset_univ hX


/-- NEP (No Empty Premise) at the family level:
    the empty set belongs to the family. -/
def NEP (F : SetFamily α) : Prop :=
  (∅ : Finset α) ∈ F.C

/-- The universe itself belongs to the family (top element present). -/
def HasTop (F : SetFamily α) : Prop :=
  F.U ∈ F.C

/-- If `X ∈ F.C` and `x ∈ X`, then `x ∈ F.U`. -/
lemma mem_univ_of_mem_mem
  (F : SetFamily α) {X : Finset α} {x : α}
  (hX : X ∈ F.C) (hx : x ∈ X) :
  x ∈ F.U :=
by
  have hsub := F.subset_univ hX
  exact hsub hx


def SC (F : SetFamily α) (x : α) : Prop :=
  ({x} : Finset α) ∈ F.C

@[simp] lemma SC_iff
  (F : SetFamily α) (x : α) :
  SC F x ↔ ({x} : Finset α) ∈ F.C := by
  rfl

def contraction (F : SetFamily α) (x : α) : SetFamily α where
  U := F.U.erase x
  C := (F.C.filter (fun X => x ∈ X)).image (fun X => X.erase x)
  subset_univ := by
    classical
    intro X hX
    rw [Finset.mem_image] at hX
    simp at hX
    obtain ⟨A,hA⟩ := hX
    rw [Finset.subset_erase]
    constructor
    · have : A ⊆ F.U := by
        exact F.subset_univ hA.1.1
      rw [←hA.2]
      have : A.erase x ⊆ A := by exact Finset.erase_subset x A
      (expose_names; exact fun ⦃a⦄ a_1 => this_1 (this a_1))
    · rcases hA with ⟨h1,h2⟩
      rw [←h2]
      exact Finset.notMem_erase x A

---SCの要素でcontractionすると、NEPになる。
theorem contraction_SC_NEP (F : SetFamily α) (x : α) :
  F.SC x → (F.contraction x).NEP := by
  intro h
  dsimp [SetFamily.SC] at h
  dsimp [SetFamily.contraction]
  dsimp [SetFamily.NEP]
  rw [Finset.mem_image]
  use {x}
  simp
  exact h










end SetFamily

end Dr1nds

/- The support (ambient universe) naturally induced by a finite family. -/
--def Dr1nds.support (C : Finset (Finset α)) : Finset α :=
--  C.biUnion id
