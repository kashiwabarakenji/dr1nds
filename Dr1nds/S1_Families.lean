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


def SC (F : SetFamily α) (x : α) : Prop :=
  ({x} : Finset α) ∈ F.C

@[simp] lemma SC_iff
  (F : SetFamily α) (x : α) :
  SC F x ↔ ({x} : Finset α) ∈ F.C := by
  rfl

end SetFamily

end Dr1nds
