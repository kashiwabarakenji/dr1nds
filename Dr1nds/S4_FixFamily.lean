import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

import Dr1nds.S0_CoreDefs
import Dr1nds.S1_Families
import Dr1nds.S2_HornNF

namespace Dr1nds

variable {α : Type} [Fintype α] [DecidableEq α]

/- ============================================================
  FixFamily (Finset版)
============================================================ -/

structure FixFamily (α : Type) [Fintype α] [DecidableEq α]
  (H : HornNF α) where
  C : Finset (Finset α)
  mem_iff : ∀ X : Finset α, X ∈ C ↔ X ∈ H.FixSet

namespace FixFamily

variable {H : HornNF α}

@[simp] theorem mem_iff' (F : FixFamily (α := α) H)
    (X : Finset α) :
    X ∈ F.C ↔ X ∈ H.FixSet :=
  F.mem_iff X

/-- FixSet の定義展開形 -/
theorem mem_iff'' (F : FixFamily (α := α) H)
    (X : Finset α) :
    X ∈ F.C ↔ (X ⊆ H.U ∧ HornNF.IsClosed H X) := by
  simp [HornNF.FixSet] --using (F.mem_iff' (X := X))

/-- 任意のメンバーは U の部分集合 -/
theorem subset_univ_of_mem
    (F : FixFamily (α := α) H)
    {X : Finset α} :
    X ∈ F.C → X ⊆ H.U := by
  intro hX
  exact (F.mem_iff'' (X := X)).1 hX |>.1

end FixFamily

/- ============================================================
  標準 FixFamily
============================================================ -/

noncomputable def Fix (H : HornNF α) : FixFamily (α := α) H :=
  { C := H.FixSet
    mem_iff := by intro X; rfl }

/- ============================================================
  ClosedPack（列挙器）
============================================================ -/

structure ClosedPack (α : Type) [DecidableEq α] where
  H : HornNF α
  C : Finset (Finset α)
  mem_iff : ∀ X : Finset α, X ∈ C ↔ X ∈ H.FixSet

namespace ClosedPack

omit [Fintype α] in
@[simp] theorem mem_iff'
    (P : ClosedPack (α := α))
    (X : Finset α) :
    X ∈ P.C ↔ X ∈ P.H.FixSet :=
  P.mem_iff X

omit [Fintype α] in
@[simp] theorem mem_iff''
    (P : ClosedPack (α := α))
    (X : Finset α) :
    X ∈ P.C ↔ (X ⊆ P.H.U ∧ HornNF.IsClosed P.H X) := by
  simp [HornNF.FixSet] --using (P.mem_iff' (X := X))

end ClosedPack

end Dr1nds
