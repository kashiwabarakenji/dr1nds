-- Dr1nds/S3_Trace.lean

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Dr1nds.S0_CoreDefs
import Dr1nds.S1_Families
import Dr1nds.ClosureSystem.Basic
--import LeanCopilot

namespace Dr1nds

variable {α : Type} [DecidableEq α]


@[simp]
lemma mem_Tr {u : α} {C : Finset (Finset α)} {Y : Finset α} :
  Y ∈ Tr u C ↔ ∃ X ∈ C, X.erase u = Y := by
  classical
  unfold Tr
  simp

/-
============================================================
  1. SetFamily structure
============================================================ -/



namespace SetFamily

variable {F : SetFamily α}

/-- Trace of a SetFamily at u. -/
def trace (F : SetFamily α) (u : α) : SetFamily α :=
{ U := F.U.erase u
  C := Tr u F.C
  subset_univ := by
    classical
    intro Y hY
    rcases (mem_Tr.mp hY) with ⟨X, hX, rfl⟩
    have hXU := F.subset_univ hX
    intro x hx
    have hxX : x ∈ X := (Finset.mem_erase.mp hx).2
    have hxU : x ∈ F.U := hXU hxX
    have hxne : x ≠ u := (Finset.mem_erase.mp hx).1
    exact Finset.mem_erase.mpr ⟨hxne, hxU⟩
}

@[simp]
lemma trace_U (F : SetFamily α) (u : α) :
  (trace F u).U = F.U.erase u := rfl

@[simp]
lemma trace_C (F : SetFamily α) (u : α) :
  (trace F u).C = Tr u F.C := rfl

end SetFamily

/-
============================================================
  2. Trace and ClosureSystem
============================================================ -/

namespace ClosureSystem

variable {α : Type} [Fintype α] [DecidableEq α]
variable  {CS : ClosureSystem α}

/-- Trace of a ClosureSystem at u. -/
def trace (CS : ClosureSystem α) (u : α) : ClosureSystem α where
  U := CS.U.erase u
  C := Tr u CS.C
  subset_univ := by
    classical
    intro Y hY
    rcases (mem_Tr.mp hY) with ⟨X, hX, rfl⟩
    have hXU := CS.subset_univ hX
    intro x hx
    have hxX : x ∈ X := (Finset.mem_erase.mp hx).2
    have hxU : x ∈ CS.U := hXU hxX
    have hxne : x ≠ u := (Finset.mem_erase.mp hx).1
    exact Finset.mem_erase.mpr ⟨hxne, hxU⟩
  mem_inter := by
    classical
    intro X Y hX hY
    rcases (mem_Tr.mp hX) with ⟨X₀, hX₀, rfl⟩
    rcases (mem_Tr.mp hY) with ⟨Y₀, hY₀, rfl⟩
    have hXY : X₀ ∩ Y₀ ∈ CS.C := CS.mem_inter hX₀ hY₀
    refine mem_Tr.mpr ⟨X₀ ∩ Y₀, hXY, ?_⟩
    ext x
    simp only [Finset.mem_erase, Finset.mem_inter]
    tauto
  top_mem := by
    classical
    have hU : CS.U ∈ CS.C := CS.top_mem
    exact mem_Tr.mpr ⟨CS.U, hU, rfl⟩

end ClosureSystem

end Dr1nds
