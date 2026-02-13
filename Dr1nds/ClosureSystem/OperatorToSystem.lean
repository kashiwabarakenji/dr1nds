-- Dr1nds/ClosureSystem/OperatorToSystem.lean
import Dr1nds.ClosureSystem.ClosureOperator
import Dr1nds.ClosureSystem.Basic
import Mathlib.Data.Finset.Powerset

namespace Dr1nds

variable {α : Type} [Fintype α][DecidableEq α]

def ClosureOperator.toClosureSystem
  (c : ClosureOperator α)
  : ClosureSystem α :=
{ U := c.U
  C :=
    (Finset.powerset c.U).filter
      (fun X => c.cl X = X)

  subset_univ := by
    intro X hX
    simp at hX
    exact hX.1

  mem_inter := by
    intro X Y hX hY
    simp
    simp at hX hY
    constructor
    ·
      obtain ⟨left, right⟩ := hX
      obtain ⟨left_1, right_1⟩ := hY
      intro x hx
      simp_all only [Finset.mem_inter]
      obtain ⟨left_2, right_2⟩ := hx
      apply left left_2
    · have : c.cl (X ∩ Y) ⊇ X ∩ Y := by
        apply c.extensive
        obtain ⟨left, right⟩ := hX
        obtain ⟨left_1, right_1⟩ := hY
        intro x hx
        simp_all only [Finset.mem_inter]
        obtain ⟨left_2, right_2⟩ := hx
        exact left left_2
      have : c.cl (X ∩ Y) ⊆ c.cl X := by
        apply c.monotone
        obtain ⟨left, right⟩ := hX
        obtain ⟨left_1, right_1⟩ := hY
        intro x hx
        simp_all only [Finset.mem_inter]
        obtain ⟨left_2, right_2⟩ := hx
        exact left left_2
        simp_all only
        simp_all only [Finset.inter_subset_left]
      have : c.cl (X ∩ Y) ⊆ c.cl Y := by
        apply c.monotone
        simp_all only
        obtain ⟨left, right⟩ := hX
        obtain ⟨left_1, right_1⟩ := hY
        rw [← right_1]
        simp_all only
        intro x hx
        simp_all only [Finset.mem_inter]
        obtain ⟨left_2, right_2⟩ := hx
        exact left left_2
        simp_all only
        simp_all only [Finset.inter_subset_right]
      rename_i this_1 this_2
      simp_all only
      obtain ⟨left, right⟩ := hX
      obtain ⟨left_1, right_1⟩ := hY
      ext a : 1
      simp_all only [Finset.mem_inter]
      apply Iff.intro
      · intro a_1
        apply And.intro
        · apply this_2
          simp_all only
        · exact this a_1
      · intro a_1
        obtain ⟨left_2, right_2⟩ := a_1
        apply this_1
        simp_all only [Finset.mem_inter, and_self]

  top_mem := by
    simp
    have h₁ : c.U ⊆ c.cl c.U := by
      apply c.extensive
      exact fun ⦃a⦄ a_1 => a_1
    have h₂ : c.cl c.U ⊆ c.U := by
       exact c.closed_in_univ fun ⦃a⦄ a_1 => a_1
    exact Finset.Subset.antisymm h₂ h₁
}
