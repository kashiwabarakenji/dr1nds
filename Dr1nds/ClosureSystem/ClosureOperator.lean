-- Dr1nds/ClosureSystem/ClosureOperator.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Defs

import Dr1nds.SetFamily.SetFamily

namespace Dr1nds

variable {α : Type} [Fintype α][DecidableEq α]

/-- A closure operator on a fixed finite universe `U : Finset α`. -/
structure ClosureOperator (α : Type) where
  U         : Finset α
  cl        : Finset α → Finset α

  extensive : ∀ {X}, X ⊆ U → X ⊆ cl X

  monotone  : ∀ {X Y},
    X ⊆ U → Y ⊆ U →
    X ⊆ Y →
    cl X ⊆ cl Y

  idemp     : ∀ {X}, X ⊆ U → cl (cl X) = cl X

  closed_in_univ : ∀ {X}, X ⊆ U → cl X ⊆ U

namespace ClosureOperator

variable (c : ClosureOperator α)

/-- Closed sets of a closure operator -/
def IsClosed (X : Finset α) : Prop :=
  c.cl X = X


/-- The family of fixed (closed) sets of a closure operator. -/
def FixFamily : SetFamily α :=
{ U := c.U
  C := c.U.powerset.filter (fun X => c.cl X = X)
  subset_univ := by
    intro X hX
    classical
    have h := Finset.mem_filter.mp hX
    exact Finset.mem_powerset.mp h.1
}

omit [Fintype α] in
lemma FixFamily_univ_mem :
  c.U ∈ c.FixFamily.C := by
  classical
  unfold FixFamily
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_powerset.mpr (by intro x hx; exact hx)
  ·
    have hU : c.U ⊆ c.U := by intro x hx; exact hx
    have h_sub₁ : c.cl c.U ⊆ c.U :=
      c.closed_in_univ (X := c.U) hU
    have h_sub₂ : c.U ⊆ c.cl c.U :=
      c.extensive (X := c.U) hU
    exact Finset.Subset.antisymm h_sub₁ h_sub₂

omit [Fintype α] in
lemma FixFamily_inter_closed
  {X Y : Finset α}
  (hX : X ∈ c.FixFamily.C)
  (hY : Y ∈ c.FixFamily.C) :
  X ∩ Y ∈ c.FixFamily.C := by
  classical
  unfold FixFamily at *
  have hX' := Finset.mem_filter.mp hX
  have hY' := Finset.mem_filter.mp hY
  have hX_sub : X ⊆ c.U := Finset.mem_powerset.mp hX'.1
  have hY_sub : Y ⊆ c.U := Finset.mem_powerset.mp hY'.1
  have hX_closed : c.cl X = X := hX'.2
  have hY_closed : c.cl Y = Y := hY'.2

  apply Finset.mem_filter.mpr
  constructor
  ·
    apply Finset.mem_powerset.mpr
    intro x hx
    exact hX_sub ((Finset.mem_inter.mp hx).1)
  ·
    apply Finset.Subset.antisymm
    ·
      intro x hx
      have h_subX :=
        c.monotone
          (X := X ∩ Y) (Y := X)
          (by
            intro x hx
            exact hX_sub ((Finset.mem_inter.mp hx).1))
          hX_sub
          (by intro x hx; exact (Finset.mem_inter.mp hx).1)
      have h_subY :=
        c.monotone
          (X := X ∩ Y) (Y := Y)
          (by
            intro x hx
            exact hY_sub ((Finset.mem_inter.mp hx).2))
          hY_sub
          (by intro x hx; exact (Finset.mem_inter.mp hx).2)
      have hxX : x ∈ X := by
        have := h_subX hx
        simpa [hX_closed] using this
      have hxY : x ∈ Y := by
        have := h_subY hx
        simpa [hY_closed] using this
      exact Finset.mem_inter.mpr ⟨hxX, hxY⟩
    ·
      intro x hx
      have h_subU : X ∩ Y ⊆ c.U := by
        intro x hx
        exact hX_sub ((Finset.mem_inter.mp hx).1)
      exact c.extensive (X := X ∩ Y) h_subU hx

omit [Fintype α] [DecidableEq α] in
/-- The universe `U` is closed. -/
lemma univ_isClosed :
  c.IsClosed c.U := by
  have hU : c.U ⊆ c.U := by intro x hx; exact hx
  have h₁ := c.extensive (X := c.U) hU
  have h₂ := c.idemp (X := c.U) hU
  -- From idempotence: cl (cl U) = cl U
  -- From extensiveness: U ⊆ cl U
  -- Since cl U ⊆ U by closed_in_univ, equality follows
  have h_closed : c.cl c.U = c.U := by
    have h_sub₁ : c.cl c.U ⊆ c.U :=
      c.closed_in_univ (X := c.U) hU
    have h_sub₂ : c.U ⊆ c.cl c.U :=
      c.extensive (X := c.U) hU
    exact Finset.Subset.antisymm h_sub₁ h_sub₂
  exact h_closed

omit [Fintype α] [DecidableEq α] in
/-- Closed sets are contained in the universe. -/
lemma closed_subset_univ
  {X : Finset α}
  (_ : c.IsClosed X)
  (hU : X ⊆ c.U) :
  X ⊆ c.U := by
  exact hU

omit [Fintype α] in
/- A singleton is SC in the FixFamily iff it is fixed by `cl`. -/
lemma SC_iff_cl_singleton
  (x : α)
  (hx : x ∈ c.U) :
  SetFamily.SC c.FixFamily x
    ↔
  c.cl ({x} : Finset α) = {x} := by
  classical
  unfold SetFamily.SC
  unfold FixFamily
  constructor
  ·
    intro h
    have h' := Finset.mem_filter.mp h
    exact h'.2
  ·
    intro hcl
    apply Finset.mem_filter.mpr
    constructor
    ·
      apply Finset.mem_powerset.mpr
      intro y hy
      simp at hy
      simpa [hy] using hx
    ·
      exact hcl

end ClosureOperator

end Dr1nds
