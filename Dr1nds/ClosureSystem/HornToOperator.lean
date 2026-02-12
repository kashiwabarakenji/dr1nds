-- Dr1nds/ClosureSystem/HornToOperator.lean

import Dr1nds.ClosureSystem.ClosureOperator
import Dr1nds.S1_HornDefs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

namespace Dr1nds

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Closure induced by Horn rules as the least closed superset (logical definition) -/
noncomputable def Horn.closure (H : Horn α) (X : Finset α) : Finset α := by
  classical
  exact
    H.U.filter fun x =>
      ∀ Y : Finset α,
        Horn.IsClosed H Y →
        X ⊆ Y →
        x ∈ Y

/-- Horn induces a closure operator -/
noncomputable def Horn.toClosureOperator (H : Horn α) : ClosureOperator α :=
{ U := H.U
  cl := H.closure

  closed_in_univ := by
    intro X hX x hx
    classical
    exact (Finset.mem_filter.mp hx).1

  extensive := by
    intro X hX x hxX
    classical
    apply Finset.mem_filter.mpr
    constructor
    · exact hX hxX
    · intro Y hY hXY
      exact hXY hxX

  monotone := by
    intro X Y hX hY hXY x hx
    classical
    apply Finset.mem_filter.mpr
    constructor
    · exact (Finset.mem_filter.mp hx).1
    · intro Z hZ hYZ
      have hXZ : X ⊆ Z :=
        fun x hxX => hYZ (hXY hxX)
      exact (Finset.mem_filter.mp hx).2 Z hZ hXZ

  idemp := by
    intro X hX
    classical
    apply Finset.ext
    intro x
    constructor

    · -- cl (cl X) ⊆ cl X
      intro hx
      have hx_prop := (Finset.mem_filter.mp hx).2
      have h_closed : Horn.IsClosed H (H.closure X) := by
        constructor
        · intro y hy
          exact (Finset.mem_filter.mp hy).1
        · intro P h hPh hPX
          apply Finset.mem_filter.mpr
          constructor
          · exact (H.valid hPh).2
          · intro Y hY hXY
            have hPZ : P ⊆ Y :=
              fun y hyP =>
                have hy_cl : y ∈ H.closure X := hPX hyP
                (Finset.mem_filter.mp hy_cl).2 Y hY hXY
            exact hY.2 hPh hPZ
      have h_self : H.closure X ⊆ H.closure X := fun y hy => hy
      exact hx_prop (H.closure X) h_closed h_self

    · -- cl X ⊆ cl (cl X)
      intro hx
      apply Finset.mem_filter.mpr
      constructor
      · exact (Finset.mem_filter.mp hx).1
      · intro Y hY hYX
        apply (Finset.mem_filter.mp hx).2 Y hY
        have h_ext : X ⊆ H.closure X :=
          by
            intro a ha
            apply Finset.mem_filter.mpr
            constructor
            · exact hX ha
            · intro Y hY hXY
              exact hXY ha
        exact fun ⦃a⦄ ha => hYX (h_ext ha)
}

end Dr1nds
