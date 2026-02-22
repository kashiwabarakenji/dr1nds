-- Dr1nds/ClosureSystem/HornClosure.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

import Dr1nds.ClosureSystem.ClosureOperator
import Dr1nds.Horn.Horn

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-!
HornNF から closure を定義し、ClosureOperator に持ち上げる。
HornToOperator.lean（Horn 版）と同じ「最小閉上位集合」の定義を使う。
-/

/-- Closure induced by HornNF rules as the least closed superset (logical definition). -/
noncomputable def HornNF.closure (H : HornNF α) (X : Finset α) : Finset α := by
  classical
  exact
    H.U.filter fun x =>
      ∀ Y : Finset α,
        HornNF.IsClosed H Y →
        X ⊆ Y →
        x ∈ Y

namespace HornNF

/-- `closure` is closed (fixed) with respect to `HornNF.IsClosed`. -/
theorem closure_isClosed (H : HornNF α) (X : Finset α) :
  HornNF.IsClosed H (H.closure X) := by
  classical
  dsimp [HornNF.IsClosed]
  constructor
  ·
    intro h P hPh hPsub
    -- show `h ∈ H.U.filter ...`
    apply Finset.mem_filter.mpr
    constructor
    · -- h ∈ U
      have : (H.prem h).Nonempty := ⟨P, hPh⟩
      exact H.head_mem_U this
    · -- show: for all closed Y with X ⊆ Y, we have h ∈ Y
      intro Y hYclosed hXY
      have hPY : P ⊆ Y := by
        intro p hpP
        have hp_cl : p ∈ H.closure X := hPsub hpP
        -- unfold membership in closure: p ∈ U and the property
        have hp_prop : ∀ Z : Finset α, HornNF.IsClosed H Z → X ⊆ Z → p ∈ Z :=
          (Finset.mem_filter.mp hp_cl).2
        exact hp_prop Y hYclosed hXY
      --dsimp [HornNF.closure] at hPsub
      dsimp [HornNF.IsClosed] at hYclosed
      rcases hYclosed with ⟨hYclosed1,hYclosed2⟩
      apply @hYclosed1
      · exact hPh
      · simp_all only

  · simp [closure]

/-- `X ⊆ U` implies `X ⊆ closure X` (extensive, as a subset lemma). -/
theorem subset_closure (H : HornNF α) (X : Finset α) (hX : X ⊆ H.U) :
  X ⊆ H.closure X := by
  classical
  intro x hxX
  apply Finset.mem_filter.mpr
  constructor
  · exact hX hxX
  · intro Y hYclosed hXY
    exact hXY hxX

theorem IsClosed_iff (H :HornNF α) (X : Finset α) :
  H.IsClosed X ↔ H.closure X = X := by
  constructor
  · intro h
    dsimp [HornNF.IsClosed] at h
    dsimp [HornNF.closure]
    ext y
    constructor
    ·
      intro a
      simp_all only [Finset.mem_filter]
      obtain ⟨left, right⟩ := a
      apply right
      · exact h
      · simp_all only [subset_refl]
    · intro hY
      simp
      constructor
      · rcases h with ⟨h1,h2⟩
        apply h2
        simp_all only
      ·
        intro Y a a_1
        apply a_1
        simp_all only
  · intro h
    dsimp [HornNF.closure] at h
    constructor
    · intro hh P hP hhP
      rw [←h]
      simp
      constructor
      · have : (H.prem hh).Nonempty := by use P
        let hp := H.head_mem_U this
        simp_all only
      · intro Y hY hXY
        dsimp [HornNF.IsClosed] at hY
        obtain ⟨left, right⟩ := hY
        apply @left
        · exact hP
        · exact hhP.trans hXY

    · rw [←h]
      simp

/-- `closure X` is always a subset of `U` (by definition as a `filter` over `U`). -/
theorem closure_subset_U (H : HornNF α) (X : Finset α) :
  H.closure X ⊆ H.U := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- If `Y` is closed and contains `X`, then `closure X ⊆ Y` (least-closed-superset property). -/
theorem closure_subset_of_subset_isClosed (H : HornNF α)
  {X Y : Finset α} (hXY : X ⊆ Y) (hY : HornNF.IsClosed H Y) :
  H.closure X ⊆ Y := by
  classical
  intro x hx
  have hx_prop : ∀ Z : Finset α, HornNF.IsClosed H Z → X ⊆ Z → x ∈ Z :=
    (Finset.mem_filter.mp hx).2
  exact hx_prop Y hY hXY

/-- Idempotence of `closure` as a set operation. -/
theorem closure_idem (H : HornNF α) (X : Finset α) :
  H.closure (H.closure X) = H.closure X := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    -- use minimality with `Y := closure X`
    have hx_prop : ∀ Z : Finset α, HornNF.IsClosed H Z → H.closure X ⊆ Z → x ∈ Z :=
      (Finset.mem_filter.mp hx).2
    have hClosed : HornNF.IsClosed H (H.closure X) :=
      HornNF.closure_isClosed (H := H) (X := X)
    have hSelf : H.closure X ⊆ H.closure X := by
      intro y hy; exact hy
    exact hx_prop (H.closure X) hClosed hSelf
  · intro hx
    -- `closure X ⊆ closure (closure X)` by extensiveness applied to `closure X ⊆ U`
    have hXU : H.closure X ⊆ H.U := HornNF.closure_subset_U (H := H) (X := X)
    have hExt : H.closure X ⊆ H.closure (H.closure X) :=
      HornNF.subset_closure (H := H) (X := H.closure X) (hX := hXU)
    exact hExt hx

end HornNF


/-!
Binder-name-stable wrapper lemmas

These are small aliases of the core closure facts, but with binder names (`A`)
chosen to match downstream code that uses named arguments. They also avoid
errors of the form “Invalid argument name ...”.
-/

namespace HornNF

/-- `A ⊆ closure H A` provided `A ⊆ H.U` (binder name `A`). -/
theorem subset_closure_A
  (H : HornNF α) (A : Finset α)
  (hA : A ⊆ H.U) :
  A ⊆ HornNF.closure (α := α) H A := by
  simpa using (HornNF.subset_closure (α := α) (H := H) (X := A) (hX := hA))

/-- `closure H A ⊆ H.U` (binder name `A`). -/
theorem closure_subset_U_A
  (H : HornNF α) (A : Finset α) :
  HornNF.closure (α := α) H A ⊆ H.U := by
  simpa using (HornNF.closure_subset_U (α := α) (H := H) (X := A))

/-- Idempotence: `closure H (closure H A) = closure H A` (binder name `A`). -/
theorem closure_idem_A
  (H : HornNF α) (A : Finset α) :
  HornNF.closure (α := α) H (HornNF.closure (α := α) H A)
    = HornNF.closure (α := α) H A := by
  simpa using (HornNF.closure_idem (α := α) (H := H) (X := A))

end HornNF

/-- HornNF induces a closure operator. -/
noncomputable def HornNF.toClosureOperator (H : HornNF α) : ClosureOperator α :=
{ U := H.U
  cl := H.closure

  closed_in_univ := by
    intro X hX x hx
    classical
    exact (Finset.mem_filter.mp hx).1

  extensive := by
    intro X hX x hxX
    classical
    -- x ∈ closure X
    apply Finset.mem_filter.mpr
    constructor
    · exact hX hxX
    · intro Y hYclosed hXY
      exact hXY hxX

  monotone := by
    intro X Y hX hY hXY x hx
    classical
    apply Finset.mem_filter.mpr
    constructor
    · exact (Finset.mem_filter.mp hx).1
    · intro Z hZclosed hYZ
      have hXZ : X ⊆ Z := by
        intro a ha
        exact hYZ (hXY ha)
      exact (Finset.mem_filter.mp hx).2 Z hZclosed hXZ

  idemp := by
    intro X hX
    classical
    apply Finset.ext
    intro x
    constructor
    · -- cl (cl X) ⊆ cl X
      intro hx
      have hx_prop : ∀ Y : Finset α, HornNF.IsClosed H Y → H.closure X ⊆ Y → x ∈ Y :=
        (Finset.mem_filter.mp hx).2
      have h_closed : HornNF.IsClosed H (H.closure X) :=
        HornNF.closure_isClosed (H := H) (X := X)
      have h_self : H.closure X ⊆ H.closure X := by intro y hy; exact hy
      exact hx_prop (H.closure X) h_closed h_self
    · -- cl X ⊆ cl (cl X)
      intro hx
      apply Finset.mem_filter.mpr
      constructor
      · exact (Finset.mem_filter.mp hx).1
      · intro Y hYclosed hYcl
        -- from X ⊆ cl X and cl X ⊆ Y, we get X ⊆ Y
        have hXcl : X ⊆ H.closure X := HornNF.subset_closure (H := H) (X := X) hX
        have hXY : X ⊆ Y := by
          intro a ha
          exact hYcl (hXcl ha)
        exact (Finset.mem_filter.mp hx).2 Y hYclosed hXY
}

end Dr1nds
