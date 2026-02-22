import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Dr1nds.Horn.Horn   -- HornNF
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.HornContraction
import Dr1nds.Horn.HornClosure
import Dr1nds.Forbid.Basic

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-
============================================================
  HornWithForbid (DR1 固定バージョン)

  意味：
    DR1 Horn 系 + ちょうど1つの forbid 閉集合
============================================================
-/

structure HornWithForbid (α : Type) [DecidableEq α] where
  H : HornNF α
  hDR1 : H.IsDR1
  hNEP : H.IsNEP

  F : Finset α                    -- forbid set
  F_subset_U : F ⊆ H.U
  F_nonempty : F.Nonempty


attribute [simp] HornWithForbid.F_subset_U
namespace HornWithForbid

noncomputable def FixSet
  (S : HornWithForbid α) :
  Finset (Finset α) :=
  (HornNF.FixSet S.H).filter
    (fun X => ¬ S.F ⊆ X)

/- ------------------------------------------------------------
  FixSet
------------------------------------------------------------ -/



@[simp] lemma mem_FixSet_withForbid_iff
  (S : HornWithForbid α)
  (X : Finset α) :
  X ∈ S.FixSet
  ↔
  X ∈ HornNF.FixSet S.H ∧ ¬ S.F ⊆ X := by
  classical
  simp [HornWithForbid.FixSet]

lemma mem_FixSet_withForbid_subset_U
  (S : HornWithForbid α)
  {X : Finset α}
  (hX : X ∈ S.FixSet) :
  X ⊆ S.H.U := by
  classical
  have h := (mem_FixSet_withForbid_iff S X).1 hX
  -- use underlying HornNF property
  exact mem_FixSet_subset_U S.H h.1


end HornWithForbid

/--
Contract a `HornWithForbid` system at a point `v`.

This operation is defined when the resulting forbid set `F.erase v` is non-empty,
and `v` is a singleton-closed (SC) point of the forbidden family `S.FixSet`.
-/
def HornWithForbid.contraction (S : HornWithForbid α) (v : α)
  (h_nonempty : (S.F.erase v).Nonempty)
  (h_sc : {v} ∈ S.FixSet) : HornWithForbid α :=
  { H := S.H.contraction v
    hDR1 := HornNF.contraction_preserves_DR1 S.H S.hDR1 v
    hNEP := by
      dsimp [HornNF.IsNEP]
      intro h P
      dsimp [HornNF.contraction] at P
      by_cases hv:h = v
      ·
        rename_i h_1
        simp_all only [mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset,
          Finset.singleton_subset_iff, Finset.subset_singleton_iff, not_or, ↓reduceIte, Finset.notMem_empty]
      ·
        simp_all only [mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset,
          Finset.singleton_subset_iff, Finset.subset_singleton_iff, not_or, ↓reduceIte,
          Finset.mem_image]
        obtain ⟨a,ha⟩ := P
        have : a ≠ ∅ := by
          intro hcon
          rw [hcon] at ha
          simp [S.hNEP] at ha
        have : a ⊆ {v} := by
          let ha2 := ha.2
          (expose_names; rw [Finset.erase_eq_empty_iff] at ha2)
          simp_all only [ne_eq, false_or, subset_refl]
        have : a = {v} := by
          simp_all only [ne_eq, Finset.subset_singleton_iff, false_or]
        rw [this] at ha
        let cond1 := h_sc.1
        dsimp [HornNF.IsClosed] at cond1
        have : v ∈ S.H.U := by
          subst this
          simp_all only [Finset.erase_singleton, and_true, ne_eq, Finset.singleton_ne_empty, not_false_eq_true,
            subset_refl]
        rcases cond1 with ⟨cond11,cond12⟩
        simp at cond12
        let ha1 := ha.1
        have hv_eq : h = v := by
        -- cond12 に P = {v} を入れる
          exact cond12 (h := h) (P := ({v} : Finset α)) ha1 (Or.inr rfl)
        exact hv hv_eq

    F := S.F.erase v
    F_subset_U := by
      dsimp [HornNF.contraction]
      have : S.F ⊆ S.H.U := by exact S.F_subset_U
      exact Finset.erase_subset_erase v this
    F_nonempty := h_nonempty
  }

@[simp] theorem contract_H (S : HornWithForbid α) (v : α)
  (h_nonempty : (S.F.erase v).Nonempty)
  (h_sc : {v} ∈ S.FixSet) :
  (S.contraction v h_nonempty h_sc).H = S.H.contraction v := rfl

@[simp] theorem contract_F (S : HornWithForbid α) (v : α)
  (h_nonempty : (S.F.erase v).Nonempty)
  (h_sc : {v} ∈S.FixSet) :
  (S.contraction v h_nonempty h_sc).F = S.F.erase v := rfl

/--
The `FixSet` of a contracted `HornWithForbid` system is the contraction of its original `FixSet`.
-/
theorem contract_FixSet_eq (S : HornWithForbid α) (v : α)
  (h_nonempty : (S.F.erase v).Nonempty)
  (h_sc : {v} ∈ S.FixSet) :
  (S.contraction v h_nonempty h_sc).FixSet = Con v S.FixSet := by
  classical
  have hvU : v ∈ S.H.U := by
    have hsingleton : ({v} : Finset α) ∈ HornNF.FixSet S.H :=
      (HornWithForbid.mem_FixSet_withForbid_iff S {v}).1 h_sc |>.1
    have hpow : ({v} : Finset α) ∈ S.H.U.powerset := (mem_FixSet_iff S.H {v}).1 hsingleton |>.1
    have hsubset : ({v} : Finset α) ⊆ S.H.U := by
      simpa [Finset.mem_powerset] using hpow
    exact hsubset (by simp)
  ext X
  constructor
  · intro hX
    have hXmem : X ∈ HornNF.FixSet (S.H.contraction v) :=
      (HornWithForbid.mem_FixSet_withForbid_iff (S.contraction v h_nonempty h_sc) X).1 hX |>.1
    have hXnot : ¬ S.F.erase v ⊆ X :=
      (HornWithForbid.mem_FixSet_withForbid_iff (S.contraction v h_nonempty h_sc) X).1 hX |>.2
    have hXcon : X ∈ Con v (HornNF.FixSet S.H) := by
      have hEq := contraction_fix_equiv (H := S.H) (x := v) hvU
      simpa [HornWithForbid.contraction, hEq] using hXmem
    rcases Finset.mem_image.mp hXcon with ⟨Y, hYfilt, hYX⟩
    rcases Finset.mem_filter.mp hYfilt with ⟨hYfix, hvY⟩
    have hYnotF : ¬ S.F ⊆ Y := by
      intro hFsubY
      apply hXnot
      intro z hz
      have hz' := Finset.mem_erase.mp hz
      have hzYerase : z ∈ Y.erase v := Finset.mem_erase.mpr ⟨hz'.1, hFsubY hz'.2⟩
      simpa [hYX] using hzYerase
    have hYmem : Y ∈ S.FixSet :=
      (HornWithForbid.mem_FixSet_withForbid_iff S Y).2 ⟨hYfix, hYnotF⟩
    apply Finset.mem_image.mpr
    refine ⟨Y, ?_, hYX⟩
    exact Finset.mem_filter.mpr ⟨hYmem, hvY⟩
  · intro hX
    rcases Finset.mem_image.mp hX with ⟨Y, hYfilt, hYX⟩
    rcases Finset.mem_filter.mp hYfilt with ⟨hYmem, hvY⟩
    have hYbase : Y ∈ HornNF.FixSet S.H :=
      (HornWithForbid.mem_FixSet_withForbid_iff S Y).1 hYmem |>.1
    have hYnotF : ¬ S.F ⊆ Y :=
      (HornWithForbid.mem_FixSet_withForbid_iff S Y).1 hYmem |>.2
    have hXconBase : X ∈ Con v (HornNF.FixSet S.H) := by
      apply Finset.mem_image.mpr
      refine ⟨Y, Finset.mem_filter.mpr ⟨hYbase, hvY⟩, hYX⟩
    have hXmem : X ∈ HornNF.FixSet (S.H.contraction v) := by
      have hEq := contraction_fix_equiv (H := S.H) (x := v) hvU
      simpa [HornWithForbid.contraction, hEq] using hXconBase
    have hXnot : ¬ S.F.erase v ⊆ X := by
      intro hEraseSub
      apply hYnotF
      intro s hs
      by_cases hsv : s = v
      · simpa [hsv] using hvY
      · have hsErase : s ∈ S.F.erase v := Finset.mem_erase.mpr ⟨hsv, hs⟩
        have hsX : s ∈ X := hEraseSub hsErase
        have hsYerase : s ∈ Y.erase v := by simpa [hYX] using hsX
        exact (Finset.mem_erase.mp hsYerase).2
    exact (HornWithForbid.mem_FixSet_withForbid_iff (S.contraction v h_nonempty h_sc) X).2
      ⟨hXmem, hXnot⟩



/- ------------------------------------------------------------
  基本補題
------------------------------------------------------------ -/

/-- `HornWithForbid.FixSet` is exactly the `Hole` of the underlying `HornNF.FixSet`. -/
lemma FixSet_eq_Hole_FixSet
  (S : HornWithForbid α) :
  S.FixSet = Hole (α := α) (HornNF.FixSet S.H) S.F := by
  classical
  simp [HornWithForbid.FixSet, Hole]

/-- `SetFamily.NEP` for the forbid-family `S.FixSet` is definitionally `∅ ∈ S.FixSet`. -/
lemma nep_iff_empty_mem_FixSet
  (S : HornWithForbid α) :
  SetFamily.NEP (
   { U := S.H.U, C := S.FixSet, subset_univ := by
      intro X hX
      -- FixSet members are subsets of U
      simp_all only [HornWithForbid.mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
   }
     : SetFamily α
    )
    ↔ (∅ : Finset α) ∈ S.FixSet := by
  rfl

/-- If the forbid-family `S.FixSet` is `NEP`, then `∅ ∈ S.FixSet`. -/
lemma empty_mem_of_nep_FixSet
  (S : HornWithForbid α)
  (h : SetFamily.NEP (
   { U := S.H.U, C := S.FixSet, subset_univ := by
      intro X hX
      -- FixSet members are subsets of U
      simp_all only [HornWithForbid.mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
   }
     : SetFamily α
    )) :
  (∅ : Finset α) ∈ S.FixSet := by
  simpa [SetFamily.NEP] using h

/-- `SetFamily.NEP` for the base family `HornNF.FixSet S.H` is definitionally `∅ ∈ HornNF.FixSet S.H`. -/
lemma nep_iff_empty_mem_base
  (S : HornWithForbid α) :
  SetFamily.NEP (
   { U := S.H.U, C := HornNF.FixSet S.H, subset_univ := by
      intro X hX
      -- FixSet members are subsets of U
      simpa using (mem_FixSet_subset_U (H := S.H) (X := X) hX)
   }
     : SetFamily α
    )
    ↔ (∅ : Finset α) ∈ HornNF.FixSet S.H := by
  rfl

/-- If `A` is nonempty, then adding the forbid via `Hole` does not change whether `∅` is present. -/
lemma empty_mem_Hole_iff
  (C : Finset (Finset α)) (A : Finset α) (hA : A.Nonempty) :
  (∅ : Finset α) ∈ Hole (α := α) C A ↔ (∅ : Finset α) ∈ C := by
  classical
  have hnot : ¬ A ⊆ (∅ : Finset α) := by
    rcases hA with ⟨a, haA⟩
    intro hsub
    have : a ∈ (∅ : Finset α) := hsub haA
    exact (List.mem_nil_iff a).mp (hsub haA)
  simp [Hole, hnot]



/-- In particular, for `HornWithForbid`, `F.Nonempty` implies `∅ ∈ S.FixSet ↔ ∅ ∈ HornNF.FixSet S.H`. -/
lemma empty_mem_FixSet_iff_empty_mem_base
  (S : HornWithForbid α) :
  (∅ : Finset α) ∈ S.FixSet ↔ (∅ : Finset α) ∈ HornNF.FixSet S.H := by
  classical
  -- `S.FixSet = Hole (FixSet) S.F` and `S.F` is nonempty.
  simpa [FixSet_eq_Hole_FixSet (α := α) S] using
    (empty_mem_Hole_iff (α := α) (C := HornNF.FixSet S.H) (A := S.F) S.F_nonempty).symm

/-- A convenient rewriting lemma for membership in `Hole (FixSet ...)`. -/
lemma mem_Hole_FixSet_iff
  (H : HornNF α) (A X : Finset α) :
  X ∈ Hole (α := α) (HornNF.FixSet H) A
    ↔ X ∈ HornNF.FixSet H ∧ ¬ A ⊆ X := by
  classical
  simp [Hole]

/-- For closed `X`, testing `A ⊆ X` is equivalent to testing `closure(A) ⊆ X`.

This requires `A ⊆ U` so that `A ⊆ closure(A)` holds. -/
lemma closure_subset_iff_subset_of_isClosed
  (H : HornNF α) (A X : Finset α)
  (hA : A ⊆ H.U)
  (hXclosed : HornNF.IsClosed H X) :
  HornNF.closure H A ⊆ X ↔ A ⊆ X := by
  classical
  constructor
  · intro hcl a ha
    -- A ⊆ closure(A) ⊆ X
    have : a ∈ HornNF.closure H A :=
      (HornNF.subset_closure (H := H) (X := A) hA) ha
    exact hcl this
  · intro hAX x hx
    -- unfold membership in `closure`
    have hx_prop : ∀ Y : Finset α, HornNF.IsClosed H Y → A ⊆ Y → x ∈ Y :=
      (Finset.mem_filter.mp hx).2
    exact hx_prop X hXclosed hAX

/-- On a closed family (in particular `FixSet`), forbidding `A` is the same as forbidding `closure(A)`.

We assume `A ⊆ U` so that `A ⊆ closure(A)` is available. -/
lemma Hole_FixSet_eq_Hole_FixSet_closure
  (H : HornNF α) (A : Finset α)
  (hA : A ⊆ H.U) :
  Hole (α := α) (HornNF.FixSet H) (HornNF.closure H A)
    = Hole (α := α) (HornNF.FixSet H) A := by
  classical
  ext X
  constructor <;> intro hX
  · -- →
    have hmem := (mem_Hole_FixSet_iff (α := α) H (HornNF.closure H A) X).1 hX
    refine (mem_Hole_FixSet_iff (α := α) H A X).2 ?_
    refine ⟨hmem.1, ?_⟩
    intro hAX
    have hXclosed : HornNF.IsClosed H X := (mem_FixSet_iff H X).1 hmem.1 |>.2
    have hcl : HornNF.closure H A ⊆ X :=
      (closure_subset_iff_subset_of_isClosed (α := α) H A X hA hXclosed).2 hAX
    exact hmem.2 hcl
  · -- ←
    have hmem := (mem_Hole_FixSet_iff (α := α) H A X).1 hX
    refine (mem_Hole_FixSet_iff (α := α) H (HornNF.closure H A) X).2 ?_
    refine ⟨hmem.1, ?_⟩
    intro hcl
    have hXclosed : HornNF.IsClosed H X := (mem_FixSet_iff H X).1 hmem.1 |>.2
    have hAX : A ⊆ X :=
      (closure_subset_iff_subset_of_isClosed (α := α) H A X hA hXclosed).1 hcl
    exact hmem.2 hAX

/-
lemma NDS_corr_eq_of_closure (n : Nat) (H : HornNF α) (A : Finset α) (hA : A ⊆ H.U) :
  NDS_corr n (FixSet H) (closure H A) = NDS_corr n (FixSet H) A := by
  have h_hole_eq : Hole (FixSet H) (closure H A) = Hole (FixSet H) A :=
    Hole_FixSet_eq_Hole_FixSet_closure H A hA
  have h_up_eq : Up (FixSet H) (closure H A) = Up (FixSet H) A := by
    ext X
    constructor <;> intro hX
    · cases' Finset.mem_filter.mp hX with hX_in_FixSet h_cls_sub_X
      have hX_closed := (mem_FixSet_iff H X).mp hX_in_FixSet |>.2
      have hA_sub_X := (closure_subset_iff_subset_of_isClosed H A X hA hX_closed).mp h_cls_sub_X
      exact Finset.mem_filter.mpr ⟨hX_in_FixSet, hA_sub_X⟩
    · cases' Finset.mem_filter.mp hX with hX_in_FixSet hA_sub_X
      have hX_closed := (mem_FixSet_iff H X).mp hX_in_FixSet |>.2
      have h_cls_sub_X := (closure_subset_iff_subset_of_isClosed H A X hA hX_closed).mpr hA_sub_X
      exact Finset.mem_filter.mpr ⟨hX_in_FixSet, h_cls_sub_X⟩
  simp [NDS_corr, h_hole_eq, h_up_eq]
  -/

/-- `Up` and `Hole` form a partition of a family (cardinality version). -/
lemma card_up_add_card_hole_eq_card
  (C : Finset (Finset α)) (A : Finset α) :
  (Up (α := α) C A).card + (Hole (α := α) C A).card = C.card := by
  classical
  -- `Up` is `filter (A ⊆ ·)` and `Hole` is its negation.
  simpa [Up, Hole] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := C) (p := fun X => A ⊆ X))

/-- The `Int`-coerced version of `card_up_add_card_hole_eq_card`. -/
lemma int_card_up_add_card_hole_eq_card
  (C : Finset (Finset α)) (A : Finset α) :
  ((Up (α := α) C A).card : Int) + (Hole (α := α) C A).card = (C.card : Int) := by
  classical
  -- coerce the Nat identity to Int
  exact_mod_cast (card_up_add_card_hole_eq_card (α := α) C A)

/-- If `F ⊆ U` and `v ∉ F`, then `F ⊆ U.erase v`. -/
lemma subset_erase_of_subset
  {U F : Finset α} {v : α} :
  F ⊆ U → v ∉ F → F ⊆ U.erase v := by
  intro hFU hvF x hx
  refine Finset.mem_erase.mpr ?_
  constructor
  · intro hxv
    subst hxv
    exact hvF hx
  · exact hFU hx

/-- A small helper: from `P ⊆ (H.trace v).U` we get `P ⊆ H.U` (forgetting the erase). -/
lemma subset_U_of_subset_traceU
  (H : HornNF α) (v : α) {P : Finset α} :
  P ⊆ (H.trace v).U → P ⊆ H.U := by
  intro hP x hx
  have hx' : x ∈ (H.trace v).U := hP hx
  exact (Finset.mem_erase.mp hx').2


/-- NEP is preserved when passing between the base family `HornNF.FixSet S.H`
    and the forbid family `S.FixSet` (since `S.F` is nonempty). -/
lemma nep_FixSet_iff_nep_base
  (S : HornWithForbid α) :
  SetFamily.NEP (
    { U := S.H.U
      C := S.FixSet
      subset_univ := by
        intro X hX
        -- FixSet members are subsets of U
        simp_all only [HornWithForbid.mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
    } : SetFamily α)
  ↔
  SetFamily.NEP (
    { U := S.H.U
      C := HornNF.FixSet S.H
      subset_univ := by
        intro X hX
        -- FixSet members are subsets of U
        simpa using (mem_FixSet_subset_U (H := S.H) (X := X) hX)
    } : SetFamily α) := by
  classical
  constructor
  · intro hNEP_forbid
    have hempty_forbid : (∅ : Finset α) ∈ S.FixSet :=
      empty_mem_of_nep_FixSet (α := α) S hNEP_forbid
    have hempty_base : (∅ : Finset α) ∈ HornNF.FixSet S.H :=
      (empty_mem_FixSet_iff_empty_mem_base (α := α) S).1 hempty_forbid
    -- base NEP is definitional `∅ ∈ base`
    simp [SetFamily.NEP]
    simp_all only [HornWithForbid.mem_FixSet_withForbid_iff, Finset.subset_empty, true_and, mem_FixSet_iff,
      Finset.mem_powerset, Finset.empty_subset]
  · intro hNEP_base
    -- base NEP is definitional `∅ ∈ base`
    have hempty_base : (∅ : Finset α) ∈ HornNF.FixSet S.H := by
      simpa [SetFamily.NEP] using hNEP_base
    have hempty_forbid : (∅ : Finset α) ∈ S.FixSet :=
      (empty_mem_FixSet_iff_empty_mem_base (α := α) S).2 hempty_base
    -- forbid NEP is definitional `∅ ∈ forbid`
    simpa [SetFamily.NEP] using hempty_forbid


/-- A convenient corollary: `S.FixSet` is NEP iff `∅` is in the base `FixSet`. -/
lemma nep_FixSet_iff_empty_mem_base
  (S : HornWithForbid α) :
  SetFamily.NEP (
    { U := S.H.U
      C := S.FixSet
      subset_univ := by
        intro X hX
        -- FixSet members are subsets of U
        simp_all only [HornWithForbid.mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
    } : SetFamily α)
  ↔ (∅ : Finset α) ∈ HornNF.FixSet S.H := by
  classical
  -- unfold NEP on the forbid side, then rewrite emptiness via the Hole characterization
  have h1 :
      SetFamily.NEP (
        { U := S.H.U
          C := S.FixSet
          subset_univ := by
            intro X hX
            simp_all only [HornWithForbid.mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
        } : SetFamily α)
      ↔ (∅ : Finset α) ∈ S.FixSet := by
    rfl
  have h2 : (∅ : Finset α) ∈ S.FixSet ↔ (∅ : Finset α) ∈ HornNF.FixSet S.H :=
    empty_mem_FixSet_iff_empty_mem_base (α := α) S
  simpa [h1] using h2

/-
============================================================
  NDS (for future use)
============================================================
-/

/-- Base closed family (without forbidding), extracted from `HornWithForbid`. -/
noncomputable def HornWithForbid.BaseC
  (S : HornWithForbid α) : Finset (Finset α) :=
  HornNF.FixSet S.H

/-- Up-set used in corrected NDS, computed in the base family. -/
noncomputable def HornWithForbid.UpBase
  (S : HornWithForbid α) : Finset (Finset α) :=
  Up (α := α) (HornWithForbid.BaseC (α := α) S) S.F

/-- Corrected NDS computed directly from `HornWithForbid` data.

This is just the core `Dr1nds.NDS_corr` applied to
`C := HornWithForbid.BaseC S` and `A := S.F`.
-/
noncomputable def HornWithForbid.NDS_corr
  (n : Nat) (S : HornWithForbid α) : Int :=
  Dr1nds.NDS_corr (α := α) n (HornWithForbid.BaseC (α := α) S) S.F

noncomputable def HornWithForbid.NDS
  (S : HornWithForbid α) : Int :=
  Dr1nds.NDS (α := α) S.H.U.card S.FixSet

end Dr1nds
