import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Dr1nds.S0_CoreDefs
import Dr1nds.S1_Families
import Dr1nds.Horn.Horn   -- HornNF
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.HornClosure
import LeanCopilot

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

/--
Trace the underlying Horn system at `a` and **replace** the forbid set by `Pprem`.

IMPORTANT:
`HornWithForbid` requires the forbid set to satisfy:
- `Pprem ⊆ (S.H.trace a).U`
- `Pprem.Nonempty`

So this constructor takes these obligations as explicit arguments.
This removes the need for axiom-level APIs.
-/
noncomputable def traceWithPrem
  (S : HornWithForbid α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (S.H.trace a).U)
  (hPne : Pprem.Nonempty) : HornWithForbid α :=
  { H := S.H.trace a
    hDR1 := by
      -- DR1 is preserved by trace (proved in the Horn layer).
      have hDR1' : HornNF.DR1 S.H := by
        simpa [HornNF.IsDR1, HornNF.DR1] using S.hDR1
      have hDR1'' : HornNF.DR1 (S.H.trace a) :=
        HornNF.trace_preserves_DR1 (H := S.H) (u := a) hDR1'
      simpa [HornNF.IsDR1, HornNF.DR1] using hDR1''
    hNEP := by
      -- NEP is preserved by trace (proved in the Horn layer).
      let tp := HornNF.trace_preserves_NEP' S.H a
      have :S.H.IsNEP := by
        dsimp [HornNF.IsNEP]
        simp [S.hNEP ]
      simp_all only
    F := Pprem
    F_subset_U := hPsub
    F_nonempty := hPne
  }

@[simp] theorem traceWithPrem_H
  (S : HornWithForbid α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (S.H.trace a).U)
  (hPne : Pprem.Nonempty) :
  (traceWithPrem (α := α) S a Pprem hPsub hPne).H = S.H.trace a := by
  rfl

@[simp] theorem traceWithPrem_F
  (S : HornWithForbid α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (S.H.trace a).U)
  (hPne : Pprem.Nonempty) :
  (traceWithPrem (α := α) S a Pprem hPsub hPne).F = Pprem := by
  rfl


/-!
`HornWithForbid` requires the forbid set to be closed.

In the singleton-forbid has-head branch, the natural new forbid set is not the raw
premise `Praw` but its closure in the traced Horn system:

  `Pprem := closure_{S.H.trace a}(Praw)`.

This wrapper constructs the obligations internally.

NOTE: Replacing `Praw` by `closure(Praw)` does **not** change the resulting
forbid-family *when we filter a closed family* (e.g. `HornNF.FixSet`), because for
closed `X` we have `Praw ⊆ X ↔ closure(Praw) ⊆ X`. A lemma for this equivalence is
added below.
-/
noncomputable def traceWithPremClosure
  (S : HornWithForbid α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (S.H.trace a).U)
  (hPne : Praw.Nonempty) : HornWithForbid α := by
  classical
  let Pprem : Finset α := HornNF.closure (S.H.trace a) Praw

  -- closure is always inside the universe because it is defined by `U.filter _`
  have hPsub' : Pprem ⊆ (S.H.trace a).U := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1

  -- nonempty is preserved because `Praw ⊆ closure(Praw)` when `Praw ⊆ U`
  have hPne' : Pprem.Nonempty := by
    rcases hPne with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact (HornNF.subset_closure (H := (S.H.trace a)) (X := Praw) hPsub) hx

  exact traceWithPrem (α := α) S a Pprem hPsub' hPne'

@[simp] theorem traceWithPremClosure_H
  (S : HornWithForbid α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (S.H.trace a).U)
  (hPne : Praw.Nonempty) :
  (traceWithPremClosure (α := α) S a Praw hPsub hPne).H = S.H.trace a := by
  classical
  simp [traceWithPremClosure]

@[simp] theorem traceWithPremClosure_F
  (S : HornWithForbid α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (S.H.trace a).U)
  (hPne : Praw.Nonempty) :
  (traceWithPremClosure (α := α) S a Praw hPsub hPne).F
    = HornNF.closure (S.H.trace a) Praw := by
  classical
  simp [traceWithPremClosure]

attribute [simp] traceWithPremClosure_H traceWithPremClosure_F


/- ------------------------------------------------------------
  FixSet
------------------------------------------------------------ -/

noncomputable def HornWithForbid.FixSet
  (S : HornWithForbid α) :
  Finset (Finset α) :=
  (HornNF.FixSet S.H).filter
    (fun X => ¬ S.F ⊆ X)

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
      simp_all only [mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
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
      simp_all only [mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
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
    simpa using this
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
  · intro hcl
    -- A ⊆ closure(A) ⊆ X
    intro a ha
    have : a ∈ HornNF.closure H A :=
      (HornNF.subset_closure (H := H) (X := A) hA) ha
    exact hcl this
  · intro hAX
    -- minimality of closure: any closed superset contains the closure
    intro x hx
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
        simp_all only [mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
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
    simp_all only [mem_FixSet_withForbid_iff, Finset.subset_empty, true_and, mem_FixSet_iff, Finset.mem_powerset,
      Finset.empty_subset]
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
        simp_all only [mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
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
            simp_all only [mem_FixSet_withForbid_iff, mem_FixSet_iff, Finset.mem_powerset]
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


/-
============================================================
  Placeholder: deletion representation theorem

  これが最重要ブリッジ補題になる。
============================================================
-/


lemma deletion_filter_equiv
  (H : HornNF α)
  (hDR1 : H.IsDR1)
  (v : α)
  (P : Finset α)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  (X : Finset α) :
  X ∈ (HornNF.FixSet H).filter (fun X => v ∉ X)
  ↔
  X ∈ (H.trace v).FixSet ∧ ¬ P ⊆ X := by
  classical
  constructor

  ----------------------------------------------------------------
  -- → direction
  ----------------------------------------------------------------
  · intro h
    have hmem := Finset.mem_filter.mp h
    have hFix := hmem.1
    have hvX := hmem.2

    have hFix_data := (mem_FixSet_iff H X).mp hFix
    have hsubU := hFix_data.1
    have ⟨hsubU, hClosed⟩ := hFix_data

    --------------------------------------------------------------
    -- 1. ¬ P ⊆ X
    --------------------------------------------------------------
    have hNotP : ¬ P ⊆ X := by
      intro hPX
      have hv : v ∈ X := by
        apply hClosed
        · exact hP
        · exact hPX
      exact hvX hv

    --------------------------------------------------------------
    -- 2. trace で閉
    --------------------------------------------------------------
    have hTraceClosed :
      HornNF.IsClosed (H.trace v) X := by
      unfold HornNF.IsClosed
      intro h Q hQ hQsub

      by_cases h_eq_v : h = v
      · subst h_eq_v
        -- trace.prem v = ∅
        simp [HornNF.trace] at hQ

      · -- h ≠ v
        simp [HornNF.trace, h_eq_v] at hQ
        rcases hQ with ⟨⟨Q₀, hQ₀, hcase⟩, _⟩

        by_cases hvQ₀ : v ∈ Q₀
        · -- composite rule
          simp [hvQ₀] at hcase
          rcases hcase with ⟨Pu, hPu, hEq⟩
          subst hEq

          -- DR1 で Pu = P
          have h_single :
            ∀ Q ∈ H.prem v, Q = P := by
            have hcard := Finset.card_eq_one.mp hUnique
            intro Q hQv
            obtain ⟨a, ha⟩ := hcard
            have hQ' : Q = a := by simpa [ha] using hQv
            have hP' : P = a := by simpa [ha] using hP
            exact hQ'.trans hP'.symm

          have hPu_eq : Pu = P := h_single Pu hPu
          subst hPu_eq

          ------------------------------------------------------------
          -- Q₀.erase v ⊆ X
          ------------------------------------------------------------
          have hQ₀sub :
            Q₀.erase v ⊆ X := by
            intro x hx
            rename_i right
            simp_all only [Finset.mem_filter, not_false_eq_true, and_self, mem_FixSet_iff, Finset.mem_powerset,
              Finset.mem_union, Finset.mem_erase, ne_eq, true_and, not_or]
            obtain ⟨left, right⟩ := right
            obtain ⟨left_1, right_1⟩ := hx
            apply hQsub
            simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, not_false_eq_true, and_self, true_or]

          ------------------------------------------------------------
          -- Q₀ ⊆ X
          ------------------------------------------------------------
          have hQ₀sub_full :
            Q₀ ⊆ X := by
            intro x hxQ₀
            by_cases h_eq_v : h = v
            · cases h_eq_v
              -- v ∈ X を導いて矛盾
              have hv_mem : v ∈ X := by
                apply hClosed hQ₀
                intro y hy
                by_cases hyv : y = v
                · subst hyv
                  exact False.elim (h_eq_v rfl)
                · have hy' : y ∈ Q₀.erase v :=
                    Finset.mem_erase.mpr ⟨hyv, hy⟩
                  exact hQ₀sub hy'
              exact False.elim (hvX hv_mem)
            · have hx' : x ∈ Q₀.erase v := by
                apply Finset.mem_erase.mpr
                rw [← @Finset.notMem_singleton]
                simp
                constructor
                · show ¬x = v
                  intro hxv
                  subst hxv
                  exact hNotP (Finset.subset_union_right.trans hQsub)
                · simp_all only [Finset.mem_filter, not_false_eq_true, and_self, mem_FixSet_iff, Finset.mem_powerset,
                  Finset.mem_union, Finset.mem_erase, ne_eq, true_and, not_or]
                --   ⟨hxv, hxQ₀⟩
              exact hQ₀sub hx'

          ------------------------------------------------------------
          -- 閉性適用
          ------------------------------------------------------------
          exact hClosed hQ₀ hQ₀sub_full

        · -- ordinary rule
          simp [hvQ₀] at hcase
          subst hcase
          exact hClosed hQ₀ hQsub

    --------------------------------------------------------------
    -- universe 部分
    --------------------------------------------------------------
    have hsubU_pow := hFix_data.1
    have hsubU : X ⊆ H.U :=
      Finset.mem_powerset.mp hsubU_pow

    have hsubU' : X ⊆ (H.trace v).U := by
      intro x hx
      have hxU := hsubU hx
      have hxv : x ≠ v := by
        intro hxeq; subst hxeq; exact hvX hx
      simpa [HornNF.trace] using
        Finset.mem_erase.mpr ⟨hxv, hxU⟩

    have hTraceFix :
      X ∈ (H.trace v).FixSet := by
      apply (mem_FixSet_iff (H.trace v) X).mpr
      have hpow :
        X ∈ (H.trace v).U.powerset :=
        Finset.mem_powerset.mpr hsubU'
      exact ⟨hpow, hTraceClosed⟩

    exact ⟨hTraceFix, hNotP⟩

  ----------------------------------------------------------------
  -- ← direction
  ----------------------------------------------------------------
  · intro h
    have hTraceFix := h.1
    have hNotP := h.2

    have hTraceData :=
      (mem_FixSet_iff (H.trace v) X).mp hTraceFix
    have hsubU' := hTraceData.1
    have hTraceClosed :
      HornNF.IsClosed (H.trace v) X :=
      hTraceData.2

    --------------------------------------------------------------
    -- v ∉ X
    --------------------------------------------------------------
    have hvX : v ∉ X := by
      intro hv
      have := Finset.mem_powerset.mp hsubU' hv
      simp [HornNF.trace] at this


    --------------------------------------------------------------
    -- H で閉
    --------------------------------------------------------------
    have hClosed :
      HornNF.IsClosed H X := by
      unfold HornNF.IsClosed
      intro h Q hQ hQsub

      by_cases h_eq_v : h = v
      · --subst h_eq_v
        -- Q = P
        have h_single :
          ∀ Q ∈ H.prem v, Q = P := by
          have hcard := Finset.card_eq_one.mp hUnique
          intro Q hQv
          obtain ⟨a, ha⟩ := hcard
          have hQ' :
            Q = a := by
            simpa [ha] using hQv
          have hP' :
            P = a := by
            simpa [ha] using hP
          exact hQ'.trans hP'.symm

        have hQeq : Q = P := by
          subst h_eq_v
          simp_all only [not_false_eq_true]
        subst hQeq
        exfalso
        exact hNotP hQsub

      · -- h ≠ v
        have hQ_trace :
          Q ∈ (H.trace v).prem h := by
          simp [HornNF.trace, h_eq_v]
          by_cases hvQ : v ∈ Q
          · -- v ∈ Q and Q ⊆ X would give v ∈ X, contradicting hvX
            exfalso; exact hvX (hQsub hvQ)
          · -- v ∉ Q: Q is unchanged in trace, and h ∉ Q by NF
            exact ⟨⟨Q, hQ, by simp [hvQ]⟩, H.nf hQ⟩

        simp_all only [not_false_eq_true, and_self, mem_FixSet_iff, Finset.mem_powerset]
        apply hTraceClosed
        on_goal 2 => { exact hQsub
        }
        · simp_all only

    have hFix :
      X ∈ HornNF.FixSet H := by
      apply (mem_FixSet_iff H X).mpr
      have hsubU : X ⊆ H.U := by
        intro x hx
        have hsubU : X ⊆ H.U := by
          intro x hx
          have hxU : x ∈ (H.trace v).U :=
            Finset.mem_powerset.mp hsubU' hx
          exact (Finset.mem_erase.mp hxU).2
        exact hsubU hx

      have hpow :
        X ∈ H.U.powerset :=
        Finset.mem_powerset.mpr hsubU
      exact ⟨hpow, hClosed⟩

    apply Finset.mem_filter.mpr
    exact ⟨hFix, hvX⟩


/--
A usable (proved) version of `deletion_as_forbid`.

To build a `HornWithForbid` object we must supply the extra structure fields
for the forbid set `P` in the trace world (`P ⊆ (H.trace v).U`, `P.Nonempty`, and
`IsClosed (H.trace v) P`). In the singleton-proof wiring these are typically
provided from NF/DR1 lemmas and the chosen-premise facts.

This theorem is the *actual* bridge used to identify the deletion-filtered family
with the forbid FixSet in the trace world.
-/
theorem deletion_as_forbid'
  (H : HornNF α)
  (hDR1 : H.IsDR1)
  (hNEP: H.IsNEP)
  (v : α)
  (P : Finset α)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  (hPsub : P ⊆ (H.trace v).U)
  (hPne : P.Nonempty)
  :
  ∃ S : HornWithForbid α,
    S.H = H.trace v ∧
    S.F = P ∧
    S.FixSet = (HornNF.FixSet H).filter (fun X => v ∉ X) := by
  classical
  -- build the forbid structure on the trace world
  let S : HornWithForbid α :=
    { H := H.trace v
      hDR1 := by
        -- If you have a lemma `HornNF.trace_preserves_DR1`, replace this with it.
        -- For now we keep it as a local assumption via `hDR1` if needed.
        -- (Most developments already have `trace_preserves_DR1`.)
        let hn := HornNF.trace_preserves_DR1 (H := H) (hDR1 := hDR1)
        apply hn
      hNEP := by
        (expose_names; exact @HornNF.isNEP_trace_of_isNEP α inst H v hNEP)
      F := P
      F_subset_U := hPsub
      F_nonempty := hPne }

  refine ⟨S, rfl, rfl, ?_⟩

  -- Extensional equality using the membership characterization.
  ext X
  -- unfold `S.FixSet` and rewrite to the `deletion_filter_equiv` statement.
  have hdel :
    X ∈ (HornNF.FixSet H).filter (fun X => v ∉ X)
      ↔ X ∈ (H.trace v).FixSet ∧ ¬ P ⊆ X :=
    deletion_filter_equiv (α := α) (H := H) (hDR1 := hDR1)
      (v := v) (P := P) (hP := hP) (hUnique := hUnique) (X := X)

  -- `X ∈ S.FixSet` is `X ∈ FixSet(trace)` plus `¬P ⊆ X`.
  -- So both sides match by `hdel`.
  --
  -- Note: `S.FixSet` is `filter (¬ P ⊆ ·)` on `FixSet(trace)` by definition.
  simp [HornWithForbid.FixSet, S, hdel]

end Dr1nds
