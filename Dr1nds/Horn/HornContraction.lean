import Dr1nds.Horn.Horn  -- HornNF 本体（現状 Horn.lean にある前提）
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Dr1nds.SetFamily.CoreDefs
import Dr1nds.Horn.Horn

namespace Dr1nds

variable {α : Type} [DecidableEq α]


/-
============================================================
  4. Horn Contraction (SKELETON ONLY)
  Purpose:
    Define rule-level contraction on HornNF and state
    preservation of structural properties (DR1, NF).

  NOTE:
    This section contains ONLY declarations (no proofs yet).
    Proofs will be filled later.
============================================================ -/

/-- Rule-level contraction at head x (skeleton definition). -/
def HornNF.contraction (x : α) (H : HornNF α) : HornNF α :=
{ U    := H.U.erase x
  prem := fun h =>
    if h = x then
      ∅
    else
      (H.prem h).image (fun P => P.erase x)

  prem_subset_U := by
    classical
    intro h P hP
    by_cases hh : h = x
    · subst hh
      -- hP : P ∈ (if True then ∅ else ...)
      -- reduce directly to membership in ∅
      simp_all only [↓reduceIte, Finset.notMem_empty]
    ·
      -- First, eliminate the `if` without unfolding `HornNF.contraction`
      have hPimg : P ∈ (H.prem h).image (fun Q => Q.erase x) := by
        simpa [hh] using hP
      rcases Finset.mem_image.mp hPimg with ⟨Q, hQ, rfl⟩
      have hQU : Q ⊆ H.U := H.prem_subset_U hQ
      intro y hy
      have hyQ : y ∈ Q := (Finset.mem_erase.mp hy).2
      have hyU : y ∈ H.U := hQU hyQ
      have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
      exact Finset.mem_erase.mpr ⟨hyne, hyU⟩

  head_mem_U := by
    classical
    intro h hne
    by_cases hh : h = x
    · subst hh
      -- prem x = ∅ in contraction world
      -- hne cannot hold
      simp_all only [↓reduceIte, Finset.not_nonempty_empty]
    ·
      -- If prem_contr h is nonempty, then prem h is nonempty
      have hne' : (H.prem h).Nonempty := by
        rcases hne with ⟨P, hP⟩
        have hPimg : P ∈ (H.prem h).image (fun Q => Q.erase x) := by
          simpa [hh] using hP
        rcases Finset.mem_image.mp hPimg with ⟨Q, hQ, _⟩
        exact ⟨Q, hQ⟩
      have hhU : h ∈ H.U := H.head_mem_U hne'
      exact Finset.mem_erase.mpr ⟨hh, hhU⟩

  nf := by
    classical
    intro h P hP
    by_cases hh : h = x
    · subst hh
      -- prem x = ∅ in contraction world
      simp_all only [↓reduceIte, Finset.notMem_empty]
    ·
      have hPimg : P ∈ (H.prem h).image (fun Q => Q.erase x) := by
        simpa [hh] using hP
      rcases Finset.mem_image.mp hPimg with ⟨Q, hQ, rfl⟩
      intro hhmem
      have : h ∈ Q := (Finset.mem_erase.mp hhmem).2
      exact H.nf hQ this
}

@[simp] lemma contraction_U (H : HornNF α) (x : α) : (H.contraction x).U = H.U.erase x := by
  rfl

@[simp] lemma contraction_prem_self (H : HornNF α) (x : α) : (H.contraction x).prem x = ∅ := by
  simp [HornNF.contraction]

@[simp] lemma contraction_prem_of_ne (H : HornNF α) {x h : α} (hh : h ≠ x) :
    (H.contraction x).prem h = (H.prem h).image (fun P => P.erase x) := by
  simp [HornNF.contraction, hh]




/-
============================================================
  SECTION: Contraction–Family Bridge Layer

  NOTE:
  The definitions and lemmas below conceptually belong to a
  separate module (e.g. HornContraction.lean or HornDeletion.lean).

  They are temporarily kept here for compilation stability,
  but are logically distinct from the core HornNF definition
  layer above.

  Future refactor plan:
    • Move con and erase lemmas to HornContraction.lean
    • Move deletion–family equivalence lemmas to HornDeletion.lean
    • Keep this file definition-only (HornNF + basic operations)

============================================================
-/

open Finset

------------------------------------------------------------
-- ConSet
------------------------------------------------------------

/- S0_CoreDefsに移動
def ConSet {α : Type} [DecidableEq α]
  (x : α) (C : Finset (Finset α)) : Finset (Finset α) :=
  (C.filter (fun X => x ∈ X)).image (fun X => X.erase x)
-/

------------------------------------------------------------
-- erase 補題
------------------------------------------------------------

lemma erase_subset_insert
  {α : Type} [DecidableEq α]
  {x : α} {P Y : Finset α} :
  P ⊆ insert x Y →
  P.erase x ⊆ Y := by
  intro hsub y hy
  have hmem := mem_erase.mp hy
  have hy_ne : y ≠ x := hmem.1
  have hyP  : y ∈ P := hmem.2
  have hyIns := hsub hyP
  exact mem_of_mem_insert_of_ne hyIns hy_ne

lemma subset_of_erase_subset_erase_insert
  {α : Type} [DecidableEq α]
  {x : α} {P X : Finset α}
  (hx : x ∈ X)
  (h : P.erase x ⊆ X.erase x) :
  P ⊆ X := by
  intro y hyP
  by_cases hyx : y = x
  · subst hyx; exact hx
  · exact Finset.mem_of_mem_erase (h (Finset.mem_erase.mpr ⟨hyx, hyP⟩))

lemma insert_erase_self_of_not_mem
  {α : Type} [DecidableEq α]
  {x : α} {Y : Finset α}
  (hx : x ∉ Y) :
  (insert x Y).erase x = Y := by
  ext y
  by_cases hy : y = x
  · subst hy; simp [hx]
  · simp [hy]

lemma not_mem_of_subset_erase
  {α : Type} [DecidableEq α]
  {x : α} {Y U : Finset α}
  (h : Y ⊆ U.erase x) :
  x ∉ Y := by
  intro hxY
  have hxUerase := h hxY
  simp_all only [mem_erase, ne_eq, not_true_eq_false, false_and]



------------------------------------------------------------
-- Family-level deletion (set-family side)
------------------------------------------------------------

/--
Family-level deletion:
Remove all closed sets containing `v`.
This is purely a set-family operation (no rule interaction).
-/
def DelSet {α : Type} [DecidableEq α]
  (v : α) (C : Finset (Finset α)) : Finset (Finset α) :=
  C.filter (fun X => v ∉ X)

@[simp] lemma mem_DelSet
  {α : Type} [DecidableEq α]
  {v : α} {C : Finset (Finset α)} {X : Finset α} :
  X ∈ DelSet v C ↔ X ∈ C ∧ v ∉ X := by
  simp [DelSet]

/--
Head-free case (rule-level deletion = family-level deletion).

If `v` has no premises in `H`, then deleting rules at `v`
coincides with simply removing closed sets containing `v`.
-/
theorem deleteRules_head_free_fix_equiv
  (H : HornNF α)
  (v : α)
  (hfree : H.prem v = ∅) :
  HornNF.FixSet (HornNF.deleteRules H v)
  =
  DelSet v (HornNF.FixSet H) := by
  classical
  apply Finset.ext
  intro X
  constructor

  ------------------------------------------------------------------
  -- → direction
  ------------------------------------------------------------------
  · intro hX
    simp [HornNF.FixSet, DelSet] at *
    rcases hX with ⟨hXsub, hXclosed⟩
    constructor

    -- X ∈ FixSet H
    ·
      have hXsubU : X ⊆ H.U := by
        intro x hx
        have hxUerase := hXsub hx
        exact (Finset.mem_erase.mp hxUerase).2

      have hXclosedU : HornNF.IsClosed H X := by
        intro h P hP hsubset
        by_cases hh : h = v
        ·
          subst hh
          -- since prem v = ∅, no premise can exist
          simp [hfree] at hP
        ·
          -- hP : P ∈ (H.deleteRules v).prem h
          -- rewrite deleteRules premise description
          have hPfilter :
              P ∈ (H.prem h).filter (fun Q => v ∉ Q) := by
            simp
            constructor
            · exact hP
            · exact not_mem_of_subset_erase fun ⦃a⦄ a_1 => hXsub (hsubset a_1)
          have hP' : P ∈ H.prem h :=
            (Finset.mem_filter.mp hPfilter).1
          simp_all only [mem_filter, true_and]
          apply hXclosed
          on_goal 2 => { exact hsubset
          }
          · simp_all only [ne_eq, not_false_eq_true, deleteRules_prem_of_ne, mem_filter, and_self]

      exact ⟨hXsubU, hXclosedU⟩

    -- v ∉ X
    · intro hvX
      have hvUerase := hXsub hvX
      exact (Finset.mem_erase.mp hvUerase).1 rfl

  ------------------------------------------------------------------
  -- ← direction
  ------------------------------------------------------------------
  · intro hX
    simp [HornNF.FixSet, DelSet] at *
    rcases hX with ⟨⟨hXsub, hXclosed⟩, hvX⟩
    constructor

    -- subset
    ·
      intro x hx
      have hxU := hXsub hx
      have hxne : x ≠ v := by
        intro hxeq
        subst hxeq
        exact hvX hx
      exact Finset.mem_erase.mpr ⟨hxne, hxU⟩

    -- closedness in deleteRules world
    ·
      intro h P hP hsubset
      by_cases hh : h = v
      · subst hh
        simp [HornNF.deleteRules] at hP
      ·
        have hPfilter : P ∈ (H.prem h).filter (fun Q => v ∉ Q) := by
          simpa [HornNF.deleteRules, hh] using hP
        have hP' : P ∈ H.prem h :=
          (Finset.mem_filter.mp hPfilter).1
        exact hXclosed hP' hsubset

------------------------------------------------------------
-- forward
------------------------------------------------------------

theorem contraction_fix_equiv_forward
  {α : Type} [DecidableEq α]
  (H : HornNF α)
  (x : α)
  (hxU : x ∈ H.U)
  {Y : Finset α}
  (hY : Y ∈ HornNF.FixSet (H.contraction x)) :
  Y ∈ Con x (HornNF.FixSet H) := by

  let X := insert x Y
  classical
  simp [HornNF.FixSet] at hY
  rcases hY with ⟨hYsub, hYclosed⟩

  -- We must show Y ∈ ConSet x (HornNF.FixSet H)
  unfold Con
  apply Finset.mem_image.mpr
  refine ⟨X, ?hXmem, ?hEq⟩

  --------------------------------------------------
  -- X ∈ (HornNF.FixSet H).filter (fun Z => x ∈ Z)
  --------------------------------------------------
  ·
    apply Finset.mem_filter.mpr
    constructor

    -- X ∈ FixSet H
    ·
      have hXsub : X ⊆ H.U := by
        intro y hy
        cases Finset.mem_insert.mp hy with
        | inl hx => subst hx; exact hxU
        | inr hyY =>
            have hyUerase := hYsub hyY
            exact Finset.mem_of_mem_erase hyUerase

      have hXclosed : HornNF.IsClosed H X := by
        intro h P hP hsubset
        by_cases hh : h = x
        · subst hh; exact Finset.mem_insert_self _ _
        ·
          have hsubsetY : P.erase x ⊆ Y :=
            erase_subset_insert (by simpa using hsubset)
          have hmemY : h ∈ Y := by
            have hPin : P.erase x ∈ (HornNF.contraction x H).prem h := by
              simp [contraction_prem_of_ne (H := H) (x := x) hh]
              simp_all only [X]
              use P
            exact hYclosed hPin hsubsetY
          exact Finset.mem_insert.mpr (Or.inr hmemY)

      have hFix : X ∈ HornNF.FixSet H := by
        simp [HornNF.FixSet]
        exact ⟨hXsub, hXclosed⟩

      exact hFix

    -- x ∈ X
    · exact Finset.mem_insert_self _ _

  --------------------------------------------------
  -- Y = X.erase x
  --------------------------------------------------
  ·
    simp [X]
    have hx_not_Y : x ∉ Y := by
      intro hxY
      have hxUerase := hYsub hxY
      have hx_contra : x ≠ x := (Finset.mem_erase.mp hxUerase).1
      exact hx_contra rfl
    exact hx_not_Y

------------------------------------------------------------
-- backward
------------------------------------------------------------

theorem contraction_fix_equiv_backward
  {α : Type} [DecidableEq α]
  (H : HornNF α)
  (x : α)
  (_ : x ∈ H.U)
  {Y : Finset α}
  (hY : Y ∈ Con x (HornNF.FixSet H)) :
  Y ∈ HornNF.FixSet (H.contraction x) := by

  unfold Con at hY
  rcases Finset.mem_image.mp hY with ⟨X, hXmem, rfl⟩
  rcases Finset.mem_filter.mp hXmem with ⟨hXfix, hxX⟩

  -- FixSet 展開
  have hXfix' := hXfix
  simp [HornNF.FixSet] at hXfix'
  rcases hXfix' with ⟨hXsub, hXclosed⟩

  simp [HornNF.FixSet]
  apply And.intro

  --------------------------------------------------
  -- subset
  --------------------------------------------------
  ·
    intro y hy
    have hyX := (mem_erase.mp hy).1
    have hy_ne := (mem_erase.mp hy).2
    simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
    --simp only [contraction_U]
    simp_all only [true_and]
    exact hXsub hy_ne

  --------------------------------------------------
  -- closed
  --------------------------------------------------
  ·
    intro h Q hQ hsubset
    by_cases hh : h = x
    ·
      have hQ' := hQ
      simp at hQ'
      subst hh
      simp_all only [mem_FixSet_iff, mem_powerset, and_self, mem_filter, mem_image, contraction_prem_self,
        notMem_empty]
    ·
      have hQ' := hQ
      simp [contraction_prem_of_ne (H := H) (x := x) hh] at hQ'
      rcases hQ' with ⟨P, hP, hPeq⟩
      subst hPeq

      have hPX :=
        subset_of_erase_subset_erase_insert hxX hsubset
      simp_all only [mem_erase, ne_eq, not_false_eq_true, true_and]
      apply hXclosed
      on_goal 2 => { exact hPX }
      · simp_all only

------------------------------------------------------------
-- 最終定理
------------------------------------------------------------

theorem contraction_fix_equiv
  {α : Type} [DecidableEq α]
  (H : HornNF α)
  (x : α)
  (hxU : x ∈ H.U) :
  HornNF.FixSet (H.contraction x)
  =
  Con x (HornNF.FixSet H) := by
  apply Finset.ext
  intro Y
  constructor
  · intro hY
    exact contraction_fix_equiv_forward H x hxU hY
  · intro hY
    exact contraction_fix_equiv_backward H x hxU hY

/-- DR1 is preserved under contraction (skeleton theorem). -/
theorem HornNF.contraction_preserves_DR1
  (H : HornNF α)
  (hDR1 : H.IsDR1)
  (x : α) :
  (H.contraction x).IsDR1
:=
by
  classical
  intro h
  by_cases hh : h = x
  · subst hh
    -- prem x = ∅
    simp_all only [contraction_prem_self, card_empty, Nat.zero_le]
  ·
    have hcard : (H.prem h).card ≤ 1 := hDR1 h
    have himg : ((H.prem h).image (fun P => P.erase x)).card ≤ (H.prem h).card :=
      Finset.card_image_le
    -- use the explicit prem form for h ≠ x
    simpa [contraction_prem_of_ne (H := H) (x := x) hh] using le_trans himg hcard

/-- NF is preserved under contraction (skeleton theorem). -/
theorem HornNF.contraction_preserves_NF
  (H : HornNF α)
  (hNF : H.IsNF)
  (x : α) :
  (H.contraction x).IsNF
:=
by
  classical
  intro h P hP
  by_cases hh : h = x
  · subst hh
    -- prem x = ∅
    simpa using (by
      -- hP : P ∈ (H.contraction x).prem x = ∅
      simp_all only [contraction_prem_self, notMem_empty])
  ·
    have hPimg : P ∈ (H.prem h).image (fun Q => Q.erase x) := by
      simpa [contraction_prem_of_ne (H := H) (x := x) hh] using hP
    rcases Finset.mem_image.mp hPimg with ⟨Q, hQ, rfl⟩
    have h_not_mem : h ∉ Q := hNF hQ
    intro hmem
    have : h ∈ Q := (Finset.mem_erase.mp hmem).2
    exact h_not_mem this

end Dr1nds
