-- Dr1nds/S2_HornNF.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Dr1nds.S1_HornDefs
import LeanCopilot

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ============================================================
  S2 : HornNF (NORMAL FORM, DEFINITIONS ONLY)
  This file is FROZEN.
  No lemmas, no proofs.
============================================================ -/

/- ------------------------------------------------------------
  0. HornNF structure
------------------------------------------------------------ -/

/--
HornNF is a head-indexed normal form of Horn systems.

For each head h : α,
  prem h : Finset (Finset α)
is the (possibly empty) finite set of premises for rules with head h.
-/
structure HornNF (α : Type) [DecidableEq α] where
  U    : Finset α
  prem : α → Finset (Finset α)

  /-- Every premise listed in `prem h` is a subset of the universe `U`. -/
  prem_subset_U : ∀ {h : α} {P : Finset α}, P ∈ prem h → P ⊆ U

  /-- Any head that actually has at least one premise must lie in the universe `U`. -/
  head_mem_U : ∀ {h : α}, (prem h).Nonempty → h ∈ U

  /-- NF is built into the structure: heads do not appear in their own premises. -/
  nf : ∀ {h : α} {P : Finset α}, P ∈ prem h → h ∉ P


/- ------------------------------------------------------------
  1. Structural conditions on HornNF
------------------------------------------------------------ -/

/--
DR1 in HornNF:
For each head h, there is at most one premise.
-/
def HornNF.IsDR1 (H : HornNF α) : Prop :=
  ∀ h : α, (H.prem h).card ≤ 1

/--
NEP in HornNF:
No empty premise appears.
-/
def HornNF.IsNEP (H : HornNF α) : Prop :=
  ∀ {h : α}, (∅ : Finset α) ∉ H.prem h

/--
NF in HornNF:
Heads do not appear in their own premises.
-/
def HornNF.IsNF (H : HornNF α) : Prop :=
  ∀ {h : α} {P : Finset α}, P ∈ H.prem h → h ∉ P


/- ------------------------------------------------------------
  2. Closedness w.r.t. HornNF
------------------------------------------------------------ -/

/--
A set X is closed w.r.t. HornNF H iff
for every head h and premise P ∈ prem h,
  P ⊆ X ⇒ h ∈ X.
-/
def HornNF.IsClosed (H : HornNF α) (X : Finset α) : Prop :=
  ∀ {h : α} {P : Finset α},
    P ∈ H.prem h →
    P ⊆ X →
    h ∈ X


noncomputable def HornNF.FixSet (H : HornNF α) : Finset (Finset α) :=
by
  classical
  exact H.U.powerset.filter (fun X => H.IsClosed X)
 --  { X | X ⊆ H.U ∧ H.IsClosed X }

/-
------------------------------------------------------------
  2b. Basic lemmas about FixSet (needed for Del-as-Hole)

  NOTE: These are tiny “bridge” lemmas used to avoid unfolding
  `FixSet` everywhere. They correspond to the Q2 request:
    X ∈ FixSet H → X ⊆ H.U.
------------------------------------------------------------ -/

@[simp] lemma mem_FixSet_iff (H : HornNF α) (X : Finset α) :
    X ∈ HornNF.FixSet H ↔ X ∈ H.U.powerset ∧ H.IsClosed X := by
  classical
  simp [HornNF.FixSet]

lemma mem_FixSet_subset_U (H : HornNF α) {X : Finset α}
    (hX : X ∈ HornNF.FixSet H) : X ⊆ H.U := by
  classical
  have hXpow : X ∈ H.U.powerset := (mem_FixSet_iff (H := H) (X := X)).1 hX |>.1
  exact (Finset.mem_powerset.mp hXpow)


/-
------------------------------------------------------------
  2c. “Deletion-world” restriction on HornNF (FILTER form)

  This is the H_del used in the Del-as-Hole plan:
    U_del   := U.erase v
    prem_del(h) := if h = v then ∅ else (prem h).filter (fun P => v ∉ P)

  IMPORTANT: We do NOT erase v from premises (no image/erase).
  We only drop premises that contain v.
------------------------------------------------------------ -/

def HornNF.del (H : HornNF α) (v : α) : HornNF α :=
{ U    := H.U.erase v
  prem := fun h =>
    if h = v then
      ∅
    else
      (H.prem h).filter (fun P => v ∉ P)

  prem_subset_U := by
    classical
    intro h P hP
    by_cases hh : h = v
    · subst hh
      -- prem v = ∅ in the deletion world, so membership is impossible
      simpa using hP
    ·
      -- eliminate the `if` by rewriting with `hh`
      have hPfilter : P ∈ (H.prem h).filter (fun Q => v ∉ Q) := by
        simpa [hh] using hP
      have hP' : P ∈ H.prem h := (Finset.mem_filter.mp hPfilter).1
      have hvnot : v ∉ P := (Finset.mem_filter.mp hPfilter).2
      have hPU : P ⊆ H.U := H.prem_subset_U hP'
      intro x hx
      have hxU : x ∈ H.U := hPU hx
      have hxne : x ≠ v := by
        -- if x = v then v ∈ P, contradicting the filter condition
        intro hxeq
        subst hxeq
        -- hvnot already obtained above
        exact hvnot hx
      exact Finset.mem_erase.mpr ⟨hxne, hxU⟩

  head_mem_U := by
    classical
    intro h hne
    by_cases hh : h = v
    · subst hh
      -- prem v = ∅ in the deletion world, so Nonempty is impossible
      rcases hne with ⟨P, hP⟩
      simpa using hP
    ·
      -- if prem_del h is nonempty, then prem h is nonempty
      have hne' : (H.prem h).Nonempty := by
        rcases hne with ⟨P, hP⟩
        have hPfilter : P ∈ (H.prem h).filter (fun Q => v ∉ Q) := by
          simpa [hh] using hP
        exact ⟨P, (Finset.mem_filter.mp hPfilter).1⟩
      have hhU : h ∈ H.U := H.head_mem_U hne'
      exact Finset.mem_erase.mpr ⟨hh, hhU⟩

  nf := by
    classical
    intro h P hP
    by_cases hh : h = v
    · subst hh
      -- prem v = ∅ in the deletion world, so membership is impossible
      simpa using hP
    ·
      have hP' : P ∈ H.prem h := by
        simp_all only [↓reduceIte, Finset.mem_filter]
      exact H.nf hP'
}

@[simp] lemma del_U (H : HornNF α) (v : α) : (HornNF.del H v).U = H.U.erase v := by
  rfl

@[simp] lemma del_prem_self (H : HornNF α) (v : α) : (HornNF.del H v).prem v = ∅ := by
  simp [HornNF.del]

@[simp] lemma del_prem_of_ne (H : HornNF α) {v h : α} (hh : h ≠ v) :
    (HornNF.del H v).prem h = (H.prem h).filter (fun P => v ∉ P) := by
  simp [HornNF.del, hh]

/-
------------------------------------------------------------
  2d. DR1 ⇒ premise uniqueness for a fixed head (Q1)
------------------------------------------------------------ -/

lemma prem_eq_of_mem_of_mem
    (H : HornNF α) (v : α)
    (hDR1 : HornNF.IsDR1 H)
    {P Q : Finset α}
    (hP : P ∈ H.prem v) (hQ : Q ∈ H.prem v) :
    P = Q := by
  classical
  have hcard : (H.prem v).card ≤ 1 := hDR1 v
  apply Finset.card_le_one.mp hcard
  exact hP
  exact hQ

/- ------------------------------------------------------------
  3. Conversion targets (placeholders only)
------------------------------------------------------------ -/

/--
Intended conversion:
Horn → HornNF (definition only, no properties asserted).
Actual construction lives in later files.
-/
def Horn.toHornNF (_ : Horn α) : HornNF α :=
  { U := ∅
    prem := fun _ => ∅
    prem_subset_U := by
      classical
      intro h P hP
      simp at hP
    head_mem_U := by
      classical
      intro h hne
      simpa using hne
    nf := by
      classical
      intro h P hP
      simp at hP
  }


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
      simpa using (by simpa using hP)
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
      simpa using (by simpa using hne)
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
      simpa using (by simpa using hP)
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



open Finset

------------------------------------------------------------
-- ConSet
------------------------------------------------------------

def ConSet {α : Type} [DecidableEq α]
  (x : α) (C : Finset (Finset α)) : Finset (Finset α) :=
  (C.filter (fun X => x ∈ X)).image (fun X => X.erase x)

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
-- forward
------------------------------------------------------------

theorem contraction_fix_equiv_forward
  {α : Type} [DecidableEq α]
  (H : HornNF α)
  (x : α)
  (hxU : x ∈ H.U)
  {Y : Finset α}
  (hY : Y ∈ HornNF.FixSet (H.contraction x)) :
  Y ∈ ConSet x (HornNF.FixSet H) := by

  let X := insert x Y
  classical
  simp [HornNF.FixSet] at hY
  rcases hY with ⟨hYsub, hYclosed⟩

  -- We must show Y ∈ ConSet x (HornNF.FixSet H)
  unfold ConSet
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
  (hY : Y ∈ ConSet x (HornNF.FixSet H)) :
  Y ∈ HornNF.FixSet (H.contraction x) := by

  unfold ConSet at hY
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
  ConSet x (HornNF.FixSet H) := by
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
    simpa using (show ((H.contraction x).prem x).card ≤ 1 by simp)
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
      simpa using hP)
  ·
    have hPimg : P ∈ (H.prem h).image (fun Q => Q.erase x) := by
      simpa [contraction_prem_of_ne (H := H) (x := x) hh] using hP
    rcases Finset.mem_image.mp hPimg with ⟨Q, hQ, rfl⟩
    have h_not_mem : h ∉ Q := hNF hQ
    intro hmem
    have : h ∈ Q := (Finset.mem_erase.mp hmem).2
    exact h_not_mem this

end Dr1nds
