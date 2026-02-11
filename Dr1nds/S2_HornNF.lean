-- Dr1nds/S2_HornNF.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
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
  prem : α → Finset (Finset α)


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

def HornNF.FixSet (H : HornNF α) (U : Finset α) : Set (Finset α) :=
  { X | X ⊆ U ∧ H.IsClosed X }

def HornNF.HornOn (H : HornNF α) (U : Finset α) : Prop :=
  ∀ (h : α) (P : Finset α), P ∈ H.prem h → (h ∈ U ∧ P ⊆ U)

def HornNF.PremOn (H : HornNF α) (U : Finset α) : Prop :=
  ∀ ⦃h : α⦄ ⦃P : Finset α⦄, P ∈ H.prem h → P ⊆ U

def HornNF.HeadOn (H : HornNF α) (U : Finset α) : Prop :=
  ∀ ⦃h : α⦄, (H.prem h).Nonempty → h ∈ U

/- ------------------------------------------------------------
  3. Conversion targets (placeholders only)
------------------------------------------------------------ -/

/--
Intended conversion:
Horn → HornNF (definition only, no properties asserted).
Actual construction lives in later files.
-/
def Horn.toHornNF (_ : Horn α) : HornNF α :=
  { prem := fun _ => ∅ }


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
{ prem := fun h =>
    if h = x then
      ∅
    else
      (H.prem h).image (fun P => P.erase x)
}



open Finset

------------------------------------------------------------
-- ConSet
------------------------------------------------------------

def ConSet {α : Type} [DecidableEq α]
  (x : α) (C : Set (Finset α)) : Set (Finset α) :=
{ Y | ∃ X ∈ C, x ∈ X ∧ Y = X.erase x }

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
  (U : Finset α)
  (x : α)
  (hxU : x ∈ U)
  (_ : HornNF.HornOn H U) --hOn
  {Y : Finset α}
  (hY : Y ∈ HornNF.FixSet (H.contraction x) (U.erase x)) :
  Y ∈ ConSet x (HornNF.FixSet H U) := by

  -- FixSet 展開（安全）
  have hY' := hY
  simp [HornNF.FixSet] at hY'
  rcases hY' with ⟨hYsub, hYclosed⟩

  let X := insert x Y

  refine ⟨X, ?_, ?_, ?_⟩

  --------------------------------------------------
  -- X ∈ FixSet H U
  --------------------------------------------------
  ·
    apply And.intro

    -- subset
    ·
      intro y hy
      have hy_split := mem_insert.mp hy
      cases hy_split with
      | inl h =>
          subst h
          exact hxU
      | inr hyY =>
          have hyUerase := hYsub hyY
          exact mem_of_mem_erase (hYsub hyY)

    -- closed
    ·
      intro h P hP hsubset
      by_cases hh : h = x
      ·
        subst hh
        exact mem_insert_self h Y
      ·
        -- prem 展開
        have hP' := hP
        have hsubsetX : P ⊆ insert x Y := by
          simpa [X] using hsubset

        have hsubsetY : P.erase x ⊆ Y :=
          erase_subset_insert hsubsetX

        -- contraction 側閉性を使う
        have hmemY : h ∈ Y := by
          apply hYclosed
          · dsimp [HornNF.contraction]
            simp [hh]
            use P
          · exact hsubsetY
        exact mem_insert.mpr (Or.inr hmemY)

  --------------------------------------------------
  -- x ∈ X
  --------------------------------------------------
  · exact mem_insert_self x Y

  --------------------------------------------------
  -- Y = X.erase x
  --------------------------------------------------
  · simp [X]
    have : x ∉ Y := by
      apply Aesop.BuiltinRules.not_intro
      intro a
      specialize hYsub a
      simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true]
    exact Eq.symm (erase_eq_of_notMem this)

------------------------------------------------------------
-- backward
------------------------------------------------------------

theorem contraction_fix_equiv_backward
  {α : Type} [DecidableEq α]
  (H : HornNF α)
  (U : Finset α)
  (x : α)
  (_ : x ∈ U) --hxU
  (_ : HornNF.HornOn H U) --hOn
  {Y : Finset α}
  (hY : Y ∈ ConSet x (HornNF.FixSet H U)) :
  Y ∈ HornNF.FixSet (H.contraction x) (U.erase x) := by

  rcases hY with ⟨X, hXfix, hxX, rfl⟩

  -- FixSet 展開
  have hXfix' := hXfix
  simp [HornNF.FixSet] at hXfix'
  rcases hXfix' with ⟨hXsub, hXclosed⟩

  apply And.intro

  --------------------------------------------------
  -- subset
  --------------------------------------------------
  ·
    intro y hy
    have hyX := (mem_erase.mp hy).1
    have hy_ne := (mem_erase.mp hy).2
    simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self, true_and]
    exact hXsub hy_ne

  --------------------------------------------------
  -- closed
  --------------------------------------------------
  ·
    intro h Q hQ hsubset
    by_cases hh : h = x
    ·
      have hQ' := hQ
      simp [HornNF.contraction, hh] at hQ'
    ·
      have hQ' := hQ
      simp [HornNF.contraction, hh] at hQ'
      rcases hQ' with ⟨P, hP, hPeq⟩
      subst hPeq

      have hPX :=
        subset_of_erase_subset_erase_insert hxX hsubset
      simp_all only [mem_erase, ne_eq, not_false_eq_true, true_and]
      apply hXclosed
      on_goal 2 => { exact hPX
      }
      · simp_all only

------------------------------------------------------------
-- 最終定理
------------------------------------------------------------

theorem contraction_fix_equiv
  {α : Type} [DecidableEq α]
  (H : HornNF α)
  (U : Finset α)
  (x : α)
  (hxU : x ∈ U)
  (hOn : HornNF.HornOn H U) :
  HornNF.FixSet (H.contraction x) (U.erase x)
  =
  ConSet x (HornNF.FixSet H U) := by
  apply Set.ext
  intro Y
  constructor
  · intro hY
    exact contraction_fix_equiv_forward H U x hxU hOn hY
  · intro hY
    exact contraction_fix_equiv_backward H U x hxU hOn hY

/-- DR1 is preserved under contraction (skeleton theorem). -/
theorem HornNF.contraction_preserves_DR1
  (H : HornNF α)
  (hDR1 : H.IsDR1)
  (x : α) :
  (H.contraction x).IsDR1 :=
by
  intro h
  by_cases hh : h = x
  · -- head = x の場合
    subst hh
    simp [HornNF.contraction]
  · -- head ≠ x の場合
    have hcard := hDR1 h
    dsimp [HornNF.contraction]
    simp [hh]
    -- card(image) ≤ card(original) ≤ 1
    refine le_trans ?_ hcard
    exact Finset.card_image_le

/-- NF is preserved under contraction (skeleton theorem). -/
theorem HornNF.contraction_preserves_NF
  (H : HornNF α)
  (hNF : H.IsNF)
  (x : α) :
  (H.contraction x).IsNF :=
by
  intro h P hP
  by_cases hh : h = x
  · -- head = x: prem x = ∅
    subst hh
    simp [HornNF.contraction] at hP
  · -- head ≠ x: image of erase
    simp [HornNF.contraction, hh] at hP
    rcases hP with ⟨Q, hQ, rfl⟩
    -- Q ∈ H.prem h and P = Q.erase x
    have h_not_Q : h ∉ Q := hNF hQ
    intro hmem
    have hmem' := Finset.mem_erase.mp hmem
    have h_in_Q : h ∈ Q := hmem'.2
    exact h_not_Q h_in_Q

end Dr1nds
