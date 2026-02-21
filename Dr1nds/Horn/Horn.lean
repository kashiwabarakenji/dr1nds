-- Dr1nds/S2_HornNF.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
--import Dr1nds.S1_HornDefs
--import LeanCopilot

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


/-
------------------------------------------------------------
  2a. NEP ⇒ ∅ is closed (and hence belongs to FixSet)

  This block is intentionally trace-free.
------------------------------------------------------------ -/

/-- If `H` is NEP (no empty premise), then the empty set is closed w.r.t. `H`. -/
lemma HornNF.isClosed_empty_of_isNEP
  (H : HornNF α)
  (hNEP : H.IsNEP) :
  HornNF.IsClosed H (∅ : Finset α) := by
  classical
  intro h P hP hPsub
  have hPempty : P = (∅ : Finset α) := by
    -- any element of `P` would have to lie in `∅`
    apply Finset.eq_empty_iff_forall_not_mem.2
    intro x hx
    have : x ∈ (∅ : Finset α) := hPsub hx
    simpa using this
  -- contradict NEP (since `P = ∅` would mean an empty premise appears)
  have : (∅ : Finset α) ∈ H.prem h := by
    simpa [hPempty] using hP
  exact False.elim (hNEP (h := h) this)



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



/-- If `H` is NEP, then `∅ ∈ FixSet H` (so the family-level NEP holds for `FixSet H`). -/
lemma HornNF.empty_mem_FixSet_of_isNEP
  (H : HornNF α)
  (hNEP : H.IsNEP) :
  (∅ : Finset α) ∈ HornNF.FixSet H := by
  classical
  -- Use the `mem_FixSet_iff` bridge to avoid unfolding `FixSet`.
  apply (mem_FixSet_iff (H := H) (X := (∅ : Finset α))).2
  refine And.intro ?_ (HornNF.isClosed_empty_of_isNEP (H := H) hNEP)
  -- `∅ ∈ U.powerset`
  have : (∅ : Finset α) ⊆ H.U := by
    intro x hx
    simpa using hx
  exact Finset.mem_powerset.2 this


/-- If the empty set is closed w.r.t. `H`, then `H` is NEP (no empty premise). -/
lemma HornNF.isNEP_of_isClosed_empty
  (H : HornNF α)
  (hClosed : HornNF.IsClosed H (∅ : Finset α)) :
  H.IsNEP := by
  classical
  intro h hempty
  have : h ∈ (∅ : Finset α) := hClosed (h := h) (P := (∅ : Finset α)) hempty (by
    intro x hx
    simpa using hx)
  simpa using this

/-- `H` is NEP iff the empty set is closed w.r.t. `H`. -/
lemma HornNF.isNEP_iff_isClosed_empty
  (H : HornNF α) :
  H.IsNEP ↔ HornNF.IsClosed H (∅ : Finset α) := by
  constructor
  · intro hNEP
    exact HornNF.isClosed_empty_of_isNEP (H := H) hNEP
  · intro hClosed
    exact HornNF.isNEP_of_isClosed_empty (H := H) hClosed

/- `H` is NEP iff `FixSet H` contains the empty set (family-level NEP for `FixSet`). -/
/- `H` is NEP iff `FixSet H` contains the empty set (family-level NEP for `FixSet`). -/
lemma HornNF.isNEP_iff_empty_mem_FixSet
  (H : HornNF α) :
  H.IsNEP ↔ (∅ : Finset α) ∈ HornNF.FixSet H := by
  constructor
  · intro hNEP
    exact HornNF.empty_mem_FixSet_of_isNEP (H := H) hNEP
  · intro hempty
    have hClosed : HornNF.IsClosed H (∅ : Finset α) := by
      -- unpack `∅ ∈ FixSet H` using the bridge lemma
      exact (mem_FixSet_iff (H := H) (X := (∅ : Finset α))).1 hempty |>.2
    let hi := HornNF.isNEP_of_isClosed_empty (H := H)
    simp_all only [mem_FixSet_iff, Finset.mem_powerset, Finset.empty_subset, and_self]

/-
  ------------------------------------------------------------
  2b-alt. Safe alias layer (do not touch existing proofs)

  Some environments are sensitive to minor proof edits here.
  To avoid breaking already-compiling code, we provide
  “alias lemmas” under fresh names and keep the originals frozen.
  ------------------------------------------------------------
-/

/-- Alias of `HornNF.isClosed_empty_of_isNEP` (kept for stable downstream rewrites). -/
lemma HornNF.isClosed_empty_of_isNEP_alt
  (H : HornNF α)
  (hNEP : H.IsNEP) :
  HornNF.IsClosed H (∅ : Finset α) := by
  let hi := HornNF.isClosed_empty_of_isNEP (H := H)
  simp_all only

/-- Alias of `HornNF.empty_mem_FixSet_of_isNEP` (kept for stable downstream rewrites). -/
lemma HornNF.empty_mem_FixSet_of_isNEP_alt
  (H : HornNF α)
  (hNEP : H.IsNEP) :
  (∅ : Finset α) ∈ HornNF.FixSet H := by
  simpa using HornNF.empty_mem_FixSet_of_isNEP (H := H) hNEP

/-- Alias of `HornNF.isNEP_of_isClosed_empty` (kept for stable downstream rewrites). -/
lemma HornNF.isNEP_of_isClosed_empty_alt
  (H : HornNF α)
  (hClosed : HornNF.IsClosed H (∅ : Finset α)) :
  H.IsNEP := by
    let hi := HornNF.isNEP_of_isClosed_empty (H := H)
    simp_all only

/-- Alias of `HornNF.isNEP_iff_isClosed_empty` (kept for stable downstream rewrites). -/
lemma HornNF.isNEP_iff_isClosed_empty_alt
  (H : HornNF α) :
  H.IsNEP ↔ HornNF.IsClosed H (∅ : Finset α) := by
  simpa using HornNF.isNEP_iff_isClosed_empty (H := H)

/-- Alias of `HornNF.isNEP_iff_empty_mem_FixSet` (preferred stable entry point). -/
lemma HornNF.isNEP_iff_empty_mem_FixSet_alt
  (H : HornNF α) :
  H.IsNEP ↔ (∅ : Finset α) ∈ HornNF.FixSet H := by
  simpa using HornNF.isNEP_iff_empty_mem_FixSet (H := H)

/-
------------------------------------------------------------
  2c. “Deletion-world” restriction on HornNF (FILTER form)

  This is the H_del used in the Del-as-Hole plan:
    U_del   := U.erase v
    prem_del(h) := if h = v then ∅ else (prem h).filter (fun P => v ∉ P)

  IMPORTANT: We do NOT erase v from premises (no image/erase).
  We only drop premises that contain v.
------------------------------------------------------------ -/

def HornNF.deleteRules (H : HornNF α) (v : α) : HornNF α :=
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

@[simp] lemma deleteRules_U (H : HornNF α) (v : α) : (HornNF.deleteRules H v).U = H.U.erase v := by
  rfl

@[simp] lemma deleteRules_prem_self (H : HornNF α) (v : α) : (HornNF.deleteRules H v).prem v = ∅ := by
  simp [HornNF.deleteRules]


@[simp] lemma deleteRules_prem_of_ne (H : HornNF α) {v h : α} (hh : h ≠ v) :
    (HornNF.deleteRules H v).prem h = (H.prem h).filter (fun P => v ∉ P) := by
  simp [HornNF.deleteRules, hh]

/-
Head-free case:
If a head `v` has no premises in `H`,
then rule-level deletion at `v` coincides with
simple filtering of premises (i.e. no rule interaction occurs).

This is the formal "head-free deletion" statement
used in the Del=Hole plan.
-/
lemma deleteRules_head_free
    (H : HornNF α)
    (v : α)
    (hfree : (H.prem v) = ∅) :
    HornNF.deleteRules H v =
    { U    := H.U.erase v
      prem := fun h =>
        if h = v then ∅ else (H.prem h).filter (fun P => v ∉ P)
      prem_subset_U := (HornNF.deleteRules H v).prem_subset_U
      head_mem_U    := (HornNF.deleteRules H v).head_mem_U
      nf            := (HornNF.deleteRules H v).nf } := by
  classical
  -- This is definitional; no interaction occurs when prem v = ∅.
  rfl

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

lemma prem_card_eq_one_of_DR1_of_nonempty
    (H : HornNF α) (v : α)
    (hDR1 : HornNF.IsDR1 H)
    (hne : (H.prem v).Nonempty) :
    (H.prem v).card = 1 := by
  classical
  have hle1 : (H.prem v).card ≤ 1 := hDR1 v
  have hpos : 0 < (H.prem v).card := Finset.card_pos.mpr hne
  have hge1 : 1 ≤ (H.prem v).card := Nat.succ_le_of_lt hpos
  exact Nat.le_antisymm hle1 hge1


lemma prem_card_eq_one_of_DR1_of_ne_empty
    (H : HornNF α) (v : α)
    (hDR1 : HornNF.IsDR1 H)
    (hne : (H.prem v) ≠ ∅) :
    (H.prem v).card = 1 := by
  classical
  apply prem_card_eq_one_of_DR1_of_nonempty (H := H) (v := v) (hDR1 := hDR1)
  exact Finset.nonempty_iff_ne_empty.mpr hne

/-- Under DR1, nonempty `prem v` has a unique premise element. -/
lemma exists_unique_prem_of_DR1_of_nonempty
    (H : HornNF α) (v : α)
    (hDR1 : HornNF.IsDR1 H)
    (hne : (H.prem v).Nonempty) :
    ∃! P : Finset α, P ∈ H.prem v
:= by
  classical
  rcases hne with ⟨P, hP⟩
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  exact prem_eq_of_mem_of_mem (H := H) (v := v) (hDR1 := hDR1) (hP := hQ) (hQ := hP)

/-- Under DR1, membership `P ∈ prem v` forces `prem v = {P}`. -/
lemma prem_eq_singleton_of_DR1_of_mem
    (H : HornNF α) (v : α)
    (hDR1 : HornNF.IsDR1 H)
    {P : Finset α}
    (hP : P ∈ H.prem v) :
    H.prem v = {P} := by
  classical
  apply Finset.ext
  intro Q
  constructor
  · intro hQ
    have : Q = P := prem_eq_of_mem_of_mem (H := H) (v := v) (hDR1 := hDR1) (hP := hQ) (hQ := hP)
    simpa [this]
  · intro hQ
    -- Q ∈ {P} implies Q = P
    simpa using (by
      rcases Finset.mem_singleton.mp hQ with rfl
      exact hP)

/- ------------------------------------------------------------
  3. Conversion targets (placeholders only)
------------------------------------------------------------ -/

/-
Intended conversion:
Horn → HornNF (definition only, no properties asserted).
Actual construction lives in later files.

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
-/

end Dr1nds
