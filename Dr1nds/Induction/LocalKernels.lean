-- Dr1nds/Induction/LocalKernels.lean
import Mathlib.Tactic
import Dr1nds.Horn.HornTrace
import Dr1nds.Forbid.HornNormalize
import Dr1nds.Forbid.Basic
import Dr1nds.Forbid.HornWithForbid
import Dr1nds.Forbid.HornBridge
import Dr1nds.Forbid.Singleton
import Dr1nds.Induction.Statements
set_option maxHeartbeats 10000000

namespace Dr1nds
variable {α : Type} [DecidableEq α]

-- =====================================
-- (S) Predicate placeholders (to be refined)
--
-- IMPORTANT:
--   These are *temporary* `abbrev := True` so that the project compiles while we freeze the API.
--   They must be replaced by the actual predicates defined in `Induction/Statements.lean`.
-- =====================================



-- =====================================
-- (0) parallel / no-parallel 分岐（独立核）
-- =====================================

/- Parallel / NoParallel for forbid-free packs. -/
abbrev Parallel0 (P : Pack0 α) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ P.H.closure {v} ∧ v ∈ P.H.closure {u}
abbrev NoParallel0 (P : Pack0 α) : Prop := ¬ Parallel0 P

/-- Parallel / NoParallel for forbid packs. -/
abbrev Parallel1 (F: HornWithForbid α) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ F.H.closure {v} ∧ v ∈ F.H.closure {u}
abbrev NoParallel1  (F: HornWithForbid α): Prop := ¬ Parallel1 F

def HasParallel0 (P : Pack0 α) (v:α) :=
  ∃ u, u ≠ v ∧ u ∈ P.H.closure {v} ∧ v ∈ P.H.closure {u}

def HasParallel1 (F : HornWithForbid α) (v:α) :=
  ∃ u, u ≠ v ∧ u ∈ F.H.closure {v} ∧ v ∈ F.H.closure {u}

/-- Wiring helper: advance one step under the parallel-branch (forbid-free). -/
axiom Q_succ_of_parallel_get
  (n : Nat) (P : Pack0 α) (hn : P.H.U.card = n)(h : α):
  HasParallel0 P h → ∃ P':Pack0 α , (P'.H.U.card = n - 1 ∧ NDS n (P.H.FixSet) ≤ NDS (n-1) (P'.H.FixSet))

/-- Parallel-branch (forbid-free): if `Parallel0 P` holds, we can close `Q n P` by the trace reduction core. -/
axiom Q_of_parallel
  (n : Nat) (P : Pack0 α) :
  Parallel0 P → Q n P

--これはおかしいのではないか。きのうほうは、Fについて成り立つのではなくて、任意のFについて成り立つはず。
/-- Wiring helper: advance one step under the parallel-branch (with forbid). -/
axiom Qcorr_succ_of_parallel_get
  (F : HornWithForbid α) (n : Nat)  (hn : F.H.U.card = n):
  Parallel1 F → ∃ F':HornWithForbid α , F'.H.U.card = n - 1 ∧ (F.NDS_corr n) ≤ (F'.NDS_corr (n - 1))

---------------------------------------------
abbrev IsSC0 (P : Pack0 α) (h : α) : Prop :=
  P.H.closure {h} = {h}

/-- SC / head-structure predicates for forbid packs. -/
abbrev IsSC1 (F: HornWithForbid α) (h : α) : Prop :=
  F.H.closure {h} = {h}

/--
No-parallel (forbid-free) ⇒ existence of an SC point.
This is the entry point to the SC-based induction branch.
-/
axiom exists_SC_no_parallel
  (P : Pack0 α) :
  NoParallel0 P → ∃ h : α, IsSC0 P h

/-- Noncomputably pick an SC point from `exists_SC_no_parallel`. -/
noncomputable def choose_SC_no_parallel
  (P : Pack0 α) (hNP : NoParallel0 P) : α :=
  Classical.choose (exists_SC_no_parallel (α := α) P hNP)

@[simp] theorem choose_SC_no_parallel_spec
  (P : Pack0 α) (hNP : NoParallel0 P) :
  IsSC0 P (choose_SC_no_parallel (α := α) P hNP) :=
  Classical.choose_spec (exists_SC_no_parallel (α := α) P hNP)
------------------------------------------------

/- No-parallel (with forbid) implies existence of an SC point *inside* the forbid set `A`.
    Picking `h ∈ A` is crucial: it prevents the forbid-update from introducing a second forbid set. -/

axiom exists_SC_in_forbid
  (F : HornWithForbid α) :
  NoParallel1 P → ∃ h : α, h ∈ F.F ∧ IsSC1 P h

/-- Noncomputably pick an SC point inside `A` from `exists_SC_in_forbid`. -/
noncomputable def choose_SC_in_forbid
  (F : HornWithForbid α) (hNP : NoParallel1 F) : α :=
  Classical.choose (exists_SC_in_forbid (α := α) F hNP)

@[simp] theorem choose_SC_in_forbid_mem
  (F : HornWithForbid α) (hNP : NoParallel1 F) :
  choose_SC_in_forbid (α := α) F hNP ∈ F.F :=
by
  simpa [choose_SC_in_forbid] using (Classical.choose_spec (exists_SC_in_forbid (α := α) F hNP)).1

@[simp] theorem choose_SC_in_forbid_spec
(F : HornWithForbid α) (hNP : NoParallel1 F) :
  IsSC1 F (choose_SC_in_forbid (α := α) F hNP) :=
by
  simpa [choose_SC_in_forbid] using (Classical.choose_spec (exists_SC_in_forbid (α := α) F hNP)).2

-----------------------------------------------------
def HasHead0 (P : Pack0 α) (h : α) : Prop :=
  (P.H.prem h).Nonempty

def HasHead1 (F :HornWithForbid  α) (h : α) : Prop :=
  (F.H.prem h).Nonempty

def IsForbidSingleton (F :HornWithForbid  α): Prop :=
  F.F.card = 1

def HasHead1s (F :HornWithForbid  α) (fs: IsForbidSingleton F):Prop := by
  let h := Classical.choose (Finset.card_eq_one.mp fs)
  exact (F.H.prem h).Nonempty

-----------------------------------------------------

noncomputable def Q_branch_headFree_get {α :Type} [DecidableEq α](P : Pack0 α) (a: α)  (hs:¬HasHead0 P a):
    ∃ P':Pack0 α , P'.H.U.card = P.H.U.card - 1 ∧ (NDS P'.H.U.card P'.H.FixSet) ≤ (NDS P'.H.U.card P'.H.FixSet)
:= sorry

axiom Q_branch_headFree
  (n : Nat) (P : Pack0 α) (h : α) :
  (∀ P':Pack0 α, P'.H.U.card = n → Q n P') →
  P.H.U.card = n + 1 → IsSC0 P h → ¬HasHead0 P h →
   Q (n+1) P

noncomputable def Q_branch_hasHead_get {α :Type} [DecidableEq α](P : Pack0 α) (a: α)  (hs:HasHead0 P a):
    ∃ P':Pack0 α , P'.H.U.card = P.H.U.card - 1 ∧ (NDS P'.H.U.card P'.H.FixSet) ≤ (NDS P'.H.U.card P'.H.FixSet)
:= sorry

axiom Q_branch_hasHead
  (n : Nat) (P : Pack0 α) (h : α) :
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) → (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  P.H.U.card = n + 1 → IsSC0 P h → HasHead0 P h →
  Q (n+1) P

noncomputable def Qcorr_singleton_headFree_get {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (heq: F.F = {a}) (hs:¬HasHead1 F a):
    ∃ F':HornWithForbid α , F'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr (F.H.U.card - 1)) ≤ (F'.NDS_corr F.H.U.card)
:= sorry

axiom Qcorr_singleton_hasHead
  (n : Nat) (F : HornWithForbid α) :
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) → (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  F.H.U.card = n + 1 → (fb:IsForbidSingleton F) → HasHead1s F fb→
   Qcorr (n+1) F

noncomputable def Qcorr_singleton_hasHead_get {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (heq: F.F = {a}) (hs:HasHead1 F a):
    ∃ F':HornWithForbid α , F'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr F.H.U.card) ≤ (F'.NDS_corr (F.H.U.card - 1))
:= sorry

axiom Qcorr_singleton_headFree
  (n : Nat) (F : HornWithForbid α)  :
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) → (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F')→
  F.H.U.card = n + 1 → (fb:IsForbidSingleton F) → ¬HasHead1s F fb→
   Qcorr (n+1) F

axiom Qcorr_ge2_hasHead
  (n : Nat) (F : HornWithForbid α) (h : α) (hh : h ∈ F.F):
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) → (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  F.H.U.card = n + 1 → ¬IsForbidSingleton F → IsSC1 F h → HasHead1 F h →
   Qcorr (n+1) F

axiom Qcorr_ge2_headFree
  (n : Nat) (F : HornWithForbid α) (h : α) (hh : h ∈ F.F):
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) → (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  F.H.U.card = n + 1 → ¬IsForbidSingleton F → IsSC1 F h → ¬HasHead1 F h →
  Qcorr (n+1) F

--パラレルな頂点が存在する場合

axiom Qcorr_ge_hasParallel
  (n : Nat) (F : HornWithForbid α) (h : α) (hh : h ∈ F.F):
  (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') → F.H.U.card = n + 1 →
  Qcorr (n+1) F


/-
(2) forbid world: split by `|A|`.

`card_cases` is a wiring helper: it is independent from the Horn/closure semantics.
We use `omit [DecidableEq α]` to keep the lemma as general as possible; the proof re-introduces `classical`.
-/
omit [DecidableEq α] in
/-- Card-split helper: any finite set has either card = 0, card = 1, or card ≥ 2.
Stepsで使っている
-/
lemma card_cases
  (A : Finset α) :
  A.card = 0 ∨ A.card = 1 ∨ 2 ≤ A.card := by
  classical
  have h : A.card = 0 ∨ A.card = 1 ∨ 2 ≤ A.card := by
    omega
  exact h

----使ってないかも。

noncomputable def tracePack0 (P : Pack0 α) (a : α) : Pack0 α :=
  { H := P.H.trace a
    hDR1 := by
      -- DR1 is preserved by trace (proved in the Horn layer).
      have hDR1' : HornNF.DR1 P.H := by
        simpa [HornNF.IsDR1, HornNF.DR1] using P.hDR1
      have hDR1'' : HornNF.DR1 (HornNF.trace P.H a) :=
        HornNF.trace_preserves_DR1 (H := P.H) (u := a) hDR1'
      simpa [HornNF.IsDR1, HornNF.DR1] using hDR1''
    hNEP := by exact P.H.trace_preserves_NEP' a P.hNEP
  }



end Dr1nds
