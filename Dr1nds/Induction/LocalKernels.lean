-- Dr1nds/Induction/LocalKernels.lean
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
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
-- (0) parallel / no-parallel 分岐（独立核）
-- =====================================

/- Parallel / NoParallel for forbid-free packs. -/
abbrev Parallel0 (P : Pack0 α) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ P.H.closure {v} ∧ v ∈ P.H.closure {u}
abbrev NoParallel0 (P : Pack0 α) : Prop := ¬ Parallel0 P

/-- Parallel / NoParallel for forbid packs. 禁止集合の中にパラレルがあるかどうか。-/
abbrev Parallel1 (F: HornWithForbid α) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ F.F ∧ v ∈ F.F ∧ u ∈ F.H.closure {v} ∧ v ∈ F.H.closure {u}
abbrev NoParallel1  (F: HornWithForbid α): Prop := ¬ Parallel1 F

--使わないかも。
def HasParallel0 (P : Pack0 α) (v:α) :=
  ∃ u, u ≠ v ∧ u ∈ P.H.closure {v} ∧ v ∈ P.H.closure {u}

def HasParallel1 (F : HornWithForbid α) (v:α) :=
  ∃ u, u ≠ v ∧ u ∈ F.H.closure {v} ∧ v ∈ F.H.closure {u}

---ほかの言明に合わせて2段階にする。getのほうは、頂点をtraceしたものがNDSが大きくなくて、Packの条件を満たすというもの。頂点を引数に入れる。
---上のほうの言明は、帰納法の仮定を仮定すると、Q n が成り立つというもの。
/-- Wiring helper: advance one step under the parallel-branch (forbid-free). -/
axiom Q_of_parallel_get
  (n : Nat) (P : Pack0 α) (hn : P.H.U.card = n):
  Parallel0 P → ∃ P':Pack0 α , (P'.H.U.card = n - 1 ∧ NDS n (P.H.FixSet) ≤ NDS (n-1) (P'.H.FixSet))

/-- Parallel-branch (forbid-free): if `Parallel0 P` holds, we can close `Q n P` by the trace reduction core. -/
theorem Q_of_parallel
  (n : Nat) (P : Pack0 α) : (∀ P':Pack0 α, P'.H.U.card = n → Q n P') →
  P.H.U.card = n + 1 →
  Parallel0 P → Q (n+1) P := by
  intro hQ hn hPar
  obtain ⟨P',hP'⟩ := Q_of_parallel_get (α := α) (n+1) P hn hPar
  simp at hP'
  dsimp [Q]
  intro hn'
  specialize hQ P'
  have :P'.H.U.card = n := by simp_all
  specialize hQ this
  dsimp [Q] at hQ
  specialize hQ this
  rw [←this] at hQ
  rw [←hn']
  rcases hP' with ⟨h1,h2⟩
  rw [←hn] at h2
  rw [←h1] at h2
  exact Int.le_trans h2 hQ

/-- Wiring helper: advance one step under the parallel-branch (with forbid). -/
axiom Qcorr_of_parallel_get
  (n : Nat) (F : HornWithForbid α)  (hn : F.H.U.card = n):
  Parallel1 F → ∃ F':HornWithForbid α , F'.H.U.card = n - 1 ∧ (F.NDS_corr n) ≤ (F'.NDS_corr (n - 1))

theorem Qcorr_ge_hasParallel
  (n : Nat) (F : HornWithForbid α) :
  (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') → F.H.U.card = n + 1 → Parallel1 F →
  Qcorr (n+1) F := by
  intro hQcorr hn hPar
  obtain ⟨F',hF'⟩ := Qcorr_of_parallel_get (α := α) (n+1) F hn hPar
  dsimp [Qcorr]
  intro hn'
  specialize hQcorr F'
  have :F'.H.U.card = n := by simp_all
  specialize hQcorr this
  dsimp [Qcorr] at hQcorr
  specialize hQcorr this
  --rw [←this] at hQcorr
  rw [←hn']
  rcases hF' with ⟨h1,h2⟩
  rw [←hn] at h2
  simp at h1
  rw [←this] at hn'
  have : n = F.H.U.card -1:= by
    subst this
    simp_all only [add_tsub_cancel_right]
  rw [this] at hQcorr
  exact Int.le_trans h2 hQcorr

---------------------------------------------
---これは、Hornレベルで定義することではないのか。HornNF.IsSCを定義した。今後は、P.H.IsSCを使う。
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
  NoParallel0 P → ∃ h : α, P.H.IsSC h

/-- Noncomputably pick an SC point from `exists_SC_no_parallel`. -/
noncomputable def choose_SC_no_parallel
  (P : Pack0 α) (hNP : NoParallel0 P) : α :=
  Classical.choose (exists_SC_no_parallel (α := α) P hNP)

@[simp] theorem choose_SC_no_parallel_spec
  (P : Pack0 α) (hNP : NoParallel0 P) :
  P.H.IsSC (choose_SC_no_parallel (α := α) P hNP) :=
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
-- Headがあるかないかの分岐。



--HornWithForbidに移動しても良いし、ここでもよい。
def HasHead1 (F :HornWithForbid  α) (h : α) : Prop :=
  (F.H.prem h).Nonempty

def IsForbidSingleton (F :HornWithForbid  α): Prop :=
  F.F.card = 1

--シングルトンの禁止集合を与えたときに、headがあるかどうか。
def HasHead1s (F :HornWithForbid  α) (fs: IsForbidSingleton F):Prop := by
  let h := Classical.choose (Finset.card_eq_one.mp fs)
  exact (F.H.prem h).Nonempty



-----------------------------------------------------
--新しいローカルカーネル

---contractionでは、閉集合族が閉集合族に。
noncomputable def Q_contraction  {α :Type} [DecidableEq α](P : Pack0 α) (a: α) (hSC: P.H.IsSC a): Pack0 α where
  H := P.H.contraction a
  hDR1 := by exact P.H.contraction_preserves_DR1 P.hDR1 a
  hNEP := by exact contraction_SC_NEP P.H a hSC

---head freeのdeletionは、traceと同じ。だったら最初からtraceと言ってもいい気もするが。
noncomputable def Q_trace {α :Type} [DecidableEq α](P : Pack0 α) (a: α) : Pack0 α where
  H := P.H.trace a
  hDR1 := by exact P.H.trace_preserves_DR1 a P.hDR1
  hNEP :=  P.H.trace_preserves_NEP a P.hNEP

noncomputable def Q_deletion_head {α :Type} [DecidableEq α](P : Pack0 α) (a: α) (hasHead: P.H.hasHead a):HornWithForbid α where
  H := P.H.trace a
  hDR1 := P.H.trace_preserves_DR1 a P.hDR1
  hNEP := P.H.trace_preserves_NEP a P.hNEP
  F := Classical.choose (exists_unique_prem_of_DR1_of_nonempty P.H a P.hDR1 hasHead)  --- headを持つ唯一のルールのpremiseを入れる。
  F_subset_U := by sorry
  F_nonempty := by sorry

-- 新しいローカルカーネル Qcorr編

noncomputable def Qcorr_contraction {α :Type} [DecidableEq α] (F: HornWithForbid α) (a: α) (hSC:F.H.IsSC a) (hA: a ∈ F.F) (geq2: F.F.card ≥ 2):
   HornWithForbid α where
  H := F.H.contraction a
  hDR1 := F.H.contraction_preserves_DR1 F.hDR1 a
  hNEP := contraction_SC_NEP F.H a hSC
  F := F.F.erase a
  F_subset_U := by
    simp_all only [ge_iff_le, contraction_U]
    gcongr
    simp_all only [HornWithForbid.F_subset_U]
  F_nonempty := by
    have hcard : (F.F.erase a).card = F.F.card - 1 :=
    Finset.card_erase_of_mem hA
    -- 2. card ≥ 2 より card - 1 ≥ 1
    have hpos : (F.F.erase a).card > 0 := by
      rw [hcard]
      exact Nat.sub_pos_of_lt geq2   -- または omega / linarith
      -- 3. card > 0 なら Nonempty
    exact Finset.card_pos.mp hpos

/-
  F : Finset α                    -- forbid set
  F_subset_U : F ⊆ H.U
  F_nonempty : F.Nonempty
-/










-----------------------------------------------------
---古いもの。完成したら消す。

---これもHornレベルで定義するべきもの。HornNF.hasHeadを作った。よってこれは使わない。
def HasHead0 (P : Pack0 α) (h : α) : Prop :=
  (P.H.prem h).Nonempty

noncomputable def Q_branch_headFree_get {α :Type} [DecidableEq α](P : Pack0 α) (a: α)  (hs:¬HasHead0 P a):
    ∃ P':Pack0 α , P'.H.U.card = P.H.U.card - 1 ∧ (NDS P.H.U.card P.H.FixSet) ≤ (NDS P'.H.U.card P'.H.FixSet)
  := sorry

theorem Q_branch_headFree
  (n : Nat) (P : Pack0 α) (h : α) :
  (∀ P':Pack0 α, P'.H.U.card = n → Q n P') →
  P.H.U.card = n + 1 → IsSC0 P h → ¬HasHead0 P h →
   Q (n+1) P := by
  intro hQ hn hSC hh
  obtain ⟨P',hP'⟩ := Q_branch_headFree_get P h hh
  dsimp [Q]
  intro hn'
  specialize hQ P'
  have :P'.H.U.card = n := by simp_all only [add_tsub_cancel_right, forall_const]
  specialize hQ this
  dsimp [Q] at hQ
  specialize hQ this
  rw [←this] at hQ
  rw [←hn']
  rcases hP' with ⟨h1,h2⟩
  exact Int.le_trans h2 hQ

noncomputable def Q_branch_hasHead_get {α :Type} [DecidableEq α](P : Pack0 α) (a: α)  (hs:HasHead0 P a):
    ∃ P':Pack0 α , P'.H.U.card = P.H.U.card - 1 ∧ (NDS P.H.U.card P.H.FixSet) ≤ (NDS P'.H.U.card P'.H.FixSet)
:= sorry

theorem Q_branch_hasHead
  (n : Nat) (P : Pack0 α) (h : α) :
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) → (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  P.H.U.card = n + 1 → IsSC0 P h → HasHead0 P h →
  Q (n+1) P := by
  intro hQ hQcorr hn hSC hh
  obtain ⟨P',hP'⟩ := Q_branch_hasHead_get P h hh
  dsimp [Q]
  intro hn'
  specialize hQ P'
  have :P'.H.U.card = n := by simp_all only [add_tsub_cancel_right, forall_const]
  specialize hQ this
  dsimp [Q] at hQ
  specialize hQ this
  rw [←this] at hQ
  rw [←hn']
  rcases hP' with ⟨h1,h2⟩
  exact Int.le_trans h2 hQ

noncomputable def Qcorr_singleton_hasHead_get {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (heq: F.F = {a}) (hs:HasHead1 F a):
    ∃ F':HornWithForbid α , F'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr F.H.U.card) ≤ (F'.NDS_corr (F.H.U.card - 1))
:= sorry

theorem Qcorr_singleton_hasHead
  (n : Nat) (F : HornWithForbid α) :
   (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  F.H.U.card = n + 1 → (fb:IsForbidSingleton F) → HasHead1s F fb→
   Qcorr (n+1) F := by
  intro hQcorr hn hSC hh
  dsimp [IsForbidSingleton] at hSC
  have :∃ a , F.F = {a} := by exact Finset.card_eq_one.mp hSC
  obtain ⟨a,ha⟩ := this
  have : HasHead1 F a := by
    dsimp [HasHead1s] at hh
    simp_all only [Finset.singleton_inj, Classical.choose_eq']
    simp_all only [Finset.card_singleton]
    exact hh
  obtain ⟨F',hF'⟩ := Qcorr_singleton_hasHead_get F a ha this
  dsimp [Qcorr]
  intro hn
  specialize hQcorr F'
  have :F'.H.U.card = n := by
    simp_all only [add_tsub_cancel_right, forall_const]
  specialize hQcorr this
  dsimp [Qcorr] at hQcorr
  specialize hQcorr this
  rw [←hn]
  rw [←this] at hQcorr
  rcases hF' with ⟨h1,h2⟩
  dsimp [HornWithForbid.NDS_corr] at h2
  dsimp [HornWithForbid.BaseC] at h2
  rw [h1] at hQcorr
  --dsimp [HornNF.FixSet] at hQcorr
  --dsimp [HornNF.FixSet] at h2
  exact Int.le_trans h2 hQcorr

noncomputable def Qcorr_singleton_headFree_get {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (heq: F.F = {a}) (hs:¬HasHead1 F a):
    ∃ P':Pack0 α , P'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr F.H.U.card) ≤ (NDS P'.H.U.card P'.H.FixSet)
:= sorry

theorem Qcorr_singleton_headFree
  (n : Nat) (F : HornWithForbid α)  :
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) →
  F.H.U.card = n + 1 → (fb:IsForbidSingleton F) → ¬HasHead1s F fb→
   Qcorr (n+1) F := by
  intro hQ hn hSC hh
  dsimp [IsForbidSingleton] at hSC
  have :∃ a , F.F = {a} := by exact Finset.card_eq_one.mp hSC
  obtain ⟨a,ha⟩ := this
  have : ¬HasHead1 F a := by
    dsimp [HasHead1s] at hh
    simp_all only [Finset.singleton_inj, Classical.choose_eq']
    simp_all only [Finset.card_singleton]
    dsimp [HasHead1]
    exact hh
  obtain ⟨P',hP'⟩ := Qcorr_singleton_headFree_get F a ha this
  dsimp [Qcorr]
  intro hn
  specialize hQ P'
  have :P'.H.U.card = n := by
    simp_all only [add_tsub_cancel_right, forall_const]
  specialize hQ this
  dsimp [Q] at hQ
  specialize hQ this
  rw [←hn]
  rw [←this] at hQ
  rcases hP' with ⟨h1,h2⟩
  dsimp [HornWithForbid.NDS_corr] at h2
  dsimp [HornWithForbid.BaseC] at h2
  rw [h1] at hQ
  rw [h1] at h2
  exact Int.le_trans h2 hQ

noncomputable def Qcorr_ge2_hasHead_get {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (geq2: F.F.card ≥ 2) (ha:a ∈ F.F) (hs:HasHead1 F a):
    ∃ F':HornWithForbid α , F'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr F.H.U.card) ≤ (F'.NDS_corr (F.H.U.card - 1))
:= sorry

theorem Qcorr_ge2_hasHead
  (n : Nat) (F : HornWithForbid α) (a : α) (hh : a ∈ F.F):
   (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  F.H.U.card = n + 1 → ¬IsForbidSingleton F → IsSC1 F a → HasHead1 F a →
   Qcorr (n+1) F
:= by
  -- 1. Introduce all hypotheses.
  intro hQ_forbid hn_card h_not_singleton h_sc1 h_has_head

  -- 2. Prepare arguments for the `_get` function.
  -- We need to show `F.F.card ≥ 2` from `¬IsForbidSingleton F`.
  have h_geq2 : F.F.card ≥ 2 := by
    dsimp [IsForbidSingleton] at h_not_singleton
    -- F.F is non-empty and its card is not 1, so it must be ≥ 2.
    have h_nonempty : F.F.Nonempty := F.F_nonempty
    cases h_card_cases : F.F.card with -- `card_cases` lemma from this file can be used.
    | zero => exfalso; simp_all only [zero_ne_one, not_false_eq_true, Finset.card_eq_zero, Finset.notMem_empty]
    | succ m =>
      cases m with
      | zero => -- card = 1
        exfalso; exact h_not_singleton (by simp [h_card_cases])
      | succ m' => -- card = m' + 2 ≥ 2
        apply Nat.le_add_left

  -- 3. Obtain the smaller problem `F'` using the `_get`
  obtain ⟨F', hF'⟩ := Qcorr_ge2_hasHead_get F a h_geq2 hh h_has_head
  rcases hF' with ⟨hF'_card, h_ineq⟩

  -- The goal is `Qcorr (n+1) F`, which unfolds to `F.NDS_corr (n+1) ≤ 0`.
  -- We use the induction hypothesis `hQ_forbid` on the smaller problem `F'`.
  -- 4. First, show `F'` has the correct card size for the IH.
  have hF'_card_n : F'.H.U.card = n := by
    rw [hF'_card, hn_card]
    simp -- n + 1 - 1 = n

  -- 5. Apply the induction hypothesis to F'.
  specialize hQ_forbid F' hF'_card_n
  -- Now `hQ_forbid` is the proposition `Qcorr n F'`, which is `F'.NDS_corr n ≤ 0`.

  -- 6. Chain the inequalities to prove the goal.
  -- `h_ineq` (from `_get`) gives `F.NDS_corr (n+1) ≤ F'.NDS_corr n`.
  -- `hQ_forbid` (from IH) gives `F'.NDS_corr n ≤ 0`.
  rw [hn_card] at h_ineq
  dsimp [Qcorr]
  intro hn
  exact Int.le_trans h_ineq (hQ_forbid hF'_card_n)


noncomputable def Qcorr_ge2_headFree_get {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (geq2: F.F.card ≥ 2) (ha:a ∈ F.F) (hs:¬HasHead1 F a):
    ∃ P':Pack0 α , P'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr F.H.U.card) ≤ (NDS P'.H.U.card P'.H.FixSet)
:= sorry

theorem Qcorr_ge2_headFree
  (n : Nat) (F : HornWithForbid α) (a : α) (ha : a ∈ F.F):
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) →
  F.H.U.card = n + 1 → ¬IsForbidSingleton F → IsSC1 F a → ¬HasHead1 F a →
  Qcorr (n+1) F := by
  intro hQ hn hs hSC hh
  have geq2: F.F.card ≥ 2:= by
    dsimp [IsForbidSingleton] at hs
    have ne := HornWithForbid.F_nonempty (α := α) F
    apply (Nat.two_le_iff F.F.card).mpr
    simp_all only [ne_eq, Finset.card_eq_zero, not_false_eq_true, and_true]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    simp_all only [Finset.notMem_empty]
  obtain ⟨P',hP'⟩ := Qcorr_ge2_headFree_get F a geq2 ha hh
  dsimp [Qcorr]
  intro hn
  specialize hQ P'
  have :P'.H.U.card = n := by
    simp_all only [add_tsub_cancel_right, forall_const]
  specialize hQ this
  dsimp [Q] at hQ
  specialize hQ this
  rw [←hn]
  rw [←this] at hQ
  rcases hP' with ⟨h1,h2⟩
  dsimp [HornWithForbid.NDS_corr] at h2
  dsimp [HornWithForbid.BaseC] at h2
  rw [h1] at hQ
  rw [h1] at h2
  exact Int.le_trans h2 hQ

--禁止集合の閉包をとってもNDSが変わらないというものは、HornNormalizeにおいている。

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

----これに気が付かずにQ_traceとして再実装した。こっちを消す。

noncomputable def tracePack0 (P : Pack0 α) (a : α) : Pack0 α :=
  { H := P.H.trace a
    hDR1 := by
      -- DR1 is preserved by trace (proved in the Horn layer).
      have hDR1' : HornNF.DR1 P.H := by
        simpa [HornNF.IsDR1, HornNF.DR1] using P.hDR1
      have hDR1'' : HornNF.DR1 (HornNF.trace P.H a) :=
        HornNF.trace_preserves_DR1 (H := P.H) (u := a) hDR1'
      simpa [HornNF.IsDR1, HornNF.DR1] using hDR1''
    hNEP := by exact P.H.trace_preserves_NEP a P.hNEP
  }



end Dr1nds
