-- Dr1nds/Induction/LocalKernels.lean
import Mathlib.Tactic
import Dr1nds.S0_CoreDefs
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.HornNormalize
import Dr1nds.Forbid.Basic
import Dr1nds.Forbid.HornWithForbid
import Dr1nds.Forbid.HornBridge
import Dr1nds.Forbid.Singleton
import Dr1nds.Induction.Statements
--import LeanCopilot
set_option maxHeartbeats 10000000

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/-!
# Induction/LocalKernels.lean (S11 aggregator)

This file is the **single entry point** for the induction wiring (`Induction/Steps.lean`).

## Policy & Design (Reflecting User Requirements)
1. **SetFamily with Universe**: We assume `HornNF` and `FixSet` carry the universe information `U`.
   `NDS` and `NDS_corr` calculations depend on this universe.
2. **NEP**: We distinguish between NEP of the family and NEP of the rules.
3. **Horn Rules**: We do *not* assume DR1 or Head-Full initially for the general `HornNF` structure.
   - **Head-free**: No rule has head `v`. In this case, deletion = trace.
   - **DR1**: Each head has at most one premise.
   - **Parallel**: Defined via closure (`u ∈ cl v` and `v ∈ cl u`).
   However, `Pack1` enforces `DR1` via hypothesis `hDR1`.
4. **Hole Family**: A family with forbid set `A` is `Hole(D, A)`. `D` is a closed family (written by Horn rules).
   `Pack1` represents this.
5. **Closure of A**: `Pack1.A` is the closure of the raw forbid set. Taking closure does not change the hole family.
6. **Normalization**: Removing rules that contain `A` (subset of premise) does not change the hole family (normalization).
   `NDS_corr` does not decrease under this normalization (`ndscorr_singleton_normalize_le`).
   We prove non-positivity for the normalized system, which implies it for the original.
7. **Induction Strategy**:
   - Branch on `|A|=1` vs `|A| >= 2`.
   - `|A|=1`: Use normalization and deletion (trace).
   - `|A|>=2`: Use SC contraction (monotone).

## Contract (frozen)
- `Steps.lean` performs only case splits and calls kernels from this file.
- All heavy mathematics lives in *kernels* here (currently frozen as `axiom`).
- Kernels must never mix the two worlds:
  * `Pack0` (forbid-free)
  * `Pack1` (with one forbid set `A`)
-/

-- =====================================
-- (S) Predicate placeholders (to be refined)
--
-- IMPORTANT:
--   These are *temporary* `abbrev := True` so that the project compiles while we freeze the API.
--   They must be replaced by the actual predicates defined in `Induction/Statements.lean`.
-- =====================================

/- Parallel / NoParallel for forbid-free packs. -/
abbrev Parallel0 (P : Pack0 α) : Prop := True
abbrev NoParallel0 (P : Pack0 α) : Prop := True

/-- SC / head-structure predicates for forbid-free packs. -/
abbrev IsSC0 (P : Pack0 α) (h : α) : Prop := True
/--
Real head-existence predicate (temporary concrete version).

We intentionally make this *nontrivial* (unlike the old `:= True` placeholder),
so that the singleton-forbid kernel can split by `head=a`.

Semantics: `HasHead* P h` means there exists at least one premise for head `h`.
This uses the underlying `HornNF` data carried by the pack.
-/
def HasHead0 (P : Pack0 α) (h : α) : Prop :=
  (P.H.prem h).Nonempty
abbrev UnaryHead0 (P : Pack0 α) (h v : α) : Prop := True
abbrev NonUnaryHead0 (P : Pack0 α) (h : α) : Prop := True

/-- Parallel / NoParallel for forbid packs. -/
abbrev Parallel1 (P : Pack1 α) : Prop := True
abbrev NoParallel1 (P : Pack1 α) : Prop := True

/-- SC / head-structure predicates for forbid packs. -/
abbrev IsSC1 (P : Pack1 α) (h : α) : Prop := True
/- With-forbid version of head-existence. -/
def HasHead1 (P : Pack1 α) (h : α) : Prop :=
  (P.S.H.prem h).Nonempty
abbrev UnaryHead1 (P : Pack1 α) (h v : α) : Prop := True
abbrev NonUnaryHead1 (P : Pack1 α) (h : α) : Prop := True

/-- Convenience: "no head" means the negation of `HasHead*`. -/
abbrev NoHead0 (P : Pack0 α) (h : α) : Prop := ¬ HasHead0 P h
abbrev NoHead1 (P : Pack1 α) (h : α) : Prop := ¬ HasHead1 P h


/-
(API) Trace packs for singleton reduction.

We now define these packs concretely.
- `tracePack0` drops the forbid world to a forbid-free pack over `H.trace a`.
- `tracePack1WithPrem` stays in the forbid world: we trace the HornNF at `a` and
  set the new forbid set to `Pprem`.

Both rely on the corresponding constructors/operations in `HornWithForbid`.
-/

noncomputable def Pack1.tracePack0 (P : Pack1 α) (a : α) : Pack0 α :=
  { H := P.S.H.trace a
    hDR1 := by
      -- DR1 is preserved by trace (proved in the Horn layer).
      have hDR1' : HornNF.DR1 P.S.H := by
        simpa [HornNF.IsDR1, HornNF.DR1] using P.S.hDR1
      have hDR1'' : HornNF.DR1 (HornNF.trace P.S.H a) :=
        HornNF.trace_preserves_DR1 (H := P.S.H) (u := a) hDR1'
      simpa [HornNF.IsDR1, HornNF.DR1] using hDR1'' }

/-/
Trace-with-prem pack used in the singleton-forbid / has-head branch.

Design intent:
- underlying HornNF world is traced at `a`, i.e. `P.S.H.trace a`;
- the new forbid set is `Pprem`.

NOTE: This definition assumes the existence of a constructor-level operation
`HornWithForbid.traceWithPrem` (defined in `Forbid/HornWithForbid.lean`), which
is responsible for discharging the structural obligations for the new forbid set
in the traced world.

If your project uses a different name, update the single line `S := ...` accordingly.
-/
noncomputable def Pack1.tracePack1WithPrem
  (P : Pack1 α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (P.S.H.trace a).U)
  (hPne : Praw.Nonempty) : Pack1 α :=
  let Hn := HornNF.normalizePrem P.S.H a
  let Sn : HornWithForbid α := {
    H := Hn
    hDR1 := HornNF.normalizePreservesDR1 P.S.H a P.S.hDR1
    F := P.S.F
    F_subset_U := by simp [Hn, HornNF.normalizePrem]; exact P.S.F_subset_U
    F_nonempty := P.S.F_nonempty
  }
  have hPsub' : Praw ⊆ (Sn.H.trace a).U := by
    rw [Sn, Hn, HornNF.normalizePrem, HornNF.normalize, HornNF.trace]
    simp [HornNF.trace] at hPsub ⊢
    exact hPsub
  { S := traceWithPremClosure (α := α) Sn a Praw hPsub' hPne }

/- Expected semantics of the trace-with-prem pack. -/
@[simp] theorem Pack1.tracePack1WithPrem_C
  (P : Pack1 α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (P.S.H.trace a).U)
  (hPne : Praw.Nonempty) :
  Pack1.C (Pack1.tracePack1WithPrem (α := α) P a Praw hPsub hPne)
    = HornNF.FixSet ((HornNF.normalizePrem P.S.H a).trace a) :=
by
  classical
  simp [Pack1.tracePack1WithPrem, Pack1.C, traceWithPremClosure_H]

@[simp] theorem Pack1.tracePack1WithPrem_A
  (P : Pack1 α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (P.S.H.trace a).U)
  (hPne : Praw.Nonempty) :
  Pack1.A (Pack1.tracePack1WithPrem (α := α) P a Praw hPsub hPne)
    = HornNF.closure ((HornNF.normalizePrem P.S.H a).trace a) Praw :=
by
  classical
  -- `Pack1.A` is defined as `closure(Araw)`.
  -- For the trace-with-prem pack, `Araw` is set to `closure Praw`.
  -- So `Pack1.A` is `closure (closure Praw)`, which is `closure Praw`.
  simp [Pack1.tracePack1WithPrem, Pack1.A, Pack1.Araw, traceWithPremClosure_F]
  apply HornNF.closure_idempotent



theorem hole_fixset_singleton_eq_hole_trace_prem
  (H : HornNF α) (hDR1 : HornNF.DR1 H) (a : α) (Pprem : Finset α)
  (h_prem_a : H.prem a = {Pprem})
  (h_norm : ∀ {h Q}, Q ∈ H.prem h → a ∉ Q) :
  Hole (α := α) (HornNF.FixSet H) {a}
    =
  Hole (α := α) (HornNF.FixSet (H.trace a)) Pprem := by
  sorry

-- =====================================
-- (0) parallel / no-parallel 分岐（独立核）
-- =====================================

/-
Parallel-branch kernels are treated as an *independent core*:
They close the goal using trace-reduction logic and do not depend on the SC-based branch.
-/

/-- Parallel-branch (forbid-free): if `Parallel0 P` holds, we can close `Q n P` by the trace reduction core. -/
axiom Q_of_parallel
  (n : Nat) (P : Pack0 α) :
  Parallel0 P → Q n P

/-- Wiring helper: advance one step under the parallel-branch (forbid-free). -/
axiom Q_succ_of_parallel
  (n : Nat) (P : Pack0 α) :
  Parallel0 P → Q n P → Q (n+1) P

/-- Parallel-branch (with forbid): if `Parallel1 P` holds, we can close `Qcorr n P` by the trace reduction core. -/
axiom Qcorr_of_parallel
  (n : Nat) (P : Pack1 α) :
  Parallel1 P → Qcorr n P

/-- Wiring helper: advance one step under the parallel-branch (with forbid). -/
axiom Qcorr_succ_of_parallel
  (n : Nat) (P : Pack1 α) :
  Parallel1 P → Qcorr n P → Qcorr (n+1) P

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

/--
Design note: in the forbid-world we must pick the SC point **inside** `A`.
If we contracted at `h ∉ A`, the forbid-update could introduce a *second* forbid set.
Keeping `h ∈ A` ensures the forbid does not proliferate.
-/

/- No-parallel (with forbid) implies existence of an SC point *inside* the forbid set `A`.
    Picking `h ∈ A` is crucial: it prevents the forbid-update from introducing a second forbid set. -/
axiom exists_SC_in_forbid
  (P : Pack1 α) :
  NoParallel1 P → ∃ h : α, h ∈ P.A ∧ IsSC1 P h

/-- Noncomputably pick an SC point inside `A` from `exists_SC_in_forbid`. -/
noncomputable def choose_SC_in_forbid
  (P : Pack1 α) (hNP : NoParallel1 P) : α :=
  Classical.choose (exists_SC_in_forbid (α := α) P hNP)

@[simp] theorem choose_SC_in_forbid_mem
  (P : Pack1 α) (hNP : NoParallel1 P) :
  choose_SC_in_forbid (α := α) P hNP ∈ P.A :=
by
  simpa [choose_SC_in_forbid] using (Classical.choose_spec (exists_SC_in_forbid (α := α) P hNP)).1

@[simp] theorem choose_SC_in_forbid_spec
  (P : Pack1 α) (hNP : NoParallel1 P) :
  IsSC1 P (choose_SC_in_forbid (α := α) P hNP) :=
by
  simpa [choose_SC_in_forbid] using (Classical.choose_spec (exists_SC_in_forbid (α := α) P hNP)).2


/-
(1) forbid-free SC step (3-way split)

Given an SC point `h` in `Pack0`, we split by the head-structure at `h`:
  (i)  no head at `h`
  (ii) unary head at `h`
  (iii) non-unary head at `h`

Each branch is a local kernel that advances `Q n P → Q (n+1) P`.
-/
axiom Q_branch_noHead
  (n : Nat) (P : Pack0 α) (h : α) :
  IsSC0 P h → NoHead0 P h →
  Q n P → Q (n+1) P

axiom Q_branch_unaryHead
  (n : Nat) (P : Pack0 α) (h v : α) :
  IsSC0 P h → UnaryHead0 P h v →
  Q n P → Q (n+1) P

axiom Q_branch_nonUnaryHead
  (n : Nat) (P : Pack0 α) (h : α) :
  IsSC0 P h → NonUnaryHead0 P h →
  Q n P → Q (n+1) P



/-
(2) forbid world: split by `|A|`.

`card_cases` is a wiring helper: it is independent from the Horn/closure semantics.
We use `omit [DecidableEq α]` to keep the lemma as general as possible; the proof re-introduces `classical`.
-/
omit [DecidableEq α] in
/-- Card-split helper: any finite set has either card = 0, card = 1, or card ≥ 2. -/
lemma card_cases
  (A : Finset α) :
  A.card = 0 ∨ A.card = 1 ∨ 2 ≤ A.card := by
  classical
  have h : A.card = 0 ∨ A.card = 1 ∨ 2 ≤ A.card := by
    omega
  exact h

-- TODO: once `Pack1` enforces `A.Nonempty`, the `card = 0` branch becomes unreachable.
-- Then we can delete `Qcorr_handle_A_empty` and simplify wiring.


/--
Helper lemma: in the DR1 world, if a head exists then the premise is unique.

This is used only at the wiring layer: once we know `HasHead1 P h`, DR1 forces
`(prem h).card = 1`.
-/
theorem prem_card_eq_one_of_hasHead1
  (P : Pack1 α) (h : α) :
  HasHead1 P h → (P.S.H.prem h).card = 1 := by
  intro hHead
  have hle : (P.S.H.prem h).card ≤ 1 := by
    simpa using (P.S.hDR1 h)
  have hpos : 0 < (P.S.H.prem h).card := by
    exact Finset.card_pos.mpr hHead
  have hone_le : 1 ≤ (P.S.H.prem h).card :=
    Nat.succ_le_of_lt hpos
  exact Nat.le_antisymm hle hone_le

/-- Noncomputably pick a premise for head `h` in a forbid-pack, assuming `HasHead1`. -/
noncomputable def choose_prem1
  (P : Pack1 α) (h : α) (hHead : HasHead1 P h) : Finset α :=
  Classical.choose hHead

@[simp] theorem choose_prem1_mem
  (P : Pack1 α) (h : α) (hHead : HasHead1 P h) :
  choose_prem1 (α := α) P h hHead ∈ P.S.H.prem h :=
  Classical.choose_spec hHead

/-- Under DR1, the chosen premise is the unique premise (cardinality form). -/
@[simp] theorem prem_card_eq_one_of_choose_prem1
  (P : Pack1 α) (h : α) (hHead : HasHead1 P h) :
  (P.S.H.prem h).card = 1 :=
by
  exact prem_card_eq_one_of_hasHead1 (α := α) (P := P) (h := h) hHead

/-- Under DR1, any premise membership forces the whole premise family to be a singleton. -/
lemma prem_eq_singleton_of_DR1_of_mem1
  (P : Pack1 α) (h : α) (Q : Finset α) :
  Q ∈ P.S.H.prem h → (P.S.H.prem h).card = 1 →
  P.S.H.prem h = ({Q} : Finset (Finset α)) :=
by
  classical
  intro hQ hcard
  -- Use `card = 1` to show all elements equal to `Q`.
  apply Finset.eq_singleton_iff_unique_mem.2
  refine ⟨hQ, ?_⟩
  intro R hR
  -- If a finset has card 1, all its members are equal.
  have : R = Q := by
    -- In a finset of card 1, any two members coincide.
    -- We can use `Finset.card_eq_one.1` to obtain a singleton representation.
    rcases Finset.card_eq_one.mp hcard with ⟨Q0, hEq⟩
    have hQ' : Q = Q0 := by
      have : Q ∈ ({Q0} : Finset (Finset α)) := by simpa [hEq] using hQ
      simpa using (Finset.mem_singleton.mp this)
    have hR' : R = Q0 := by
      have : R ∈ ({Q0} : Finset (Finset α)) := by simpa [hEq] using hR
      simpa using (Finset.mem_singleton.mp this)
    simpa [hQ', hR']
  simpa [this]

/-- Convenience: the chosen premise witnesses `prem h = {Q}` under DR1. -/
lemma prem_eq_singleton_of_choose_prem1
  (P : Pack1 α) (h : α) (hHead : HasHead1 P h) :
  P.S.H.prem h = ({choose_prem1 (α := α) P h hHead} : Finset (Finset α)) :=
by
  classical
  apply prem_eq_singleton_of_DR1_of_mem1 (α := α) (P := P) (h := h)
    (Q := choose_prem1 (α := α) P h hHead)
  · simpa using choose_prem1_mem (α := α) P h hHead
  · simpa using prem_card_eq_one_of_choose_prem1 (α := α) P h hHead


/--
Helper lemma (LocalKernels): in the DR1 world, if a head exists then the premise is unique.

We use a suffix `_LK` to avoid name clashes with similarly named lemmas living in `Horn.lean` / `HornBridge.lean`.
-/
theorem prem_card_eq_one_of_hasHead1_LK
  (P : Pack1 α) (h : α) :
  HasHead1 P h → (P.S.H.prem h).card = 1 := by
  intro hHead
  have hle : (P.S.H.prem h).card ≤ 1 := by
    simpa using (P.S.hDR1 h)
  have hpos : 0 < (P.S.H.prem h).card := by
    exact Finset.card_pos.mpr hHead
  have hone_le : 1 ≤ (P.S.H.prem h).card :=
    Nat.succ_le_of_lt hpos
  exact Nat.le_antisymm hle hone_le

/-- Noncomputably pick a premise for head `h` in a forbid-pack, assuming `HasHead1`. -/
noncomputable def choose_prem1_LK
  (P : Pack1 α) (h : α) (hHead : HasHead1 P h) : Finset α :=
  Classical.choose hHead

@[simp] theorem choose_prem1_LK_mem
  (P : Pack1 α) (h : α) (hHead : HasHead1 P h) :
  choose_prem1_LK (α := α) P h hHead ∈ P.S.H.prem h :=
  Classical.choose_spec hHead

@[simp] theorem prem_card_eq_one_of_choose_prem1_LK
  (P : Pack1 α) (h : α) (hHead : HasHead1 P h) :
  (P.S.H.prem h).card = 1 :=
by
  exact prem_card_eq_one_of_hasHead1_LK (α := α) (P := P) (h := h) hHead

/--
Under DR1, any premise membership forces the whole premise family to be a singleton.
(Kept locally to avoid importing extra lemmas.)
-/
lemma prem_eq_singleton_of_DR1_of_mem1_LK
  (P : Pack1 α) (h : α) (Q : Finset α) :
  Q ∈ P.S.H.prem h → (P.S.H.prem h).card = 1 →
  P.S.H.prem h = ({Q} : Finset (Finset α)) :=
by
  classical
  intro hQ hcard
  apply Finset.eq_singleton_iff_unique_mem.2
  refine ⟨hQ, ?_⟩
  intro R hR
  rcases Finset.card_eq_one.mp hcard with ⟨Q0, hEq⟩
  have hQ' : Q = Q0 := by
    have : Q ∈ ({Q0} : Finset (Finset α)) := by
      simpa [hEq] using hQ
    simpa using (Finset.mem_singleton.mp this)
  have hR' : R = Q0 := by
    have : R ∈ ({Q0} : Finset (Finset α)) := by
      simpa [hEq] using hR
    simpa using (Finset.mem_singleton.mp this)
  simpa [hQ', hR']

/-- Convenience: the chosen premise witnesses `prem h = {Q}` under DR1. -/
lemma prem_eq_singleton_of_choose_prem1_LK
  (P : Pack1 α) (h : α) (hHead : HasHead1 P h) :
  P.S.H.prem h = ({choose_prem1_LK (α := α) P h hHead} : Finset (Finset α)) :=
by
  classical
  apply prem_eq_singleton_of_DR1_of_mem1_LK (α := α) (P := P) (h := h)
    (Q := choose_prem1_LK (α := α) P h hHead)
  · simpa using choose_prem1_LK_mem (α := α) P h hHead
  · simpa using prem_card_eq_one_of_choose_prem1_LK (α := α) P h hHead

/--
Kernel for the singleton-forbid, has-head case on a *normalized* Horn system.

If `H` is `a`-normalized (no premise contains `a`), and `prem a = {Pprem}`,
then the `NDS_corr` for `({a}, n+1)` can be bounded by the `NDS_corr` for `(Pprem, n)`
in the traced world.

Policy: "If `a` has a head `P -> a`, then deletion of `a` yields the same family on `U \ {a}`
(only universe differs). The new forbid set is `P`.
|UP| count is also the same before and after."
-/
axiom qcorr_singleton_hasHead_normalized_step
  (n : Nat) (H : HornNF α) (a : α)
  (h_norm : ∀ {h Q}, Q ∈ H.prem h → a ∉ Q)
  (Pprem : Finset α)
  (h_prem_a : H.prem a = {Pprem})
  (h_IH : NDS_corr n (HornNF.FixSet (H.trace a)) Pprem ≤ 0) :
  NDS_corr (n+1) (HornNF.FixSet H) {a} ≤ 0




/-/
-- Has-head singleton kernel after normalization.
--
-- This lemma isolates the heavy call to `qcorr_singleton_hasHead_P_step` so that
-- `Qcorr_handle_A_singleton` stays lightweight for elaboration.
-/
lemma qcorr_singleton_hasHead_normalized
  (n : Nat)
  (P : Pack1 α) (a : α)
  (Pprem : Finset α)
  (hmem : Pprem ∈ P.S.H.prem a)
  (hcard : (P.S.H.prem a).card = 1)
  (hvU : a ∈ P.S.H.U)
  (hQ_trace : NDS_corr (α := α) n (HornNF.FixSet ((HornNF.normalizePrem P.S.H a).trace a)) Pprem ≤ 0) :
  NDS_corr (α := α) n.succ (HornNF.FixSet (HornNF.normalizePrem (α := α) P.S.H a)) ({a} : Finset α) ≤ 0 := by
  -- 1. Define the normalized system.
  let Hn := HornNF.normalizePrem (α := α) P.S.H a

  -- 2. Apply the dedicated step kernel for normalized systems with a single-premise head.
  apply qcorr_singleton_hasHead_normalized_step (n := n) (H := Hn) (a := a)

  -- 3. Discharge the kernel's side conditions.
  -- 3a. Show that Hn is indeed `a`-normalized. This is true by definition of `normalizePrem`.
  · exact HornNF.normalizePrem_noPremContains (α := α) P.S.H a

  -- 3b. Show that `Hn.prem a = {Pprem}`.
  · -- First, establish that `P.S.H.prem a` is the singleton `{Pprem}`.
    have h_prem_a_orig : P.S.H.prem a = {Pprem} := by
      apply prem_eq_singleton_of_DR1_of_mem1 (α := α) (P := P) (h := a) (Q := Pprem)
      · exact hmem
      · exact hcard

    -- Normalization filters premises `Q` where `a ∉ Q`. We must show `a ∉ Pprem`.
    -- This follows from the DR1 property, which forbids self-dependencies.
    have ha_notin_Pprem : a ∉ Pprem := by
      apply P.S.H.nf (h := a) (P := Pprem)
      exact hmem

    -- With `a ∉ Pprem`, the filter in `normalizePrem` is a no-op for `prem a`.
    simp [Hn, HornNF.normalize, h_prem_a_orig]
    ext a_1 : 1
    simp_all only [Finset.mem_singleton, Finset.card_singleton, Finset.mem_filter]
    apply Iff.intro
    intro a_2
    on_goal 2 => intro a_2
    on_goal 2 => subst a_2
    on_goal 2 => apply And.intro
    on_goal 2 => { rfl
    }
    simp_all only [Finset.mem_singleton, Finset.card_singleton]
    · simp_all only [Finset.mem_singleton, Finset.card_singleton, not_false_eq_true]

  -- 3c. Provide the induction hypothesis, transferred to the traced normalized world.
  · -- We use `trace_normalizePrem_eq_trace` to show that the traced worlds are identical.
    exact hQ_trace

/-/
`|A| = 1` branch (singleton-forbid kernel, rewired to the correct IH packs).

Wiring-only lemma:
- Split by `HasHead1 P a`.
- Route IH to the appropriate trace pack and call the corresponding singleton-step kernel.

NOTE: This lemma must NOT take `Qcorr n P` as IH. The IH lives on the trace world.
-/
theorem Qcorr_handle_A_singleton
  (n : Nat) (P : Pack1 α) (a : α) :
  P.A = ({a} : Finset α) →
  (NoHead1 P a → Q n (Pack1.tracePack0 (α := α) P a)) →
  (HasHead1 P a →
    ∃ Pprem,
      Pprem ∈ P.S.H.prem a ∧
      (P.S.H.prem a).card = 1 ∧
      ∃ hPsub : Pprem ⊆ (P.S.H.trace a).U,
      ∃ hPne : Pprem.Nonempty, -- No hPclosed required here
        Qcorr n (Pack1.tracePack1WithPrem (α := α) P a Pprem hPsub hPne)) →
  Qcorr (n+1) P :=
by
  intro hA h_no_head_IH h_has_head_IH
  -- The goal is `Qcorr (n+1) P`. By `hA`, `P.A = {a}`.
  rw [hA] at *; clear hA

  -- We split on whether `a` is a head or not.
  by_cases h_head_case : HasHead1 P a

  -- Case 1: `a` has a head.
  · -- 1a. Obtain the premise `Pprem` (raw) and the induction hypothesis for the traced world.
    rcases h_has_head_IH h_head_case with ⟨Pprem, h_prem_mem, h_prem_card, hPsub, hPne, h_qcorr_trace⟩

    -- 1b. Unfold the IH `Qcorr` into the `NDS_corr` inequality.
    have h_IH_nds : NDS_corr n (HornNF.FixSet ((HornNF.normalizePrem P.S.H a).trace a)) (HornNF.closure ((HornNF.normalizePrem P.S.H a).trace a) Pprem) ≤ 0 := by
      simpa [Qcorr, Pack1.tracePack1WithPrem_C, Pack1.tracePack1WithPrem_A] using h_qcorr_trace

    -- 1c. The goal is `Qcorr (n+1) P`, which is `NDS_corr (n+1) (FixSet P.S.H) {a} ≤ 0`.
    -- We use the normalization strategy. Normalization preserves `NDS_corr` for singleton forbid.
    rw [Qcorr, Pack1.C, hA]
    dsimp [NDS_corr]
    apply le_trans (HornNF.ndscorr_singleton_normalize_le (n.succ) P.S.H a)

    -- 1d. Now the goal is `NDS_corr (n.succ) (FixSet (normalizePrem P.S.H a)) {a} ≤ 0`.
    -- This is exactly what `qcorr_singleton_hasHead_normalized` proves.
    apply qcorr_singleton_hasHead_normalized
    · exact h_prem_mem
    · exact h_prem_card
    · -- We need `a ∈ P.S.H.U`. This follows from `a ∈ P.A` and `P.A ⊆ P.S.H.U`.
      have ha_in_A : a ∈ P.A := by simp
      have hA_sub_U : P.A ⊆ P.S.H.U := HornNF.closure_subset_U P.S.hFsub
      exact hA_sub_U ha_in_A
    · exact h_IH_nds

  -- Case 2: `a` has no head.
  · -- 2a. Obtain the induction hypothesis for the traced world (forbid-free).
    have h_q_trace := h_no_head_IH h_head_case
    -- 2b. Normalize P.S.H to Hn.
    let Hn := HornNF.normalizePrem P.S.H a
    apply le_trans (HornNF.ndscorr_singleton_normalize_le (n.succ) P.S.H a)
    apply qcorr_singleton_noHead_step n Hn a
    · have ha_in_A : a ∈ P.A := by simp
      have hA_sub_U : P.A ⊆ P.S.H.U := HornNF.closure_subset_U P.S.hFsub
      exact hA_sub_U ha_in_A
    · simp [Hn, HornNF.normalizePrem, HornNF.normalize]
      rw [Finset.filter_eq_empty_iff]
      intro P hP
      have : P.S.H.prem a = ∅ := by
         rw [Finset.eq_empty_iff_forall_not_mem]
         intro x hx
         exact h_head_case ⟨x, hx⟩
      rw [this] at hP
      contradiction
    · exact HornNF.normalizePrem_noPremContains P.S.H a
    · rw [HornNF.trace_normalizePrem_eq_of_head_free]
      · exact h_q_trace
      · rw [Finset.eq_empty_iff_forall_not_mem]
        intro x hx
        exact h_head_case ⟨x, hx⟩

/--
|A| = 0 branch (temporary).

In the final spec we expect `Pack1` to enforce `A.Nonempty`, making this case unreachable.
We keep it as a separate kernel for now to avoid re-wiring churn while the pack definitions evolve.

In particular, **do not** route `A.card = 0` into the singleton kernel.
That would conflate two different reduction patterns.
-/
axiom Qcorr_handle_A_empty
  (n : Nat) (P : Pack1 α) :
  (P.A).card = 0 →
  Qcorr n P → Qcorr (n+1) P

/--
|A| ≥ 2 branch (SC step inside the forbid set).

Policy: pick `h ∈ A` which is SC in the forbid-pack sense, and apply the SC-contraction step.
The side condition `h ∈ A` is essential: contracting outside `A` could introduce a new forbid set.
In this branch, it is expected that `NDS_corr` is **monotone (nondecreasing) under contraction at SC points**.
-/
axiom Qcorr_branch_A_ge2
  (n : Nat) (P : Pack1 α) (h : α) :
  IsSC1 P h → h ∈ P.A →
  Qcorr n P → Qcorr (n+1) P

#print axioms Dr1nds.Qcorr_handle_A_singleton


end Dr1nds
