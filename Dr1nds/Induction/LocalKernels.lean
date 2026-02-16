-- Dr1nds/Induction/LocalKernels.lean
import Mathlib.Tactic
import Dr1nds.Induction.Statements
import Dr1nds.Forbid.Basic
import Dr1nds.S0_CoreDefs

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/-!
# Induction/LocalKernels.lean (S11 aggregator)

This file is the **single entry point** for the induction wiring (`Induction/Steps.lean`).

## Contract (frozen)
- `Steps.lean` performs only case splits and calls kernels from this file.
- All heavy mathematics lives in *kernels* here (currently frozen as `axiom`).
- Kernels must never mix the two worlds:
  * `Pack0` (forbid-free)
  * `Pack1` (with one forbid set `A`)

## TODO roadmap (implementation order suggestion)
1. Replace the placeholder predicates (`Parallel0`, `IsSC1`, ...) by the real ones from `Induction/Statements.lean`.
2. Implement the `|A| = 1` kernel (`Qcorr_handle_A_singleton`) via the singleton-forbid reduction.
3. Implement the `|A| ≥ 2` kernel (`Qcorr_branch_A_ge2`) using SC-contraction monotonicity of `NDS_corr`.
4. Keep `A.card = 0` only until `Pack1` enforces `A.Nonempty`.
-/



/-
S11 (Induction/LocalKernels): **Local kernel API aggregator**.

Purpose
- S10 (wiring) should import ONLY this file and perform case splits.
- All mathematically heavy steps live here as *named kernels* (currently frozen as `axiom`).

Design rules (frozen)
1. forbid-free (`Pack0`) and with-forbid (`Pack1`) are **never mixed** in one lemma.
2. `|A| = 1` is handled by a **dedicated singleton kernel** (typically a deletion-world reduction).
3. `|A| ≥ 2` uses the **SC-contraction kernel** with `h ∈ A` to avoid introducing a second forbid.
4. Parallel-branch (trace reduction) is an **independent core**: it provides its own step lemmas.

Implementation note
- At this stage we intentionally keep internal predicates as placeholders (see section (S)).
  These will be replaced by the real definitions in `Induction/Statements.lean`.
- The goal right now is to stabilize *wiring-level names and signatures*.
-/

/--
NOTE (frozen wiring discipline)

* This file is the ONLY place where `Steps.lean` is allowed to call “heavy math”.
* `Steps.lean` must remain pure case-splitting + application of the kernels here.
* Kernels are kept as `axiom` for now to stabilize names/signatures.

When we later replace placeholders (`Parallel0`, `IsSC1`, ...), the *signatures in Steps* must not change.
Only the meaning of these predicates is allowed to change.
-/

/-
(S) Predicate placeholders

We intentionally freeze **names** of the hypotheses that the wiring layer will mention.
At the moment they are defined as `abbrev ... := True` so that we can:
- stabilize file/module boundaries,
- stabilize `Steps.lean` signatures,
- iterate on the mathematical content *without* rewiring.

Later, each placeholder will be replaced by the real predicate from `Induction/Statements.lean`.
Crucially: **the argument lists in `Steps.lean` must not change**; only the meaning of the predicates changes.
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
  -- use Nat.lt_trichotomy / linear arithmetic on Nat
  have h : A.card = 0 ∨ A.card = 1 ∨ 2 ≤ A.card := by
    omega
  exact h

-- TODO: once `Pack1` enforces `A.Nonempty`, the `card = 0` branch becomes unreachable.
-- Then we can delete `Qcorr_handle_A_empty` and simplify wiring.


/--
Helper axiom (temporary): in the DR1 world, if a head exists then the premise is unique.

This is a placeholder to keep the wiring stable while we move the real lemma into the HornNF/Statements layer.
-/
axiom prem_card_eq_one_of_hasHead1
  (P : Pack1 α) (h : α) :
  HasHead1 P h → (P.S.H.prem h).card = 1

/--
Singleton-forbid kernel (head-free case).

This will be implemented in `Dr1nds/Forbid/Singleton.lean` and re-exported here.
For now we keep it as an axiom so that we can theorem-ize `Qcorr_handle_A_singleton`.
-/
axiom qcorr_singleton_noHead
  (n : Nat) (P : Pack1 α) (a : α) :
  P.A = ({a} : Finset α) → NoHead1 P a →
  Qcorr n P → Qcorr (n+1) P

/--
Singleton-forbid kernel (has-head case), P-version.

This will be implemented in `Dr1nds/Forbid/Singleton.lean` using `Forbid/HornBridge.lean`.
-/
axiom qcorr_singleton_hasHead_P
  (n : Nat) (P : Pack1 α) (a : α)
  (P0 : Finset α) :
  P.A = ({a} : Finset α) → P0 ∈ P.S.H.prem a → (P.S.H.prem a).card = 1 →
  Qcorr n P → Qcorr (n+1) P

/--
`|A| = 1` branch (singleton-forbid kernel).

Implementation (wiring-level):
- Extract `a` with `A = {a}`.
- Split by `HasHead1 P a`.
- Delegate to the corresponding singleton kernel.

All heavy math is kept out of this file and lives in the singleton kernels.
-/
theorem Qcorr_handle_A_singleton
  (n : Nat) (P : Pack1 α) :
  (P.A).card = 1 →
  Qcorr n P → Qcorr (n+1) P := by
  classical
  intro hAcard hIH
  -- obtain the unique element a with A = {a}
  rcases Finset.card_eq_one.mp hAcard with ⟨a, hAeq⟩
  -- split by whether a has an incoming head rule
  by_cases hHead : HasHead1 P a
  · -- has-head case
    rcases hHead with ⟨P0, hP0mem⟩
    have hUnique : (P.S.H.prem a).card = 1 := prem_card_eq_one_of_hasHead1 (P := P) (h := a) ⟨P0, hP0mem⟩
    exact qcorr_singleton_hasHead_P (n := n) (P := P) (a := a) (P0 := P0) hAeq hP0mem hUnique hIH
  · -- no-head case
    have hNoHead : NoHead1 P a := by
      exact hHead
    exact qcorr_singleton_noHead (n := n) (P := P) (a := a) hAeq hNoHead hIH

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

Frozen intent: pick `h ∈ A` which is SC in the forbid-pack sense, and apply the SC-contraction step.
This is the branch where we use the monotonicity of `NDS_corr` under contraction at an SC point.
The side condition `h ∈ A` is essential: contracting outside `A` could introduce a new forbid set.
In this branch, it is expected that `NDS_corr` is **monotone (nondecreasing) under contraction at SC points**.
-/
axiom Qcorr_branch_A_ge2
  (n : Nat) (P : Pack1 α) (h : α) :
  IsSC1 P h → h ∈ P.A →
  Qcorr n P → Qcorr (n+1) P

end Dr1nds
