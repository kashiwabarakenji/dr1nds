-- Dr1nds/Induction/LocalKernels.lean
import Mathlib.Tactic
import Dr1nds.Induction.Statements
import Dr1nds.Forbid.Basic
import Dr1nds.S0_CoreDefs
import Dr1nds.Horn.HornWithForbid
import Dr1nds.Forbid.HornBridge
import Dr1nds.Forbid.Singleton
import LeanCopilot

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
  (P : Pack1 α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (P.S.H.trace a).U)
  (hPne : Pprem.Nonempty)
  (hPclosed : (P.S.H.trace a).IsClosed Pprem) : Pack1 α :=
  { S := traceWithPrem (α := α) P.S a Pprem hPsub hPne hPclosed }

/- Expected semantics of the trace-with-prem pack. -/
@[simp] theorem Pack1.tracePack1WithPrem_C
  (P : Pack1 α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (P.S.H.trace a).U)
  (hPne : Pprem.Nonempty)
  (hPclosed : (P.S.H.trace a).IsClosed Pprem) :
  Pack1.C (Pack1.tracePack1WithPrem (α := α) P a Pprem hPsub hPne hPclosed)
    = HornNF.FixSet (P.S.H.trace a) :=
by
  classical
  simp [Pack1.tracePack1WithPrem, Pack1.C, traceWithPrem_H]

@[simp] theorem Pack1.tracePack1WithPrem_A
  (P : Pack1 α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (P.S.H.trace a).U)
  (hPne : Pprem.Nonempty)
  (hPclosed : (P.S.H.trace a).IsClosed Pprem) :
  Pack1.A (Pack1.tracePack1WithPrem (α := α) P a Pprem hPsub hPne hPclosed)
    = Pprem :=
by
  classical
  simp [Pack1.tracePack1WithPrem, Pack1.A, traceWithPrem_F]

/- API placeholder: normalization assumption (no premise contains a forbidden element). -/

axiom Pack1.noPremContains_forbid
  (P : Pack1 α) (a : α) :
  a ∈ Pack1.A (α := α) P →
  ∀ {h : α} {Q : Finset α}, Q ∈ P.S.H.prem h → a ∉ Q


-- =====================================
-- (A) Phase (2-A) / (2-B) TODO targets (statement skeletons)
--
-- These are the *missing mathematical statements* needed to finish the |A|=1 story
-- without keeping the normalization hypothesis as an explicit axiom.
--
-- Rule of thumb:
-- - (2-A) makes trace packs concrete (defs + rfl lemmas) and deletes the four
--   `tracePack*_C/H/A` axioms above.
-- - (2-B) proves that we may normalize away premises containing the forbidden
--   singleton element `a` (NF-A), and then reuse the existing HornBridge lemmas.
--
-- For now we only add the *targets as axioms* so that the end-to-end wiring
-- can be kept stable while we theorem-ize them one by one.
-- =====================================

/-
(2-B) NF-A (normalization) blueprint.

We normalize a HornNF by deleting all premises that contain the distinguished element `a`.
This produces an equivalent closure behaviour on the singleton-forbid world.

Implementation strategy (later theorem-ization):
- define `HornNF.normalizePrem` as a `filter (fun Q => a ∉ Q)` on each `prem h`;
- prove `normalizePrem_noPremContains` by simp;
- show that on the singleton-forbid branch, normalization preserves the relevant
  `Hole/Up` families (or at least their cards), hence preserves `NDS_corr`.
-/
namespace HornNF

/-!
(2-B) Normalization layer

NOTE:
- `normalize` and its core properties already live in `Dr1nds/Horn/HornTrace.lean`.
- The |A|=1 pipeline currently does **not** require the additional “public no-normalization entrypoints”.
- Therefore we do not keep extra axioms here; we simply re-export the existing normalization operator.

If later you want to route singleton-forbid through normalization at the wiring layer,
add the *specific* bridge lemmas at that time.
-/

/-- Premise-normalization: remove all premises that contain `a`.

This is a thin alias to `HornNF.normalize` defined in `HornTrace.lean`.
-/
abbrev normalizePrem (H : HornNF α) (a : α) : HornNF α :=
  HornNF.normalize (α := α) H a

/-- After normalization, no premise contains `a`. -/
lemma normalizePrem_noPremContains
  (H : HornNF α) (a : α) :
  ∀ {h : α} {Q : Finset α}, Q ∈ (normalizePrem (α := α) H a).prem h → a ∉ Q := by
  -- `normalizePrem` is an alias, so this is exactly the lemma from `HornTrace.lean`.
  intro h Q hQ
  simpa [normalizePrem] using (normalize_noPremContains (H := H) (a := a) (h := h) (Q := Q) hQ)

/-- Consequence: on singleton forbid, the Hole family is invariant under normalization. -/
theorem hole_fixset_singleton_normalize_eq
  (H : HornNF α) (a : α) :
  Hole (α := α) (HornNF.FixSet H) ({a} : Finset α)
    =
  Hole (α := α) (HornNF.FixSet (normalizePrem (α := α) H a)) ({a} : Finset α) := by
  -- This is exactly `normalize_hole_fixset_eq` from `HornTrace.lean`.
  simpa [normalizePrem] using (normalize_hole_fixset_eq (H := H) (a := a)).symm

end HornNF


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
      ∃ hPne : Pprem.Nonempty,
      ∃ hPclosed : (P.S.H.trace a).IsClosed Pprem,
        Qcorr n (Pack1.tracePack1WithPrem (α := α) P a Pprem hPsub hPne hPclosed)) →
  Qcorr (n+1) P :=
by
  classical
  intro hA hNoHeadIH hHasHeadIH
  by_cases hHead : HasHead1 P a
  · -- has-head branch: shift forbid to a chosen premise
    rcases hHasHeadIH hHead with ⟨Pprem, hmem, hcard, hPsub, hPne, hPclosed, hIH⟩
    -- bridge the pack-level IH to the HornNF kernel
    have haA : a ∈ P.A := by
      simpa [hA] using (Finset.mem_singleton.mpr rfl)
    have hA' : P.S.F = ({a} : Finset α) := by
      simpa [Pack1.A] using hA
    have haF : a ∈ P.S.F := by
      simpa [Pack1.A] using haA
    have hvU : a ∈ P.S.H.U := by
      exact P.S.F_subset_U haF
    have hNoPremV :
        ∀ {h : α} {Q : Finset α}, Q ∈ P.S.H.prem h → a ∉ Q :=
      Pack1.noPremContains_forbid (α := α) P a haA
    have hQ_trace :
        NDS_corr (α := α) n (HornNF.FixSet (P.S.H.trace a)) Pprem ≤ 0 := by
      have hQ := Qcorr_implies_NDSCorr_le_zero (α := α) (n := n)
        (P := Pack1.tracePack1WithPrem (α := α) P a Pprem hPsub hPne hPclosed) hIH
      -- rewrite the trace-pack C/A to the HornNF trace world
      rw [Pack1.tracePack1WithPrem_C (P := P) (a := a) (Pprem := Pprem)
            (hPsub := hPsub) (hPne := hPne) (hPclosed := hPclosed),
          Pack1.tracePack1WithPrem_A (P := P) (a := a) (Pprem := Pprem)
            (hPsub := hPsub) (hPne := hPne) (hPclosed := hPclosed)] at hQ
      exact hQ
    have hRes :
        NDS_corr (α := α) n.succ (HornNF.FixSet P.S.H) ({a} : Finset α) ≤ 0 :=
      qcorr_singleton_hasHead_P_step (α := α)
        (n := n) (H := P.S.H) (hDR1 := P.S.hDR1)
        (v := a) (P := Pprem)
        (hvU := hvU) (hP := hmem) (hUnique := hcard)
        (hNoPremV := hNoPremV) (hQ_trace := hQ_trace)
    dsimp [Qcorr, Pack1.C, Pack1.A]
    rw [hA']
    exact hRes
  · -- no-head branch: forbid disappears in the trace/deletion world
    have hNoHead : NoHead1 P a := by
      -- `NoHead1` is defined as `¬ HasHead1` in this file
      simpa [NoHead1] using hHead
    have haA : a ∈ P.A := by
      simpa [hA] using (Finset.mem_singleton.mpr rfl)
    have hA' : P.S.F = ({a} : Finset α) := by
      simpa [Pack1.A] using hA
    have haF : a ∈ P.S.F := by
      simpa [Pack1.A] using haA
    have hvU : a ∈ P.S.H.U := by
      exact P.S.F_subset_U haF
    have hNoPremV :
        ∀ {h : α} {Q : Finset α}, Q ∈ P.S.H.prem h → a ∉ Q :=
      Pack1.noPremContains_forbid (α := α) P a haA
    have hfree : P.S.H.prem a = ∅ := by
      classical
      by_contra hne
      have hnonempty : (P.S.H.prem a).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hne
      exact hNoHead hnonempty
    have hIH : Q n (Pack1.tracePack0 (α := α) P a) := hNoHeadIH hNoHead
    have hQ_trace :
        NDS (α := α) n (HornNF.FixSet (P.S.H.trace a)) ≤ 0 := by
      have hQ := Q_implies_NDS_le_zero (α := α) (n := n)
        (P := Pack1.tracePack0 (α := α) P a) hIH
      dsimp [Pack0.C] at hQ
      simpa using hQ
    have hRes :
        NDS_corr (α := α) n.succ (HornNF.FixSet P.S.H) ({a} : Finset α) ≤ 0 :=
      qcorr_singleton_noHead_step (α := α)
        (n := n) (H := P.S.H) (v := a)
        (hvU := hvU) (hfree := hfree)
        (hNoPremV := hNoPremV) (hQ_trace := hQ_trace)
    dsimp [Qcorr, Pack1.C, Pack1.A]
    rw [hA']
    exact hRes


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
The side condition `h ∈ A` is essential: contracting outside `A` could introduce a new forbid set.
In this branch, it is expected that `NDS_corr` is **monotone (nondecreasing) under contraction at SC points**.
-/
axiom Qcorr_branch_A_ge2
  (n : Nat) (P : Pack1 α) (h : α) :
  IsSC1 P h → h ∈ P.A →
  Qcorr n P → Qcorr (n+1) P

#print axioms Dr1nds.Qcorr_handle_A_singleton


end Dr1nds
