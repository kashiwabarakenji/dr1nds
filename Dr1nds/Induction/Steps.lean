-- Dr1nds/Induction/Steps.lean
import Mathlib.Tactic

import Dr1nds.Induction.Statements
import Dr1nds.Induction.LocalKernels
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.HornClosure

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/-
S10(wiring) 相当：
- case split と「どの局所核を呼ぶか」だけを書く
- 数学的な中身（局所核）は LocalKernels 側へ
-/

/- ============================================================
  (W0) forbid なし pack：SC 点 h に対する head-structure 3-way split

  NOTE (設計メモ / 凍結ポイント)
  - Steps(S10) は *wiring のみ* を書く方針。
    この 3-way split 自体は「分岐仕様」なので、最終的には
      (a) Induction/Statements.lean（仕様として凍結）
      または
      (b) Induction/LocalKernels.lean（局所核として供給）
    に移動するのが筋。

  - いまはコンパイルと全体配線の安定化を優先し、ここに axiom として置く。
============================================================ -/

/-- forbid-free: for an SC point `h`, either there is no head, or there is a unary head witness, or the head is non-unary. -/
axiom SC_head_cases0
  (P : Pack0 α) (h : α) :
  IsSC0 P h →
  (NoHead0 P h) ∨ (∃ v : α, UnaryHead0 P h v) ∨ (NonUnaryHead0 P h)

/- ============================================================
  (W1) NEP transport (wiring-level placeholders)

  We carry NEP as a *family-level* property: `NEP C := (∅ : Finset α) ∈ C`.
  In the singleton-forbid branch, the IH is applied to trace-world packs, so we
  need to transport NEP from the original pack to the trace packs.

  NOTE (freeze): these are expected to be discharged in the Forbid/HornTrace/HornBridge
  layer later; for now they are wiring-level placeholders.
============================================================ -/

/- If the base family of `P` is NEP, then the trace-pack0 base family is NEP. -/
theorem nep_tracePack0_of_nep
  (P : Pack1 α) (a : α) :
  NEP (Pack1.C (α := α) P) → NEP (Pack0.C (Pack1.tracePack0 (α := α) P a)) :=
by
  intro hNEP
  classical

  -- Unfold NEP as `∅ ∈ _`.
  -- Now: `hNEP : (∅ : Finset α) ∈ Pack1.C P`.

  -- Move from `Pack1.C P` to `FixSet P.S.H`.
  have hempty : (∅ : Finset α) ∈ HornNF.FixSet P.S.H := by
    have h0 : (∅ : Finset α) ∈ Pack1.C (α := α) P := hNEP
    -- `Pack1.C` is the base family of `P` (expected to be `FixSet P.S.H`).
    simp [Pack1.C] at h0
    exact hNEP

  -- `∅` stays closed under trace.
  have hempty_tr : (∅ : Finset α) ∈ HornNF.FixSet (P.S.H.trace a) := by
    exact
      HornNF.empty_mem_fixset_trace_of_empty_mem_fixset
        (α := α) (H := P.S.H) (u := a) hempty

  -- Repackage as NEP for the trace pack.
  -- `tracePack0` is expected to have base family `FixSet (H.trace a)`.
  -- After rewriting `Pack0.C`, the goal is exactly `hempty_tr`.
  simp [Pack0.C]
  exact hempty_tr

/-- If the base family of `P` is NEP, then the trace-with-prem pack base family is NEP. -/
theorem nep_tracePack1WithPrem_of_nep
  (P : Pack1 α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (P.S.H.trace a).U)
  (hPne : Pprem.Nonempty)
  (hPclosed : (P.S.H.trace a).IsClosed Pprem) :
  NEP (Pack1.C (α := α) P) →
    NEP (Pack1.C (Pack1.tracePack1WithPrem (α := α) P a Pprem hPsub hPne hPclosed)) := by
  intro hNEP
  classical

  -- `NEP` is `∅ ∈ _`.
  have h0C : (∅ : Finset α) ∈ Pack1.C (α := α) P := hNEP

  -- Move from `Pack1.C P` to `FixSet P.S.H`.
  have hempty : (∅ : Finset α) ∈ HornNF.FixSet P.S.H := by
    simp [Pack1.C] at h0C
    exact hNEP

  -- Transport `∅ ∈ FixSet` across rule-level trace.
  have hempty_tr : (∅ : Finset α) ∈ HornNF.FixSet (P.S.H.trace a) := by
    exact
      HornNF.empty_mem_fixset_trace_of_empty_mem_fixset
        (α := α) (H := P.S.H) (u := a) hempty

  -- Repackage as NEP for the trace-with-prem pack.
  -- `tracePack1WithPrem` is expected to have base family `FixSet (H.trace a)`.
  simp [Pack1.C]
  exact hempty_tr

/- Wiring helper: provide the obligations needed to build `tracePack1WithPrem`.-/
/- Wiring helper: provide the obligations needed to build `tracePack1WithPrem`.

IMPORTANT:
`HornNF.prem a` is not assumed to contain *closed* sets. Therefore we close the premise
by taking `closure` in the traced world.

This lemma produces the obligations for
  `Pcl := HornNF.closure (P.S.H.trace a) Praw`.

We keep `Praw.Nonempty` as an explicit hypothesis (rather than trying to derive it
from `Praw ∈ prem a`), because empty-premise rules may exist.
-/
theorem tracePack1WithPrem_obligations
  (P : Pack1 α) (a : α) (Praw : Finset α) :
  Praw ∈ P.S.H.prem a →
  Praw ⊆ (P.S.H.trace a).U →
  Praw.Nonempty →
    let Pcl : Finset α := HornNF.closure (P.S.H.trace a) Praw
    (Pcl ⊆ (P.S.H.trace a).U) ∧
    Pcl.Nonempty ∧
    (P.S.H.trace a).IsClosed Pcl := by
  intro hmem hPrawSub hne
  classical
  -- Define the closed forbid set in the traced world.
  let Pcl : Finset α := HornNF.closure (P.S.H.trace a) Praw
  have hPcl_sub : Pcl ⊆ (P.S.H.trace a).U := by
    -- `closure` stays inside the universe.
    simpa [Pcl] using (HornNF.closure_subset_U (H := P.S.H.trace a) (X := Praw))
  have hPcl_ne : Pcl.Nonempty := by
    rcases hne with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hx' : x ∈ HornNF.closure (P.S.H.trace a) Praw := by
      -- `subset_closure` is the inclusion `Praw ⊆ closure(Praw)`; it needs `Praw ⊆ U` and the element `x`.
      exact
        HornNF.subset_closure
          (H := P.S.H.trace a)
          (X := Praw)
          (hX := hPrawSub)
          (a := x)
          hx
    simpa [Pcl] using hx'
  have hPcl_closed : (P.S.H.trace a).IsClosed Pcl := by
    -- `closure` is closed.
    simp [Pcl]
    let hc := (HornNF.closure_isClosed (H := P.S.H.trace a) )
    simp_all only [Pcl]
  refine ⟨hPcl_sub, hPcl_ne, ?_⟩
  simp_all only [Pcl]



/- Helper: obtain the arguments needed to build `tracePack1WithPrem` from a prem-membership proof.
    This isolates the (temporary) wiring-level axiom from the rest of the steps. -/

theorem tracePack1WithPrem_args
  (P : Pack1 α) (a : α) (Praw : Finset α)
  (hmem : Praw ∈ P.S.H.prem a)
  (hPrawSub : Praw ⊆ (P.S.H.trace a).U)
  (hne : Praw.Nonempty) :
  let Pcl : Finset α := HornNF.closure (P.S.H.trace a) Praw
  ∃ (hPsub : Pcl ⊆ (P.S.H.trace a).U),
    ∃ (hPne : Pcl.Nonempty),
      ∃ (hPclosed : (P.S.H.trace a).IsClosed Pcl),
        True := by
  classical
  let Pcl : Finset α := HornNF.closure (P.S.H.trace a) Praw
  have hObs :=
    tracePack1WithPrem_obligations (α := α) (P := P) (a := a) (Praw := Praw) hmem hPrawSub hne
  -- unpack the obligations
  have hPsub : Pcl ⊆ (P.S.H.trace a).U := by
    simpa [Pcl] using hObs.1
  have hPne : Pcl.Nonempty := by
    simpa [Pcl] using hObs.2.1
  have hPclosed : (P.S.H.trace a).IsClosed Pcl := by
    simp_all only [Pcl]
  exact ⟨hPsub, ⟨hPne, ⟨hPclosed, trivial⟩⟩⟩


/- ============================================================
  (S10-0) Q-step (forbid-free)
============================================================ -/

/--
forbid なし版の帰納ステップ（構造のみ）：
Parallel なら独立核へ、NoParallel なら SC を取り 3-way split。
-/
theorem Q_step0
  (n : Nat) (P : Pack0 α) :
  Q n P → Q (n+1) P := by
  intro hQ
  classical
  by_cases hPar : Parallel0 P
  · -- parallel branch（独立核）
    exact Q_succ_of_parallel (α := α) (n := n) (P := P) hPar hQ
  · -- no-parallel branch：SC を取って分岐
    have hNP : NoParallel0 P := by
      -- NOTE (設計メモ): 現在 NoParallel0 は abbrev True なので trivial。
      -- 将来 `NoParallel0 P := ¬ Parallel0 P` に差し替えたら、ここは `hPar` から構成する。
      trivial
    let h := choose_SC_no_parallel (α := α) P hNP
    have hSC : IsSC0 P h := choose_SC_no_parallel_spec (α := α) P hNP

    -- SC 点で head 構造を 3-way split
    have hcases : (NoHead0 P h) ∨ (∃ v : α, UnaryHead0 P h v) ∨ (NonUnaryHead0 P h) :=
      SC_head_cases0 (α := α) (P := P) (h := h) hSC

    cases hcases with
    | inl hNo =>
        -- head なし
        exact Q_branch_noHead (α := α) (n := n) (P := P) (h := h) hSC hNo hQ
    | inr hrest =>
        cases hrest with
        | inl hUnaryExists =>
            -- unary head
            rcases hUnaryExists with ⟨v, hUnary⟩
            exact Q_branch_unaryHead (α := α) (n := n) (P := P) (h := h) (v := v) hSC hUnary hQ
        | inr hNonUnary =>
            -- non-unary head
            exact Q_branch_nonUnaryHead (α := α) (n := n) (P := P) (h := h) hSC hNonUnary hQ


/- ============================================================
  (S10-1) Qcorr-step (with forbid A)
============================================================ -/

/--
forbid あり版の帰納ステップ（構造のみ）：
Parallel なら独立核へ、NoParallel なら
|A|=1 を専用核、|A|≥2 を “A 内 SC” で進める。
-/
/-/
forbid あり版の帰納ステップ（構造のみ）。

NOTE (freeze): `|A|=1` の分岐は “同一 pack のまま n→n+1” ではなく、
trace/deletion により **別 pack（台 n）** に IH を当てる構造なので、
このステップは `T n` / `Tcorr n`（∀pack 形）を IH として受け取る。
-/
theorem Qcorr_step1
  (n : Nat) (P : Pack1 α) :
  T (α := α) n → Tcorr (α := α) n → Qcorr (α := α) (n+1) P := by
  intro hT hTcorr
  classical
  by_cases hPar : Parallel1 P
  · -- parallel branch（独立核）
    exact Qcorr_succ_of_parallel (α := α) (n := n) (P := P) hPar (hTcorr P)
  · -- no-parallel branch：A の大きさで分岐
    have hNP : NoParallel1 P := by
      trivial
    have hCardCases := card_cases (α := α) P.A
    rcases hCardCases with h0 | h1 | hge2
    · -- A.card=0（暫定：専用核）
      exact Qcorr_handle_A_empty (α := α) (n := n) (P := P) h0 (hTcorr P)
    · -- A.card=1（専用核：台落ち）
      -- `A.card = 1` から代表元 `a` を取り、`A = {a}` を得る
      obtain ⟨a, hAeq⟩ := Finset.card_eq_one.mp h1
      -- singleton kernel は trace-world への IH を要求するので、`T/Tcorr` から供給する
      refine Qcorr_handle_A_singleton (α := α) (n := n) (P := P) (a := a) ?_ ?_ ?_
      · -- `A = {a}`
        simpa [Pack1.A] using hAeq
      · -- NoHead branch IH : Q n (tracePack0 ...)
        intro hNo
        exact hT (Pack1.tracePack0 (α := α) P a)
      · -- HasHead branch IH : ∃Pprem, ... ∧ Qcorr n (tracePack1WithPrem ...)
        intro hHead
        classical
        -- NOTE: with the current placeholder definitions (`Parallel1 := True` / `NoParallel1 := True`),
        -- this branch is unreachable, so we close it by contradiction.
        exact False.elim (hPar trivial)
    · -- A.card≥2（A 内 SC を取って進める）
      let h := choose_SC_in_forbid (α := α) P hNP
      have hmem : h ∈ P.A := choose_SC_in_forbid_mem (α := α) P hNP
      have hSC : IsSC1 P h := choose_SC_in_forbid_spec (α := α) P hNP
      exact Qcorr_branch_A_ge2 (α := α) (n := n) (P := P) (h := h) hSC hmem (hTcorr P)


/- ============================================================
  (S10-1') Qcorr-step (with forbid A, NEP-carrying IH)

  This is the variant that the mutual induction should use once NEP is adopted.
  We keep the old `Qcorr_step1` around to avoid breaking existing wiring.
============================================================ -/

theorem Qcorr_step1_NEP
  (n : Nat) (P : Pack1 α) :
  TNEP (α := α) n → TcorrNEP (α := α) n →
  NEP (Pack1.C (α := α) P) →
  Qcorr (α := α) (n+1) P := by
  intro hTNEP hTcorrNEP hNEP
  classical
  by_cases hPar : Parallel1 P
  · -- parallel branch（独立核）
    exact Qcorr_succ_of_parallel (α := α) (n := n) (P := P) hPar (hTcorrNEP P hNEP)
  · -- no-parallel branch：A の大きさで分岐
    have hNP : NoParallel1 P := by
      trivial
    have hCardCases := card_cases (α := α) P.A
    rcases hCardCases with h0 | h1 | hge2
    · -- A.card=0（暫定：専用核）
      exact Qcorr_handle_A_empty (α := α) (n := n) (P := P) h0 (hTcorrNEP P hNEP)
    · -- A.card=1（専用核：台落ち）
      obtain ⟨a, hAeq⟩ := Finset.card_eq_one.mp h1
      refine Qcorr_handle_A_singleton (α := α) (n := n) (P := P) (a := a) ?_ ?_ ?_
      · -- `A = {a}`
        simpa [Pack1.A] using hAeq
      · -- NoHead branch IH : Q n (tracePack0 ...)
        intro hNo
        have hNEP_tr : NEP (Pack0.C (Pack1.tracePack0 (α := α) P a)) :=
          nep_tracePack0_of_nep (α := α) (P := P) (a := a) hNEP
        exact hTNEP (Pack1.tracePack0 (α := α) P a) hNEP_tr
      · -- HasHead branch IH : ∃Pprem, ... ∧ Qcorr n (tracePack1WithPrem ...)
        intro hHead
        classical
        -- NOTE: with the current placeholder definitions (`Parallel1 := True` / `NoParallel1 := True`),
        -- this branch is unreachable, so we close it by contradiction.
        exact False.elim (hPar trivial)
    · -- A.card≥2（A 内 SC を取って進める）
      let h := choose_SC_in_forbid (α := α) P hNP
      have hmem : h ∈ P.A := choose_SC_in_forbid_mem (α := α) P hNP
      have hSC : IsSC1 P h := choose_SC_in_forbid_spec (α := α) P hNP
      exact Qcorr_branch_A_ge2 (α := α) (n := n) (P := P) (h := h) hSC hmem (hTcorrNEP P hNEP)

/- ============================================================
  (S10-global) Lift local steps to global (∀-quantified) steps.

  These are the steps that the mutual induction should use.
============================================================ -/

/-- Global step for forbid-free statement. -/
theorem T_step0
  (n : Nat) : T (α := α) n → T (α := α) (n+1) := by
  intro IH
  intro P
  exact Q_step0 (n := n) (P := P) (IH P)

/-- Global step for forbid statement. -/
theorem Tcorr_step1
  (n : Nat) : T (α := α) n → Tcorr (α := α) n → Tcorr (α := α) (n+1) := by
  intro IH_T IH_Tcorr
  intro P
  exact Qcorr_step1 (n := n) (P := P) IH_T IH_Tcorr

/-- Global step for forbid-free statement (NEP-carrying). -/
theorem TNEP_step0
  (n : Nat) : TNEP (α := α) n → TNEP (α := α) (n+1) := by
  intro IH
  intro P hNEP
  exact Q_step0 (n := n) (P := P) (IH P hNEP)

/-- Global step for forbid statement (NEP-carrying). -/
theorem TcorrNEP_step1
  (n : Nat) : TNEP (α := α) n → TcorrNEP (α := α) n → TcorrNEP (α := α) (n+1) := by
  intro IH_T IH_Tcorr
  intro P hNEP
  exact Qcorr_step1_NEP (n := n) (P := P) IH_T IH_Tcorr hNEP

end Dr1nds
