-- Dr1nds/Induction/Steps.lean
import Mathlib.Tactic

import Dr1nds.Induction.Statements
import Dr1nds.Induction.LocalKernels

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
theorem Qcorr_step1
  (n : Nat) (P : Pack1 α) :
  Qcorr n P → Qcorr (n+1) P := by
  intro hQ
  classical
  by_cases hPar : Parallel1 P
  · -- parallel branch（独立核）
    exact Qcorr_succ_of_parallel (α := α) (n := n) (P := P) hPar hQ
  · -- no-parallel branch：A の大きさで分岐
    -- NOTE (凍結): この `card_cases` による分岐構造自体を S10(wiring) の仕様として固定する。
    have hNP : NoParallel1 P := by
      trivial
    have hCardCases := card_cases (α := α) P.A
    -- A.card = 0 は理論上排除したい（forbid は1つで Nonempty を仮定する設計が自然）
    -- ただし wiring の骨格としては一旦受けて、0 の場合は singleton 分岐に合流させる等で扱える。
    -- 今は “0 or 1 は専用核” へ寄せる。
    rcases hCardCases with h0 | h1 | hge2
    · -- A.card=0（暫定：専用核）
      /-
      NOTE (設計メモ / 凍結)
      - 仕様としては `Pack1` 側で `A.Nonempty` を仮定してこの分岐自体を消すのが本筋。
      - ただし現段階では wiring を total に保つため、空 forbid は専用核へ投げる。
      -/
      exact Qcorr_handle_A_empty (α := α) (n := n) (P := P) h0 hQ
    · -- A.card=1 branch（専用核）
      exact Qcorr_handle_A_singleton (α := α) (n := n) (P := P) h1 hQ
    · -- A.card≥2 branch（A 内 SC を取って進める）
      let h := choose_SC_in_forbid (α := α) P hNP
      have hmem : h ∈ P.A := choose_SC_in_forbid_mem (α := α) P hNP
      have hSC : IsSC1 P h := choose_SC_in_forbid_spec (α := α) P hNP
      exact Qcorr_branch_A_ge2 (α := α) (n := n) (P := P) (h := h) hSC hmem hQ

end Dr1nds
