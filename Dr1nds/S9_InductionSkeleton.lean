-- Dr1nds/S9_InductionSkeleton.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs
import Dr1nds.S4_FixFamily
import Dr1nds.S8_Statements
import Dr1nds.S10_Steps
import Dr1nds.S11_LocalKernels

namespace Dr1nds

open Dr1nds
open Dr1nds.Local
open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
S9_InductionSkeleton.lean

目的：
- 相互帰納（Q と Qcorr）の“枠”を Lean 側で固定する。
- ここでは lemma は基本的に `axiom` / `sorry` でよい（骨格優先）。

方針（案A）：
- Q n : 通常会計 NDS ≤ 0
- Qcorr n : forbid 付き会計 NDS_corr ≤ 0
- Q n を示すとき、必要なら Qcorr (n-1) を IH として使う
- Qcorr n を示すとき、必要なら Q (n-1) を IH として使う
-/

namespace Induction

/-- 相互帰納の主定理（骨格） -/
theorem main_mutual (n : Nat) (P : HypPack α) :
    Q (α := α) n P ∧ (∀ A : Finset α, ForbidOK (α := α) P A → Qcorr (α := α) n P A) := by
  classical

  induction n with
  | zero =>
      -- n = 0
      -- NOTE: `Step.Q_step` / `Step.Qcorr_step` are designed for the `n ≥ 1` accounting step.
      -- Base case is kept as a skeleton (`sorry`) to avoid forcing an impossible `1 ≤ 0`.
      have hQ : Q (α := α) 0 P := by
        sorry
      refine ⟨hQ, ?_⟩
      intro A hOK
      have hQcorr0 : Qcorr (α := α) 0 P A := by
        sorry
      exact hQcorr0

  | succ n ih =>
      -- n = n+1
      -- ここでは「枠の固定」が目的なので、IH は名前付けして保持しておく
      have hQ_prev : Q (α := α) n P := ih.1
      have _hQcorr_prev : (∀ A : Finset α, ForbidOK (α := α) P A → Qcorr (α := α) n P A) := ih.2

      -- 現段階では hQ_prev / hQcorr_prev を内部で使うステップは S10/S11 側に置く
      -- （ここでは Q_step / Qcorr_step が骨格 API を提供している想定）
      have hn' : 1 ≤ Nat.succ n := by
        exact Nat.succ_le_succ (Nat.zero_le n)

      have hQ : Q (α := α) (Nat.succ n) P :=
        Step.Q_step (α := α) (n := Nat.succ n) (hn := hn') (P := P) hQ_prev

      refine ⟨hQ, ?_⟩
      intro A hOK
      -- forbid 側は Step 側（S10_Steps）に委譲：必要な前提は明示して渡す
      have hQcorr : Qcorr (α := α) (Nat.succ n) P A :=
        Step.Qcorr_step (α := α) (n := Nat.succ n) (hn := hn') (P := P) (A := A) hOK hQ_prev
      exact hQcorr

/-- 通常会計だけ取り出し -/
theorem main_Q (n : Nat) (P : HypPack α) : Q (α := α) n P := by
  exact (main_mutual (α := α) n P).1

/-- forbid 付き会計だけ取り出し（ForbidOK 前提つき） -/
theorem main_Qcorr (n : Nat) (P : HypPack α) (A : Finset α) :
    ForbidOK (α := α) P A → Qcorr (α := α) n P A := by
  intro hOK
  exact (main_mutual (α := α) n P).2 A hOK
