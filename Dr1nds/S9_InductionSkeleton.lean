-- Dr1nds/S9_InductionSkeleton.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs
import Dr1nds.S4_FixFamily
import Dr1nds.S8_Statements
import Dr1nds.S11_LocalKernels

namespace Dr1nds

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
      -- n = 0: Q_step で Q(0) を閉じ、Qcorr_step で forbid 版を閉じる
      have hex : ∃ v : α, GoodV_for_Q (α := α) P v := by
        rcases Local.exists_good_v_for_Q (α := α) 0 P with ⟨v, hv⟩
        exact ⟨v, hv⟩
      have hQ : Q (α := α) 0 P := by
        exact Q_step (α := α) 0 P hex
      refine ⟨hQ, ?_⟩
      intro A hOK
      exact Qcorr_step (α := α) 0 P A hOK
  | succ n ih =>
      -- n = n+1: ここでは骨格として Q_step / Qcorr_step をそのまま使う
      have hex : ∃ v : α, GoodV_for_Q (α := α) P v := by
        rcases Local.exists_good_v_for_Q (α := α) (Nat.succ n) P with ⟨v, hv⟩
        exact ⟨v, hv⟩
      have hQ : Q (α := α) (Nat.succ n) P := by
        exact Q_step (α := α) (Nat.succ n) P hex
      refine ⟨hQ, ?_⟩
      intro A hOK
      exact Qcorr_step (α := α) (Nat.succ n) P A hOK

/-- 通常会計だけ取り出し -/
theorem main_Q (n : Nat) (P : HypPack α) : Q (α := α) n P := by
  exact (main_mutual (α := α) n P).1

/-- forbid 付き会計だけ取り出し（ForbidOK 前提つき） -/
theorem main_Qcorr (n : Nat) (P : HypPack α) (A : Finset α) :
    ForbidOK (α := α) P A → Qcorr (α := α) n P A := by
  intro hOK
  exact (main_mutual (α := α) n P).2 A hOK
