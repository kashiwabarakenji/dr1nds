-- Dr1nds/S9_InductionSkeleton.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs
import Dr1nds.S8_Statements
import Dr1nds.S10_Steps

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
S9_InductionSkeleton.lean

# 目的（このファイルで“凍結”したいこと）

このファイルは **相互帰納の“配線”だけ** を固定する。
数学的な中身（会計等式・representability・Del-bound・good v・unary 比較核など）は
S8/S10/S11 に置き、このファイルはそれらを呼び出して結合するだけに徹する。

- `Q n P`      : 通常会計（NDS ≤ 0）
- `Qcorr n P A`: forbid 付き会計（NDS_corr ≤ 0）
- `IH n P`     : 相互帰納で運ぶ“束”（`Q` と `Qcorr` をまとめたもの）

# 設計メモ（重要）

* **ここでは「クラス閉性」を要求しない。**
  `con` / `Del` / `Hole` の結果が同じクラスに戻ることを一般論として示す必要はなく、
  必要なときにだけ `S11_LocalKernels` が「IH を当てられる pack が存在する」ことを
  局所的に供給する（representability を *局所存在* として扱う）方針。

* **IH は bundling して運ぶ。**
  つまり帰納で運ぶ命題は

  `IH(n,P) := Q(n,P) ∧ (∀A, ForbidOK(P,A) → Qcorr(n,P,A))`

  で固定する。
  S10 のステップ（`Q_step`, `Qcorr_step`）が必要とするのは基本的にこの形。

* **base case (n=0) は“定義依存”なので、ここでは核を決めるだけにする。**
  `n=0` は `CON_ID` 型の会計ステップ（n≥1）を回せないため、
  `Q 0 P` / `Qcorr 0 P A` の扱いは「定義上の規約」または「別補題」で閉じる。
  ここでは `base_Q` / `base_Qcorr` を *placeholder* として置き、
  後で S11（あるいは S8 の仕様側）で確定させる。

このファイルの理想形：
- `main_mutual` が `induction n` で唯一箇所の再帰を担う。
- 中身は `Step.Q_step` / `Step.Qcorr_step` と base 補題の呼び出しのみ。
- したがって、このファイルが壊れるときは「仕様（S8/S10）変更の影響」であり、
  逆にこのファイルが安定すればプロジェクト全体の配線も安定する。
-/

namespace Induction

/--
(base) n=0 の通常側。

将来的には、次のどちらかで `sorry` を外す：
- 方針A: `NDS 0 C` の定義を “必ず 0” にしてしまい、自動で閉じる。
- 方針B: `n=0` のときの `w(0, X)` の定義から直接評価して閉じる。

いずれにせよ **S10 の会計ステップは使わない**（n≥1 が前提のため）。
ここは「定義の確定」に依存するので、S11（局所核）側で最終的に証明するのが安全。
-/
axiom base_Q (P : HypPack α) : Q (α := α) 0 P

/--
(base) n=0 の forbid 側。

こちらも `NDS_corr 0 C A` の定義に依存する。
通常は `NDS_corr = NDS(Hole) + |Up|` なので、
`n=0` の重みの定義と `Up.card ≥ 0` を合わせて閉じる形になる想定。

注意：`ForbidOK`（2 ≤ card）を前提にする必要があるかは仕様次第。
この骨格では「後で必要なら前提を足す」方針で、いったん前提無しに置く。
-/
axiom base_Qcorr (P : HypPack α) (A : Finset α) : Qcorr (α := α) 0 P A

/-- 相互帰納の主定理（骨格） -/
theorem main_mutual (n : Nat) :
    ∀ P : HypPack α, IH (α := α) n P := by
  classical
  induction n with
  | zero =>
      intro P
      refine ⟨base_Q (α := α) P, ?_⟩
      intro A hOK
      -- `hOK` はここでは未使用（将来 `base_Qcorr` の前提にする可能性はある）。
      exact base_Qcorr (α := α) P A
  | succ n ih =>
      intro P
      -- n = n+1
      -- IH is already the polymorphic bundled statement: ∀ P', IH n P'
      have hn' : 1 ≤ Nat.succ n := by
        exact Nat.succ_le_succ (Nat.zero_le n)

      have hQ : Q (α := α) (Nat.succ n) P :=
        Step.Q_step (α := α) (n := Nat.succ n) (hn := hn') (P := P) ih

      refine ⟨hQ, ?_⟩
      intro A hOK
      exact Step.Qcorr_step (α := α)
        (n := Nat.succ n) (hn := hn') (P := P) (A := A) hOK ih


/- 通常会計だけ取り出し -/
theorem main_Q (n : Nat) : ∀ P : HypPack α, Q (α := α) n P := by
  intro P
  exact (main_mutual (α := α) n P).1

/- forbid 付き会計だけ取り出し（ForbidOK 前提つき） -/
theorem main_Qcorr (n : Nat) :
    ∀ (P : HypPack α) (A : Finset α), ForbidOK (α := α) P A → Qcorr (α := α) n P A := by
  intro P A hOK

  exact (main_mutual (α := α) n P).2 A hOK

end Induction

end Dr1nds
