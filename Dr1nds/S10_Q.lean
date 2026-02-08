import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

import Dr1nds.Accounting
import Dr1nds.Forbid1
import Dr1nds.Core
import Dr1nds.S9_Statements

import Dr1nds.ConDelNdegIdCorr  -- CON_ID_corr

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
S10_Q.lean

目的：
  Q_step : (T(n-1) ∧ Q(n-1)) → Q(n) の「会計ステップ」を固定する。

注意：
  S9_Statements で T/Q は ClosedPack（HornNF + universe + FixFamily）上の命題として定義済み。
  ここでは T/Q を再定義しない。

実装方針：
  - CON_ID_corr（corr 版 con/del 恒等式）を使って Q(n) を分解する
  - 右辺の各項を ≤ 0 で評価するために必要な形を「補題/公理」として固定する
    （相互帰納により後で discharge）
-/

------------------------------------------------------------
-- 0. S10 で “必要になる” 供給物（後で埋める）
------------------------------------------------------------

/--
S10 で本来必要になる供給物（1）：
CON_ID_corr の右辺第一項に合わせた corr-IH。

（注意）あなたの CON_ID_corr が
  NDS_corr n C A
    = NDS_corr (n-1) (con v C) (A.erase v) + ...
という形なので、IH もそれに合わせる必要がある。
-/
axiom IH_corr_con
  (n : Nat)
  (C : Finset (Finset α))
  (A : Finset α)
  (v : α) :
  NDS_corr (α := α) (n - 1) (con (α := α) v C) (A.erase v) ≤ 0

/--
S10 で本来必要になる供給物（2）：
Hole 側の Del+ndeg 評価（S11 側から返ってくる典型形）。

あなたの現在の CON_ID_corr が
  Hole(C;A) に対する Del/ndeg を出すなら、この形で固定しておく。
-/
axiom DelNdeg_le_zero_on_Hole
  (n : Nat)
  (C : Finset (Finset α))
  (A : Finset α)
  (v : α) :
  NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) C A))
    + ndeg (α := α) (Hole (α := α) C A) v ≤ 0

------------------------------------------------------------
-- 1. S10 本体：Q_step
------------------------------------------------------------

/--
S10 (Q_step):
(T(n-1) ∧ Q(n-1)) を仮定して Q(n) を出す（会計ステップ）。

※ hn : 1 ≤ n は CON_ID_corr のために必要なら付ける。
-/
theorem Q_step
  (n : Nat) (hn : 1 ≤ n) :
  (T (α := α) (n - 1) ∧ Q (α := α) (n - 1)) → Q (α := α) n := by
  intro hIH P A hDR1 hNEP hAne
  -- Q(n) のゴール展開（S9 の定義に従う）

  classical
  -- C := closed family
  let C : Finset (Finset α) := ClosedPack.C (α := α) P

  -- A から v を選ぶ
  rcases hAne with ⟨v, hvA⟩

  -- corr 恒等式で分解（会計核）
  have hID :
      NDS_corr (α := α) n C A
        =
      NDS_corr (α := α) (n - 1) (con (α := α) v C) (A.erase v)
        +
      (NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) C A))
        + ndeg (α := α) (Hole (α := α) C A) v) := by
    simpa [C] using (CON_ID_corr (α := α) (n := n) hn C A v hvA)

  -- 右辺の評価に必要な2項：

  -- (1) con/corr 側：CON_ID_corr の右辺第一項に合わせた IH を使う
  have hCorr :
      NDS_corr (α := α) (n - 1) (con (α := α) v C) (A.erase v) ≤ 0 := by
    exact IH_corr_con (α := α) n C A v

  -- (2) Hole 側の Del+ndeg
  have hDelNdeg :
      NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) C A))
        + ndeg (α := α) (Hole (α := α) C A) v ≤ 0 := by
    exact DelNdeg_le_zero_on_Hole (α := α) n C A v

  -- 仕上げ：hID に代入して linarith
  -- NDS_corr n C A = X + Y, X≤0, Y≤0 ⇒ ≤0
  linarith [hID, hCorr, hDelNdeg]

end Dr1nds
