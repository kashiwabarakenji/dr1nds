import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornWithForbid

set_option autoImplicit false

/-
============================================================
  Induction Statements (FREEZE SPEC)
  目的：
    - 帰納法で運ぶ命題 Q / Qcorr の「型」と「入出力」を凍結する
    - 証明は S10(wiring) と S11(local kernels) へ分離
  方針：
    - ここでは数学的中身を一切書かない（すべて Prop の仕様として固定）
    - forbid あり/なしを混ぜない
    - |A|=1 も許す（ただし次のステップの取り扱いは別分岐にする）
============================================================
-/

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ------------------------------------------------------------
  0. パック型（必要最小限）
  ここは後で自由に変えてよい。
  「何を帰納法の入力に取るか」を固定する役目だけ。
------------------------------------------------------------ -/

-- forbid なし世界：DR1(+NEP+NF) HornNF と、その閉集合族 C = FixSet
structure Pack0 (α : Type) [DecidableEq α] where
  H : _root_.Dr1nds.HornNF α
  hDR1 : H.IsDR1
  -- 追加で必要なら：
  -- hNEP : H.IsNEP
  -- hNF  : H.IsNF

-- forbid あり世界：DR1 HornNF + forbid 閉集合 F（あなたの HornWithForbid と同型）
structure Pack1 (α : Type) [DecidableEq α] where
  S : _root_.Dr1nds.HornWithForbid α
  -- HornWithForbid に DR1/closed などを含めている想定なので、ここは薄くする。
  -- 必要ならここに追加条件を持たせてもよい。


/- ------------------------------------------------------------
  1. 帰納法で運ぶ命題 Q / Qcorr
  ここが最重要の凍結点。
------------------------------------------------------------ -/

/-- forbid なし世界の「評価対象 family」 -/
noncomputable def Pack0.C (P : Pack0 α) : Finset (Finset α) :=
  P.H.FixSet

/-- forbid あり世界の「評価対象 family」（forbid を入れる前の基底 family）。
    注意：`HornWithForbid.FixSet` は legacy 実装で forbid-filter 済み（= Hole 側）なので、
    `NDS_corr` を二重 Hole にしないため、ここでは基底 `HornNF.FixSet` を採用する。 -/
noncomputable def Pack1.C (P : Pack1 α) : Finset (Finset α) :=
  P.S.H.FixSet

/-- forbid あり世界の forbid 集合（Hole/Up に渡す A） -/
def Pack1.A (P : Pack1 α) : Finset α :=
  P.S.F

/- ------------------------------------------------------------
  1'. 帰納法で運ぶ命題 Q / Qcorr（定義固定）

  方針（親スレ合意）：
  - Q / Qcorr は「評価命題」そのものに固定する。
  - これにより |A|=1 分岐のような “等式で評価を落として IH を当てる” 型のステップが
    そのまま Lean で閉じられる。
------------------------------------------------------------ -/

/-- forbid なし世界（Pack0）での主命題：`NDS ≤ 0`。 -/
def Q (n : Nat) (P : Pack0 α) : Prop :=
  _root_.Dr1nds.NDS n (Pack0.C P) ≤ 0

/-- forbid あり世界（Pack1）での主命題：`NDS_corr ≤ 0`。 -/
def Qcorr (n : Nat) (P : Pack1 α) : Prop :=
  _root_.Dr1nds.NDS_corr n (Pack1.C P) (Pack1.A P) ≤ 0


/- ------------------------------------------------------------
  2'. Q_implies_NDS_le_zero, Qcorr_implies_NDSCorr_le_zero の定義的証明
------------------------------------------------------------ -/

/-- Q から “NDS ≤ 0” が出る（定義により自明） -/
theorem Q_implies_NDS_le_zero
  (n : Nat) (P : Pack0 α) :
  Q n P →
  _root_.Dr1nds.NDS n (Pack0.C P) ≤ 0 :=
by
  intro hQ
  simpa [Q] using hQ

/-- Qcorr から “NDS_corr ≤ 0” が出る（定義により自明） -/
theorem Qcorr_implies_NDSCorr_le_zero
  (n : Nat) (P : Pack1 α) :
  Qcorr n P →
  _root_.Dr1nds.NDS_corr n (Pack1.C P) (Pack1.A P) ≤ 0 :=
by
  intro hQ
  simpa [Qcorr] using hQ


/- ------------------------------------------------------------
  3. Base case（独立核として凍結）
  ここは後で埋める。
------------------------------------------------------------ -/

axiom Q_base (P : Pack0 α) : Q 0 P

axiom Qcorr_base (P : Pack1 α) : Qcorr 0 P


/- ------------------------------------------------------------
  4. Induction Step について

  注意：帰納ステップ（wiring）は `Dr1nds/Induction/Steps.lean` に実装し、
  枝の本体（局所核）は `Dr1nds/Induction/LocalKernels.lean` が提供する。

  この `Statements.lean` は「命題の型・評価への射影・base case」だけを凍結し、
  `Q_step` / `Qcorr_step` を axiom としては置かない。
------------------------------------------------------------ -/


/- ------------------------------------------------------------
  5. 目的定理（Statements では証明しない）
------------------------------------------------------------ -/

-- 最終ゴール（例）
theorem main_goal_from_Q
  (n : Nat) (P : Pack0 α) :
  Q n P →
  _root_.Dr1nds.NDS n (Pack0.C P) ≤ 0 :=
by
  intro hQ
  simpa [Q] using hQ

theorem main_goal_from_Qcorr
  (n : Nat) (P : Pack1 α) :
  Qcorr n P →
  _root_.Dr1nds.NDS_corr n (Pack1.C P) (Pack1.A P) ≤ 0 :=
by
  intro hQ
  simpa [Qcorr] using hQ

end Dr1nds
