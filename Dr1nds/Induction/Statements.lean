import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornClosure
import Dr1nds.Forbid.HornWithForbid
import Dr1nds.SetFamily.CoreDefs


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
  hNEP : H.IsNEP
  -- hNF  : H.IsNF

/- ------------------------------------------------------------
  1'. 帰納法で運ぶ命題 Q / Qcorr（定義固定）

  方針（親スレ合意）：
  - Q / Qcorr は「評価命題」そのものに固定する。
  - これにより |A|=1 分岐のような “等式で評価を落として IH を当てる” 型のステップが
    そのまま Lean で閉じられる。
------------------------------------------------------------ -/

-- forbid なし世界（Pack0）での主命題：`NDS ≤ 0`。
def Q (n : Nat) (P : Pack0 α) : Prop :=
  P.H.U.card = n → NDS n P.H.FixSet ≤ 0

-- forbid あり世界（Pack1）での主命題：`NDS_corr ≤ 0`。
-- 注意：forbid は常に `Pack1.A = closure(Araw)` を用いる。

def Qcorr (n : Nat) (F : HornWithForbid α) : Prop :=
  F.H.U.card = n → NDS_corr n F.H.FixSet F.F ≤ 0

/-
Set-family level NEP: the family contains the empty set.

We keep NEP at the *family* level so it can be shared across the Horn/ClosureSystem/WithForbid worlds.
In this project we will apply it primarily to the *base* family `Pack*.C` (not Hole-filtered families),
so it does not conflict with the “no double Hole” convention for `NDS_corr`.
-/
-- def NEP (C : Finset (Finset α)) : Prop :=
--   (∅ : Finset α) ∈ C

/- ------------------------------------------------------------
  3. Base case（独立核として凍結）
  ここは後で埋める。
------------------------------------------------------------ -/

axiom Q_base (P : Pack0 α) : Q 0 P

axiom Qcorr_base (P : HornWithForbid α) : Qcorr 0 P

end Dr1nds
