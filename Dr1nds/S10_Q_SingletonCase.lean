import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.Accounting
import Dr1nds.Forbid1
import Dr1nds.ConDelNdegIdCorr
import Dr1nds.S9_Statements
import Dr1nds.S10_SingletonTools

namespace Dr1nds
open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
S10_SingletonCase.lean

目的：
  S10_Q の Case1（A = {v}）を処理する。

設計方針（重要）：
  * A = {v} は unary rule 由来の forbid
  * Hole C {v} は v-deletion に一致
  * 会計不等式は使わない
  * 台集合が 1 減るので、T / Q の帰納法で閉じる
-/

------------------------------------------------------------
-- 1. 基本補題（集合論的事実）
------------------------------------------------------------

lemma singleton_erase_empty
  (v : α) :
  ({v} : Finset α).erase v = ∅ := by
  simp

/-- singleton forbid の Hole 展開 -/
lemma Hole_singleton
  (C : Finset (Finset α)) (v : α) :
  Hole (α := α) C ({v} : Finset α)
    = C.filter (fun X => v ∉ X) := by
  unfold Hole
  ext X
  simp [Finset.singleton_subset_iff]

/-- singleton forbid の Up 展開 -/
lemma Up_singleton
  (C : Finset (Finset α)) (v : α) :
  Up (α := α) C ({v} : Finset α)
    = C.filter (fun X => v ∈ X) := by
  unfold Up
  ext X
  simp [Finset.singleton_subset_iff]

/-- Hole C {v} = Del v C （定義一致） -/
lemma Hole_singleton_eq_Del
  (C : Finset (Finset α)) (v : α) :
  Hole (α := α) C ({v} : Finset α)
    =
  Del (α := α) v C := by
  -- Del の定義が filter (v ∉ X) であることを使用
  simp [Hole_singleton, Del]

------------------------------------------------------------
-- 2. Case1 の意味論的仮定（unary forbid 起源）
------------------------------------------------------------

/--
A = {v} が出現しているのは、
unary rule v → h を head h で contraction した場合のみ。

この「起源条件」は S10_Q 側の設計で保証される。
ここでは predicate として凍結する。
-/
def SingletonForbidFromUnary
  (P : ClosedPack (α := α)) (v : α) : Prop := True

------------------------------------------------------------
-- 3. Case1 の主補題（結論は Q）
------------------------------------------------------------
/--
v-deletion によって得られる ClosedPack。
実装詳細は後でよいので、ここでは structure として凍結。
-/
axiom DelPack
  (P : ClosedPack (α := α)) (v : α) : ClosedPack (α := α)

/-- 台集合サイズが 1 減る -/
axiom DelPack_card
  (n : Nat) (P : ClosedPack (α := α)) (v : α) :
  P.U.card = n →
  (DelPack P v).U.card = n - 1

/-- DR1 は保存される -/
axiom DelPack_DR1
  (P : ClosedPack (α := α)) (v : α) :
  P.R.IsDR1 →
  (DelPack P v).R.IsDR1

/-- NEP は保存される -/
axiom DelPack_NEP
  (P : ClosedPack (α := α)) (v : α) :
  P.R.IsNEP →
  (DelPack P v).R.IsNEP

/--
Case1 の核心：
singleton forbid は deletion pack の empty forbid に帰着
-/
axiom NDS_corr_singleton_to_delete
  (n : Nat) (P : ClosedPack (α := α)) (v : α) :
  NDS_corr (α := α) n P.C ({v} : Finset α)
    =
  NDS_corr (α := α) (n - 1) (DelPack P v).C ∅
/--
S10_Q Case1（A = {v}）用の主補題。

重要：
  * 結論は NDS ≤ 0 ではなく Q n
  * 証明は deletion による台集合縮小 → 帰納法
-/
theorem Q_step_singleton_case
  (n : Nat)
  (P : ClosedPack (α := α))
  (v : α)
  (hcard : P.U.card = n)
  (hDR1 : P.R.IsDR1)
  (hNEP : P.R.IsNEP)
  (hQ : Q (α := α) (n - 1)) :
  NDS_corr (α := α) n P.C ({v} : Finset α) ≤ 0 :=
by
  -- deletion pack に翻訳
  have hrewrite :=
    NDS_corr_singleton_to_delete (α := α) n P v
  -- 書き換え
  have :
    NDS_corr (α := α) (n - 1) (DelPack P v).C ∅ ≤ 0 := by
      -- Q(n-1) を empty forbid に適用
      apply hQ
      · exact DelPack_card (α := α) n P v hcard
      · exact DelPack_DR1 (α := α) P v hDR1
      · exact DelPack_NEP (α := α) P v hNEP
      · -- empty forbid は Nonempty 不要（定義次第）
        -- ここは S9 の Q 定義に合わせて調整
        simp
        sorry
      · simp
  -- 元に戻す
  simpa [hrewrite] using this


------------------------------------------------------------
-- 4. （参考）Case1 で実際に行う変形の流れ（コメント）
------------------------------------------------------------

/-
この補題の内部で想定している流れ（Lean では書かない）：

1. A = {v} より
     Hole C A = Hole C {v}

2. Hole_singleton_eq_Del より
     Hole C {v} = Del v C

3. 問題は Del v C 上の Q/T になる
   → 台集合サイズが 1 減っている

4. 帰納仮定 (T(n-1), Q(n-1)) を適用

以上で Case1 は閉じる。
-/

end Dr1nds
