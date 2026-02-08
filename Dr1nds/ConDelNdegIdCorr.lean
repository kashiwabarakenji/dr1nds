import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

import Dr1nds.Accounting
import Dr1nds.ConDelNdegId
import Dr1nds.Forbid1

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
forbid1（corr）版の con/Del 会計恒等式。

狙い：
  NDS_corr n C A を、点 v で「v∈X / v∉X」に分割し、
  n→n-1 の weight 変換で con/Del に落とす。

この補題があると S10_Q の Q_step は「代入＋linarith」で終わる。
-/

/--
corr 版の基本恒等式（S10 が必要とする “会計の核”）。

※ここでは最終形だけを固定し、詳細証明はこのファイル内で詰める。
（あなたの作業では、まずこの lemma を完成させるのが子スレッドのゴール。）
-/
theorem CON_ID_corr
  (n : Nat) (hn : 1 ≤ n)
  (C : Finset (Finset α)) (A : Finset α)
  (v : α) (hvA : v ∈ A) :
  NDS_corr (α := α) n C A
    =
  -- 「v を落とした corr」＋「Del+ndeg 型の補正」
  NDS_corr (α := α) (n - 1) (con (α := α) v C) (A.erase v)
    +
  (NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) C A))
      + ndeg (α := α) (Hole (α := α) C A) v) := by
  -- TODO: ここを会計で埋める（v∈X / v∉X による Hole の分割）
  -- まずは仕様を固定するため admit 可（後で必ず消す）
  admit

end Dr1nds
