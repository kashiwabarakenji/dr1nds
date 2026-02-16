-- Dr1nds/Forbid/Update.lean
import Mathlib.Tactic

import Dr1nds.Forbid.Basic
import Dr1nds.S0_CoreDefs

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/-
forbid 更新規則（凍結仕様）
ここでの「世界」は “DR1 + forbid 1つ” の表現。
family だけでなく (rules + forbid) 側の操作が必要になるので、
まずは「言明として」固定しておく。
-/

/-- (SPEC) contraction で forbid を更新した結果（後で定義に置き換える）。 -/
axiom forbid_update_contraction
  (A : Finset α) (h : α) : Finset α

/-- (SPEC) deletion で forbid を更新した結果（後で定義に置き換える）。 -/
axiom forbid_update_deletion
  (A : Finset α) (h : α) : Finset α

/-- (SPEC) trace で forbid を更新した結果（後で定義に置き換える）。 -/
axiom forbid_update_trace
  (A : Finset α) (h : α) : Finset α

/-- (SPEC) contraction の singleton forbid は `erase`（期待される最小仕様）。 -/
axiom forbid_update_contraction_singleton
  (a h : α) :
  forbid_update_contraction ({a} : Finset α) h = ({a} : Finset α).erase h

end Dr1nds
