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

-- 例：contraction すると forbid は A.erase h になる（通常の forbid-1 ルート）
axiom forbid_update_contraction
  (A : Finset α) (h : α) :
  True

-- 例：deletion では forbid が「置換」される（P->h があれば new forbid = cl(P)）
axiom forbid_update_deletion
  (A : Finset α) (h : α) :
  True

-- 例：trace でも同様に “rules の minor” が走る
axiom forbid_update_trace
  (A : Finset α) (h : α) :
  True

end Dr1nds
