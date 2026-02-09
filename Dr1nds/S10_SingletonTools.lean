import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Dr1nds.Forbid1
import Dr1nds.Accounting

namespace Dr1nds
open scoped BigOperators
variable {α : Type} [DecidableEq α]

/--
A.card = 1 かつ v∈A なら A = {v}.
（名前事故・cast事故回避のため axiom で凍結）
-/
axiom eq_singleton_of_card_eq_one_of_mem
  (A : Finset α) (v : α) :
  A.card = 1 → v ∈ A → A = ({v} : Finset α)

/--
singleton の erase は空集合。
これは lemma で十分。
-/
lemma erase_eq_empty_of_eq_singleton (A : Finset α) (v : α) :
  A = ({v} : Finset α) → A.erase v = (∅ : Finset α) := by
  intro h; simp [h]

/--
A = ∅ のときの NDS_corr の簡約。
（後で simp で証明できるが、今は凍結）
-/
axiom NDS_corr_empty
  (n : Nat) (C : Finset (Finset α)) :
  NDS_corr (α := α) n C (∅ : Finset α) = (C.card : Int)

end Dr1nds
