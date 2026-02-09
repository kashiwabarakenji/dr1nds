import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-- weight: w_n(X) = 2|X| - n (as Int) -/
def w (n : Nat) (X : Finset α) : Int :=
  (2 : Int) * (X.card : Int) - (n : Int)

/-- NDS_n(C) = Σ_{X∈C} w_n(X) -/
def NDS (n : Nat) (C : Finset (Finset α)) : Int :=
  ∑ X ∈ C, w (α := α) n X

/-- deg_C(u) = #{X∈C : u∈X} -/
def deg (C : Finset (Finset α)) (u : α) : Nat :=
  (C.filter (fun X => u ∈ X)).card

/-- ndeg_C(u) = 2*deg_C(u) - |C| (as Int) -/
def ndeg (C : Finset (Finset α)) (u : α) : Int :=
  (2 : Int) * (deg (α := α) C u : Int) - (C.card : Int)

namespace Accounting

/-- w_n(X) = w_{n-1}(X) - 1 (Int identity). -/
lemma w_succ (n : Nat) (X : Finset α) :
    w (α := α) n.succ X = w (α := α) n X - 1 := by
  -- simp [w]; ring みたいな流れ（Int の整理）
  -- `simp [w]` のあと `linarith` でも可
  sorry

/-- If u∈X then w_n(X) = w_{n-1}(X.erase u). -/
lemma w_erase_eq (n : Nat) {u : α} {X : Finset α} (hu : u ∈ X) :
    w (α := α) n X = w (α := α) (n-1) (X.erase u) := by
  -- key: card_erase_of_mem hu, Int coercions
  -- `have : (X.erase u).card = X.card - 1 := card_erase_of_mem hu`
  sorry

/-- Basic partition of C by membership of u: |C| = |{X∈C | u∈X}| + |{X∈C | u∉X}| -/
lemma card_partition_mem (C : Finset (Finset α)) (u : α) :
    C.card =
      (C.filter (fun X => u ∈ X)).card +
      (C.filter (fun X => u ∉ X)).card := by
  -- standard: card_filter_add_card_filter_neg_eq_card
  -- in Mathlib: `Finset.card_filter_add_card_filter_neg_eq` 系を探して使う
  sorry

/-- ndeg = deg - |Del| (Del = filter (u∉X)). -/
lemma ndeg_eq_deg_sub_del (C : Finset (Finset α)) (u : α) :
    ndeg (α := α) C u
      = (deg (α := α) C u : Int) - ((C.filter (fun X => u ∉ X)).card : Int) := by
  -- expand ndeg, deg, use card_partition_mem
  -- Int で整理
  sorry

/-- (sum split) NDS over C = sum over u∈X part + sum over u∉X part. -/
lemma NDS_split_mem (n : Nat) (C : Finset (Finset α)) (u : α) :
    NDS (α := α) n C
      = (∑ X ∈ (C.filter (fun X => u ∈ X)), w (α := α) n X)
        + (∑ X ∈ (C.filter (fun X => u ∉ X)), w (α := α) n X) := by
  -- `by classical`
  -- use `Finset.sum_filter_add_sum_filter_not` みたいな補題（なければ自作）
  sorry

end Accounting
end Dr1nds
