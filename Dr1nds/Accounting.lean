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

end Dr1nds
