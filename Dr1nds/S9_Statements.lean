import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.Core
import Dr1nds.Accounting
import Dr1nds.Forbid1

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-
S9_Statements.lean

目的：
  相互帰納の「命題そのもの」を凍結する。

重要：
  T/Q は「任意の集合族」ではなく、
  HornNF R と universe U により与えられた FixFamily F : FixFamily R U の
  closed family F.C に対する主張として定義する。

注意（重要）：
  NDS のパラメータ n は universe の大きさ |U| と一致させる必要があるので
  P.U.card = n を仮定として入れる（後段の con/trace で必須）。
-/

------------------------------------------------------------
-- 0. Closed family package
------------------------------------------------------------

structure ClosedPack where
  R : HornNF α
  U : Finset α
  F : FixFamily (α := α) R U

namespace ClosedPack

variable (P : ClosedPack (α := α))

/-- The underlying family of closed sets. -/
abbrev C : Finset (Finset α) := P.F.C

end ClosedPack


------------------------------------------------------------
-- 1. T / Q
------------------------------------------------------------

/--
T(n):
For every closed family coming from some HornNF system,
if (|U|=n) and the system is DR1 and NEP, then NDS_n(C) ≤ 0.
-/
def T (n : Nat) : Prop :=
  ∀ (P : ClosedPack (α := α)),
    P.U.card = n →
    P.R.IsDR1 →
    P.R.IsNEP →
    NDS (α := α) n (ClosedPack.C (α := α) P) ≤ 0

/--
Q(n):
For every closed family coming from some HornNF system,
if (|U|=n) and the system is DR1 and NEP, then for every nonempty forbid A⊆U,
NDS_corr_n(C;A) ≤ 0.
-/
def Q (n : Nat) : Prop :=
  ∀ (P : ClosedPack) (A : Finset α),
    P.U.card = n →
    P.R.IsDR1 →
    P.R.IsNEP →
    2 ≤ A.card →
    A ⊆ P.U →
    NDS_corr n P.C A ≤ 0

------------------------------------------------------------
-- 2. Mutual induction step "types" (S10 / S11)
------------------------------------------------------------

/--
S11: Q(n) → T(n+1)

（実装は S11_T.lean 側で与える。ここでは型だけ凍結。）
-/
axiom T_step (n : Nat) :
  Q (α := α) n → T (α := α) (n + 1)

/-
S10: (T(n) ∧ Q(n)) → Q(n+1)

（実装は S10_Q.lean 側で与える。ここでは型だけ凍結。）
-/
-- axiom Q_step (n : Nat) :
--   (T (α := α) n ∧ Q (α := α) n) → Q (α := α) (n + 1)

end Dr1nds
