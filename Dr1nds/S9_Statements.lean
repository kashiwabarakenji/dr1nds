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
  ここでの T/Q は「任意の集合族 C」ではなく、
  HornNF R と universe U により与えられた FixFamily F : FixFamily R U の
  closed family F.C に対する主張として定義する。

  DR1/NEP は HornNF の述語として Core にあるのでそれを仮定に入れる。
  NF は HornNF に built-in（構造体のフィールド nf）なので別仮定は不要。

注：
  forbid1 では A=∅ が特別扱いになるので、Q には A.Nonempty を入れる。
-/

------------------------------------------------------------
-- 0. 使う “閉集合族” のパッケージ
------------------------------------------------------------

/--
Closed-family package:
a HornNF system `R`, a universe `U`, and a family `F : FixFamily R U`.
-/
structure ClosedPack where
  R : HornNF α
  U : Finset α
  F : FixFamily (α := α) R U

namespace ClosedPack

variable (P : ClosedPack (α := α))

/-- The underlying family of closed sets. -/
def C : Finset (Finset α) := P.F.C

end ClosedPack


------------------------------------------------------------
-- 1. T / Q（S9 の本体）
------------------------------------------------------------

/--
T(n):
For every closed family coming from some HornNF system,
if the system is DR1 and NEP, then NDS_n(C) ≤ 0.
-/
def T (n : Nat) : Prop :=
  ∀ (P : ClosedPack (α := α)),
    (P.R.IsDR1) →
    (P.R.IsNEP) →
    NDS (α := α) n (ClosedPack.C (α := α) P) ≤ 0

/--
Q(n):
For every closed family coming from some HornNF system,
if the system is DR1 and NEP, then for every nonempty forbid A,
NDS_corr_n(C;A) ≤ 0.

補足：
- forbid1 では A=∅ が特別扱いになるので A.Nonempty を仮定に入れる。
- A ⊆ U は「本来は」入れた方が自然だが、Forbid1 の定義自体は U を参照しない。
  必要になった段階（S10 証明で使う等）で仮定に入れてもよい。
  ここでは最小限として A.Nonempty のみ入れる。
-/
def Q (n : Nat) : Prop :=
  ∀ (P : ClosedPack (α := α)) (A : Finset α),
    (P.R.IsDR1) →
    (P.R.IsNEP) →
    A.Nonempty →
    NDS_corr (α := α) n (ClosedPack.C (α := α) P) A ≤ 0


------------------------------------------------------------
-- 2. 相互帰納ステップの「型」を凍結（S10/S11）
------------------------------------------------------------

/--
S11: Q(n−1) → T(n)

（実装は S11_T.lean 側で与える。ここでは型だけ凍結。）
-/
axiom T_step (n : Nat) :
  Q (α := α) (n - 1) → T (α := α) n

/-
S10: (T(n−1) ∧ Q(n−1)) → Q(n)

重要：forbid-corr の帰納では、通常 T(n−1) だけでは足りず、
「corr 版の IH」も必要になるため Q(n−1) を仮定に含める。
（実装は S10_Q.lean 側で与える。ここでは型だけ凍結。）
-/
--axiom Q_step (n : Nat) :
--  (T (α := α) (n - 1) ∧ Q (α := α) (n - 1)) → Q (α := α) n

end Dr1nds
