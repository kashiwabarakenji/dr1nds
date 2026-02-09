import Dr1nds.S9_Statements
import Dr1nds.Forbid1
import Dr1nds.Accounting
import Dr1nds.Core
import Dr1nds.S7_LocalGood

namespace Dr1nds
open scoped BigOperators
variable {α : Type} [DecidableEq α]

/--
S7 の最重要核（A1 案）：
Hole 側の Del + ndeg が非正。

※ 今は axiom で凍結。
※ 仮定は「起源付き（ClosedPack）」に閉じている。
-/
axiom DelNdeg_le_zero_on_Hole
  (n : Nat)
  (P : ClosedPack (α := α))
  (A : Finset α)
  (v : α) :
  P.R.IsDR1 →
  P.R.IsNEP →
  A ⊆ P.U →
  v ∈ A →
  LocalGood (α := α) P A v →
  NDS (α := α) (n - 1)
      (Del (α := α) v (Hole (α := α) (ClosedPack.C (α := α) P) A))
    + ndeg (α := α)
        (Hole (α := α) (ClosedPack.C (α := α) P) A) v ≤ 0

end Dr1nds
