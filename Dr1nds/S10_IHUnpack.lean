import Dr1nds.S9_Statements
import Dr1nds.Forbid1

namespace Dr1nds
open scoped BigOperators
variable {α : Type} [DecidableEq α]

/--
IH を ClosedPack 形で使うための unpack 補題。
B2（A.erase v 非空）の Case2 用。
-/
axiom IH_corr_con_pack
  (n : Nat)
  (P : ClosedPack (α := α))
  (A : Finset α)
  (v : α) :
  Q (α := α) (n - 1) →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1)
    (con (α := α) v (ClosedPack.C (α := α) P))
    (A.erase v) ≤ 0

end Dr1nds
