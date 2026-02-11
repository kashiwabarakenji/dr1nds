-- Dr1nds/S9_Main.lean
import Dr1nds.S8_Statements

namespace Dr1nds
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

theorem main_from_Q
  (n : Nat) (P : HypPack α) :
  Q (α := α) n P → NDS (α := α) n P.C ≤ 0 := by
  intro hQ
  simpa [Q] using hQ

end Dr1nds
