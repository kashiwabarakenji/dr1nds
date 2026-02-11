import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs

namespace Dr1nds

variable {α : Type} [Fintype α] [DecidableEq α]

/--
ClosureSystem α

有限集合（Finset α）の族で、
- 全体集合を含み
- 2 つの閉集合の共通部分で閉じている

という最小限の公理だけを持つ抽象構造。
-/
structure ClosureSystem (α : Type)[Fintype α] [DecidableEq α]  :=
  (U : Finset α)
  (C : Set (Finset α))
  (mem_inter :
     ∀ {X Y : Finset α}, X ∈ C → Y ∈ C → X ∩ Y ∈ C)
  (top_mem : U ∈ C)

end Dr1nds
