import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs
import Dr1nds.S1_Families

namespace Dr1nds

variable {α : Type} [Fintype α] [DecidableEq α]

/--
ClosureSystem α

SetFamily を継承し、
- 全体集合を含み
- 2 つの閉集合の共通部分で閉じている

という最小限の公理だけを持つ構造。

※ Set ではなく Finset (Finset α) で統一する。
-/
structure ClosureSystem (α : Type) [Fintype α] [DecidableEq α]
  extends SetFamily α :=
  (mem_inter :
     ∀ {X Y : Finset α}, X ∈ C → Y ∈ C → X ∩ Y ∈ C)
  (top_mem : U ∈ C)

end Dr1nds
