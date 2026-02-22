import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs
import Dr1nds.SetFamily.SetFamily

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


namespace ClosureSystem

variable (S : ClosureSystem α)

/-- A closure system is `NEP` iff it contains the empty set.  (This is the SetFamily-level `NEP`.) -/
lemma nep_iff_empty_mem : SetFamily.NEP  (S.toSetFamily) ↔ (∅ : Finset α) ∈ S.C := by
  rfl

/-- If a closure system is `NEP`, then the empty set is a closed set. -/
lemma empty_mem_of_nep (h : SetFamily.NEP (S.toSetFamily)) : (∅ : Finset α) ∈ S.C := by
  simpa [SetFamily.NEP] using h

end ClosureSystem

end Dr1nds
