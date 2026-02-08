import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/--
A plain finite family of subsets of U.
This does NOT require `U ∈ C` (needed for "holey families", deletions, forbids, ...).
-/
structure SetFamily (α : Type) [DecidableEq α] where
  U : Finset α
  C : Finset (Finset α)
  subset_univ : ∀ {X : Finset α}, X ∈ C → X ⊆ U

namespace SetFamily

@[simp] lemma subset_univ_of_mem (F : SetFamily α) {X : Finset α} (hX : X ∈ F.C) :
    X ⊆ F.U :=
  F.subset_univ hX

end SetFamily


/--
A closure system on U (finite):
- contains U
- closed under intersection
(we keep it minimal; add `∅ ∈ C` later if you want)
-/
structure ClosureSystem (α : Type) [DecidableEq α] extends SetFamily α where
  top_mem : U ∈ C
  inter_mem : ∀ {X Y : Finset α}, X ∈ C → Y ∈ C → (X ∩ Y) ∈ C

namespace ClosureSystem

@[simp] lemma mem_top (CS : ClosureSystem α) : CS.U ∈ CS.C := CS.top_mem

lemma mem_inter (CS : ClosureSystem α) {X Y : Finset α}
    (hX : X ∈ CS.C) (hY : Y ∈ CS.C) : (X ∩ Y) ∈ CS.C :=
  CS.inter_mem hX hY

lemma subset_univ_of_mem (CS : ClosureSystem α) {X : Finset α} (hX : X ∈ CS.C) :
    X ⊆ CS.U :=
  CS.toSetFamily.subset_univ hX

end ClosureSystem

end Dr1nds
