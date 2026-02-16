-- Dr1nds/Forbid/World.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs          -- NDS, NDS_corr, Up, Hole
import Dr1nds.Forbid.Basic         -- 基本補題（Up/Hole, singleton, corr_implies_hole_bound）

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-- forbid は「無し」か「1個の禁止集合 A」。 -/
abbrev Forbid (α : Type) := Option (Finset α)

/--
ForbidWorld: 「台サイズ n（=Nat）」は NDS の引数として外から与える運用でよいので、
ここでは family と forbid だけを保持する薄いラッパ。
-/
structure ForbidWorld (α : Type) [DecidableEq α] where
  Cbase : Finset (Finset α)
  A     : Forbid α

namespace ForbidWorld

variable (W : ForbidWorld α)

/-- forbid を適用した family（A=None なら Cbase, A=some A なら Hole Cbase A） -/
def C : Finset (Finset α) :=
  match W.A with
  | none    => W.Cbase
  | some A  => Hole (α := α) W.Cbase A

/-- Up 集合（A=None のときは ∅ を返す運用にしておくと式が安定する） -/
def UpSet : Finset (Finset α) :=
  match W.A with
  | none    => ∅
  | some A  => Up (α := α) W.Cbase A

/-- corrected NDS（A=None のときは NDS） -/
def NDSCorr (n : Nat) : Int :=
  match W.A with
  | none    => NDS (α := α) n W.Cbase
  | some A  => NDS_corr (α := α) n W.Cbase A

@[simp] lemma C_none (C : Finset (Finset α)) :
  (ForbidWorld.mk (α := α) C none).C = C := by
  rfl

@[simp] lemma C_some (C : Finset (Finset α)) (A : Finset α) :
  (ForbidWorld.mk (α := α) C (some A)).C = Hole (α := α) C A := by
  rfl

@[simp] lemma UpSet_none (C : Finset (Finset α)) :
  (ForbidWorld.mk (α := α) C none).UpSet = (∅ : Finset (Finset α)) := by
  rfl

@[simp] lemma UpSet_some (C : Finset (Finset α)) (A : Finset α) :
  (ForbidWorld.mk (α := α) C (some A)).UpSet = Up (α := α) C A := by
  rfl

@[simp] lemma NDSCorr_none (n : Nat) (C : Finset (Finset α)) :
  (ForbidWorld.mk (α := α) C none).NDSCorr n = NDS (α := α) n C := by
  rfl

@[simp] lemma NDSCorr_some (n : Nat) (C : Finset (Finset α)) (A : Finset α) :
  (ForbidWorld.mk (α := α) C (some A)).NDSCorr n = NDS_corr (α := α) n C A := by
  rfl

end ForbidWorld

end Dr1nds
