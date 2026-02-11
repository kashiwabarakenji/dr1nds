-- Dr1nds/S11_LocalKernels.lean
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs
import Dr1nds.S8_Statements

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ============================================================
  S11 : Local kernels (SKELETON)
  目的：S10_Steps から呼ばれる「局所核 API」を一本化する。
  方針：骨格優先。中身は axiom/sorry で後回し。

  注意：このファイルは *S10_Steps を import しない*（循環依存を避ける）。
============================================================ -/

namespace Local

structure GoodV_for_Q (n : Nat) (P : HypPack (α := α)) where
  v : α
  hndeg : ndeg (α := α) P.C v ≤ 0

axiom exists_goodV_for_Q
  (n : Nat) (P : HypPack (α := α)) :
  Nonempty (GoodV_for_Q (α := α) n P)

noncomputable def choose_goodV_for_Q (n : Nat) (P : HypPack (α := α)) :
    GoodV_for_Q (α := α) n P :=
  Classical.choice (exists_goodV_for_Q (α := α) n P)

@[simp] theorem goodV_ndeg
  {n : Nat} {P : HypPack (α := α)} (gv : GoodV_for_Q (α := α) n P) :
  ndeg (α := α) P.C gv.v ≤ 0 :=
  gv.hndeg

axiom IH_Q_gives_con_bound
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0

axiom Del_bound
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0

axiom choose_v_in_A
  (P : HypPack (α := α)) (A : Finset α) :
  ForbidOK (α := α) P A → ∃ v : α, v ∈ A

axiom erase_empty_or_nonempty
  (A : Finset α) (v : α) : v ∈ A → ((A.erase v) = ∅ ∨ (A.erase v).Nonempty)

axiom Qcorr_case1_singleton
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A → v ∈ A → (A.erase v) = ∅ →
  NDS_corr (α := α) n P.C A ≤ 0

axiom Del_hole_bound
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A → v ∈ A →
  NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A)) ≤ 0

axiom ndeg_hole_le_zero_of_choice
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A → v ∈ A →
  ndeg (α := α) (Hole (α := α) P.C A) v ≤ 0

end Local

end Dr1nds
