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


/-
  Canonical API namespace for local kernels.
  S10_Steps should import this file and refer to either `Local.*` or the re-exported names below.
-/
namespace Local

structure GoodV_for_Q (n : Nat) (P : HypPack (α := α)) where
  v : α
  hndeg : ndeg (α := α) P.C v ≤ 0

axiom exists_goodV_for_Q
  (n : Nat) (P : HypPack (α := α)) :
  Nonempty (GoodV_for_Q (α := α) n P)

/-- Nonempty witness extractor for `GoodV_for_Q` (keeps tactics-simple usage). -/
noncomputable def choose_goodV_for_Q (n : Nat) (P : HypPack (α := α)) :
    GoodV_for_Q (α := α) n P :=
  Classical.choice (exists_goodV_for_Q (α := α) n P)

/-- Legacy / convenience form: just a vertex with `ndeg ≤ 0`. -/
theorem exists_good_v_for_Q (n : Nat) (P : HypPack (α := α)) :
    ∃ v : α, ndeg (α := α) P.C v ≤ 0 := by
  classical
  let gv : GoodV_for_Q (α := α) n P := Classical.choice (exists_goodV_for_Q (α := α) n P)
  exact ⟨gv.v, gv.hndeg⟩

/-- Spec lemma for the chosen good vertex. -/
@[simp] theorem choose_goodV_for_Q_ndeg (n : Nat) (P : HypPack (α := α)) :
    ndeg (α := α) P.C (choose_goodV_for_Q (α := α) n P).v ≤ 0 :=
  (choose_goodV_for_Q (α := α) n P).hndeg


@[simp] theorem goodV_ndeg
  {n : Nat} {P : HypPack (α := α)} (gv : GoodV_for_Q (α := α) n P) :
  ndeg (α := α) P.C gv.v ≤ 0 :=
  gv.hndeg

/--
con 後の世界を IH の対象（HypPack）として返すための API。
S9（Horn 保存／表現可能性）を埋める段階で中身を正当化する。

最小形としては `C` の同一視だけを返す（`U` や `H` の更新は後回しでOK）。
-/
axiom exists_con_pack
  (P : HypPack (α := α)) (v : α) :
  ∃ Pcon : HypPack (α := α),
    Pcon.C = con (α := α) v P.C

/-- Noncomputably choose a con-pack. -/
noncomputable def choose_con_pack
  (P : HypPack (α := α)) (v : α) : HypPack (α := α) :=
  Classical.choose (exists_con_pack (α := α) (P := P) (v := v))

/-- Spec lemma: the chosen pack enumerates `con v P.C`. -/
@[simp] theorem choose_con_pack_C
  (P : HypPack (α := α)) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).C = con (α := α) v P.C :=
  Classical.choose_spec (exists_con_pack (α := α) (P := P) (v := v))

axiom IH_Q_gives_con_bound
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0

axiom Del_bound
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0

/-- Choose an element of `A` from `ForbidOK P A` (uses `A.Nonempty`). -/
theorem choose_v_in_A
  (P : HypPack (α := α)) (A : Finset α) :
  ForbidOK (α := α) P A → ∃ v : α, v ∈ A := by
  intro hOK
  have hne : A.Nonempty := ForbidOK.nonempty (α := α) (P := P) (A := A) hOK
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, hv⟩

/-- Noncomputably pick an element `v ∈ A` from `ForbidOK P A`. -/
noncomputable def pick_v_in_A
  (P : HypPack (α := α)) (A : Finset α) (hOK : ForbidOK (α := α) P A) : α :=
  Classical.choose (choose_v_in_A (α := α) (P := P) (A := A) hOK)

@[simp] theorem pick_v_in_A_mem
  (P : HypPack (α := α)) (A : Finset α) (hOK : ForbidOK (α := α) P A) :
  pick_v_in_A (α := α) P A hOK ∈ A :=
  Classical.choose_spec (choose_v_in_A (α := α) (P := P) (A := A) hOK)

/-- From `ForbidOK` we can always extract `A.Nonempty` (helper for case splits). -/
theorem forbidOK_nonempty (P : HypPack (α := α)) (A : Finset α) :
    ForbidOK (α := α) P A → A.Nonempty := by
  intro h
  exact (ForbidOK.nonempty (α := α) (P := P) (A := A) h)

--/-- Case split helper for `A.erase v`: either empty or nonempty. -/
theorem erase_empty_or_nonempty
  (A : Finset α) (v : α) : v ∈ A → ((A.erase v) = ∅ ∨ (A.erase v).Nonempty) := by
  intro _hv
  classical
  by_cases h : A.erase v = ∅
  · exact Or.inl h
  · exact Or.inr (Finset.nonempty_iff_ne_empty.2 h)

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
