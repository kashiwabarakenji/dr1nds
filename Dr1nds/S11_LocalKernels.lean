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
/-- Up-cardinality is always nonnegative (as an Int). -/
lemma Up_card_nonneg
  (C : Finset (Finset α)) (A : Finset α) :
  (0 : Int) ≤ (Up (α := α) C A).card := by
  -- `card` is a Nat; its coercion to Int is nonnegative.
  simpa using Int.ofNat_nonneg (Up (α := α) C A).card

/-- From a corrected bound we can drop the nonnegative `Up` term
    and obtain the plain `Hole` bound. -/
lemma corr_implies_hole_bound
  (n : Nat)
  (C : Finset (Finset α))
  (A : Finset α)
  (h : NDS_corr (α := α) n C A ≤ 0) :
  NDS (α := α) n (Hole (α := α) C A) ≤ 0 := by
  classical
  -- unfold the definition of NDS_corr
  -- NDS_corr n C A = NDS n (Hole C A) + (Up C A).card
  have h' :
      NDS (α := α) n (Hole (α := α) C A)
        + (Up (α := α) C A).card ≤ 0 := by
    simpa [NDS_corr] using h
  -- the Up-card term is nonnegative
  have hup : (0 : Int) ≤ (Up (α := α) C A).card :=
    Up_card_nonneg (α := α) C A
  -- so we can drop it from the left-hand side
  have : NDS (α := α) n (Hole (α := α) C A) ≤ 0 := by
    have := h'
    -- a + b ≤ 0 and 0 ≤ b  ⇒  a ≤ 0
    have := sub_nonpos.mpr h'
    -- more directly: use linear arithmetic
    linarith
  exact this



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

/-- Alias simp-lemma (kept for backward compatibility with earlier S10 code). -/
@[simp] theorem choose_con_pack_C'
  (P : HypPack (α := α)) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).C = con (α := α) v P.C := by
  simpa using (choose_con_pack_C (α := α) (P := P) (v := v))

/--
Con-branch bound (preferred):
use a con-pack enumerating `con v P.C` so later steps can stay in `HypPack` form.
-/
axiom IH_Q_gives_con_bound
  (n : Nat) (P : HypPack (α := α)) (v : α)
  (Pc : HypPack (α := α)) (hPcC : Pc.C = con (α := α) v P.C) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) Pc.C ≤ 0


/-
============================================================
  Del-branch upper bound (new kernel)

  Purpose:
  In `Q_step`, after applying `CON_ID`, we need an upper bound
    NDS (n-1) (Del v P.C) ≤ 0.

  The intended route is to bound the Del-branch by a forbid-corrected
  inequality on the con-branch, using the DR1 premise `Pv` for head `v`.

  We keep this as a local kernel (axiom) for now, so that the induction
  skeleton can be closed before proving the combinatorial core.
============================================================ -/

/--
DR1 implies `prem v` has at most one element; when it is nonempty we can pick the unique premise.
(Statement-only; proof postponed.)
-/
axiom choose_prem_of_hasHead
  (P : HypPack (α := α)) (v : α) :
  (P.H.prem v).Nonempty →
  { Pv : Finset α // Pv ∈ P.H.prem v }

/--
Optional strengthening: in the intended templates, the chosen `Pv` contains the head `v`.
(Statement-only; adjust/replace later if your NF/encoding changes.)
-/
axiom prem_contains_head_choice
  (P : HypPack (α := α)) (v : α)
  (h : (P.H.prem v).Nonempty) :
  let Pv := (choose_prem_of_hasHead (α := α) (P := P) (v := v) h).1
  v ∈ Pv

/-- Noncomputably pick `Pv` from `prem v` when nonempty. -/
noncomputable def pick_prem
  (P : HypPack (α := α)) (v : α) (h : (P.H.prem v).Nonempty) : Finset α :=
  (choose_prem_of_hasHead (α := α) (P := P) (v := v) h).1

@[simp] theorem pick_prem_mem
  (P : HypPack (α := α)) (v : α) (h : (P.H.prem v).Nonempty) :
  pick_prem (α := α) P v h ∈ P.H.prem v :=
  (choose_prem_of_hasHead (α := α) (P := P) (v := v) h).2

@[simp] theorem pick_prem_contains_head
  (P : HypPack (α := α)) (v : α) (h : (P.H.prem v).Nonempty) :
  v ∈ pick_prem (α := α) P v h := by
  simpa [pick_prem] using (prem_contains_head_choice (α := α) (P := P) (v := v) h)

/--
Del-branch bound (recommended kernel):

Given a con-pack `Pc` enumerating `con v P.C`, we can bound the Del-branch
by a forbid-corrected inequality on the con-branch with forbid set `Pv.erase v`.

This is the cleanest interface for `S10_Steps` because it avoids type-mismatch
between `Qcorr` (which is stated for `HypPack`) and the raw family `con v P.C`.
-/
axiom Del_branch_bound
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α))
  (v : α)
  (Pc : HypPack (α := α))
  (hPcC : Pc.C = con (α := α) v P.C)
  (Pv : Finset α) :
  (v ∈ Pv) →
  Qcorr (α := α) (n - 1) Pc (Pv.erase v) →
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
