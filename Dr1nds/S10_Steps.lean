-- Dr1nds/S10_Steps.lean
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

import Dr1nds.S0_CoreDefs
import Dr1nds.S9_IH_Unpack
import Dr1nds.S8_Statements          -- Q / Qcorr / ForbidOK / HypPack / CON_ID_pack / CON_ID_corr_pack
import Dr1nds.S5_Forbid_Compat       -- forbid / Hole / Up 互換補題（Del-bound branch で使用）
import Dr1nds.S11_LocalKernels       -- v選択・局所評価 API


namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ============================================================
  S10 : Step lemmas (SKELETON)
  目的：
    - Q と Qcorr のステップを「配線」だけ確定する
    - 局所核は S11_LocalKernels の axiom / theorem 群に“丸投げ”する
============================================================ -/

namespace Step

/-- `2 ≤ A.card` かつ `v∈A` なら `A.erase v` は空でない。

`Qcorr_step` の互換的な case split（`erase_empty_or_nonempty`）を将来削除するための
局所補題。`ForbidOK` を `2 ≤ card` に固定した設計では、この補題により
`A.erase v = ∅` の分岐は“理論上起きない”ことを Lean 側でも明示できる。
-/
lemma erase_nonempty_of_two_le_card
  (A : Finset α) (v : α) (hv : v ∈ A) (h2 : 2 ≤ A.card) :
  (A.erase v).Nonempty := by
  classical
  have hcard : (A.erase v).card = A.card - 1 := by
    simpa using (Finset.card_erase_of_mem hv)
  have hpos : 0 < (A.erase v).card := by
    have hlt : 1 < A.card := Nat.lt_of_lt_of_le (by decide : (1:Nat) < 2) h2
    have : 0 < A.card - 1 := Nat.sub_pos_of_lt hlt
    simpa [hcard] using this
  exact Finset.card_pos.mp hpos

/-- `A ⊆ U` なら `A.erase v ⊆ U.erase v`。-/
lemma erase_subset_erase
  (A U : Finset α) (v : α) (hAU : A ⊆ U) :
  A.erase v ⊆ U.erase v := by
  intro x hx
  have hxA : x ∈ A := Finset.mem_of_mem_erase hx
  have hxU : x ∈ U := hAU hxA
  have hxne : x ≠ v := (Finset.mem_erase.mp hx).1
  exact Finset.mem_erase.mpr ⟨hxne, hxU⟩

lemma ForbidOK.subset_U {P : HypPack (α := α)} {A : Finset α}
  (hOK : ForbidOK (α := α) P A) : A ⊆ P.H.U :=
by
  exact hOK.1

lemma ForbidOK.card_two_le {P : HypPack (α := α)} {A : Finset α}
  (hOK : ForbidOK (α := α) P A) : 2 ≤ A.card :=
by
  exact hOK.2

lemma ForbidOK.erase_nonempty {P : HypPack (α := α)} {A : Finset α} {v : α}
  (hOK : ForbidOK (α := α) P A) (hv : v ∈ A) : (A.erase v).Nonempty :=
by
  exact erase_nonempty_of_two_le_card (A := A) (v := v) hv hOK.2

/- ------------------------------------------------------------
  Q_step（通常 NDS）
------------------------------------------------------------ -/

theorem Q_step
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α)) :
  (∀ P' : HypPack α, IH (α := α) (n - 1) P') →
  Q (α := α) n P := by
  classical
  intro ihAll
  have hIH : IH (α := α) (n - 1) P := ihAll P
  have hQ : Q (α := α) (n - 1) P := hIH.1
  show NDS (α := α) n P.C ≤ 0

  set v : α := choose_good_v_for_Q (α := α) (n := n) P with hv

  have hv_ndeg : ndeg (α := α) P.C v ≤ 0 := by
    simpa [hv] using (choose_good_v_for_Q_spec (α := α) (n := n) (P := P))

  -- con-branch: apply IH to the chosen con-pack, then rewrite back to the con-family.
  let Pc : HypPack (α := α) := choose_con_pack (α := α) (P := P) (v := v)
  have hIHc : IH (α := α) (n - 1) Pc := ihAll Pc
  have hcon : NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0 := by
    have hPc : NDS (α := α) (n - 1) Pc.C ≤ 0 := hIHc.1
    -- NOTE: use the non-simp equality lemma to avoid `simp` rewriting `t=t` into `True`.
    have hPcC : Pc.C = con (α := α) v P.C := by
      simpa [Pc] using (choose_con_pack_C_eq (α := α) (P := P) (v := v))
    simpa [hPcC] using hPc

  have hdel :
      NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0 :=
    Del_bound_of_Q (α := α) (n := n) (hn := hn) (P := P) (v := v) hQ

  have hid :
      NDS (α := α) n P.C
        =
      NDS (α := α) (n - 1) (con (α := α) v P.C)
        +
      NDS (α := α) (n - 1) (Del (α := α) v P.C)
        +
      ndeg (α := α) P.C v :=
    CON_ID_pack (α := α) (n := n) (hn := hn) (P := P) (v := v)

  calc
    NDS (α := α) n P.C
        =
      NDS (α := α) (n - 1) (con (α := α) v P.C)
        +
      NDS (α := α) (n - 1) (Del (α := α) v P.C)
        +
      ndeg (α := α) P.C v := by
        simpa using hid
    _ ≤ 0 := by
      linarith [hcon, hdel, hv_ndeg]


/- ------------------------------------------------------------
  Qcorr_step（forbid 付き NDS_corr）
------------------------------------------------------------ -/

theorem Qcorr_step
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α)) (A : Finset α) :
  ForbidOK (α := α) P A →
  (∀ P' : HypPack α, IH (α := α) (n - 1) P') →
  Qcorr (α := α) n P A := by
  classical
  intro hOK ihAll
  have hIH : IH (α := α) (n - 1) P := ihAll P
  have hQ : Q (α := α) (n - 1) P := hIH.1
  show NDS_corr (α := α) n P.C A ≤ 0

  have hAcard2 : 2 ≤ A.card :=
    ForbidOK.card_two_le (α := α) (P := P) (A := A) hOK
  have hAne : A.Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by decide : (0:Nat) < 2) hAcard2)

  rcases hAne with ⟨v, hvA⟩

  have hEraseNonempty : (A.erase v).Nonempty :=
    ForbidOK.erase_nonempty (α := α) (P := P) (A := A) (v := v) hOK hvA

  -- con-branch: apply IH to the con-family directly (no pack needed).
  have hconCorr :
      NDS_corr (α := α) (n - 1)
        (con (α := α) v P.C)
        (A.erase v) ≤ 0 := by
    simpa using
      (corr_con_bound_of_IH_all (α := α) (n := n) (ihAll := ihAll)
        (P := P) (A := A) (v := v) hvA hEraseNonempty)

  have hdelHole :
      NDS (α := α) (n - 1)
        (Del (α := α) v (Hole (α := α) P.C A)) ≤ 0 :=
    Del_hole_bound (α := α) (n := n) (P := P) (A := A) (v := v) hOK hvA

  have hndegHole :
      ndeg (α := α) (Hole (α := α) P.C A) v ≤ 0 :=
    ndeg_hole_le_zero_of_choice (α := α) (n := n) (P := P) (A := A) (v := v) hOK hvA

  have hidCorr :
      NDS_corr (α := α) n P.C A
        =
      NDS_corr (α := α) (n - 1) (con (α := α) v P.C) (A.erase v)
        +
      (NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A))
          + ndeg (α := α) (Hole (α := α) P.C A) v) :=
    CON_ID_corr_pack (α := α) (n := n) (hn := hn) (P := P) (A := A) (v := v)

  calc
    NDS_corr (α := α) n P.C A
        =
      NDS_corr (α := α) (n - 1) (con (α := α) v P.C) (A.erase v)
        +
      (NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A))
          + ndeg (α := α) (Hole (α := α) P.C A) v) := by
        simpa using hidCorr
    _ ≤ 0 := by
      linarith [hconCorr, hdelHole, hndegHole]

end Step

end Dr1nds

-- NOTE:
-- S10 は「配線」専用ファイルなので、外部補助（LeanCopilot 等）への依存は避ける。
-- ここでの目的は S8/S9/S11 の API を呼び出して `linarith` で閉じることだけ。
