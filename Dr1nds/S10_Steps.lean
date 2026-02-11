-- Dr1nds/S10_Steps.lean
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

import Dr1nds.S0_CoreDefs
import Dr1nds.S8_Statements          -- Q / Qcorr / ForbidOK / HypPack / CON_ID_pack / CON_ID_corr_pack
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

/- ------------------------------------------------------------
  Q_step（通常 NDS）
------------------------------------------------------------ -/

theorem Q_step
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α)) :
  Q (α := α) (n - 1) P →
  Q (α := α) n P := by
  classical
  intro hIH
  show NDS (α := α) n P.C ≤ 0

  let gv : Local.GoodV_for_Q (α := α) n P :=
    Local.choose_goodV_for_Q (α := α) (n := n) P
  let v : α := gv.v
  have hv_ndeg : ndeg (α := α) P.C v ≤ 0 := gv.hndeg

  have hcon :
      NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0 :=
    Local.IH_Q_gives_con_bound (α := α) (n := n) (P := P) (v := v) hIH

  have hdel :
      NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0 :=
    Local.Del_bound (α := α) (n := n) (P := P) (v := v)

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
      linarith


/- ------------------------------------------------------------
  Qcorr_step（forbid 付き NDS_corr）
------------------------------------------------------------ -/

theorem Qcorr_step
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α)) (A : Finset α) :
  ForbidOK (α := α) P A →
  Q (α := α) (n - 1) P →
  Qcorr (α := α) n P A := by
  classical
  intro hOK hIH
  show NDS_corr (α := α) n P.C A ≤ 0

  have hvExists : ∃ v : α, v ∈ A :=
    Local.choose_v_in_A (α := α) (P := P) (A := A) hOK
  let v : α := Classical.choose hvExists
  have hvA : v ∈ A := Classical.choose_spec hvExists

  have hcase := Local.erase_empty_or_nonempty (α := α) (A := A) (v := v) hvA
  cases hcase with
  | inl hEraseEmpty =>
      exact Local.Qcorr_case1_singleton (α := α) (n := n) (P := P) (A := A) (v := v) hOK hvA hEraseEmpty

  | inr hEraseNonempty =>
      have hconCorr :
          NDS_corr (α := α) (n - 1)
            (con (α := α) v P.C)
            (A.erase v) ≤ 0 :=
        IH_corr_con_pack (α := α) (n := n) (P := P) (A := A) (v := v) hIH hvA hEraseNonempty

      have hdelHole :
          NDS (α := α) (n - 1)
            (Del (α := α) v (Hole (α := α) P.C A)) ≤ 0 :=
        Local.Del_hole_bound (α := α) (n := n) (P := P) (A := A) (v := v) hOK hvA

      have hndegHole :
          ndeg (α := α) (Hole (α := α) P.C A) v ≤ 0 :=
        Local.ndeg_hole_le_zero_of_choice (α := α) (n := n) (P := P) (A := A) (v := v) hOK hvA

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
          linarith

end Step

end Dr1nds
