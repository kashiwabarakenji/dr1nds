-- Dr1nds/S10_Steps.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs
import Dr1nds.S8_Statements          -- Q / Qcorr / ForbidOK / HypPack / CON_ID_pack / CON_ID_corr_pack
import Dr1nds.S11_LocalKernels        -- v選択・局所評価 API

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/- ============================================================
  S10 : Step lemmas (SKELETON)
  目的：
    - Q と Qcorr のステップを「配線」だけ確定する
    - 局所核は S11_LocalKernels の axiom 群に“丸投げ”する
============================================================ -/

namespace Step

/-
  注意：
  ここでの「Q」の正確な意味は S8_Statements に依存します。
  想定は「HypPack を引数に取り、NDS≤0 を主張する命題」。
  このファイルは “ステップで何を呼ぶか” を固定するのが目的で、
  実際の inequality の詰めは後回し（全部 sorry）。
-/

/- ------------------------------------------------------------
  Q_step（通常 NDS）
------------------------------------------------------------ -/

/--
Q_step（通常版）：
  n≥1 として、v を局所核で選び、
  CON_ID で NDS_n を (con, Del, ndeg) に分解し、
  IH（con側）+ Del側 bound + ndeg≤0 で閉じる。

※ここで “IH をどう渡すか” は S11.IH_Q_gives_con_bound に吸収している。
-/
theorem Q_step
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α)) :
  Q (α := α) (n - 1) P →
  Q (α := α) n P := by
  classical
  intro hIH
  show NDS (α := α) n P.C ≤ 0

  -- 1) v を選ぶ（局所核：ndeg_C(v) ≤ 0）
  -- `exists_goodV_for_Q : ∃ gv, True` から `gv` を取り出す（rcases/obtain を避ける）
  let gv : Local.GoodV_for_Q (α := α) n P :=
     Local.choose_goodV_for_Q (α := α) (n := n) P
  let v : α := gv.v
  have hv_ndeg : ndeg (α := α) P.C v ≤ 0 := gv.hndeg

  -- 2) con 側：IH から NDS(n-1)(con v C) ≤ 0 を得る
  have hcon :
      NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0 :=
    Local.IH_Q_gives_con_bound (α := α) (n := n) (P := P) (v := v) hIH

  -- 3) Del 側：局所核で NDS(n-1)(Del v C) ≤ 0 を得る
  have hdel :
      NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0 :=
    Local.Del_bound (α := α) (n := n) (P := P) (v := v)

  -- 4) 会計恒等式 CON_ID を入れる
  have hid :
      NDS (α := α) n P.C
        =
      NDS (α := α) (n - 1) (con (α := α) v P.C)
        +
      NDS (α := α) (n - 1) (Del (α := α) v P.C)
        +
      ndeg (α := α) P.C v :=
    CON_ID_pack (α := α) (n := n) (hn := hn) (P := P) (v := v)

  -- 5) 線形合成（Int なので `linarith` がそのまま通る）
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
      -- hcon, hdel, hv_ndeg をまとめて叩く
      linarith


/- ------------------------------------------------------------
  Qcorr_step（forbid 付き NDS_corr）
------------------------------------------------------------ -/

/--
Qcorr_step（forbid 版）：
  ForbidOK P A の下で v∈A を選び、
  Case 分岐：A.erase v = ∅ / Nonempty
  - Nonempty のときは IH_corr_con_pack（S9）で con 側の NDS_corr を閉じる
  - 常に Del(hole) 側 bound と ndeg(hole)≤0 を局所核から取る
  - CON_ID_corr（forbid 会計恒等式）で結合して ≤0

※ここでも「どこで何を呼ぶか」だけを固定し、証明は全部 sorry。
-/
theorem Qcorr_step
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α)) (A : Finset α) :
  ForbidOK (α := α) P A →
  Q (α := α) (n - 1) P →
  Qcorr (α := α) n P A := by
  classical
  intro hOK hIH
  show NDS_corr (α := α) n P.C A ≤ 0

  -- 1) v∈A を選ぶ
  -- `obtain/rcases` を避けて `Classical.choose` で取り出す
  let v : α := Classical.choose (Local.choose_v_in_A (α := α) (P := P) (A := A) hOK)
  have hvA : v ∈ A := Classical.choose_spec (Local.choose_v_in_A (α := α) (P := P) (A := A) hOK)

  -- 2) Case: A.erase v = ∅ or Nonempty
  have hcase := Local.erase_empty_or_nonempty (α := α) (A := A) (v := v) hvA
  cases hcase with
  | inl hEraseEmpty =>
      -- Case2A: A.erase v = ∅ （実質 singleton case）
      -- このケースは局所核（S11）に一撃で丸投げする。
      exact Local.Qcorr_case1_singleton
        (α := α) (n := n) (P := P) (A := A) (v := v)
        hOK hvA hEraseEmpty

  | inr hEraseNonempty =>
      -- Case2B: (A.erase v).Nonempty（B2 case）
      -- 3) con 側：S9 の IH_corr_con_pack を適用する
      have hconCorr :
          NDS_corr (α := α) (n - 1)
            (con (α := α) v P.C)
            (A.erase v) ≤ 0 :=
        IH_corr_con_pack (α := α) (n := n) (P := P) (A := A) (v := v) hIH hvA hEraseNonempty

      -- 4) Del(hole) 側 bound
      have hdelHole :
          NDS (α := α) (n - 1)
            (Del (α := α) v (Hole (α := α) P.C A)) ≤ 0 :=
        Local.Del_hole_bound (α := α) (n := n) (P := P) (A := A) (v := v) hOK hvA

      -- 5) ndeg(hole) ≤ 0
      have hndegHole :
          ndeg (α := α) (Hole (α := α) P.C A) v ≤ 0 :=
        Local.ndeg_hole_le_zero_of_choice (α := α) (n := n) (P := P) (A := A) (v := v) hOK hvA

      -- 6) forbid 会計恒等式 CON_ID_corr を入れて結合
      --    ※この定理名・形は S5_Forbid_Compat に合わせる（ここは skeleton）
      have hidCorr :
          NDS_corr (α := α) n P.C A
            =
          NDS_corr (α := α) (n - 1) (con (α := α) v P.C) (A.erase v)
            +
          (NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A))
              + ndeg (α := α) (Hole (α := α) P.C A) v) := by
        -- forbid 会計恒等式（pack 版）
        exact CON_ID_corr_pack (α := α) (n := n) (hn := hn) (P := P) (A := A) (v := v)

      -- 7) hidCorr と (hconCorr, hdelHole, hndegHole) から ≤0
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
