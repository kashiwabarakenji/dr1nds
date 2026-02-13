-- Dr1nds/S10_Steps.lean
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

import Dr1nds.S0_CoreDefs
import Dr1nds.S9_IH_Unpack
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

-- ============================================================
-- 【メンテ用メモ】コメント運用と命名
--
-- * Lean のブロックコメントは `/- ... -/` なので、コメント本文中に `/-` や `-/` を
--   そのまま書くと、意図せずコメントの開始/終了として解釈されてパースが壊れる。
--   ここでは安全のため、長文説明は基本的に `--` の行コメントで書く。
--
-- * S10 は wiring 専用。S11 の API 名（choose_* / *_bound など）に合わせる。
--   S10 側で名前を別に作らない（後で二重定義・unknown identifier の温床になる）。
-- ============================================================

/-
【S10 の立場（wiring 専用）— 将来の作業方針メモ】

S10 は「帰納法の1ステップを閉じるための *配線だけ*」を担う。
ここでは
  * 会計等式（S8）を `rw` / `linarith` で組み立てる
  * 必要な局所評価・representability（con/Del/Hole 側の pack 供給など）は S11 に丸投げ
という役割分離を崩さない。

重要：同名の補題/axiom が `S8_Statements.lean` 側に残っていても、
以後「ステップとして参照するのは常に `Step.Q_step` / `Step.Qcorr_step`」に統一する。
（S8 側は“仕様”の置き場、S10 側は“使う側”の置き場、という整理。）

このファイルは Lean の実装が進むにつれて、
  - S11 の axiom が theorem に置き換わっても、S10 は import と呼び出しだけで済む
  - 逆に、S10 にローカルな場合分けや構成（good v の取り方等）を書き始めると破綻する
ので、S10 には「証明中身」を増やさない。
-/

/-
【S10 で“置く”補助補題の方針】

S10 は wiring 専用だが、次の2種類だけは S10 に置いてよい：

(1) *型・引数形の整形*（後で S11 の核へ渡すための前処理）
    例：`ForbidOK` から `A.erase v` の `Nonempty` を引く、`erase` の subset を整理する等。

(2) *文書仕様の“分岐削除”のための局所補題*（proof は短く、S11 を汚さない）
    例：`2 ≤ A.card` かつ `v∈A` なら `(A.erase v).Nonempty`。

それ以外（good v の構成、Del-as-Hole、representability の本体など）は S11 に置く。
-/

/-- `2 ≤ A.card` かつ `v∈A` なら `A.erase v` は空でない。

`Qcorr_step` の互換的な case split（`erase_empty_or_nonempty`）を将来削除するための
局所補題。`ForbidOK` を `2 ≤ card` に固定した設計では、この補題により
`A.erase v = ∅` の分岐は“理論上起きない”ことを Lean 側でも明示できる。
-/
lemma erase_nonempty_of_two_le_card
  (A : Finset α) (v : α) (hv : v ∈ A) (h2 : 2 ≤ A.card) :
  (A.erase v).Nonempty := by
  classical
  -- `card_erase_of_mem` と `Nat.sub_pos_of_lt` を使って `card (erase v) > 0` を示す
  have hcard : (A.erase v).card = A.card - 1 := by
    simpa using (Finset.card_erase_of_mem hv)
  have hpos : 0 < (A.erase v).card := by
    -- `2 ≤ A.card` から `1 < A.card`
    have hlt : 1 < A.card := Nat.lt_of_lt_of_le (by decide : (1:Nat) < 2) h2
    -- `0 < A.card - 1`
    have : 0 < A.card - 1 := Nat.sub_pos_of_lt hlt
    simpa [hcard] using this
  -- `card_pos` から Nonempty
  exact Finset.card_pos.mp hpos

/-- `A ⊆ U` かつ `v∈A` なら `A.erase v ⊆ U.erase v`。

`Qcorr_step` の con-branch で `ForbidOK(Pc, A.erase v)` の `subset` 成分を作るときに便利。
（ただし Pc.U が `P.U.erase v` であることは representability 核として S11 側で供給する。）
-/
lemma erase_subset_erase
  (A U : Finset α) (v : α) (hAU : A ⊆ U) :
  A.erase v ⊆ U.erase v := by
  intro x hx
  have hxA : x ∈ A := by
    -- `erase_subset` を使って A への membership を戻す
    exact Finset.mem_of_mem_erase hx
  have hxU : x ∈ U := hAU hxA
  -- `x=v` の場合は erase で落ちるので矛盾、`x≠v` なら両方の erase に入る
  have hxne : x ≠ v := (Finset.mem_erase.mp hx).1
  exact Finset.mem_erase.mpr ⟨hxne, hxU⟩

/-- `ForbidOK` から `A ⊆ P.H.U` を取り出すだけの補助補題。
S10 の証明中で `hOK.1` などのフィールド参照が散らばるのを避ける目的。-/
lemma ForbidOK.subset_U {P : HypPack (α := α)} {A : Finset α}
  (hOK : ForbidOK (α := α) P A) : A ⊆ P.H.U :=
by
  exact hOK.1

/-- `ForbidOK` から `2 ≤ A.card` を取り出すだけの補助補題。-/
lemma ForbidOK.card_two_le {P : HypPack (α := α)} {A : Finset α}
  (hOK : ForbidOK (α := α) P A) : 2 ≤ A.card :=
by
  exact hOK.2

/-- `ForbidOK` と `v∈A` から `A.erase v` の `Nonempty` を得る補助補題。
`Qcorr_step` の singleton 分岐を将来削除する時の “置き換え先” を固定する。-/
lemma ForbidOK.erase_nonempty {P : HypPack (α := α)} {A : Finset α} {v : α}
  (hOK : ForbidOK (α := α) P A) (hv : v ∈ A) : (A.erase v).Nonempty :=
by
  exact erase_nonempty_of_two_le_card (A := A) (v := v) hv hOK.2

/- ------------------------------------------------------------
  Q_step（通常 NDS）
------------------------------------------------------------ -/

/--
【S10 から見た Del-bound】

`Q_step` の最終行（`linarith`）に必要な Del 側上界。
本来は S11 の局所核（representability＋IH 適用＋書き戻し）で証明されるべきだが、
S10 は wiring 専用なので **ここでは axiom のまま保持**する。

将来の置き換え方針：
  - S11 で `Del_bound` を theorem として証明（方針C：Del-as-Hole + Qcorr から取り出す）
  - S10 側はこの axiom を削除し、`Local.Del_bound`（あるいは `Local.del_bound`）の theorem を呼ぶ

-- 置き換えの目標（S11 に theorem が来たら）：
--   `Step.Del_bound` を削除して
--   `have hdel := Local.Del_bound (n := n) (P := P) (v := v)`
--   の形に差し替える。
-- （S10 は import と呼び出し先の変更だけで済ませるのが目的。）
-/
theorem Q_step
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α)) :
  Q (α := α) (n - 1) P →
  Q (α := α) n P := by
  classical
  intro hIH
  -- 以降は完全に「等式（S8）＋3つの局所 bound（S11）→ linarith」という配線のみ。
  -- good v の選択・con-pack の供給・con 側 IH 適用は S11 の API に委譲する。
  show NDS (α := α) n P.C ≤ 0

  -- good v（通常ステップ用）：`GoodV_for_Q P` は `α → Prop`（=「この v は通常ステップで良い」）として扱う。
  -- S11 は「良い v の存在」を保証しており、ここでは選択した v を使うだけ（構成は S11 に丸投げ）。
  classical
  set v : α := choose_good_v_for_Q (α := α) (P := P) (n := n) with hv
  have hv_good : GoodV_for_Q (α := α) P v := by
    -- `choose_goodV_for_Q` の選択仕様（S11 側で提供される）
    let cg := choose_good_v_for_Q_spec (α := α) (P := P) (n := n)
    simp [hv]
    simp_all only [v]
    exact cg

  -- `GoodV_for_Q` の中身は「ndeg ≤ 0」を含む（あるいはそれと同値）。
  -- ここは定義展開で落ちる形にしておく（設計変更があれば S11 側の spec を合わせる）。
  have hv_ndeg : ndeg (α := α) P.C v ≤ 0 := by
    simpa [GoodV_for_Q] using hv_good

  -- con 側の bound は IH から直接引ける（unpack 済み補題を使う）。
  have hcon : NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0 := by
    exact IH_Q_gives_con_bound (α := α) (n := n) (P := P) (v := v) hIH

  have hdel :
      NDS (n - 1) (Del v P.C) ≤ 0 :=
    Del_bound_of_Q n hn P v hIH

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
  Q (α := α) (n - 1) P →
  Qcorr (α := α) n P A := by
  classical
  intro hOK hIH
  -- 注意：最新方針では `ForbidOK(P,A)` は `2 ≤ A.card` を含み、singleton forbid は射程外。
  -- よって `v∈A` を取った時点で `(A.erase v).Nonempty` が従い、
  -- `A.erase v = ∅` の分岐は「理論上起きない」。
  -- ただし現行コードでは互換性のため `erase_empty_or_nonempty` で分岐を残している。
  -- 将来的には `erase_nonempty_of_two_le_card`（＋`ForbidOK` から `2 ≤ card` を取り出す補題）
  -- を用いて分岐を削除する。
  show NDS_corr (α := α) n P.C A ≤ 0

  -- `ForbidOK` から `2 ≤ A.card` を取り出し、`A` が空でないことを得る。
  have hAcard2 : 2 ≤ A.card := ForbidOK.card_two_le (α := α) (P := P) (A := A) hOK
  have hAne : A.Nonempty := by
    -- `2 ≤ card` なら `0 < card` なので Nonempty
    exact Finset.card_pos.mp (lt_of_lt_of_le (by decide : (0:Nat) < 2) hAcard2)

  -- forbid 集合 A から 1 点 v を取る（choice）。
  rcases hAne with ⟨v, hvA⟩

  -- `ForbidOK` では singleton は射程外なので、`erase` は必ず nonempty。
  have hEraseNonempty : (A.erase v).Nonempty :=
    ForbidOK.erase_nonempty (α := α) (P := P) (A := A) (v := v) hOK hvA

  have hconCorr :
      NDS_corr (α := α) (n - 1)
        (con (α := α) v P.C)
        (A.erase v) ≤ 0 := by
    -- con-branch の forbid-bound は「Q (n-1) P」から直接引ける（S9_IH_Unpack 側）
    simpa using
      (Qcorr_con_case2 (α := α) (n := n) (P := P) (A := A) (v := v)
        hIH hvA hEraseNonempty)

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

/-
【TODO（S10 側で今後“増やさない”もの／増やすなら skeleton のみ）】

S10 で今後やることは「中身を書く」ではなく、S11 の theorem 化に合わせて
  * 呼び出し先（axiom → theorem）を差し替える
  * 不要になった互換分岐（singleton case）を削除する
程度に留める。

S10 に追加してよいのは、
  * S11 の局所核へ渡すための “引数形の凍結”
  * `have` で作れる自明補題（`A.erase v ⊆ P.U.erase v` など）
だけ。

逆に、次のような内容は S10 に書かない：
  * good v の構成（SC/NoParallel/trace などの本体）
  * Del-as-Hole / con-as-pack の representability の証明
  * forbid 付き会計の中身（CON_ID_corr_pack の導出）

それらは S11（局所核）または S8（等式仕様）に置く。
-/

end Step

end Dr1nds
