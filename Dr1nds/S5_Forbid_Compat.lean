-- Dr1nds/S5_Forbid_Compat.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S6_ConDelNdegId  -- CON_ID（通常会計）を参照する前提

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/- ============================================================
  S5 : forbid 互換（凍結 I/O・skeleton）

  目的：S10（Q_step / Qcorr_step）の配線が「式変形の詳細」に依存しないよう、
  forbid（Hole/Up）と contraction（con）の相互作用で必要になる“書き換え接口”だけを
  このファイルで凍結する。

  方針：
  * 基本定義は S0_CoreDefs（con / Del / Hole / Up / NDS / ndeg / NDS_corr）を正とする。
  * forbid は必ず同一の台 C 上で Hole(C,A) / Up(C,A) として扱う（再閉包しない）。
  * ここでは「証明の中身」ではなく、S10 が使う “唯一の形” を保証する補題 API を固定する。

  実装メモ：
  * 現状は axiom で凍結しているが、最終的には Finset.erase の基本補題と ext/フィルター計算で
    lemma 化して置き換える（下の各 axiom に TODO を付ける）。
  * 置き換え後も S10 側の import を壊さないため、名前と型は維持するのが基本。
============================================================ -/

namespace S5

/- ------------------------------------------------------------
  0. Basic membership helper
------------------------------------------------------------ -/

omit [DecidableEq α] in
/-- If v∈A and A ⊆ X then v∈X. -/
lemma mem_of_subset_of_mem {A X : Finset α} {v : α} (hvA : v ∈ A) (hAX : A ⊆ X) :
    v ∈ X := by
  exact hAX hvA

/- ------------------------------------------------------------
  1. Key rewriting kernels (axioms for now)
------------------------------------------------------------ -/

/--
【TODO（最重要・ここから崩す）】erase_subset_erase_iff の lemma 化

狙い：v∈A, v∈X の下で
  (A.erase v ⊆ X.erase v) ↔ (A ⊆ X)
を Finset の一般補題として証明する。

方針：
* → 方向：
    任意 a∈A を取り、a=v と a≠v で場合分け。
    - a=v は仮定 v∈X で処理。
    - a≠v は a∈A.erase v を得て、仮定から a∈X.erase v、よって a∈X。
* ← 方向：
    erase_subset_erase は標準補題として作れるので、A⊆X から自動で出る。

実装ヒント：
* `by classical` + `constructor` + `intro h` の形で書く。
* 既存補題：`Finset.mem_erase`, `Finset.mem_of_subset`, `Finset.erase_subset_erase`,
  `by_cases a = v`。

備考：この補題が通れば、con_Up_eq_Up_con / con_Hole_eq_Hole_con は ext だけで落ちやすい。
-/
axiom erase_subset_erase_iff
  (A X : Finset α) (v : α) :
  v ∈ A → v ∈ X →
  (A.erase v ⊆ X.erase v) ↔ (A ⊆ X)

/--
【TODO】con_Up_eq_Up_con の lemma 化（erase_subset_erase_iff に依存）

狙い：v∈A の下で
  con v (Up C A) = Up (con v C) (A.erase v)

方針：
* `Finset.ext` で集合等式に落とし、要素 `X` について
    X∈con v (Up C A) ↔ X∈Up (con v C) (A.erase v)
  を示す。
* 左辺の membership は「∃Y, Y∈Up C A ∧ Y.erase v = X」の形に展開される（con の定義）。
* `Up` 側は「A ⊆ Y」の条件を持つので、erase_subset_erase_iff で
    (A.erase v ⊆ Y.erase v) ↔ (A ⊆ Y)
  を繋げるのが核心。

実装ヒント：
* con の定義が `image (erase v)` なら、`Finset.mem_image` を使う。
* `Up` が filter なら、`Finset.mem_filter` を使う。
* injectivity が必要なら `Finset.erase_inj` ではなく、mem 前提付きの `injOn` を組む。
-/
axiom con_Up_eq_Up_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  con (α := α) v (Up (α := α) C A)
    =
  Up (α := α) (con (α := α) v C) (A.erase v)

/--
【TODO】con_Hole_eq_Hole_con の lemma 化（con_Up_eq_Up_con と同型）

狙い：v∈A の下で
  con v (Hole C A) = Hole (con v C) (A.erase v)

方針：
* `Hole C A = C \ Up C A`（定義がそうなっている前提）を展開し、
  con が差集合とどう絡むかを ext で押さえる。
* 実装上は「membership を直接展開」する方が安定：
    X∈Hole C A ↔ X∈C ∧ ¬(A ⊆ X)
  の形にしてから erase_subset_erase_iff を当てる。

注意：
* `simp` が効かない場合は `constructor` で二方向を手で書く。
-/
axiom con_Hole_eq_Hole_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  con (α := α) v (Hole (α := α) C A)
    =
  Hole (α := α) (con (α := α) v C) (A.erase v)

/--
【TODO】card_Up_eq_card_Up_con の lemma 化（実は con_Up_eq_Up_con から従う）

狙い：v∈A の下で
  |Up(C,A)| = |Up(con v C, A.erase v)|

方針：
* まず con_Up_eq_Up_con を lemma 化して、
    Up C A の con 像が右辺の Up と等しいことを得る。
* その上で「con が card を保存する条件（= erase が injOn）」を別補題として用意し、
  card の等式に落とす。

代替（より簡単）：
* 直接 `Finset.card_congr` で双射を作る：
    Y ↦ Y.erase v
  を Up C A 上で取り、逆写像は `insert v` などでは一般に戻れないので、
  右辺の候補集合が con 像であること（con_Up_eq_Up_con）を先に確立するのが安全。

実装では、この補題は“後回しでよい”：S10 の配線で必要なのは多くの場合
NDS_corr の定義展開で出る card(Up) の項を移送できることだけ。
-/
axiom card_Up_eq_card_Up_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  (Up (α := α) C A).card
    =
  (Up (α := α) (con (α := α) v C) (A.erase v)).card

/-
【置き換えロードマップ（推奨順）】
1. erase_subset_erase_iff を lemma 化（Finset 基本補題だけで閉じるはず）
2. con_Up_eq_Up_con / con_Hole_eq_Hole_con を ext + filter/image 展開で lemma 化
3. card_Up_eq_card_Up_con は (2) と con の card 保存（injOn）補題から導出

配置案：
* (1) はこのファイル内に残してよい（汎用だが依存が軽い）
* (2)(3) も S5 に置いてよいが、将来的に con/Hole/Up の一般補題群が肥大化するなら
  `S0_CoreDefs` 直下に移してもよい。

注意：S10 の import を壊さないため、公開名（lemma/axiom 名）と型は維持する。
-/

/- ------------------------------------------------------------
  2. The corrected accounting identity (CON_ID_corr) : frozen shape
------------------------------------------------------------ -/

/--
(CON_ID_corr: frozen shape)

Let D := Hole(C,A). Apply CON_ID to D and rewrite the con-part and the correction term
using the kernels above, to obtain the standard Q-step interface:

  NDS_corr_n(C;A)
    = NDS_corr_{n-1}(con_v(C); A.erase v)
      + ( NDS_{n-1}(Del_v(Hole(C,A))) + ndeg_{Hole(C,A)}(v) )

This is exactly what S10/Q-step wants.
-/
theorem CON_ID_corr
  (n : Nat) (hn : 1 ≤ n)
  (C : Finset (Finset α)) (A : Finset α)
  (v : α) (hvA : v ∈ A) :
  NDS_corr (α := α) n C A
    =
  NDS_corr (α := α) (n - 1) (con (α := α) v C) (A.erase v)
    +
  (NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) C A))
      + ndeg (α := α) (Hole (α := α) C A) v) := by
  classical
  -- set D := Hole C A
  set D : Finset (Finset α) := Hole (α := α) C A

  -- Start from the definition of NDS_corr
  unfold NDS_corr

  -- Apply the usual accounting identity CON_ID to D
  have hCON :
      NDS (α := α) n D
        =
      NDS (α := α) (n - 1) (con (α := α) v D)
        +
      NDS (α := α) (n - 1) (Del (α := α) v D)
        +
      ndeg (α := α) D v := by
    simpa [D] using (Accounting.CON_ID (α := α) (n := n) (hn := hn) (C := D) (u := v))

  -- Rewrite the NDS-part using CON_ID
  rw [hCON]

  -- 以降の実質的な変形は「凍結した書き換え核（axiom）」に完全に委譲する。
  -- S10/S11 ではこの中身を触らない設計（wiring の安定化）。

  -- Rewrite con(Hole C A) to Hole(con C)(A.erase v)
  have hcon : con (α := α) v D = Hole (α := α) (con (α := α) v C) (A.erase v) := by
    -- from the frozen kernel
    simpa [D] using (con_Hole_eq_Hole_con (α := α) (C := C) (A := A) (v := v) hvA)

  -- Rewrite the correction term card(Up C A)
  have hcard : (Up (α := α) C A).card = (Up (α := α) (con (α := α) v C) (A.erase v)).card := by
    simpa using (card_Up_eq_card_Up_con (α := α) (C := C) (A := A) (v := v) hvA)

  -- Replace con v D and card(Up C A)
  rw [hcon]
  -- now the first term matches the Hole-part of NDS_corr (n-1) (con v C) (A.erase v)
  -- and we rewrite the correction card using hcard
  -- (note: Del-part and ndeg-part already match the target shape after unfolding D)
  simp [D, hcard, add_left_comm, add_comm]

/--
Optional convenience: assoc/comm reshaping, if you prefer
  NDS_corr n C A =
    NDS_corr (n-1) (con v C) (A.erase v)
    + NDS (n-1) (Del v (Hole C A))
    + ndeg (Hole C A) v
-/
theorem CON_ID_corr_assoc
  (n : Nat) (hn : 1 ≤ n)
  (C : Finset (Finset α)) (A : Finset α)
  (v : α) (hvA : v ∈ A) :
  NDS_corr (α := α) n C A
    =
  NDS_corr (α := α) (n - 1) (con (α := α) v C) (A.erase v)
    +
  NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) C A))
    +
  ndeg (α := α) (Hole (α := α) C A) v := by
  classical
  -- Once CON_ID_corr is available, this is just reassociation.
  simpa [add_assoc] using (CON_ID_corr (α := α) (n := n) (hn := hn) (C := C) (A := A) (v := v) hvA)

end S5

end Dr1nds
