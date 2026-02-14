-- Dr1nds/S5_Forbid_Compat.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanCopilot

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
lemma erase_subset_erase_iff
  (A X : Finset α) (v : α) :
  v ∈ A → v ∈ X →
  ((A.erase v ⊆ X.erase v) ↔ (A ⊆ X)) := by
  classical
  intro hvA hvX
  constructor
  · intro h a haA
    by_cases hav : a = v
    · subst hav
      simp_all only
    ·
      have haAerase : a ∈ A.erase v := by
        exact Finset.mem_erase.mpr ⟨hav, haA⟩
      have haXerase : a ∈ X.erase v := by
        apply h
        rw [Finset.mem_erase] at haAerase
        simp_all only [not_false_eq_true, ne_eq, Finset.mem_erase, and_self]

      exact (Finset.mem_erase.mp haXerase).2
  · intro h
    -- monotonicity of erase
    intro a haAerase
    have haA : a ∈ A := (Finset.mem_erase.mp haAerase).2
    have haX : a ∈ X := h haA
    have hav : a ≠ v := (Finset.mem_erase.mp haAerase).1
    exact Finset.mem_erase.mpr ⟨hav, haX⟩

lemma con_Up_eq_Up_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  con (α := α) v (Up (α := α) C A)
    =
  Up (α := α) (con (α := α) v C) (A.erase v) := by
  classical
  intro hvA
  ext X
  constructor
  · intro hX
    -- unpack membership in `con`
    rcases Finset.mem_image.mp hX with ⟨Y, hY, rfl⟩
    rcases Finset.mem_filter.mp hY with ⟨hYUp, hvY⟩
    rcases Finset.mem_filter.mp hYUp with ⟨hYC, hAY⟩
    -- show membership in RHS filter
    refine Finset.mem_filter.mpr ?_
    refine And.intro ?hXcon ?hAerase
    · -- X ∈ con v C
      refine Finset.mem_image.mpr ?_
      refine ⟨Y, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hYC, hvY⟩
    · -- (A.erase v) ⊆ (Y.erase v)
      have hvY' : v ∈ Y := hvY
      have hiff := (erase_subset_erase_iff (α := α) (A := A) (X := Y) (v := v)) hvA hvY'
      exact (hiff.2 hAY)
  · intro hX
    rcases Finset.mem_filter.mp hX with ⟨hXcon, hAerase⟩
    -- unpack membership in con v C
    rcases Finset.mem_image.mp hXcon with ⟨Y, hY, hYX⟩
    rcases Finset.mem_filter.mp hY with ⟨hYC, hvY⟩
    -- want: Y ∈ Up C A and v ∈ Y, and X = Y.erase v
    -- rewrite goal using hYX
    subst hYX
    refine Finset.mem_image.mpr ?_
    refine ⟨Y, ?_, rfl⟩
    -- show Y ∈ (Up C A).filter (v∈_)
    refine Finset.mem_filter.mpr ?_
    refine And.intro ?hYUp hvY
    refine Finset.mem_filter.mpr ?_
    refine And.intro hYC ?hAY
    have hvY' : v ∈ Y := hvY
    have hiff := (erase_subset_erase_iff (α := α) (A := A) (X := Y) (v := v)) hvA hvY'
    exact (hiff.1 hAerase)

lemma con_Hole_eq_Hole_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  con (α := α) v (Hole (α := α) C A)
    =
  Hole (α := α) (con (α := α) v C) (A.erase v) := by
  classical
  intro hvA
  ext X
  constructor
  · intro hX
    rcases Finset.mem_image.mp hX with ⟨Y, hY, rfl⟩
    rcases Finset.mem_filter.mp hY with ⟨hYHole, hvY⟩
    rcases Finset.mem_filter.mp hYHole with ⟨hYC, hNotAY⟩
    -- RHS: X ∈ con v C and ¬(A.erase v ⊆ X)
    refine Finset.mem_filter.mpr ?_
    refine And.intro ?hXcon ?hNot
    · refine Finset.mem_image.mpr ?_
      refine ⟨Y, Finset.mem_filter.mpr ⟨hYC, hvY⟩, rfl⟩
    · -- if A.erase v ⊆ Y.erase v then A ⊆ Y (since v∈A and v∈Y) contradicting hNotAY
      intro hSub
      have hiff := (erase_subset_erase_iff (α := α) (A := A) (X := Y) (v := v)) hvA hvY
      have hAY : A ⊆ Y := (hiff.1 hSub)
      exact hNotAY hAY
  · intro hX
    rcases Finset.mem_filter.mp hX with ⟨hXcon, hNot⟩
    rcases Finset.mem_image.mp hXcon with ⟨Y, hY, hYX⟩
    rcases Finset.mem_filter.mp hY with ⟨hYC, hvY⟩
    subst hYX
    -- show membership in LHS: Y ∈ Hole C A and v∈Y
    refine Finset.mem_image.mpr ?_
    refine ⟨Y, ?_, rfl⟩
    refine Finset.mem_filter.mpr ?_
    refine And.intro ?hYHole hvY
    refine Finset.mem_filter.mpr ?_
    refine And.intro hYC ?hNotAY
    -- ¬(A ⊆ Y): otherwise A.erase v ⊆ Y.erase v and contradict hNot
    intro hAY
    have hiff := (erase_subset_erase_iff (α := α) (A := A) (X := Y) (v := v)) hvA hvY
    have : A.erase v ⊆ Y.erase v := (hiff.2 hAY)
    exact hNot this

lemma card_Up_eq_card_Up_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  (Up (α := α) C A).card
    =
  (Up (α := α) (con (α := α) v C) (A.erase v)).card := by
  classical
  intro hvA

  -- Every X in Up C A contains v.
  have hv_mem_up : ∀ {X : Finset α}, X ∈ Up (α := α) C A → v ∈ X := by
    intro X hX
    have hAX : A ⊆ X := (Finset.mem_filter.mp hX).2
    exact hAX hvA

  -- On Up C A, the filter (v ∈ ·) is redundant.
  have hfilter : (Up (α := α) C A).filter (fun X => v ∈ X) = Up (α := α) C A := by
    ext X
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).1
    · intro h
      exact Finset.mem_filter.mpr ⟨h, hv_mem_up (X := X) h⟩

  -- Rewrite con v (Up C A) as an image by erase.
  have hcon_as_image :
      con (α := α) v (Up (α := α) C A)
        = (Up (α := α) C A).image (fun X => X.erase v) := by
    simp [con, hfilter]

  -- `erase v` is injective on the carrier `Up C A` (because every member contains v).
  have hinjOn : Set.InjOn (fun X : Finset α => X.erase v)
      (↑(Up (α := α) C A) : Set (Finset α)) := by
    intro X hX Y hY hEq
    have hvX : v ∈ X := hv_mem_up (X := X) (by simpa using hX)
    have hvY : v ∈ Y := hv_mem_up (X := Y) (by simpa using hY)
    -- Insert v back to recover the original set.
    have : insert v (X.erase v) = insert v (Y.erase v) := by
      simpa [hEq]
    simpa [Finset.insert_erase hvX, Finset.insert_erase hvY] using this

  -- Therefore the image has the same cardinality.
  have hcard_image :
      (con (α := α) v (Up (α := α) C A)).card = (Up (α := α) C A).card := by
    -- card(image f s) = card s iff f is injective on s
    have hci : ((Up (α := α) C A).image (fun X => X.erase v)).card = (Up (α := α) C A).card :=
      (Finset.card_image_iff).2 hinjOn
    -- rewrite con to image
    simpa [hcon_as_image] using hci

  -- Now rewrite con(Up C A) using the set equality con_Up_eq_Up_con.
  have hEq : con (α := α) v (Up (α := α) C A)
      = Up (α := α) (con (α := α) v C) (A.erase v) :=
    con_Up_eq_Up_con (α := α) (C := C) (A := A) (v := v) hvA

  -- Combine.
  -- hcard_image : card(con v (Up C A)) = card(Up C A)
  -- so card(Up C A) = card(Up (con v C) (A.erase v))
  have : (Up (α := α) C A).card = (Up (α := α) (con (α := α) v C) (A.erase v)).card := by
    -- flip hcard_image and rewrite by hEq
    have : (Up (α := α) C A).card = (con (α := α) v (Up (α := α) C A)).card := by
      exact Eq.symm hcard_image
    simpa [hEq] using this
  exact this

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
