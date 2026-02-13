-- Dr1nds/S6_ConDelNdegId.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S0_CoreDefs

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/- ============================================================
  S6 : Core accounting identity (CON_ID)  [SKELETON / FROZEN I/O]
  Policy:
    * base defs: S0_CoreDefs
    * this file fixes the I/O of the accounting identity
    * proofs can be filled later (axiom / lemma skeleton)
============================================================ -/

namespace Accounting

/-
  【証明戦略（日本語）】
  1) C に関する和を u∈X と u∉X のフィルターに分解する。
     → 本ファイルの lemma sum_filter_mem_add_sum_filter_not_mem を使用。
  2) w の項を u∈X と u∉X でそれぞれ w_of_mem_erase, w_of_not_mem を使って書き換える。
  3) u∈X のフィルター上の和を erase u の像（con u C）上の和に書き換える。
     → lemma sum_filter_mem_eq_sum_image_con と erase_inj_on_mem の injectivity を利用。
  4) +1/ -1 のカウントを ndeg にまとめる。
     → card_eq_deg_add_card_Del と ndeg_eq_deg_sub_card_Del を利用。
  5) 唯一の非自明な組合せ論的ポイントは erase の injectivity（lemma erase_injOn）。

-/


/- ============================================================
  0. Tiny accounting lemmas about w

  【注意】
  本ファイルは CON_ID の **入出力仕様（I/O）を固定化（frozen）したもの**です。
  現在の `sorry` は意図的なプレースホルダーであり、証明は未完成です。
  下流のファイルは証明ではなく定理の「命題文」のみを依存すべきです。
============================================================ -/

/-- succ shift: w (n+1) X = w n X - 1 -/
lemma w_succ (n : Nat) (X : Finset α) :
    w (α := α) n.succ X = w (α := α) n X - 1 := by
  /-
  【用途】
  w の定義上の基本的な性質。CON_ID のステップ2の w の書き換えに利用。
  【証明方針】
  定義展開後の単純な算術操作（Natの引き算など）。
  【場所】
  ここで証明してもよいし、基本ファイルに移してもよい。
  -/
  sorry

/--
If u∈X and n≥1, then
  w n X = w (n-1) (X.erase u) + 1
This is the “membership part” used in CON_ID.
-/
lemma w_of_mem_erase
  (n : Nat) (hn : 1 ≤ n) (u : α) (X : Finset α) (hu : u ∈ X) :
  w (α := α) n X = w (α := α) (n - 1) (X.erase u) + 1 := by
  /-
  【用途】
  CON_ID のステップ2で u∈X の場合の w の書き換えに使う。
  【証明方針】
  w の定義からの単純な場合分けと算術操作。
  【場所】
  ここで証明してもよいし、基本ファイルに移してもよい。
  -/
  sorry

/--
If u∉X and n≥1, then
  w n X = w (n-1) X - 1
This is the “non-membership part” used in CON_ID.
-/
lemma w_of_not_mem
  (n : Nat) (hn : 1 ≤ n) (u : α) (X : Finset α) (hu : u ∉ X) :
  w (α := α) n X = w (α := α) (n - 1) X - 1 := by
  /-
  【用途】
  CON_ID のステップ2で u∉X の場合の w の書き換えに使う。
  【証明方針】
  w の定義からの単純な場合分けと算術操作。
  【場所】
  ここで証明してもよいし、基本ファイルに移してもよい。
  -/
  sorry


/- ============================================================
  1. Partition lemmas (filter split)
============================================================ -/

/-- The two filters (u∈X) and (u∉X) are disjoint. -/
lemma disjoint_filter_mem_not_mem
  (C : Finset (Finset α)) (u : α) :
  Disjoint (C.filter (fun X => u ∈ X)) (C.filter (fun X => u ∉ X)) := by
  classical
  /-
  【用途】
  CON_ID のステップ1でフィルターの和集合分解の離散性を使う。
  【証明方針】
  フィルターの定義からの集合論的証明。
  【場所】
  ここで証明してよい。
  -/
  sorry

/-- Union of the two filters gives back C. -/
lemma union_filter_mem_not_mem
  (C : Finset (Finset α)) (u : α) :
  (C.filter (fun X => u ∈ X)) ∪ (C.filter (fun X => u ∉ X)) = C := by
  classical
  /-
  【用途】
  CON_ID のステップ1でフィルターの和集合分解を使う。
  【証明方針】
  フィルターの定義からの集合論的証明。
  【場所】
  ここで証明してよい。
  -/
  sorry

/-- Card partition: |C| = |{u∈X}| + |{u∉X}|. -/
lemma card_filter_mem_add_card_filter_not_mem
  (C : Finset (Finset α)) (u : α) :
  (C.filter (fun X => u ∈ X)).card + (C.filter (fun X => u ∉ X)).card = C.card := by
  classical
  /-
  【用途】
  CON_ID のステップ1でカードの分解に使う。
  【証明方針】
  Finset.cardの加法性、離散性を使う。
  【場所】
  ここで証明してよい。
  -/
  sorry

/-- Sum partition: sum over C is sum over the disjoint union of the two filters. -/
lemma sum_filter_mem_add_sum_filter_not_mem
  (n : Nat) (C : Finset (Finset α)) (u : α) :
  (∑ X ∈ C, w (α := α) n X)
    =
  (∑ X ∈ (C.filter (fun X => u ∈ X)), w (α := α) n X)
    +
  (∑ X ∈ (C.filter (fun X => u ∉ X)), w (α := α) n X) := by
  classical
  /-
  【用途】
  CON_ID のステップ1で和の分解に使う。
  【証明方針】
  Finset.sum_union と離散性を使う。
  【場所】
  ここで証明してよい。
  -/
  sorry


/- ============================================================
  2. Injectivity of erase u on sets containing u
============================================================ -/

/--
Key engine: erase u is injective on {X | u∈X}.
This is what prevents collision in con-image (image-level).
-/
lemma erase_injOn (u : α) :
    Set.InjOn (fun X : Finset α => X.erase u) {X : Finset α | u ∈ X} := by
  classical
  /-
  【用途】
  CON_ID のステップ3で con の像への和の書き換えに必須。
  擬似的な「衝突しない」性質を保証し、sum_image の適用を可能にする。
  【証明方針】
  元素の包含関係と集合の性質からの場合分け。
  【場所】
  ここで証明してよい。
  -/
  sorry

/--
A convenient Finset-form: if X,Y∈C and both contain u, and erase u equal, then X=Y.
-/
lemma erase_inj_on_mem
  (C : Finset (Finset α)) (u : α) :
  ∀ ⦃X Y : Finset α⦄, X ∈ C → Y ∈ C → u ∈ X → u ∈ Y → X.erase u = Y.erase u → X = Y := by
  classical
  intro X Y hX hY huX huY hEq
  exact (erase_injOn (α := α) u) huX huY hEq


/- ============================================================
  2.5. Missing glue lemmas (planned)
============================================================ -/

/--
(sum_filter_mem_eq_sum_image_con)
  ∑ X ∈ (C.filter (fun X => u ∈ X)), w n (X.erase u)
  を con u C に対する和に書き換える補助定理。
  これは CON_ID のステップ3の sum_image 適用に必要。
-/
lemma sum_filter_mem_eq_sum_image_con
  (n : Nat) (C : Finset (Finset α)) (u : α) :
  (∑ X ∈ (C.filter (fun X => u ∈ X)), w (α := α) n (X.erase u))
    =
  (∑ Y ∈ (con (α := α) u C), w (α := α) n Y) := by
  classical
  /-
  【用途】
  CON_ID のステップ3で sum_image を使って和を con の像に書き換える。
  【証明方針】
  Finset.sum_image + erase_inj_on_mem の injectivity を使う。
  【場所】
  ここで証明予定。
  -/
  sorry

/--
(card_con_eq_deg)
  (con u C).card = deg C u
  これは erase の injectivity から導かれる。
-/
lemma card_con_eq_deg (C : Finset (Finset α)) (u : α) :
  (con (α := α) u C).card = deg (α := α) C u := by
  classical
  /-
  【用途】
  CON_ID のステップ4で ndeg の計算に必要。
  【証明方針】
  erase_inj_on_mem の injectivity と Finset.card_image から導出。
  【場所】
  ここで証明予定。
  -/
  sorry

/--
(sum_con_def)
  con の定義を展開し、con u C = (C.filter (u∈X)).image (λ X, X.erase u) であることを示す補助定理。
  S0_CoreDefs の定義に合わせて調整する必要あり。
-/
lemma sum_con_def (C : Finset (Finset α)) (u : α) :
  con (α := α) u C = (C.filter (fun X => u ∈ X)).image (fun X => X.erase u) := by
  /-
  【用途】
  con の定義の展開に使い、CON_ID のステップ3の和の書き換えに役立てる。
  【証明方針】
  con の定義を確認し、Finset の image と filter の関係を示す。
  【場所】
  ここで証明予定。定義に合わせて調整が必要。
  -/
  sorry


/- ============================================================
  3. Bridge: deg / ndeg relation to the two filters
============================================================ -/

/-- deg C u is exactly the card of the (u∈X)-filter (by rfl). -/
lemma deg_eq_card_filter_mem (C : Finset (Finset α)) (u : α) :
    deg (α := α) C u = (C.filter (fun X => u ∈ X)).card := by
  rfl

/-- Del u C is exactly the (u∉X)-filter (by rfl). -/
lemma Del_eq_filter_not_mem (C : Finset (Finset α)) (u : α) :
    Del (α := α) u C = C.filter (fun X => u ∉ X) := by
  rfl

/--
Basic card identity:
  |C| = deg C u + |Del u C|
-/
lemma card_eq_deg_add_card_Del (C : Finset (Finset α)) (u : α) :
    C.card = deg (α := α) C u + (Del (α := α) u C).card := by
  classical
  /-
  【用途】
  CON_ID のステップ4でカードの分解に使う。
  【証明方針】
  card_filter_mem_add_card_filter_not_mem と rfl 展開を使う。
  【場所】
  ここで証明してよい。
  -/
  sorry

/--
Rewrite ndeg in the convenient "deg - DelCard" form:
  ndeg C u = (deg C u : Int) - (Del u C).card
-/
lemma ndeg_eq_deg_sub_card_Del (C : Finset (Finset α)) (u : α) :
    ndeg (α := α) C u = (deg (α := α) C u : Int) - ((Del (α := α) u C).card : Int) := by
  classical
  /-
  【用途】
  CON_ID のステップ4で ndeg の計算に使う。
  【証明方針】
  deg と Del の定義展開と整数の引き算。
  【場所】
  ここで証明してよい。
  -/
  sorry


/- ============================================================
  4. Main theorem: CON_ID
============================================================ -/


/--
(CON_ID)
  NDS_n(C)
    = NDS_{n-1}(con_u(C)) + NDS_{n-1}(Del_u(C)) + ndeg_C(u)
-/
theorem CON_ID
    (n : Nat) (hn : 1 ≤ n) (C : Finset (Finset α)) (u : α) :
    NDS (α := α) n C
      =
    NDS (α := α) (n - 1) (con (α := α) u C)
      +
    NDS (α := α) (n - 1) (Del (α := α) u C)
      +
    ndeg (α := α) C u := by
  sorry

/- ------------------------------------------------------------
  5. Assoc-friendly variant
------------------------------------------------------------ -/

/--
A rearranged / assoc-friendly version, to reduce parenthesis noise downstream.
-/

lemma CON_ID_assoc
  (n : Nat) (hn : 1 ≤ n) (C : Finset (Finset α)) (u : α) :
  NDS (α := α) n C
    =
  NDS (α := α) (n - 1) (con (α := α) u C)
    +
  (NDS (α := α) (n - 1) (Del (α := α) u C) + ndeg (α := α) C u) := by
  simpa [add_assoc, add_left_comm, add_comm] using
    (CON_ID (α := α) (n := n) (hn := hn) (C := C) (u := u))

end Accounting
end Dr1nds
