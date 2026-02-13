-- Dr1nds/S5_ForbidConLemmas.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S6_ConDelNdegId  -- erase_injOn / erase_inj_on_mem など（会計核側に一本化）

/-
  このファイルは Forbid/Hole/Up と con の関係に関するインターフェースの凍結を目的としている。
  ここで定義される公理群は暫定的なものであり、以下の要素を使った補題証明により将来的に置き換えられる予定である：
    (a) S0_CoreDefs の定義
    (b) S6_ConDelNdegId にある erase_injOn / erase_inj_on_mem 等の射影の単射性補題
    (c) Finset の基本的な書き換え
  移行計画としては、まず erase_subset_erase_iff を証明し、それを用いて con_Up_eq_Up_con と con_Hole_eq_Hole_con を証明、
  その後カード数に関する補題を証明し、最終的に CON_ID_corr_shape を補題として導出できる形にすることを目指す。
-/

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/- ============================================================
  S5 : Forbid / Hole / Up under con (SKELETON / FROZEN I/O)
  Policy:
    * base defs: S0_CoreDefs
    * this file freezes the "commutation + card" interfaces
    * proofs can be filled later
============================================================ -/

namespace Forbid

/- ------------------------------------------------------------
  0. Elementary helper
------------------------------------------------------------ -/

omit [DecidableEq α] in
/-- v∈A and A⊆X implies v∈X. -/
lemma mem_of_subset_of_mem {A X : Finset α} {v : α}
  (hvA : v ∈ A) (hAX : A ⊆ X) : v ∈ X :=
by
  exact hAX hvA

/-- v∈A ⇒ every X in Up(C,A) contains v. -/
lemma Up_all_mem_v (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    ∀ X ∈ Up (α := α) C A, v ∈ X := by
  classical
  intro X hX
  -- unfold Up; get A ⊆ X; then apply mem_of_subset_of_mem
  -- Up C A = filter (A ⊆ X)
  have hAX : A ⊆ X := (Finset.mem_filter.1 hX).2
  exact mem_of_subset_of_mem (α := α) (A := A) (X := X) (v := v) hvA hAX

/- ------------------------------------------------------------
  1. Core equivalence: (A.erase v ⊆ X.erase v) ↔ (A ⊆ X)
     under v∈A and v∈X.
------------------------------------------------------------ -/

/-
  【erase_subset_erase_iff の説明】
  - S8 会計などで頻出する基本補題で、erase による包含関係の前後関係を明示的に扱う。
  - 証明には、v ∈ A と v ∈ X という前提が必須である。これは erase による要素除去の影響を正確に扱うため。
  - 具体的には、erase の injectivity 補題（erase_inj_on_mem 等）と Finset の包含関係の基本性質を用いる想定。
  - TODO: 証明可能になったら axiom を lemma に置き換えること。
-/
axiom erase_subset_erase_iff (A X : Finset α) (v : α) (hvA : v ∈ A) (hvX : v ∈ X) :
    (A.erase v ⊆ X.erase v) ↔ (A ⊆ X)

/-
  【erase_subset_erase_iff の証明スケルトン例（コメントアウト）】
  erase_subset_erase_of_subset {A X v} (hvA : v ∈ A) (hAX : A ⊆ X) : A.erase v ⊆ X.erase v :=
    by intros x hx; simp only [Finset.mem_erase] at *; cases hx with hneq hmem;
    cases Finset.mem_of_subset hAX hmem; simp [*]

  subset_of_erase_subset_erase {A X v} (hvA : v ∈ A) (hvX : v ∈ X) (h : A.erase v ⊆ X.erase v) : A ⊆ X :=
    by intros x hx; by_cases hxeq : x = v;
       simp [hxeq, hvX, hvA];
       [exact hvX, exact h (Finset.mem_erase_of_ne_of_mem hxeq hx)]

  -- さらに、Up_all_mem_v により v ∈ X が Up(C,A) の任意の X に対して成り立つことを補助的に利用する。
-/

/- ------------------------------------------------------------
  2. Commutation of Up/Hole with con
------------------------------------------------------------ -/

/-
  【con_Up_eq_Up_con の説明】
  - S10 の Q-step や S11 の kernel 部分で利用される。
  - 証明には Finset.ext による集合の等号証明、con・Up のメンバシップ定義の展開が必要。
  - erase_subset_erase_iff を用いて、v ∈ A と Up(C,A) の各要素 X に対する v ∈ X の前提を活用する。
  - con の像の単射性には erase_inj_on_mem 等の補題を利用する想定。
  - TODO: 証明可能になったら axiom を lemma に置き換えること。
-/
axiom con_Up_eq_Up_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    con (α := α) v (Up (α := α) C A)
      =
    Up (α := α) (con (α := α) v C) (A.erase v)

/-
  【con_Hole_eq_Hole_con の説明】
  - S10 の Q-step や S11 の kernel 部分で利用される。
  - con_Up_eq_Up_con と類似の証明戦略で、Hole の定義を使う。
  - con の像の単射性や erase_subset_erase_iff を活用。
  - TODO: 証明可能になったら axiom を lemma に置き換えること。
-/
axiom con_Hole_eq_Hole_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    con (α := α) v (Hole (α := α) C A)
      =
    Hole (α := α) (con (α := α) v C) (A.erase v)

/-
  【con_Up_eq_Up_con と con_Hole_eq_Hole_con の証明戦略スケルトン（コメントアウト）】
  - Finset.ext による集合の等号証明を行う。
  - con, Up, Hole のメンバシップ条件（S0_CoreDefs 由来）を展開し、両辺のメンバシップを比較。
  - Up の場合、X ∈ Up(C,A) は A ⊆ X かつ X ∈ C であることを利用。
  - con の定義により、con v X のメンバシップは erase 操作と関連。
  - erase_subset_erase_iff により、A.erase v ⊆ X.erase v と A ⊆ X の等価性を活用。
  - さらに erase_inj_on_mem 等の injectivity 補題を使い、con の像の一意性を確保。
-/

/- ------------------------------------------------------------
  3. Card transfer of Up under con (v∈A)
------------------------------------------------------------ -/

/-
  【card_Up_eq_card_Up_con の説明】
  - Up の集合としての等式 con_Up_eq_Up_con から導かれるカード数の等式。
  - Finset.card_congr や simp 等を利用して証明可能と想定。
  - DecidableEq α や Classical の仮定が必要になることがある。
  - TODO: 証明可能になったら axiom を lemma に置き換えること。
-/
axiom card_Up_eq_card_Up_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    (Up (α := α) C A).card
      =
    (Up (α := α) (con (α := α) v C) (A.erase v)).card

/- ------------------------------------------------------------
  4. Corrected CON identity skeleton (the shape used in Q-step)
------------------------------------------------------------ -/

/-
  【CON_ID_corr_shape の説明】
  - これは新しい数学的事実ではなく、
    ・S6_ConDelNdegId などにある基本的な CON_ID を D := Hole(C,A) に適用したもの
    ・con と Hole, Up の交換補題および Up のカード数補題を組み合わせたパッケージング
  - 将来的にはこの axiom を削除し、これらの補題の書き換えによって導出される形にしたい。
  - S10 の Q-step において必要な形を満たすために設けている。
-/
axiom CON_ID_corr_shape
  (n : Nat) (hn : 1 ≤ n)
  (C : Finset (Finset α)) (A : Finset α)
  (v : α) (hvA : v ∈ A) :
  NDS_corr (α := α) n C A
    =
  NDS_corr (α := α) (n - 1) (con (α := α) v C) (A.erase v)
    +
  (NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) C A))
      + ndeg (α := α) (Hole (α := α) C A) v)

end Forbid

end Dr1nds
