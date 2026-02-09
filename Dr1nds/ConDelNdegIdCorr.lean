import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

import Dr1nds.Accounting
import Dr1nds.ConDelNdegId
import Dr1nds.Forbid1

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
  CON_ID_corr を埋めるための補題スケルトン群。

  方向性：
  (1) NDS_corr n C A = NDS n (Hole C A) + |Up_C(A)|
  (2) まず D := Hole C A に CON_ID を適用して NDS n D を分解
  (3) con_v(D) が Hole (con_v(C)) (A.erase v) と一致すること
  (4) |Up_C(A)| が |Up_{con_v(C)}(A.erase v)| と一致すること（v∈A を使う）
  を示して、RHS の NDS_corr (n-1) ... を作る。
-/

-- ここで使う記号の整合（Forbid1 側の定義を想定）
-- Up  : Up (C) (A) := {X∈C | A ⊆ X}
-- Hole: Hole C A := C \ Up C A  （または filter 版）
-- NDS_corr n C A := NDS n (Hole C A) + |Up C A|

/- ============================================================
  0. 基本：Up に入る集合は v を含む（v∈A のとき）
============================================================ -/

/-- v∈A なら、A⊆X から v∈X が従う（Up 側で v∈X が自動） -/
lemma mem_of_subset_of_mem {A X : Finset α} {v : α} (hvA : v ∈ A) (hAX : A ⊆ X) :
    v ∈ X := by
  exact hAX hvA

/-- v∈A のとき、Up_C(A) の各要素は v を含む -/
lemma Up_all_mem_v (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    ∀ X ∈ Up (α := α) C A, v ∈ X := by
  classical
  intro X hX
  -- Up の定義に応じて展開（mem_filter / mem_sdiff など）
  -- `A ⊆ X` を取り出して hvA を流すだけ
  sorry


/- ============================================================
  1. 核：con(Hole C A) = Hole (con C) (A.erase v) （v∈A を使う）
============================================================ -/

/--
v∈A のもとで
  (A.erase v) ⊆ (X.erase v)  ∧ v∈X   ⇔   A ⊆ X
が成り立つ（これが Hole/Up の整合の最重要核）。
-/
lemma erase_subset_erase_iff (A X : Finset α) (v : α) (hvA : v ∈ A) (hvX : v ∈ X) :
    (A.erase v ⊆ X.erase v) ↔ (A ⊆ X) := by
  classical
  -- ⊆ の両方向を elementwise で示す
  -- (→) : a∈A なら a=v と a≠v で分岐
  -- (←) : erase は単調なので `Finset.erase_subset_erase` 系で終わる
  sorry

/--
v∈A の下で、Up は con と可換：
  con_v(Up_C(A)) = Up_{con_v(C)}(A.erase v)
（集合として一致）
-/
lemma con_Up_eq_Up_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    con (α := α) v (Up (α := α) C A)
      =
    Up (α := α) (con (α := α) v C) (A.erase v) := by
  classical
  -- ext Y; constructor
  -- 片方：Y=X.erase v, X∈C, v∈X, A⊆X から (A.erase v)⊆Y を得る
  -- 逆：Y∈Up(con C)(A.erase v) なら Y=X.erase v を満たす X を取り、
  --     erase_subset_erase_iff を使って A⊆X に戻し、X∈Up(C)(A) を得る
  sorry

/--
v∈A の下で、Hole も con と可換：
  con_v(Hole C A) = Hole (con_v(C)) (A.erase v)
（集合として一致）
-/
lemma con_Hole_eq_Hole_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    con (α := α) v (Hole (α := α) C A)
      =
    Hole (α := α) (con (α := α) v C) (A.erase v) := by
  classical
  -- Hole = C \ Up(C,A) なので、上の con_Up_eq_Up_con と
  -- con の定義（filter+image）を使って ext で押し切る
  -- ※ここは set-image が絡むので、まずは `ext` で membership 同値を作るのが安全
  sorry


/- ============================================================
  2. 核：|Up_C(A)| = |Up_{con C}(A.erase v)| （v∈A のとき）
============================================================ -/

/--
v∈A の下で、X ↦ X.erase v は Up_C(A) から Up_{con C}(A.erase v) への全単射になる。
（重複が潰れる可能性があるので、injective は「v∈X」が効く）
-/
lemma card_Up_eq_card_Up_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    (Up (α := α) C A).card
      =
    (Up (α := α) (con (α := α) v C) (A.erase v)).card := by
  classical
  -- 方針：
  -- (1) v∈A より Up_C(A) の各 X は v∈X（Up_all_mem_v）
  -- (2) erase は「vを含む集合」上で injective（ConDelNdegId で作った補題を使う）
  -- (3) image で card が保たれる
  -- (4) image がちょうど RHS の Up になる（con_Up_eq_Up_con を使う）
  --
  -- 実装の定石は：
  --   have hvX : ∀ X ∈ Up C A, v ∈ X := ...
  --   have hinj : Set.InjOn (fun X => X.erase v) {X | X∈Up C A} := ...
  --   calc card(Up C A) = card(image erase ...) := by ...
  --   _ = card(Up (con C) (A.erase v)) := by simp [con_Up_eq_Up_con]
  sorry


/- ============================================================
  3. 仕上げ：CON_ID_corr の証明骨格（埋め方の設計図）
============================================================ -/

theorem CON_ID_corr_skeleton
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
  -- 1) unfold NDS_corr
  --    NDS_corr n C A = NDS n (Hole C A) + |Up C A|
  -- 2) CON_ID を D := Hole C A に適用
  --    NDS n D = NDS(n-1)(con v D) + NDS(n-1)(Del v D) + ndeg D v
  -- 3) con v D を Hole (con v C) (A.erase v) に rewrite（con_Hole_eq_Hole_con）
  -- 4) |Up C A| を |Up (con v C) (A.erase v)| に rewrite（card_Up_eq_card_Up_con）
  -- 5) 定義を戻して NDS_corr(n-1) を作り、assoc を整える
  --
  -- ここまでできれば、S10 の Q_step は “rewrite して linarith” で終わる。
  sorry

end Dr1nds
