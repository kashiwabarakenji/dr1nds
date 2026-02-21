-- Dr1nds/S6_ConDelNdegId.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
--import LeanCopilot

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

omit [DecidableEq α] in
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
  simp [Dr1nds.w, Nat.succ_eq_add_one, Int.natCast_succ, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

omit [DecidableEq α] in
/-- succ shift for NDS: NDS (n+1) C = NDS n C - |C| -/
lemma NDS_succ (n : Nat) (C : Finset (Finset α)) :
    NDS (α := α) n.succ C = NDS (α := α) n C - (C.card : Int) := by
  classical
  -- expand NDS and apply `w_succ` pointwise
  simp [Dr1nds.NDS, w_succ, sub_eq_add_neg]
  simp [Finset.sum_add_distrib]

/--
If u∈X and n≥1, then
  w n X = w (n-1) (X.erase u) + 1
This is the “membership part” used in CON_ID.
-/
lemma w_of_mem_erase
  (n : Nat) (hn : 1 ≤ n) (u : α) (X : Finset α) (hu : u ∈ X) :
  w (α := α) n X = w (α := α) (n - 1) (X.erase u) + 1 := by
  classical
  -- `n≥1` lets us treat `n` as `k.succ`, so `n-1 = k`.
  cases n with
  | zero =>
      -- contradiction: 1 ≤ 0
      cases (Nat.not_succ_le_zero 0) hn
  | succ k =>
      -- In this case, `n = k.succ` and `n-1 = k`.
      -- Use `card_erase_add_one` to relate `|X|` and `|X.erase u|`.
      -- Then it is a direct calculation from the definition of `w`.
      simp [Dr1nds.w, Int.natCast_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      -- 2. (k + 1 - 1) を k に簡約する
      -- 3. u ∈ X なので、X.erase u の濃度は X.card - 1 になることを適用
      rw [Finset.card_erase_of_mem hu]
      -- 4. X.card > 0 であることを確認（u ∈ X より自明だが、自然数の引き算で必要になる場合がある）
      have h_card_pos : 0 < X.card := Finset.card_pos.mpr ⟨u, hu⟩

      -- 5. 自然数の算術として等式を解く (k + (card - 1) + 1 = k + 1 + card)
      omega

omit [DecidableEq α] in
/--
If u∉X and n≥1, then
  w n X = w (n-1) X - 1
This is the “non-membership part” used in CON_ID.
-/
lemma w_of_not_mem
  (n : Nat) (hn : 1 ≤ n) (u : α) (X : Finset α) (_hu : u ∉ X) :
  w (α := α) n X = w (α := α) (n - 1) X - 1 := by
  -- Pure shift in the ambient parameter `n`.
  -- The assumption `u ∉ X` is not needed for this arithmetic identity.
  have hsucc : (n - 1).succ = n := by
    cases n with
    | zero =>
        cases (Nat.not_succ_le_zero 0) hn
    | succ k =>
        simp
  calc
    w (α := α) n X
        = w (α := α) (n - 1).succ X := by simp_all only [Nat.succ_eq_add_one, Nat.sub_add_cancel]
    _   = w (α := α) (n - 1) X - 1 := by
          simpa using (w_succ (α := α) (n := n - 1) (X := X))


/- ============================================================
  1. Partition lemmas (filter split)
============================================================ -/

/-- The two filters (u∈X) and (u∉X) are disjoint. -/
lemma disjoint_filter_mem_not_mem
  (C : Finset (Finset α)) (u : α) :
  Disjoint (C.filter (fun X => u ∈ X)) (C.filter (fun X => u ∉ X)) :=
  by
    classical
    refine Finset.disjoint_left.2 ?_
    intro X hXmem hXnot
    have hu1 : u ∈ X := (Finset.mem_filter.mp hXmem).2
    have hu2 : u ∉ X := (Finset.mem_filter.mp hXnot).2
    exact hu2 hu1

/-- Union of the two filters gives back C. -/
lemma union_filter_mem_not_mem
  (C : Finset (Finset α)) (u : α) :
  (C.filter (fun X => u ∈ X)) ∪ (C.filter (fun X => u ∉ X)) = C :=
  by
    classical
    ext X
    by_cases hu : u ∈ X
    · simp [hu]
    · simp [hu]

/-- Card partition: |C| = |{u∈X}| + |{u∉X}|. -/
lemma card_filter_mem_add_card_filter_not_mem
  (C : Finset (Finset α)) (u : α) :
  (C.filter (fun X => u ∈ X)).card + (C.filter (fun X => u ∉ X)).card = C.card :=
  by
    classical
    -- standard partition of a finset by a decidable predicate
    simpa using (Finset.filter_card_add_filter_neg_card_eq_card (s := C) (p := fun X : Finset α => u ∈ X))

/-- Sum partition: sum over C is sum over the disjoint union of the two filters. -/
lemma sum_filter_mem_add_sum_filter_not_mem
  (n : Nat) (C : Finset (Finset α)) (u : α) :
  (∑ X ∈ C, w (α := α) n X)
    =
  (∑ X ∈ (C.filter (fun X => u ∈ X)), w (α := α) n X)
    +
  (∑ X ∈ (C.filter (fun X => u ∉ X)), w (α := α) n X) :=
  by
    classical
    -- rewrite the LHS using the disjoint union decomposition
    have hdisj := disjoint_filter_mem_not_mem (α := α) (C := C) (u := u)
    have hunion := union_filter_mem_not_mem (α := α) (C := C) (u := u)
    -- `sum` over a disjoint union splits
    -- first rewrite `C` as the union of the two filters
    simpa [hunion, Finset.sum_union, hdisj, add_comm, add_left_comm, add_assoc]
      using (Finset.sum_union hdisj (f := fun X : Finset α => w (α := α) n X))


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
  intro X hX Y hY hEq
  have hIns : insert u (X.erase u) = insert u (Y.erase u) :=
    congrArg (fun Z : Finset α => insert u Z) hEq
  simpa [Finset.insert_erase hX, Finset.insert_erase hY] using hIns

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
  -- s = {X ∈ C | u∈X}, g = erase u
  -- sum_image:  ∑ y in s.image g, f y = ∑ x in s, f (g x)
  -- これを左右どちらに合わせるかだけ
  simpa [con] using
    (Finset.sum_image
      (s := C.filter (fun X => u ∈ X))
      (f := fun Y => w (α := α) n Y)
      (g := fun X => X.erase u)
      (by
        intro X hX Y hY hXY
        -- hX : X ∈ filter ... なので u∈X が取れる
        have huX : u ∈ X := by
          -- filter の membership を分解
          have : u ∈ X := by
            simpa using (Finset.mem_filter.mp hX).2
          exact this
        have huY : u ∈ Y := by
          simpa using (Finset.mem_filter.mp hY).2
        exact erase_inj_on_mem ({X ∈ C | u ∈ X}) u hX hY huX huY hXY
      )).symm

/--
(card_con_eq_deg)
  (con u C).card = deg C u
  これは erase の injectivity から導かれる。
-/
lemma card_con_eq_deg (C : Finset (Finset α)) (u : α) :
  (con (α := α) u C).card = deg (α := α) C u :=
by
  classical
  -- We count `con u C` by exhibiting a bijection between
  --   s := {X ∈ C | u ∈ X}
  -- and
  --   t := con u C = s.image (fun X => X.erase u).
  -- The map is `X ↦ X.erase u`, which is injective on `u ∈ X`.
  let s : Finset (Finset α) := C.filter (fun X => u ∈ X)
  let t : Finset (Finset α) := con (α := α) u C
  have ht : t = s.image (fun X : Finset α => X.erase u) := by
    simp [t, s, con]
  -- Use `Finset.card_bij` (injective-on-domain is enough; no global injectivity needed).
  have hcard : s.card = t.card := by
    -- Bijection data
    refine Finset.card_bij (s := s) (t := t)
      (i := fun X _ => X.erase u)
      (hi := ?_)
      (i_inj := ?_)
      (i_surj := ?_)
    · intro X hX
      -- show `X.erase u ∈ t`
      -- `t` is the image of `s` under `erase u`
      simpa [ht] using Finset.mem_image_of_mem (fun X : Finset α => X.erase u) hX
    · intro X1 hX1 X2 hX2 hEq
      -- extract `u ∈ Xi` from filter-membership
      have hu1 : u ∈ X1 := (Finset.mem_filter.mp hX1).2
      have hu2 : u ∈ X2 := (Finset.mem_filter.mp hX2).2
      exact (erase_injOn (α := α) u) hu1 hu2 hEq
    · intro Y hY
      -- surjectivity: any Y in the image comes from some X in s
      -- unfold membership in `t` using `ht`
      have hY' : Y ∈ s.image (fun X : Finset α => X.erase u) := by
        simpa [ht] using hY
      rcases Finset.mem_image.mp hY' with ⟨X, hXs, rfl⟩
      exact ⟨X, hXs, rfl⟩
  -- Now rewrite `deg` and finish.
  -- `deg C u` is definitionally the card of the filter.
  -- `con u C` is `t`.
  simpa [deg, s, t] using hcard.symm

/--
(sum_con_def)
  con の定義を展開し、con u C = (C.filter (u∈X)).image (λ X, X.erase u) であることを示す補助定理。
  S0_CoreDefs の定義に合わせて調整する必要あり。
-/
lemma sum_con_def (C : Finset (Finset α)) (u : α) :
  con (α := α) u C = (C.filter (fun X => u ∈ X)).image (fun X => X.erase u) := by
  simp [con]
  /-
  【用途】
  con の定義の展開に使い、CON_ID のステップ3の和の書き換えに役立てる。
  【証明方針】
  con の定義を確認し、Finset の image と filter の関係を示す。
  【場所】
  ここで証明予定。定義に合わせて調整が必要。
  -/

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
    C.card = deg (α := α) C u + (Del (α := α) u C).card :=
  by
    classical
    -- unfold `deg` and `Del` (both are filter-cards by definition in S0)
    -- and use the standard partition card identity.
    simpa [deg_eq_card_filter_mem, Del_eq_filter_not_mem] using
      (card_filter_mem_add_card_filter_not_mem (α := α) (C := C) (u := u)).symm

/--
Rewrite ndeg in the convenient "deg - DelCard" form:
  ndeg C u = (deg C u : Int) - (Del u C).card
-/
lemma ndeg_eq_deg_sub_card_Del (C : Finset (Finset α)) (u : α) :
    ndeg (α := α) C u = (deg (α := α) C u : Int) - ((Del (α := α) u C).card : Int) := by
  classical
  -- `ndeg` is defined from `deg` and the total card of `C`; rewrite that total card
  -- using the standard partition `C = {X | u∈X} ⊔ {X | u∉X}`.
  have hcardNat : C.card = deg (α := α) C u + (Del (α := α) u C).card :=
    card_eq_deg_add_card_Del (α := α) (C := C) (u := u)
  have hcard : (C.card : Int) = (deg (α := α) C u : Int) + ((Del (α := α) u C).card : Int) :=
    congrArg (fun t : Nat => (t : Int)) hcardNat

  -- Now unfold `ndeg` and compute.
  -- The intended normal form is `deg - Del.card`.
  -- This works for the standard definition `ndeg = 2*deg - |C|`.

  simp [Dr1nds.ndeg, hcard]
  simp_all only [Int.natCast_add]
  norm_cast
  simp_all only [Int.natCast_mul, Int.cast_ofNat_Int, Int.natCast_add]
  omega



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
