-- Dr1nds/S6_ConDelNdegId.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

import Dr1nds.SetFamily.CoreDefs

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/- ============================================================
  S6 : Core accounting identity (CON_ID)  [SKELETON / FROZEN I/O]
  Policy:
    * base defs: S0_CoreDefs
    * this file fixes the I/O of the accounting identity
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
  simp [Dr1nds.w, Nat.succ_eq_add_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

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
      simp [Dr1nds.w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
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
  (∑ Y ∈ (Con (α := α) u C), w (α := α) n Y) := by
  classical
  -- s = {X ∈ C | u∈X}, g = erase u
  -- sum_image:  ∑ y in s.image g, f y = ∑ x in s, f (g x)
  -- これを左右どちらに合わせるかだけ
  simpa [Con] using
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
  (Con (α := α) u C).card = deg (α := α) C u :=
by
  classical
  -- We count `con u C` by exhibiting a bijection between
  --   s := {X ∈ C | u ∈ X}
  -- and
  --   t := con u C = s.image (fun X => X.erase u).
  -- The map is `X ↦ X.erase u`, which is injective on `u ∈ X`.
  let s : Finset (Finset α) := C.filter (fun X => u ∈ X)
  let t : Finset (Finset α) := Con (α := α) u C
  have ht : t = s.image (fun X : Finset α => X.erase u) := by
    simp [t, s, Con]
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
  Con (α := α) u C = (C.filter (fun X => u ∈ X)).image (fun X => X.erase u) := by
  simp [Con]
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
  simp_all only [Nat.cast_add]
  rw [ndeg]
  simp_all only [Nat.cast_add]
  ring

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
    NDS (α := α) (n - 1) (Con (α := α) u C)
      +
    NDS (α := α) (n - 1) (Del (α := α) u C)
      +
    ndeg (α := α) C u := by
  dsimp [NDS]
  dsimp [ndeg,deg]
  dsimp [Con,Del]
  let ideq := sum_filter_mem_add_sum_filter_not_mem (n-1) C u
  dsimp [w] at ideq
  let A := C.filter (fun X => u ∈ X)
  let B := C.filter (fun X => u ∉ X)
  let D := Finset.image (fun X => X.erase u) A

  have sum_split : ∑ X ∈ C, w n X = ∑ X ∈ A, w n X + ∑ X ∈ B, w n X := by
    simp only [A, B]
    exact sum_filter_mem_add_sum_filter_not_mem n C u
  -- 2) A上: w n X = w (n-1) (X.erase u) + 1
  have hA_eq : ∀ X ∈ A, w n X = w (n - 1) (X.erase u) + 1 := by
    intro X hX
    simp only [A, Finset.mem_filter] at hX
    simp only [w, Finset.card_erase_of_mem hX.2]
    ring_nf
    have :X.card ≥ 1:= by
      simp_all only [ge_iff_le, Finset.one_le_card, A, B]
      obtain ⟨left, right⟩ := hX
      exact ⟨u, right⟩
    simp_all only [ge_iff_le, Finset.one_le_card, Nat.cast_sub, Nat.cast_one, A, B]
    obtain ⟨left, right⟩ := hX
    ring


  -- 3) B上: w n X = w (n-1) X - 1
  have hB_eq : ∀ X ∈ B, w n X = w (n - 1) X - 1 := by
    intro X hX
    simp only [w]
    omega
  -- 4) A上の和を書き換え
  have sumA : ∑ X ∈ A, w n X = ∑ X ∈ A, w (n - 1) (X.erase u) + ↑A.card := by
    rw [Finset.sum_congr rfl hA_eq]
    rw [Finset.sum_add_distrib, Finset.sum_const]
    simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, mul_one,
      Finset.mem_filter, and_imp, A, B]
  -- 5) erase の単射性
  have hinj : ∀ X ∈ A, ∀ Y ∈ A, Finset.erase X u = Finset.erase Y u → X = Y := by
    intro X hX Y hY heq
    simp only [A, Finset.mem_filter] at hX hY
    rw [← Finset.insert_erase hX.2, ← Finset.insert_erase hY.2, heq]
  -- 6) A上のeraseの和 = D上の和
  have sumD : ∑ X ∈ A, w (n - 1) (X.erase u) = ∑ X ∈ D, w (n - 1) X := by
    exact (Finset.sum_image hinj).symm
  -- 7) B上の和を書き換え
  have sumB : ∑ X ∈ B, w n X = ∑ X ∈ B, w (n - 1) X - ↑B.card := by
    rw [Finset.sum_congr rfl hB_eq]
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, mul_one, Finset.mem_filter, and_self,
      and_imp, A, B, D]
  -- 8) |A| + |B| = |C|
  have hcard : (A.card : ℤ) + ↑B.card = ↑C.card := by
    --have := Finset.filter_card_add_filter_neg_card_eq_card C (fun X => u ∈ X)
    simp only [A, B]
    have h := Finset.filter_card_add_filter_neg_card_eq_card (s := C) (p := fun X => u ∈ X)
    push_cast [← h]
    simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, mul_one, Finset.mem_filter, and_self,
      and_imp, A, B, D]
  -- 9) 合成
  rw [sum_split, sumA, sumD, sumB]
  linarith

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
  NDS (α := α) (n - 1) (Con (α := α) u C)
    +
  (NDS (α := α) (n - 1) (Del (α := α) u C) + ndeg (α := α) C u) := by
  simpa [add_assoc, add_left_comm, add_comm] using
    (CON_ID (α := α) (n := n) (hn := hn) (C := C) (u := u))

/- ============================================================
  6. Trace-PairTrace identity
============================================================ -/

lemma mem_Con_iff
  (u : α) (C : Finset (Finset α)) (Y : Finset α) :
  Y ∈ Con (α := α) u C ↔ u ∉ Y ∧ (Y ∪ {u} : Finset α) ∈ C := by
  classical
  constructor
  · intro hY
    rcases Finset.mem_image.mp hY with ⟨X, hXf, hYX⟩
    have hXC : X ∈ C := (Finset.mem_filter.mp hXf).1
    have huX : u ∈ X := (Finset.mem_filter.mp hXf).2
    have huY : u ∉ Y := by
      rw [← hYX]
      exact Finset.notMem_erase u X
    have hYcup : (Y ∪ {u} : Finset α) = X := by
      rw [← hYX]
      simpa [Finset.union_comm, Finset.union_left_comm, Finset.union_assoc] using
        (Finset.insert_erase huX)
    exact ⟨huY, by simpa [hYcup] using hXC⟩
  · intro h
    rcases h with ⟨huY, hYcup⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨Y ∪ {u}, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ?_
      refine ⟨hYcup, ?_⟩
      exact Finset.mem_union_right Y (Finset.mem_singleton.mpr rfl)
    · simp [huY]

lemma mem_PairTr_iff
  (u : α) (C : Finset (Finset α)) (Y : Finset α) :
  Y ∈ PairTr (α := α) u C ↔ Y ∈ C ∧ u ∉ Y ∧ (Y ∪ {u} : Finset α) ∈ C := by
  simp [PairTr, and_left_comm]

lemma mem_Tr_iff_mem_Del_or_mem_Con
  (u : α) (C : Finset (Finset α)) (Y : Finset α) :
  Y ∈ Tr (α := α) u C ↔ Y ∈ Del (α := α) u C ∨ Y ∈ Con (α := α) u C := by
  classical
  constructor
  · intro hY
    rcases Finset.mem_image.mp hY with ⟨X, hXC, hYX⟩
    by_cases huX : u ∈ X
    · right
      refine Finset.mem_image.mpr ?_
      refine ⟨X, Finset.mem_filter.mpr ⟨hXC, huX⟩, hYX⟩
    · left
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, ?_⟩
      · simpa [← hYX, Finset.erase_eq_of_notMem huX] using hXC
      · simpa [← hYX, Finset.erase_eq_of_notMem huX] using huX
  · intro hY
    rcases hY with hDel | hCon
    · have hYC : Y ∈ C := (Finset.mem_filter.mp hDel).1
      refine Finset.mem_image.mpr ?_
      exact ⟨Y, hYC, by simp [(Finset.mem_filter.mp hDel).2]⟩
    · rcases Finset.mem_image.mp hCon with ⟨X, hXf, hYX⟩
      refine Finset.mem_image.mpr ?_
      exact ⟨X, (Finset.mem_filter.mp hXf).1, hYX⟩

lemma Tr_eq_Del_union_Con
  (u : α) (C : Finset (Finset α)) :
  Tr (α := α) u C = Del (α := α) u C ∪ Con (α := α) u C := by
  classical
  ext Y
  simpa [Finset.mem_union] using (mem_Tr_iff_mem_Del_or_mem_Con (α := α) u C Y)

lemma PairTr_eq_Del_inter_Con
  (u : α) (C : Finset (Finset α)) :
  PairTr (α := α) u C = Del (α := α) u C ∩ Con (α := α) u C := by
  classical
  ext Y
  constructor
  · intro hY
    have hPair := (mem_PairTr_iff (α := α) u C Y).1 hY
    rcases hPair with ⟨hYC, huY, hYcup⟩
    refine Finset.mem_inter.mpr ?_
    refine ⟨Finset.mem_filter.mpr ⟨hYC, huY⟩, ?_⟩
    exact (mem_Con_iff (α := α) u C Y).2 ⟨huY, hYcup⟩
  · intro hY
    rcases Finset.mem_inter.mp hY with ⟨hDel, hCon⟩
    have hYC : Y ∈ C := (Finset.mem_filter.mp hDel).1
    have huY : u ∉ Y := (Finset.mem_filter.mp hDel).2
    have hYcup : (Y ∪ {u} : Finset α) ∈ C := (mem_Con_iff (α := α) u C Y).1 hCon |>.2
    exact (mem_PairTr_iff (α := α) u C Y).2 ⟨hYC, huY, hYcup⟩

lemma NDS_Tr_add_NDS_PairTr_eq_NDS_Del_add_NDS_Con
  (n : Nat) (u : α) (C : Finset (Finset α)) :
  NDS (α := α) n (Tr (α := α) u C) + NDS (α := α) n (PairTr (α := α) u C)
    = NDS (α := α) n (Del (α := α) u C) + NDS (α := α) n (Con (α := α) u C) := by
  classical
  have hTr : Tr (α := α) u C = Del (α := α) u C ∪ Con (α := α) u C :=
    Tr_eq_Del_union_Con (α := α) u C
  have hPair : PairTr (α := α) u C = Del (α := α) u C ∩ Con (α := α) u C :=
    PairTr_eq_Del_inter_Con (α := α) u C
  rw [hTr, hPair]
  simpa [NDS, add_comm, add_left_comm, add_assoc] using
    (Finset.sum_union_inter
      (s₁ := Del (α := α) u C)
      (s₂ := Con (α := α) u C)
      (f := fun X : Finset α => w (α := α) n X))

theorem TRACE_ID
  (n : Nat) (hn : 1 ≤ n) (C : Finset (Finset α)) (u : α) :
  NDS (α := α) n C
    =
  NDS (α := α) (n - 1) (Tr (α := α) u C)
    +
  NDS (α := α) (n - 1) (PairTr (α := α) u C)
    +
  ndeg (α := α) C u := by
  have hConId := CON_ID (α := α) (n := n) (hn := hn) (C := C) (u := u)
  have hTracePart :=
    NDS_Tr_add_NDS_PairTr_eq_NDS_Del_add_NDS_Con
      (α := α) (n := n - 1) (u := u) (C := C)
  linarith [hConId, hTracePart]

end Accounting
end Dr1nds
