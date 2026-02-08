import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import LeanCopilot

import Dr1nds.Core
import Dr1nds.Accounting

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
con / Del と NDS の恒等式（CON_ID）

con_u(C)  := { X\{u} | X∈C, u∈X }
Del_u(C)  := { X∈C | u∉X }

CON_ID:
  NDS_n(C)
    = NDS_{n-1}(con_u(C)) + NDS_{n-1}(Del_u(C)) + ndeg_C(u)
-/

/- 定義はCoreにある。 con_u(C) := image erase over sets containing u -/
--def con (u : α) (C : Finset (Finset α)) : Finset (Finset α) :=
--  (C.filter (fun X => u ∈ X)).image (fun X => X.erase u)

/- Del_u(C) := filter out sets not containing u -/
--def Del (u : α) (C : Finset (Finset α)) : Finset (Finset α) :=
--  C.filter (fun X => u ∉ X)

/- ------------------------------------------------------------
  Basic weight transforms
------------------------------------------------------------ -/

/-- If u∈X, then w_n(X) = w_{n-1}(X\{u}) + 1. -/
lemma w_of_mem_erase
  (n : Nat) (hn : 1 ≤ n) (u : α) (X : Finset α) (hu : u ∈ X) :
  w (α := α) n X = w (α := α) (n - 1) (X.erase u) + 1 := by
  -- w n X = 2|X| - n
  -- card (erase) = card X - 1
  have hcard : (X.erase u).card = X.card - 1 := by
    exact Finset.card_erase_of_mem hu
  -- Int 化して計算
  unfold w
  -- `Nat.succ_le_iff` 等で n-1 が Nat であることは hn で保証される
  -- ここは単純な環計算
  -- 2|X| - n = 2(|X|-1) - (n-1) + 1
  -- ring で押す
  -- まず hcard を Int に持ち上げる
  have hcardInt : ((X.erase u).card : Int) = (X.card : Int) - 1 := by
    -- Nat の引き算を Int に
    -- hcard : (erase).card = card - 1 (Nat)
    -- 右辺は Nat なので Int にするときは `Int.ofNat` が入る
    -- simp が面倒なので `zify` を使う
    -- ここは simp で十分
    -- 注意: (X.card - 1 : Nat) を Int 化すると (X.card : Int) - 1 に simp できる
    let ca := congrArg (fun t : Nat => (t : Int)) hcard
    simp [hcard]
    have : X.card ≥ 1 := by
      simp_all only [ge_iff_le, Finset.one_le_card]
      exact ⟨u, hu⟩
    simp_all only [ge_iff_le, Finset.one_le_card, Nat.cast_sub, Nat.cast_one]
  -- ここからは ring
  -- w n X = 2*|X| - n
  -- RHS = (2*|erase| - (n-1)) + 1
  --     = 2*(|X|-1) - (n-1) + 1
  --     = 2|X| - 2 - n + 1 + 1
  --     = 2|X| - n
  -- simp/ring
  -- 先に (X.erase u).card を置換
  simp [hcardInt, hn, Int.sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  ring

omit [DecidableEq α] in
/-- If u∉X, then w_n(X) = w_{n-1}(X) - 1. -/
lemma w_of_not_mem
  (n : Nat) (hn : 1 ≤ n) (u : α) (X : Finset α) (_ : u ∉ X) :
  w (α := α) n X = w (α := α) (n - 1) X - 1 := by
  -- u∉X ⇒ erase しても card は変わらないが、ここは erase を使わない形にする
  unfold w
  -- 2|X| - n = (2|X| - (n-1)) - 1
  -- ring で終わる
  have : (n : Int) = ((n - 1 : Nat) : Int) + 1 := by
    -- hn : 1 ≤ n なので n = (n-1)+1
    have hn' : n = (n - 1) + 1 := by simp_all only [Nat.sub_add_cancel]--
    -- Int 化
    let ca := congrArg (fun t : Nat => (t : Int)) hn'
    exact ca
  -- 代入して ring
  simp [this, Int.sub_eq_add_neg]
  ring

/- ------------------------------------------------------------
  Filter partition lemmas for Cu/Du
------------------------------------------------------------ -/

private lemma disjoint_filter_contains_not
  (C : Finset (Finset α)) (u : α) :
  Disjoint (C.filter (fun X => u ∈ X)) (C.filter (fun X => u ∉ X)) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro X h1 h2
  have hu1 : u ∈ X := (Finset.mem_filter.1 h1).2
  have hu2 : u ∉ X := (Finset.mem_filter.1 h2).2
  exact hu2 hu1

private lemma union_filter_contains_not
  (C : Finset (Finset α)) (u : α) :
  (C.filter (fun X => u ∈ X)) ∪ (C.filter (fun X => u ∉ X)) = C := by
  classical
  ext X
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact (Finset.mem_filter.1 h).1
    · exact (Finset.mem_filter.1 h).1
  · intro hXC
    by_cases hu : u ∈ X
    · simp_all only [Finset.mem_union, Finset.mem_filter, and_self, not_true_eq_false, and_false, or_false]
    · simp_all only [Finset.mem_union, Finset.mem_filter, and_false, not_false_eq_true, and_self, or_true]

/-- Card partition: |C| = |Cu| + |Du| -/
private lemma card_filter_contains_add_card_filter_not
  (C : Finset (Finset α)) (u : α) :
  (C.filter (fun X => u ∈ X)).card + (C.filter (fun X => u ∉ X)).card = C.card := by
  classical
  have hdisj := disjoint_filter_contains_not (α := α) C u
  have hunion := union_filter_contains_not (α := α) C u
  -- card_union_of_disjoint : card (s ∪ t) = card s + card t
  have hcard := Finset.card_union_of_disjoint hdisj
  -- rewrite union = C
  -- hcard : (Cu ∪ Du).card = Cu.card + Du.card
  -- so Cu.card + Du.card = C.card
  -- by simp [hunion] at hcard? careful:
  have : ((C.filter (fun X => u ∈ X)) ∪ (C.filter (fun X => u ∉ X))).card
        = (C.filter (fun X => u ∈ X)).card + (C.filter (fun X => u ∉ X)).card := hcard
  -- replace union by C
  simpa [hunion] using this.symm

/- ------------------------------------------------------------
  Injectivity of erase on sets containing u
------------------------------------------------------------ -/

private lemma erase_injOn_on_contains
  (u : α) (Cu : Finset (Finset α)) :
  Set.InjOn (fun X : Finset α => X.erase u) {X : Finset α | X ∈ Cu ∧ u ∈ X} := by
  intro X hX Y hY hEq
  -- if u∈X and u∈Y and erase u equal, then X = Y
  -- because X = insert u (X.erase u)
  have huX : u ∈ X := hX.2
  have huY : u ∈ Y := hY.2
  -- use ext
  ext a
  by_cases ha : a = u
  · subst ha
    simp [huX, huY]
  · -- a ≠ u
    have : a ∈ X.erase u ↔ a ∈ Y.erase u := by simp [hEq]
    -- membership in erase for a≠u
    simpa [Finset.mem_erase, ha] using this

/- ------------------------------------------------------------
  Main identity: CON_ID
------------------------------------------------------------ -/

theorem CON_ID
    (n : Nat) (hn : 1 ≤ n) (C : Finset (Finset α)) (u : α) :
    NDS (α := α) n C
      =
    NDS (α := α) (n - 1) (con (α := α) u C)
      +
    NDS (α := α) (n - 1) (Del (α := α) u C)
      +
    ndeg (α := α) C u := by
  classical
  -- abbreviations
  set Cu : Finset (Finset α) := C.filter (fun X => u ∈ X)
  set Du : Finset (Finset α) := C.filter (fun X => u ∉ X)

  -- rewrite NDS n C by partitioning C into Cu and Du
  have hcardSum : Cu.card + Du.card = C.card := by
    simpa [Cu, Du] using card_filter_contains_add_card_filter_not (α := α) C u

  -- Part A: sum over Cu
  have hA :
      (∑ X ∈ Cu, w (α := α) n X)
        =
      NDS (α := α) (n - 1) (con (α := α) u C) + (Cu.card : Int) := by
    -- rewrite each term using w_of_mem_erase
    have hw :
        (∑ X ∈ Cu, w (α := α) n X)
          =
        (∑ X ∈ Cu, (w (α := α) (n - 1) (X.erase u) + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro X hX
      have huX : u ∈ X := (Finset.mem_filter.1 hX).2
      simp [w_of_mem_erase (α := α) (n := n) (hn := hn) (u := u) (X := X) huX]
    -- separate +1
    have hsep :
        (∑ X ∈ Cu, (w (α := α) (n - 1) (X.erase u) + 1))
          =
        (∑ X ∈ Cu, w (α := α) (n - 1) (X.erase u)) + (Cu.card : Int) := by
      calc
        (∑ X ∈ Cu, (w (α := α) (n - 1) (X.erase u) + 1))
            =
          (∑ X ∈ Cu, w (α := α) (n - 1) (X.erase u))
            + (∑ X ∈ Cu, (1 : Int)) := by
              simp [Finset.sum_add_distrib]
        _ = (∑ X ∈ Cu, w (α := α) (n - 1) (X.erase u)) + (Cu.card : Int) := by
              simp
    -- convert sum over erase to sum over image (= con)
    have hcon : con (α := α) u C = Cu.image (fun X => X.erase u) := by
      rfl
    -- use sum_image with injOn on Cu (erase is injective on sets containing u)
    have hinj :
        Set.InjOn (fun X : Finset α => X.erase u) {X : Finset α | X ∈ Cu} := by
      intro X hX Y hY hEq
      -- from membership in Cu we get u∈X, u∈Y
      have huX : u ∈ X := (Finset.mem_filter.1 hX).2
      have huY : u ∈ Y := (Finset.mem_filter.1 hY).2
      -- same ext proof as earlier
      ext a
      by_cases ha : a = u
      · subst ha; simp [huX, huY]
      · have : a ∈ X.erase u ↔ a ∈ Y.erase u := by simp [hEq]
        simpa [Finset.mem_erase, ha] using this
    have himage :
        (∑ Y ∈ (Cu.image (fun X => X.erase u)), w (α := α) (n - 1) Y)
          =
        (∑ X ∈ Cu, w (α := α) (n - 1) (X.erase u)) := by
      -- Finset.sum_image needs an injOn lemma expressed on membership
      -- We can use simp form of sum_image
      -- Direction depends; we want LHS = RHS
      classical
      simp_all only [Finset.mem_filter, Finset.coe_filter, Finset.sum_image, Cu, Du]

    -- assemble
    calc
      (∑ X ∈ Cu, w (α := α) n X)
          =
        (∑ X ∈ Cu, (w (α := α) (n - 1) (X.erase u) + 1)) := by
          exact hw
      _ =
        (∑ X ∈ Cu, w (α := α) (n - 1) (X.erase u)) + (Cu.card : Int) := by
          exact hsep
      _ =
        (∑ Y ∈ (Cu.image (fun X => X.erase u)), w (α := α) (n - 1) Y) + (Cu.card : Int) := by
          rw [himage]
      _ =
        NDS (α := α) (n - 1) (con (α := α) u C) + (Cu.card : Int) := by
          simp [NDS, hcon]

  -- Part B: sum over Du
  have hB :
      (∑ X ∈ Du, w (α := α) n X)
        =
      NDS (α := α) (n - 1) (Del (α := α) u C) - (Du.card : Int) := by
    have hw :
        (∑ X ∈ Du, w (α := α) n X)
          =
        (∑ X ∈ Du, (w (α := α) (n - 1) X - 1)) := by
      refine Finset.sum_congr rfl ?_
      intro X hX
      have huX : u ∉ X := (Finset.mem_filter.1 hX).2
      simp [w_of_not_mem (α := α) (n := n) (hn := hn) (u := u) (X := X) huX]
    have hsep :
        (∑ X ∈ Du, (w (α := α) (n - 1) X - 1))
          =
        (∑ X ∈ Du, w (α := α) (n - 1) X) - (Du.card : Int) := by
      calc
        (∑ X ∈ Du, (w (α := α) (n - 1) X - 1))
            =
          (∑ X ∈ Du, w (α := α) (n - 1) X) - (∑ X ∈ Du, (1 : Int)) := by
            simp [Finset.sum_sub_distrib]
        _ = (∑ X ∈ Du, w (α := α) (n - 1) X) - (Du.card : Int) := by
            simp
    have hdel : Del (α := α) u C = Du := by
      rfl
    calc
      (∑ X ∈ Du, w (α := α) n X)
          =
        (∑ X ∈ Du, (w (α := α) (n - 1) X - 1)) := by exact hw
      _ =
        (∑ X ∈ Du, w (α := α) (n - 1) X) - (Du.card : Int) := by exact hsep
      _ =
        NDS (α := α) (n - 1) (Del (α := α) u C) - (Du.card : Int) := by
          simp [NDS, hdel]

  -- card difference equals ndeg
  have hcard :
      (Cu.card : Int) - (Du.card : Int) = ndeg (α := α) C u := by
    -- deg C u = Cu.card
    -- ndeg = 2*deg - |C|, and |C| = Cu+Du
    have hsumInt : (C.card : Int) = (Cu.card : Int) + (Du.card : Int) := by
      -- from Nat equality hcardSum
      have := congrArg (fun t : Nat => (t : Int)) hcardSum
      -- (a+b : Nat) coerces to Int as (a:Int)+(b:Int)
      simp_all only [Cu, Du]
      rw [← Nat.cast_add, hcardSum]
    unfold ndeg deg
    -- deg C u is (C.filter ...).card = Cu.card
    -- so show: Cu - Du = 2*Cu - C
    -- and rewrite C using hsumInt
    calc
      (Cu.card : Int) - (Du.card : Int)
          =
        (2 * (Cu.card : Int)) - ((Cu.card : Int) + (Du.card : Int)) := by ring
      _ =
        (2 * (Cu.card : Int)) - (C.card : Int) := by
          -- replace (Cu+Du) with C
          simp [hsumInt]
      _ =
        (2 : Int) * ((C.filter (fun X => u ∈ X)).card : Int) - (C.card : Int) := by
          simp [Cu]
      _ = ndeg (α := α) C u := by
          rfl

  -- Finally assemble NDS
  -- NDS n C = sum over Cu + sum over Du
  have hsplit :
      NDS (α := α) n C
        =
      (∑ X ∈ Cu, w (α := α) n X) + (∑ X ∈ Du, w (α := α) n X) := by
    -- use union partition
    -- C = Cu ∪ Du and disjoint
    have hdisj := disjoint_filter_contains_not (α := α) C u
    have hunion := union_filter_contains_not (α := α) C u
    -- sum over union of disjoint = sum + sum
    -- NDS is sum over C
    unfold NDS
    -- rewrite C as union, then use sum_union
    -- sum_union needs disjoint and g respects membership
    -- easiest: use `by` with `simp [hunion]` after rewriting
    -- We'll do: sum over C = sum over union = sum+sum
    -- Note: `Finset.sum_union` exists for disjoint
    calc
      (∑ X ∈ C, w (α := α) n X)
          =
        (∑ X ∈ (Cu ∪ Du), w (α := α) n X) := by
          simp_all only [Cu, Du]
      _ =
        (∑ X ∈ Cu, w (α := α) n X) + (∑ X ∈ Du, w (α := α) n X) := by
          simpa using (Finset.sum_union hdisj)

  -- now rewrite using hA, hB, hcard
  calc
    NDS (α := α) n C
        =
      (∑ X ∈ Cu, w (α := α) n X) + (∑ X ∈ Du, w (α := α) n X) := by
          exact hsplit
    _ =
      (NDS (α := α) (n - 1) (con (α := α) u C) + (Cu.card : Int))
        +
      (NDS (α := α) (n - 1) (Del (α := α) u C) - (Du.card : Int)) := by
          rw [hA, hB]
    _ =
      NDS (α := α) (n - 1) (con (α := α) u C)
        +
      NDS (α := α) (n - 1) (Del (α := α) u C)
        +
      ((Cu.card : Int) - (Du.card : Int)) := by
          ring
    _ =
      NDS (α := α) (n - 1) (con (α := α) u C)
        +
      NDS (α := α) (n - 1) (Del (α := α) u C)
        +
      ndeg (α := α) C u := by
          simp [hcard]

end Dr1nds
