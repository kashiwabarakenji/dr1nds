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

/- ============================================================
  0. Tiny accounting lemmas about w
============================================================ -/

/-- succ shift: w (n+1) X = w n X - 1 -/
lemma w_succ (n : Nat) (X : Finset α) :
    w (α := α) n.succ X = w (α := α) n X - 1 := by
  sorry

/--
If u∈X and n≥1, then
  w n X = w (n-1) (X.erase u) + 1
This is the “membership part” used in CON_ID.
-/
lemma w_of_mem_erase
  (n : Nat) (hn : 1 ≤ n) (u : α) (X : Finset α) (hu : u ∈ X) :
  w (α := α) n X = w (α := α) (n - 1) (X.erase u) + 1 := by
  sorry

/--
If u∉X and n≥1, then
  w n X = w (n-1) X - 1
This is the “non-membership part” used in CON_ID.
-/
lemma w_of_not_mem
  (n : Nat) (hn : 1 ≤ n) (u : α) (X : Finset α) (hu : u ∉ X) :
  w (α := α) n X = w (α := α) (n - 1) X - 1 := by
  sorry


/- ============================================================
  1. Partition lemmas (filter split)
============================================================ -/

/-- The two filters (u∈X) and (u∉X) are disjoint. -/
lemma disjoint_filter_mem_not_mem
  (C : Finset (Finset α)) (u : α) :
  Disjoint (C.filter (fun X => u ∈ X)) (C.filter (fun X => u ∉ X)) := by
  classical
  sorry

/-- Union of the two filters gives back C. -/
lemma union_filter_mem_not_mem
  (C : Finset (Finset α)) (u : α) :
  (C.filter (fun X => u ∈ X)) ∪ (C.filter (fun X => u ∉ X)) = C := by
  classical
  sorry

/-- Card partition: |C| = |{u∈X}| + |{u∉X}|. -/
lemma card_filter_mem_add_card_filter_not_mem
  (C : Finset (Finset α)) (u : α) :
  (C.filter (fun X => u ∈ X)).card + (C.filter (fun X => u ∉ X)).card = C.card := by
  classical
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
  -- typical proof: rewrite C as union, then Finset.sum_union with disjointness
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
  -- ext a; split a=u / a≠u
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
  -- uses card_filter_mem_add_card_filter_not_mem + rfl unfolding
  sorry

/--
Rewrite ndeg in the convenient "deg - DelCard" form:
  ndeg C u = (deg C u : Int) - (Del u C).card
-/
lemma ndeg_eq_deg_sub_card_Del (C : Finset (Finset α)) (u : α) :
    ndeg (α := α) C u = (deg (α := α) C u : Int) - ((Del (α := α) u C).card : Int) := by
  classical
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
  classical
  -- Strategy (later proof):
  -- 1) split sum over C into (u∈X) + (u∉X)
  -- 2) rewrite w terms using w_of_mem_erase / w_of_not_mem
  -- 3) convert sum over (u∈X) to sum over con-image using sum_image + injectivity
  -- 4) collect +1/-1 counts into ndeg via card_eq_deg_add_card_Del / ndeg_eq...
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
