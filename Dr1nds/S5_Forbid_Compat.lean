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
  S5 : Forbid compatibility (FROZEN I/O, skeleton)
  Policy:
    * base defs: S0_CoreDefs
    * forbid is always Hole(C,A) / Up(C,A) in the same base family C
    * we only freeze the rewriting interfaces needed by S10 (Q-step)
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
(ERASE-SUBSET kernel)

When v∈A and v∈X, we can recover A ⊆ X from (A.erase v) ⊆ (X.erase v), and conversely.

This is the algebraic core behind commuting con with Up/Hole.
-/
axiom erase_subset_erase_iff
  (A X : Finset α) (v : α) :
  v ∈ A → v ∈ X →
  (A.erase v ⊆ X.erase v) ↔ (A ⊆ X)

/--
con commutes with Up, under v∈A:

  con_v(Up(C,A)) = Up(con_v(C), A.erase v)
-/
axiom con_Up_eq_Up_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  con (α := α) v (Up (α := α) C A)
    =
  Up (α := α) (con (α := α) v C) (A.erase v)

/--
con commutes with Hole, under v∈A:

  con_v(Hole(C,A)) = Hole(con_v(C), A.erase v)
-/
axiom con_Hole_eq_Hole_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  con (α := α) v (Hole (α := α) C A)
    =
  Hole (α := α) (con (α := α) v C) (A.erase v)

/--
Card transport for Up, under v∈A:

  |Up(C,A)| = |Up(con_v(C), A.erase v)|
-/
axiom card_Up_eq_card_Up_con
  (C : Finset (Finset α)) (A : Finset α) (v : α) :
  v ∈ A →
  (Up (α := α) C A).card
    =
  (Up (α := α) (con (α := α) v C) (A.erase v)).card

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
