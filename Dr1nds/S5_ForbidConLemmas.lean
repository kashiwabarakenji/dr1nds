-- Dr1nds/S5_ForbidConLemmas.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S6_ConDelNdegId  -- erase_injOn / erase_inj_on_mem など（会計核側に一本化）

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

/--
Main equivalence used everywhere:
  (A.erase v ⊆ X.erase v) ↔ (A ⊆ X)
assuming v∈A and v∈X.

This is frozen as an interface lemma; proof will be filled later.
-/
axiom erase_subset_erase_iff (A X : Finset α) (v : α) (hvA : v ∈ A) (hvX : v ∈ X) :
    (A.erase v ⊆ X.erase v) ↔ (A ⊆ X)

/- ------------------------------------------------------------
  2. Commutation of Up/Hole with con
------------------------------------------------------------ -/

/--
Under v∈A:
  con_v(Up(C,A)) = Up(con_v(C), A.erase v)

Frozen as an interface lemma; proof will be filled later.
-/
axiom con_Up_eq_Up_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    con (α := α) v (Up (α := α) C A)
      =
    Up (α := α) (con (α := α) v C) (A.erase v)

/--
Under v∈A:
  con_v(Hole(C,A)) = Hole(con_v(C), A.erase v)

Frozen as an interface lemma; proof will be filled later.
-/
axiom con_Hole_eq_Hole_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    con (α := α) v (Hole (α := α) C A)
      =
    Hole (α := α) (con (α := α) v C) (A.erase v)

/- ------------------------------------------------------------
  3. Card transfer of Up under con (v∈A)
------------------------------------------------------------ -/

/--
Under v∈A:
  card(Up(C,A)) = card(Up(con_v(C), A.erase v))

Frozen as an interface lemma; proof will be filled later.
-/
axiom card_Up_eq_card_Up_con
    (C : Finset (Finset α)) (A : Finset α) (v : α) (hvA : v ∈ A) :
    (Up (α := α) C A).card
      =
    (Up (α := α) (con (α := α) v C) (A.erase v)).card

/- ------------------------------------------------------------
  4. Corrected CON identity skeleton (the shape used in Q-step)
------------------------------------------------------------ -/

/--
(CON_ID_corr - skeleton form)

This packages the two rewrites:
  con(Hole) = Hole(con) and |Up| preserved,
so that after applying CON_ID to D := Hole(C,A),
the RHS can be rewritten to involve NDS_corr (n-1) (con v C) (A.erase v)
plus the remaining Del/ndeg term over Hole(C,A).

Note: this is the *shape* needed by S10/Q-step.
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
