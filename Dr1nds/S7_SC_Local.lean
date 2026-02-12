-- Dr1nds/S7_SC_Local.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S1_Families
import Dr1nds.S6_ConDelNdegId  -- Accounting.CON_ID を使う側になるので依存を固定

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

open SetFamily

/- ============================================================
  S7 : Local inequality at an SC point (FROZEN I/O, skeleton)
  Policy:
    * base defs: S0_CoreDefs
    * no global Horn/DR1 assumptions here (pure family-level lemma)
    * provide only the exact I/O used by S10/Q-step and T-step
============================================================ -/

namespace S7

/- ------------------------------------------------------------
  0. SC predicate (family-level)
------------------------------------------------------------ -/

/- SC point in a family C: singleton {s} is in C. -/
--def SC (C : Finset (Finset α)) (s : α) : Prop :=
--  ({s} : Finset α) ∈ C

--omit [DecidableEq α] in
--@[simp] lemma SC_iff (C : Finset (Finset α)) (s : α) :
--  SC (α := α) C s ↔ ({s} : Finset α) ∈ C := by
--  rfl

/- ------------------------------------------------------------
  1. The local target inequality (the exact shape used downstream)
------------------------------------------------------------ -/

/--
(Local-SC inequality, frozen shape)

Let D := Hole(C,A). If s is SC in the *base* family C, then
the local term at s in the deletion-world is ≤ 0:

  NDS_{n-1}(Del_s(D)) + ndeg_D(s) ≤ 0

This is the UC-S7 entry in your S11 list.
-/
axiom local_SC_del_ndeg_le_zero
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α) :
  (2 ≤ A.card) →
  SC F s →
  (NDS (n - 1) (Del s (Hole F.C A))
      +
    ndeg (Hole F.C A) s
  ≤ 0)

/- ------------------------------------------------------------
  2. Convenience wrappers (to reduce rewriting noise)
------------------------------------------------------------ -/

/-- A named abbreviation for D := Hole(C,A). -/
def D (F : SetFamily α) (A : Finset α) : Finset (Finset α) :=
  Hole F.C A

/-- Same inequality, written with D := Hole(C,A). -/
lemma local_SC_del_ndeg_le_zero'
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α)
  (hA : 2 ≤ A.card)
  (hSC : SC F s) :
  (NDS (n - 1) (Del s (D F A))
      +
    ndeg (D F A) s
  ≤ 0) := by
  -- purely a wrapper
  simpa [D] using local_SC_del_ndeg_le_zero n F A s hA hSC

/- ------------------------------------------------------------
  3. Projected bounds used by forbid-step (still skeleton)
------------------------------------------------------------ -/

/--
If `s` is an SC point (in the base family `C`), then the *ndeg* term in the hole family is non-positive.

This is exported as a standalone bound because the forbid-step splits the local inequality.
-/
axiom local_SC_ndeg_hole_le_zero
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α) :
  (2 ≤ A.card) →
  SC F s →
  ndeg (Hole F.C A) s ≤ 0

/--
If `s` is an SC point (in the base family `C`), then the *Del-branch* term in the hole family is non-positive.

Kept separate because S10/S11 often call it without rewriting the full local inequality.
-/
axiom local_SC_Del_hole_bound
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α) :
  (2 ≤ A.card) →
  SC F s →
  NDS (n - 1) (Del s (Hole F.C A)) ≤ 0

/-- Same as `local_SC_Del_hole_bound`, written with `D := Hole(C,A)` to reduce rewriting noise. -/
lemma local_SC_Del_D_bound'
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α)
  (hA : 2 ≤ A.card)
  (hSC : SC F s) :
  NDS (n - 1) (Del s (D F A)) ≤ 0 := by
  simpa [D] using local_SC_Del_hole_bound n F A s hA hSC

end S7

end Dr1nds
