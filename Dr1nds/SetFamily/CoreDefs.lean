-- Dr1nds/S0_CoreDefs.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import LeanCopilot

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/- ============================================================
  S0 : Core Definitions (FROZEN)
  This file contains ONLY definitions.
  No lemmas, no proofs.
============================================================ -/

/- ------------------------------------------------------------
  0. Weight / NDS (accounting base)
------------------------------------------------------------ -/

/-- weight: w_n(X) = 2|X| - n -/
def w (n : Nat) (X : Finset α) : Int :=
  (2 : Int) * (X.card : Int) - (n : Int)

/-- NDS_n(C) = Σ_{X∈C} w_n(X) -/
def NDS (n : Nat) (C : Finset (Finset α)) : Int :=
  ∑ X ∈ C, w (α := α) n X


/- ------------------------------------------------------------
  1. Degree / normalized degree
------------------------------------------------------------ -/

/-- deg_C(u) = #{ X∈C | u∈X } -/
def deg (C : Finset (Finset α)) (u : α) : Nat :=
  (C.filter (fun X => u ∈ X)).card

/-- ndeg_C(u) = 2*deg_C(u) - |C| -/
def ndeg (C : Finset (Finset α)) (u : α) : Int :=
  (2 : Int) * (deg (α := α) C u : Int) - (C.card : Int)


/- ------------------------------------------------------------
  2. Basic family operations (IMAGE ROUTE)
------------------------------------------------------------ -/

/--
Deletion:
  Del_u(C) = { X∈C | u∉X }

Note:
  Del_u(C) is NOT assumed to be a closure system.
-/
def Del (u : α) (C : Finset (Finset α)) : Finset (Finset α) :=
  C.filter (fun X => u ∉ X)

/--
Trace (PROJECT TRACE):
  Tr_u(C) = { X.erase u | X∈C }

This is the image of *all* closed sets under erasing u.
-/
def Tr (u : α) (C : Finset (Finset α)) : Finset (Finset α) :=
  C.image (fun X => X.erase u)


/--
Contraction (RESTRICTED TRACE):
  con_u(C) = { X.erase u | X∈C ∧ u∈X }

IMPORTANT:
  - image-level (duplicates are merged)
  - this is NOT the same as Tr_u
-/
def Con (u : α) (C : Finset (Finset α)) : Finset (Finset α) :=
  (C.filter (fun X => u ∈ X)).image (fun X => X.erase u)



/- ------------------------------------------------------------
  5. Design notes (FROZEN INTENT)
------------------------------------------------------------ -/
/-
  * Del_u(C) is not closed → always handled via Hole(Del_u(C), A)
  * Tr_u(C) and con_u(C) are DISTINCT:
      Tr_u : erase-image of all sets
      con_u: erase-image of sets containing u
  * forbid is always represented as Hole(C,A)
  * NO closure operator, NO fold, NO implicit completion
-/

end Dr1nds
