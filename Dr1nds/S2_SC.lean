/-
S2_SC.lean

Purpose:
--------
Define Singleton-Closed (SC) points.

New framework (C-based):
  SC C v :≡ {v} ∈ C

This file is intentionally minimal:
- no Prem
- no cl / Reach / Parallel
- no axioms
- just the definition + tiny interface lemmas

S3_NoParallel_SC.lean imports this file and proves existence of SC
under NoParallel (in that file).
-/

import Mathlib.Data.Finset.Basic

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-- Singleton-Closed point (C-based): the singleton `{v}` belongs to the family `C`. -/
def SC (C : Finset (Finset α)) (v : α) : Prop :=
  ({v} : Finset α) ∈ C

/-- Unfolding lemma for `SC`. -/
@[simp] lemma SC_def (C : Finset (Finset α)) (v : α) :
  SC (α := α) C v ↔ (({v} : Finset α) ∈ C) := by
  rfl

/-- Convenience: if `{v} ∈ C` then `SC C v`. -/
lemma SC_of_mem {C : Finset (Finset α)} {v : α}
  (h : ({v} : Finset α) ∈ C) : SC (α := α) C v := by
  exact h

/-- Convenience: if `SC C v` then `{v} ∈ C`. -/
lemma mem_of_SC {C : Finset (Finset α)} {v : α}
  (h : SC (α := α) C v) : ({v} : Finset α) ∈ C := by
  exact h

end Dr1nds
