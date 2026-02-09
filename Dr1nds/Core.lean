import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Function
import LeanCopilot

import Dr1nds.Accounting  -- w / NDS / deg / ndeg をここから使う（あなたの既存設計）

namespace Dr1nds

open Finset
open Set

variable {α : Type} [DecidableEq α]

/- ============================================================
  0. General Horn system (multiple rules per head), NF built-in
============================================================ -/

/--
A general Horn rule system over `α`.

For each head `h : α`, we store a finite set of premises `prem h : Finset (Finset α)`.
So we allow multiple rules with the same head.

NF (no self-premise) is built into the structure:
  for every rule P -> h, we have h ∉ P.
-/
structure HornNF (α : Type) [DecidableEq α] where
  prem : α → Finset (Finset α)
  nf : ∀ (h : α) (P : Finset α), P ∈ prem h → h ∉ P

attribute [simp] HornNF.nf

namespace HornNF

variable (R : HornNF α)

/-- DR1 predicate: each head has at most one rule (premise). -/
def IsDR1 : Prop :=
  ∀ h : α, (R.prem h).card ≤ 1

/-- NEP predicate: no empty-premise rules. -/
def IsNEP : Prop :=
  ∀ h : α, (∅ : Finset α) ∉ R.prem h

end HornNF


/- ============================================================
  1. Closedness predicate induced by Horn rules
============================================================ -/

/--
`IsClosed R X` means: X is closed under all Horn rules of R.
I.e. whenever a rule P -> h exists and P ⊆ X, then h ∈ X.
-/
def IsClosed (R : HornNF α) (X : Finset α) : Prop :=
  ∀ (h : α) (P : Finset α), P ∈ R.prem h → P ⊆ X → h ∈ X

/--
`HornOn R U` is the "well-scoped rules" condition relative to a universe `U`:

- every rule head lies in `U`
- every premise lies in `U`

This is NOT built into `HornNF`; we keep it as an explicit assumption when needed
(e.g. to prove `U` is Closed, or to keep `Fix` nonempty).
-/
def HornOn (R : HornNF α) (U : Finset α) : Prop :=
  ∀ (h : α) (P : Finset α), P ∈ R.prem h → (h ∈ U ∧ P ⊆ U)


/- ============================================================
  2. FixFamily object (closed family packaged with spec)
============================================================ -/

/--
`FixFamily R U` packages a family `C : Finset (Finset α)` intended to be
the closed sets inside a universe `U`, characterized by:

  X ∈ C  ↔  (X ⊆ U) ∧ IsClosed R X.

We do NOT compute closure here; we only keep this specification.
-/
structure FixFamily (R : HornNF α) (U : Finset α) where
  C : Finset (Finset α)
  mem_iff : ∀ X : Finset α, X ∈ C ↔ (X ⊆ U ∧ IsClosed (α := α) R X)

namespace FixFamily

variable {R : HornNF α} {U : Finset α} (F : FixFamily (α := α) R U)

theorem mem_iff' (X : Finset α) :
    X ∈ F.C ↔ (X ⊆ U ∧ IsClosed (α := α) R X) :=
  F.mem_iff X

/--
Intersection-closure of `IsClosed` (no universe assumption needed):
if X and Y are closed then X∩Y is closed.
-/
lemma isClosed_inter {X Y : Finset α} :
    IsClosed (α := α) R X → IsClosed (α := α) R Y →
    IsClosed (α := α) R (X ∩ Y) := by
  intro hX hY h P hP hPXY
  have hPX : P ⊆ X := by
    intro x hx
    have : x ∈ X ∩ Y := hPXY hx
    exact (mem_inter.mp this).1
  have hPY : P ⊆ Y := by
    intro x hx
    have : x ∈ X ∩ Y := hPXY hx
    exact (mem_inter.mp this).2
  have hx : h ∈ X := hX h P hP hPX
  have hy : h ∈ Y := hY h P hP hPY
  exact mem_inter.mpr ⟨hx, hy⟩

/--
If rules are well-scoped in U (`HornOn R U`), then `U` is closed.
This is the lemma you want for CF-univ on Fix families.
-/
lemma isClosed_univ (hOn : HornOn (α := α) R U) :
    IsClosed (α := α) R U := by
  intro h P hP hPU
  exact (hOn h P hP).1

/--
CF-univ for FixFamily, assuming `HornOn R U`.
-/
lemma mem_univ (hOn : HornOn (α := α) R U) :
    U ∈ F.C := by
  refine (F.mem_iff' (R := R) (U := U) U).2 ?_
  refine ⟨subset_rfl, isClosed_univ (R := R) (U := U) hOn⟩

/--
CF-inter for FixFamily: membership is closed under `∩`.
-/
lemma mem_inter {X Y : Finset α} :
    X ∈ F.C → Y ∈ F.C → (X ∩ Y) ∈ F.C := by
  intro hX hY
  rcases (F.mem_iff' (R := R) (U := U) X).1 hX with ⟨hXU, hXC⟩
  rcases (F.mem_iff' (R := R) (U := U) Y).1 hY with ⟨hYU, hYC⟩
  refine (F.mem_iff' (R := R) (U := U) (X ∩ Y)).2 ?_
  refine ⟨?_, isClosed_inter (R := R) hXC hYC⟩
  intro x hx
  have hxX : x ∈ X := by simp_all only [Finset.mem_inter]
  exact hXU hxX

end FixFamily


/- ============================================================
  3. Basic operations on families: Del / con (set-image)
============================================================ -/

/--
Deletion: Del_u(C) = { X∈C | u∉X }.
-/
def Del (u : α) (C : Finset (Finset α)) : Finset (Finset α) :=
  C.filter (fun X => u ∉ X)

/--
Contraction-image (set-level, duplicates removed):
con_u(C) = { X.erase u | X∈C and u∈X }.
-/
def con (u : α) (C : Finset (Finset α)) : Finset (Finset α) :=
  (C.filter (fun X => u ∈ X)).image (fun X => X.erase u)

/--
Key technical lemma for the "set-image contraction" style:
`erase u` is injective on the domain `{X | u ∈ X}`.

This is the engine behind:
- `card (con u C) = deg_C(u)` (when you rewrite deg as a filter-card)
- the "no collision" accounting steps in S1/S6 style arguments
-/
lemma erase_injOn (u : α) :
    Set.InjOn (fun X : Finset α => X.erase u) {X | u ∈ X} := by
  intro X hX Y hY hEq
  ext a
  by_cases ha : a = u
  · subst ha
    simp_all only [mem_setOf_eq]

  · -- for a≠u, membership in `erase u` is equivalent to membership in the original set
    have : (a ∈ X.erase u) = (a ∈ Y.erase u) := by
      simp [hEq]
    simpa [Finset.mem_erase, ha] using this

end Dr1nds
