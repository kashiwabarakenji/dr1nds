import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

import Dr1nds.Accounting  -- w / NDS / deg / ndeg をここから使う

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ============================================================
  0. General Horn system (Premises per head), NF built-in
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

end Dr1nds
