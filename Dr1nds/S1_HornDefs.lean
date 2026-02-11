-- Dr1nds/S1_HornDefs.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import LeanCopilot

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ============================================================
  S1 : Horn rule systems (DEFINITIONS ONLY)
  This file is FROZEN.
  No lemmas, no proofs, no automation.
============================================================ -/

/- ------------------------------------------------------------
  0. Horn rules
------------------------------------------------------------ -/

/--
A Horn rule is a pair (P, h):
  premise P : Finset α
  head     h : α
-/
abbrev Rule (α : Type) := Finset α × α

/--
A (finite) Horn rule system over α.
-/
structure Horn (α : Type) [DecidableEq α] where
  rules : Finset (Rule α)


/- ------------------------------------------------------------
  1. Structural conditions on Horn systems
------------------------------------------------------------ -/

/--
DR1 (unique head):
For each head h, there is at most one rule with head h.
-/
def Horn.DR1 (H : Horn α) : Prop :=
  ∀ {P₁ P₂ : Finset α} {h : α},
    (P₁, h) ∈ H.rules →
    (P₂, h) ∈ H.rules →
    P₁ = P₂

/--
NEP (non-empty premise):
No rule has empty premise.
-/
def Horn.NEP (H : Horn α) : Prop :=
  ∀ {P : Finset α} {h : α},
    (P, h) ∈ H.rules →
    P.Nonempty

/--
NF (no self-premise):
The head does not belong to its own premise.
-/
def Horn.NF (H : Horn α) : Prop :=
  ∀ {P : Finset α} {h : α},
    (P, h) ∈ H.rules →
    h ∉ P


/- ------------------------------------------------------------
  2. Closedness with respect to a Horn system
------------------------------------------------------------ -/

/--
A set X is closed w.r.t. a Horn system H iff
for every rule P → h,
  P ⊆ X ⇒ h ∈ X.
-/
def Horn.IsClosed (H : Horn α) (X : Finset α) : Prop :=
  ∀ {P : Finset α} {h : α},
    (P, h) ∈ H.rules →
    P ⊆ X →
    h ∈ X


/- ------------------------------------------------------------
  3. Head existence (used for premSet / premOpt later)
------------------------------------------------------------ -/

/--
There exists a rule with head h.
-/

def Horn.HasHead (H : Horn α) (h : α) : Prop :=
  ∃ P : Finset α, (P, h) ∈ H.rules

/--
Rule-level contraction at head x:
  - Remove rules whose head is x
  - For other rules (P, h), replace premise by P.erase x
-/
def Horn.contraction (H : Horn α) (x : α) : Horn α :=
{ rules :=
    (H.rules.filter (fun r => r.2 ≠ x)).image
      (fun r => (r.1.erase x, r.2)) }


end Dr1nds
