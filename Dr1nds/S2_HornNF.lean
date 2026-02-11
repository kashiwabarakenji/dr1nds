-- Dr1nds/S2_HornNF.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Dr1nds.S1_HornDefs

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ============================================================
  S2 : HornNF (NORMAL FORM, DEFINITIONS ONLY)
  This file is FROZEN.
  No lemmas, no proofs.
============================================================ -/

/- ------------------------------------------------------------
  0. HornNF structure
------------------------------------------------------------ -/

/--
HornNF is a head-indexed normal form of Horn systems.

For each head h : α,
  prem h : Finset (Finset α)
is the (possibly empty) finite set of premises for rules with head h.
-/
structure HornNF (α : Type) [DecidableEq α] where
  prem : α → Finset (Finset α)


/- ------------------------------------------------------------
  1. Structural conditions on HornNF
------------------------------------------------------------ -/

/--
DR1 in HornNF:
For each head h, there is at most one premise.
-/
def HornNF.IsDR1 (H : HornNF α) : Prop :=
  ∀ h : α, (H.prem h).card ≤ 1

/--
NEP in HornNF:
No empty premise appears.
-/
def HornNF.IsNEP (H : HornNF α) : Prop :=
  ∀ {h : α}, (∅ : Finset α) ∉ H.prem h

/--
NF in HornNF:
Heads do not appear in their own premises.
-/
def HornNF.IsNF (H : HornNF α) : Prop :=
  ∀ {h : α} {P : Finset α}, P ∈ H.prem h → h ∉ P


/- ------------------------------------------------------------
  2. Closedness w.r.t. HornNF
------------------------------------------------------------ -/

/--
A set X is closed w.r.t. HornNF H iff
for every head h and premise P ∈ prem h,
  P ⊆ X ⇒ h ∈ X.
-/
def HornNF.IsClosed (H : HornNF α) (X : Finset α) : Prop :=
  ∀ {h : α} {P : Finset α},
    P ∈ H.prem h →
    P ⊆ X →
    h ∈ X

def HornNF.FixSet (H : HornNF α) (U : Finset α) : Set (Finset α) :=
  { X | X ⊆ U ∧ H.IsClosed X }

def HornNF.HornOn (H : HornNF α) (U : Finset α) : Prop :=
  ∀ (h : α) (P : Finset α), P ∈ H.prem h → (h ∈ U ∧ P ⊆ U)

def HornNF.PremOn (H : HornNF α) (U : Finset α) : Prop :=
  ∀ ⦃h : α⦄ ⦃P : Finset α⦄, P ∈ H.prem h → P ⊆ U

def HornNF.HeadOn (H : HornNF α) (U : Finset α) : Prop :=
  ∀ ⦃h : α⦄, (H.prem h).Nonempty → h ∈ U

/- ------------------------------------------------------------
  3. Conversion targets (placeholders only)
------------------------------------------------------------ -/

/--
Intended conversion:
Horn → HornNF (definition only, no properties asserted).
Actual construction lives in later files.
-/
def Horn.toHornNF (H : Horn α) : HornNF α :=
  { prem := fun _ => ∅ }

end Dr1nds
