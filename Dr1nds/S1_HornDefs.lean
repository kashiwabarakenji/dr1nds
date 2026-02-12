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
  U     : Finset α
  rules : Finset (Rule α)
  valid :
    ∀ {P : Finset α} {h : α},
      (P, h) ∈ rules →
      P ⊆ U ∧ h ∈ U


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
  X ⊆ H.U ∧
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
{
  U := H.U.erase x
  rules :=
    (H.rules.filter (fun r => r.2 ≠ x)).image
      (fun r => (r.1.erase x, r.2))
  valid := by
    intro P h hh
    classical
    simp at hh
    obtain ⟨a, ha, rfl⟩ := hh
    -- ha : (a, h) ∈ H.rules ∧ h ≠ x
    obtain ⟨ha_rule, h_ne_x⟩ := ha
    -- use validity of original Horn system
    have hvalid := H.valid ha_rule
    obtain ⟨ha_subset, h_in_U⟩ := hvalid
    constructor
    · -- P ⊆ H.U.erase x
      -- P = a.erase x
      intro y hy
      have hy' : y ∈ a := by
        exact Finset.mem_of_mem_erase hy
      have hyU : y ∈ H.U := ha_subset hy'
      have hy_ne_x : y ≠ x := by
        exact Finset.ne_of_mem_erase hy
      apply Finset.mem_erase.mpr
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
    · -- h ∈ H.U.erase x
      have hxU : h ∈ H.U := h_in_U
      have hx_ne_x : h ≠ x := h_ne_x
      apply Finset.mem_erase.mpr
      simp_all only [not_false_eq_true, ne_eq, and_self]
}
end Dr1nds
