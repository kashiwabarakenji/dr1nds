import Mathlib.Data.Finset.Basic

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/--
General Horn rule system over α.
A rule is (premise P, head h).
We keep everything finitary via Finset.
-/
abbrev Rule (α : Type) := (Finset α) × α

structure Horn (α : Type) [DecidableEq α] where
  rules : Finset (Rule α)

namespace Horn

/-- DR1: each head appears in at most one rule. -/
def DR1 (H : Horn α) : Prop :=
  ∀ {P₁ P₂ : Finset α} {h : α},
    (P₁, h) ∈ H.rules → (P₂, h) ∈ H.rules → P₁ = P₂

/-- NEP: no empty premise rules. -/
def NEP (H : Horn α) : Prop :=
  ∀ {P : Finset α} {h : α}, (P, h) ∈ H.rules → P.Nonempty

/-- NF: no self-premise (head ∉ premise). -/
def NF (H : Horn α) : Prop :=
  ∀ {P : Finset α} {h : α}, (P, h) ∈ H.rules → h ∉ P

/--
Closedness of a set X w.r.t. Horn rules:
for every rule P → h, if P ⊆ X then h ∈ X.
This is the "rule satisfaction" definition (no closure operator needed).
-/
def IsClosed (H : Horn α) (X : Finset α) : Prop :=
  ∀ {P : Finset α} {h : α}, (P, h) ∈ H.rules → P ⊆ X → h ∈ X

end Horn

end Dr1nds
