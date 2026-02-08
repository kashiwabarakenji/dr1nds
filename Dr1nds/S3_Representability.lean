import Dr1nds.S1_Families
import Dr1nds.S2_Horn

namespace Dr1nds

variable {α : Type} [DecidableEq α]

open Horn

/--
`H` represents `CS` if membership in CS.C is characterized by:
  X ⊆ U  ∧  IsClosed(H) X
This is your old `FixFamily.mem_iff` の一般版です。
-/
def Represents (H : Horn α) (CS : ClosureSystem α) : Prop :=
  ∀ X : Finset α,
    X ∈ CS.C ↔ (X ⊆ CS.U ∧ Horn.IsClosed (α := α) H X)

/--
A closure system is DR1-realizable if it is represented by some Horn system
satisfying DR1 + NEP (+ NF if you want).
-/
def DR1Realizable (CS : ClosureSystem α) : Prop :=
  ∃ H : Horn α,
    Horn.DR1 (α := α) H ∧ Horn.NEP (α := α) H ∧ Horn.NF (α := α) H ∧ Represents (α := α) H CS

end Dr1nds
