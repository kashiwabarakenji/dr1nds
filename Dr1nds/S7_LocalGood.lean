import Dr1nds.S9_Statements

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/--
LocalGood(P,A,v):
S7 で差し替えられる「局所条件」。
今はダミー（True）で凍結する。
-/
def LocalGood (P : ClosedPack (α := α)) (A : Finset α) (v : α) : Prop := True

end Dr1nds
