import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/--
ClosureSystem (Finset 版):
- 台集合 U を持つ
- 族 C ⊆ 𝒫(U) が
  (i) U を含み
  (ii) 2集合の共通部分で閉じる
  (iii) 要素はすべて U の部分集合
を満たす、という最小の構造。

※ Horn からこれを作るのは後段（Core/Horn 側）でやる。
-/
structure ClosureSystem (α : Type) [DecidableEq α] where
  U : Finset α
  C : Finset (Finset α)
  top_mem : U ∈ C
  subset_univ : ∀ X : Finset α, X ∈ C → X ⊆ U
  inter_mem :
    ∀ X : Finset α, X ∈ C →
    ∀ Y : Finset α, Y ∈ C →
      X ∩ Y ∈ C

end Dr1nds
