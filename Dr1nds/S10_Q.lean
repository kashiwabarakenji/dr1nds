import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S9_Statements
import Dr1nds.Forbid1
import Dr1nds.Accounting
import Dr1nds.S7_LocalGood
import Dr1nds.S7_DelNdegKernel
import Dr1nds.S10_SingletonTools
import Dr1nds.S10_Q_singletonCase
import Dr1nds.S10_IHUnpack

namespace Dr1nds
open scoped BigOperators
variable {α : Type} [DecidableEq α]

/--
S10: (T(n−1) ∧ Q(n−1)) → Q(n)

B2 方針（確定）：
- Q は「2 ≤ A.card」のみを射程に取る
- by_cases A.card = 1
  * Case1: A = {v}
      → 専用補題 Q_step_singleton_case に完全委譲
  * Case2: 2 ≤ A.card
      → IH (n−1) + DelNdeg 核 + CON_ID_corr
- このファイルでは「分岐構造と依存関係」を凍結するのみ
- 証明の数値部分は後段で埋める
-/
theorem Q_step
  (n : Nat) :
  (T (α := α) (n - 1) ∧ Q (α := α) (n - 1)) →
  Q (α := α) n :=
by
  intro hTQ
  rcases hTQ with ⟨hT, hQ⟩

  -- Q(n) の定義展開
  unfold Q
  intro P A hcard hDR1 hNEP hAcard hA_sub

  -- A.card = 1 かどうかで分岐
  by_cases hcardA : A.card = 1

  ------------------------------------------------------------------
  -- Case1: A = {v}
  ------------------------------------------------------------------
  ·
    -- A = {v} を得る
    obtain ⟨v, hvA⟩ : ∃ v, v ∈ A := by
      -- card = 1 なら必ず要素がある
      have : 0 < A.card := by
        simp [hcardA] --using (Nat.succ_le_iff.mp (by decide : 1 ≤ A.card))
      exact Finset.card_pos.mp this

    have hAeq : A = ({v} : Finset α) :=
      eq_singleton_of_card_eq_one_of_mem A v hcardA hvA
    subst hAeq

    -- Case1 は「unary forbid 由来 → deletion → 帰納法」
    -- として専用補題に完全委譲する
    have h :=
      Q_step_singleton_case
        (α := α) n P v
        hcard hDR1 hNEP
        -- 起源条件（S10 の設計で保証）
    exact h hQ

  ------------------------------------------------------------------
  -- Case2: 2 ≤ A.card
  ------------------------------------------------------------------
  ·
    -- card ≠ 1 かつ 2 ≤ A.card（Q の仮定）よりそのまま使う
    have hcardA2 : 2 ≤ A.card := hAcard

    -- erase v が nonempty（card ≥ 2 なら必ず）
    have hAerase_ne : (A.erase ?v).Nonempty := by
      -- v は任意に取れる：A.card ≥ 2 なら erase 後も非空
      -- skeleton（後で mathlib 補題に置換）
      sorry

    sorry
    sorry
    /-
    -- IH を pack 形で適用（corr 側）
    have hCorr := IH_corr_con_pack (α := α) n P A
      hcard hDR1 hNEP hcardA2 hA_sub hAerase_ne hT hQ
    -- Del + ndeg 側（核）
    have hDel :
      NDS (α := α) n
          (Del (α := α) ?v (Hole (α := α) (ClosedPack.C P) A))
        + ndeg (α := α) (Hole (α := α) (ClosedPack.C P) A) ?v ≤ 0 :=
      DelNdeg_le_zero_on_Hole
        (α := α) (n + 1) P A ?v
        hDR1 hNEP hA_sub
        (by sorry)
        trivial
    -/

    -- Accounting の恒等式（CON_ID_corr）で結合
    -- skeleton（後で linarith 等で閉じる）

end Dr1nds
