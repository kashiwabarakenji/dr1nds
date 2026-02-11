-- Dr1nds/S9_IH_Unpack.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S8_Statements

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/- ============================================================
  S9 : IH unpack / bridge (SKELETON, FROZEN)
  目的：
    - S10/S11 の骨格で必要になる IH の呼び出し口だけを固定
    - con/erase 後の「pack」を厳密に構成するのは後回し
============================================================ -/

namespace IH

/--
通常側 IH（con で n を 1 減らした対象に適用するための口）。

本来は「(n-1) 世界の HypPack」を構成して Q を適用するのが筋だが，
ここでは骨格優先で、必要な形を直接 axiom 化して固定する。
-/
axiom Q_con
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0

/-- Compatibility name used by older skeletons (e.g. S11). -/
theorem IH_Q_gives_con_bound
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0 :=
by
  intro ih
  exact Q_con (α := α) n P v ih


/--
forbid 側 IH（Case2：v∈A かつ A.erase v が非空）。

S10 の B2（A.erase v 非空）で使う「口」。
`Q (n-1) → Qcorr(n-1)` ではなく、
骨格上必要な不等式を直接返す形にしておく。
-/
axiom Qcorr_con_case2
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  Q (α := α) (n - 1) P →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1) (con (α := α) v P.C) (A.erase v) ≤ 0

/-- Compatibility name used by older skeletons (e.g. S8). -/
theorem IH_corr_con_pack
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  Q (α := α) (n - 1) P →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1) (con (α := α) v P.C) (A.erase v) ≤ 0 :=
by
  intro ih hv hne
  exact Qcorr_con_case2 (α := α) n P A v ih hv hne


/--
必要なら「forbidOK が erase で保存される」も口として固定しておく。

※これは後でちゃんと証明できる（A⊆U, 2≤|A| から 2≤|A.erase v| は一般に落ちないので、
  実際には Case2 の前提（Nonempty など）に合わせて条件を調整する可能性がある）。
  いまは骨格を優先して弱い形（nonempty だけ）に留める。
-/
theorem forbidOK_erase_nonempty
  (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A →
  v ∈ A →
  (A.erase v).Nonempty := by
  classical
  intro hOK hv
  rcases hOK with ⟨hAU, hAne, hAcard⟩
  -- `2 ≤ A.card` and `v ∈ A` imply `A.erase v` is nonempty.
  have hlt : 1 < A.card := lt_of_lt_of_le (by decide : 1 < 2) hAcard
  have hpos : 0 < A.card - 1 := Nat.sub_pos_of_lt hlt
  have hpos' : 0 < (A.erase v).card := by
    simpa [Finset.card_erase_of_mem hv] using hpos
  exact Finset.card_pos.1 hpos'

end IH

end Dr1nds
