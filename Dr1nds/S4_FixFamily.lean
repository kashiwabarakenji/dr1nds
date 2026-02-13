import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

import Dr1nds.S0_CoreDefs
import Dr1nds.S1_Families
import Dr1nds.S2_HornNF

/-!
# S4_FixFamily.lean（役割メモ / 今後の方針）

このファイルは「HornNF から得られる閉集合族（FixSet）」を
Lean の後続モジュール（会計・帰納・局所核）で扱いやすい形に“列挙器として包む”ための薄い層です。

## なぜ Finset 版を残すのか
- 研究ノート上の主要対象は SetFamily / ClosureSystem ですが、会計（NDS/deg/ndeg）や `Finset.sum` を使う箇所では
  `Finset (Finset α)` による列挙が必要になります。
- そこで、本ファイルでは「FixSet を Finset として持つこと」と「メンバーシップ同値」を最小限だけ提供します。

## 今後の整理（重要）
- **このファイル自体には axiom は置かない**方針です。
  証明が重いのは S8/S10/S11 側（会計等式・wiring・局所核）なので、
  ここは *definitional glue*（同値の貼り合わせ）に徹します。
- 将来的に SetFamily / ClosureSystem 側へ寄せたくなった場合も、
  ここは「列挙器（Finset）」として残し、
  SetFamily 側の概念（SC など）とは **変換補題で接続**するのが安全です。

## ここで追加しがちな補題の置き場所
- `X ∈ C → X ⊆ U` のような「FixSet の定義展開で出るもの」は **ここ**。
- `con / Del / Hole` と `FixSet` の相互作用（representability など）は **S11_LocalKernels**。
- `IH` の unpack / 使い回しは **S9_IH_Unpack / S9_InductionSkeleton**。
- 会計等式（CON_ID / CON_ID_corr）は **S8_Accounting 系**。

（このコメントは“設計の凍結点”として残す。実装が進んだら更新してよい。）
-/

namespace Dr1nds

variable {α : Type} [Fintype α] [DecidableEq α]

/- ============================================================
  FixFamily（Finset 版：FixSet の列挙器）

  - `FixFamily H` は「`H.FixSet : Finset (Finset α)` を C として持つ」だけの薄い wrapper。
  - `mem_iff` により、後続のファイルでは `X ∈ F.C` と `X ∈ H.FixSet` を自由に行き来できる。
  - この層では “閉集合族としての性質” を証明しすぎない（重い補題は S11 に寄せる）。
============================================================ -/

/- NOTE:
`FixFamily` は（いまのところ）`Fintype α` を仮定して `H.FixSet` を Finset として扱う。
将来 `α` を無限型に拡張したくなった場合は、このファイルは「有限部分台 U 上の列挙」に限定して残し、
一般論は SetFamily/ClosureSystem 側へ逃がす。
-/
structure FixFamily (α : Type) [Fintype α] [DecidableEq α]
  (H : HornNF α) where
  C : Finset (Finset α)
  mem_iff : ∀ X : Finset α, X ∈ C ↔ X ∈ H.FixSet

namespace FixFamily

variable {H : HornNF α}

@[simp] theorem mem_iff' (F : FixFamily (α := α) H)
    (X : Finset α) :
    X ∈ F.C ↔ X ∈ H.FixSet :=
  F.mem_iff X

/-- FixSet の定義展開形 -/
theorem mem_iff'' (F : FixFamily (α := α) H)
    (X : Finset α) :
    X ∈ F.C ↔ (X ⊆ H.U ∧ HornNF.IsClosed H X) := by
  simp [HornNF.FixSet] --using (F.mem_iff' (X := X))

/-- 任意のメンバーは U の部分集合 -/
theorem subset_univ_of_mem
    (F : FixFamily (α := α) H)
    {X : Finset α} :
    X ∈ F.C → X ⊆ H.U := by
  intro hX
  exact (F.mem_iff'' (X := X)).1 hX |>.1

end FixFamily

/- ============================================================
  標準 FixFamily

  `Fix H` は “`C := H.FixSet` をそのまま採用する” 標準実装。
  この `rfl` 同値は simp の入口として便利。
============================================================ -/

noncomputable def Fix (H : HornNF α) : FixFamily (α := α) H :=
  { C := H.FixSet
    mem_iff := by intro X; rfl }

/- ============================================================
  ClosedPack（列挙器：後段の pack 階層との互換のため）

  目的：
  - 後段（S8/S9/S10/S11）では `HypPack`/`ClosedPack` という名前が既に使われているため、
    ここでも同型の列挙器を用意して “依存関係の都合” を吸収する。

  方針：
  - このファイルでは `ClosedPack` を **FixSet の列挙器**としてだけ扱い、
    NDS / con / Del / Hole と絡む主張は書かない（＝ここに axiom を置かない）。
  - もし `ClosedPack` と `HypPack` の変換が必要なら、
    それは S9/S11 側で「必要になった形だけ」補題化する（過剰一般化しない）。
============================================================ -/

structure ClosedPack (α : Type) [DecidableEq α] where
  H : HornNF α
  C : Finset (Finset α)
  mem_iff : ∀ X : Finset α, X ∈ C ↔ X ∈ H.FixSet

namespace ClosedPack

/- NOTE:
`omit [Fintype α]` を使っているのは、`ClosedPack` 自体は列挙器なので
「メンバーシップ同値を述べるだけなら Fintype を要しない」形にしておくため。
ただし本プロジェクトでは最終的に `Finset` 上で会計を回すので、実利用はほぼ `[Fintype α]` 下になる。
-/

omit [Fintype α] in
@[simp] theorem mem_iff'
    (P : ClosedPack (α := α))
    (X : Finset α) :
    X ∈ P.C ↔ X ∈ P.H.FixSet :=
  P.mem_iff X

omit [Fintype α] in
@[simp] theorem mem_iff''
    (P : ClosedPack (α := α))
    (X : Finset α) :
    X ∈ P.C ↔ (X ⊆ P.H.U ∧ HornNF.IsClosed P.H X) := by
  simp [HornNF.FixSet] --using (P.mem_iff' (X := X))

end ClosedPack

end Dr1nds
