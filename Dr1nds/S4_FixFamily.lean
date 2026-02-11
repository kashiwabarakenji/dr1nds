import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

import Dr1nds.S0_CoreDefs        -- HornNF / IsClosed / HornOn
import Dr1nds.S1_Families -- ClosureSystem / iterInter
import Dr1nds.ClosureSystem.IterInter-- FixFamily structure
import Dr1nds.S2_HornNF         -- HornNF structure

namespace Dr1nds

variable {α : Type} [Fintype α] [DecidableEq α]

/-!
S4_FixFamily.lean（現行方針：Set(Finset α) で「外延的に」Fix を扱う）

狙い：
- HornNF と有限台 U のもとで「閉集合族（FixSet）」を Set として定義する。
- その Set を package した構造体 FixFamily を置く。
- ここでは「定義中心」：必要最小の補題だけ（証明は後回しでもOK）。
-/

/- ============================================================
  0. FixFamily（Set 版パッケージ）
============================================================ -/

/--
FixFamily(H,U) は Set (Finset α) を 1 本だけ持つ薄いラッパ。

意図：
- “C は FixSet(H,U) そのもの” を package する。
- 以後「X ∈ F.C ↔ ...」で展開できるように mem_iff を持たせる。
-/
structure FixFamily (H : HornNF α) (U : Finset α) where
  C : Set (Finset α)
  mem_iff : ∀ X : Finset α, X ∈ C ↔ X ∈ HornNF.FixSet (α := α) H U

namespace FixFamily

variable {H : HornNF α} {U : Finset α}

@[simp] theorem mem_iff' (F : FixFamily (α := α) H U) (X : Finset α) :
    X ∈ F.C ↔ X ∈ HornNF.FixSet (α := α) H U :=
  F.mem_iff X

/-- 展開用：FixSet の定義を噛ませた形 -/
theorem mem_iff'' (F : FixFamily (α := α) H U) (X : Finset α) :
    X ∈ F.C ↔ (X ⊆ U ∧ HornNF.IsClosed (α := α) H X) := by
  simpa [HornNF.FixSet] using (F.mem_iff' (X := X))

/-- 任意のメンバーは U の部分集合 -/
theorem subset_univ_of_mem (F : FixFamily (α := α) H U) {X : Finset α} :
    X ∈ F.C → X ⊆ U := by
  intro hX
  have : X ⊆ U ∧ HornNF.IsClosed (α := α) H X := (F.mem_iff'' (X := X)).1 hX
  exact this.1

/-- HornOn(H,U) を仮定すれば U 自身が閉（従って U ∈ FixSet） -/
theorem mem_top_of_hornOn (F : FixFamily (α := α) H U) :
    HornNF.HornOn (α := α) H U → (U ∈ F.C) := by
  intro hOn
  -- 目標：U ∈ FixSet(H,U)
  apply (F.mem_iff' (X := U)).2
  -- FixSet の定義に戻す
  refine ⟨by intro x hx; exact hx, ?_⟩
  -- U が IsClosed であること：prem ⊆ U は自明なので head ∈ U を示す必要がある
  -- ここは「HornOn をどう定義したか」や「IsClosed の定義」に依存するので、骨格だけ置く
  -- （後で必要な公理・補題を足して埋める）
  -- 典型的には `simp [HornNF.IsClosed]` の後、hOn を使う流れ。
  sorry

/--
交わり閉性：X,Y が FixSet に入るなら X∩Y も入る。
これは HornNF.IsClosed が単調（P ⊆ X∩Y なら P ⊆ X かつ P ⊆ Y）であることから出る。
-/
theorem mem_inter
  (F : FixFamily (α := α) H U) {X Y : Finset α} :
  X ∈ F.C → Y ∈ F.C → (X ∩ Y) ∈ F.C := by
  intro hX hY
  have hX' : X ⊆ U ∧ HornNF.IsClosed (α := α) H X := (F.mem_iff'' (X := X)).1 hX
  have hY' : Y ⊆ U ∧ HornNF.IsClosed (α := α) H Y := (F.mem_iff'' (X := Y)).1 hY
  -- 交わりは U の部分集合
  have hSub : X ∩ Y ⊆ U := by
    intro a ha
    have : a ∈ X := by
      have := (Finset.mem_inter.1 ha).1
      exact this
    exact hX'.1 this
  -- IsClosed の部分が本体。後回しで skeleton にしておく。
  have hClosed : HornNF.IsClosed (α := α) H (X ∩ Y) := by
    -- 定義展開 → P ⊆ X∩Y なら P ⊆ X と P ⊆ Y を使って閉性を示す
    -- （HornNF.IsClosed の定義次第で simp が効く）
    sorry
  -- 戻す
  apply (F.mem_iff'' (X := X ∩ Y)).2
  exact ⟨hSub, hClosed⟩

end FixFamily


/- ============================================================
  1. “標準の FixFamily” の構成子：Fix(H,U)
============================================================ -/

/--
Fix(H,U) を “定義により” package したもの。
C = FixSet(H,U).
-/
def Fix (H : HornNF α) (U : Finset α) : FixFamily (α := α) H U :=
  { C := HornNF.FixSet (α := α) H U
    mem_iff := by intro X; rfl }


/- ============================================================
  2. Finset 列挙版（ClosedPack）：あとで会計（NDS）側と接続するための器
============================================================ -/

/--
ClosedPack：FixSet(H,U) の有限列挙 C : Finset (Finset α) を持ち、
列挙と仕様の対応 `mem_iff` を持つ。
-/
structure ClosedPack (α : Type) [DecidableEq α] where
  U : Finset α
  H : HornNF α
  C : Finset (Finset α)
  mem_iff : ∀ X : Finset α, X ∈ C ↔ X ∈ HornNF.FixSet (α := α) H U

namespace ClosedPack

@[simp] theorem mem_iff' (P : ClosedPack (α := α)) (X : Finset α) :
    X ∈ P.C ↔ X ∈ HornNF.FixSet (α := α) P.H P.U :=
  P.mem_iff X

theorem mem_iff'' (P : ClosedPack (α := α)) (X : Finset α) :
    X ∈ P.C ↔ (X ⊆ P.U ∧ HornNF.IsClosed (α := α) P.H X) := by
  simpa [HornNF.FixSet] using (P.mem_iff' (X := X))

end ClosedPack




end Dr1nds
