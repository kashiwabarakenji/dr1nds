-- Dr1nds/Forbid/SingletonCase.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs
import Dr1nds.Forbid.Basic
import Dr1nds.Forbid.World

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-!
# Forbid.SingletonCase

forbid がシングルトン `A = {a}` の場合に必要になる “世界の正規化・移送” を凍結する。

重要：
- ここでの主張は「族の表現（DR1 ルール）が違っても、禁止集合が {a} なら正規化できる」
  というあなたのアイディアを、Lean 側で使える I/O にすること。
- Horn 側の定義（どのように Cbase を作るか）は別ファイルで接続する。
-/

/- ------------------------------------------------------------
  0. Family-level monotonicity lemma for NDS_corr
------------------------------------------------------------ -/

/--
`NDS_corr n C A = NDS n (Hole C A) + |Up C A|` なので、
Hole 部分が一致していて Up-card が小さくなれば、NDS_corr は（増えずに）改善する。

この補題は “ルールを削除して Up が減る” などの操作で使う。
-/
lemma NDS_corr_mono_of_Hole_eq_and_Up_card_le
  (n : Nat)
  (C₁ C₂ : Finset (Finset α))
  (A : Finset α)
  (hHole : Hole (α := α) C₁ A = Hole (α := α) C₂ A)
  (hUp : (Up (α := α) C₁ A).card ≤ (Up (α := α) C₂ A).card) :
  NDS_corr (α := α) n C₁ A ≤ NDS_corr (α := α) n C₂ A := by
  classical
  -- NDS_corr = NDS(Hole) + card(Up)
  -- Hole が等しいので NDS(Hole) は同じ、あとは card(Up) の単調性
  -- ここは純会計なので linarith で落とせる形にしておく
  -- （必要なら後で補題分解する）
  have : NDS (α := α) n (Hole (α := α) C₁ A)
          = NDS (α := α) n (Hole (α := α) C₂ A) := by
    simp [hHole]
  -- Int への coercion
  have hUpInt :
      (Up (α := α) C₁ A).card ≤ (Up (α := α) C₂ A).card := hUp
  -- 仕上げ
  -- （NDS は Int、card は Nat→Int coercion があるので）
  -- ここは `linarith` に任せるのが一番安定
  -- ただし simp 展開を少し補助
  dsimp [NDS_corr]
  -- `this` を rewrite してから linarith
  -- note: simp で this を使うには書き換え
  -- (linarith は rewrite 後に効く)
  -- ↓
  -- NDS(Hole C₁ A) + card(Up C₁ A) ≤ NDS(Hole C₂ A) + card(Up C₂ A)
  -- で、左の NDS(Hole) を右に書き換えて card 単調性を使う。
  -- ここでは `simp [this]` の形を使う
  have : NDS (α := α) n (Hole (α := α) C₁ A)
            + (Up (α := α) C₁ A).card
          ≤ NDS (α := α) n (Hole (α := α) C₂ A)
            + (Up (α := α) C₂ A).card := by
    -- `this` で NDS(Hole) を同一化し card の単調性で結ぶ
    -- Nat≤Nat を Int の linarith に渡す
    have hUp' : ((Up (α := α) C₁ A).card : Int) ≤ (Up (α := α) C₂ A).card := by
      simp_all only [Nat.cast_le]
    -- rewrite
    -- NDS(Hole C₁) = NDS(Hole C₂)
    -- なので
    -- NDS(Hole C₂) + card₁ ≤ NDS(Hole C₂) + card₂
    -- が card 単調性から従う
    -- linarith で閉じる
    -- (simp で NDS 部分を書き換える)
    -- NOTE: `simp [this]` は `this` を rewrite に使う
    simpa [this] using (add_le_add_left hUp' (NDS (α := α) n (Hole (α := α) C₂ A)))
  simpa [NDS_corr] using this

/- ------------------------------------------------------------
  1. (S1) singleton forbid: normalization (rule deletion) skeleton
------------------------------------------------------------ -/

/--
(S1) シングルトン forbid `A = {a}` のときの正規化核。

直感：
- forbid `{a}` がある世界では `a ∈ X` な閉集合は “捨てられる側” に数えられる。
- `{a}` を前提に含むルールは、そもそも forbid により発火不能（意味がない）なので削除してよい。
- この削除は「族（Hole 側）」を変えず、Up を増やさない（むしろ減らす）ので NDSCorr は悪化しない。

Lean 化では、まず “正規化操作” を抽象化して、
spec（Hole 不変・Up-card 単調）を axiom として固定し、
上の `NDS_corr_mono...` から結論を引き出すのが安全。
-/
axiom normalize_singleton_base
  (C : Finset (Finset α)) (a : α) :
  Finset (Finset α)

axiom normalize_singleton_base_spec
  (C : Finset (Finset α)) (a : α) :
  Hole (α := α) (normalize_singleton_base (α := α) C a) ({a} : Finset α)
    = Hole (α := α) C ({a} : Finset α)
  ∧ (Up (α := α) (normalize_singleton_base (α := α) C a) ({a} : Finset α)).card
      ≤ (Up (α := α) C ({a} : Finset α)).card

/-- (S1) 正規化により `NDS_corr` は悪化しない（増えない）。 -/
theorem NDS_corr_singleton_normalize_le
  (n : Nat) (C : Finset (Finset α)) (a : α) :
  NDS_corr (α := α) n (normalize_singleton_base (α := α) C a) ({a} : Finset α)
    ≤ NDS_corr (α := α) n C ({a} : Finset α) := by
  classical
  obtain ⟨hHole, hUp⟩ :=
    normalize_singleton_base_spec (α := α) (C := C) (a := a)
  -- monotonicity lemma
  have := NDS_corr_mono_of_Hole_eq_and_Up_card_le (α := α)
    (n := n)
    (C₁ := normalize_singleton_base (α := α) C a)
    (C₂ := C)
    (A := ({a} : Finset α))
    (hHole := by simp [hHole] )
    (hUp := hUp)
  -- 上の補題は ≤ の向きが “Up が小さいなら改善” なので、
  -- ここでは C₁=normalize, C₂=original で合っている。
  simpa using this

/- ------------------------------------------------------------
  2. (S2) singleton forbid transport via head rule P -> a
------------------------------------------------------------ -/

/--
(S2) `P → a` があるとき、forbid `{a}` の世界を `U\\{a}` の forbid（=cl P）世界へ移送する核。

ここで `clP` は “U\\{a} 世界の closure で閉包化した P” を想定しているが、
Horn 側の定義に依存するので、ここでは引数として渡す形で凍結する。
-/
axiom singleton_forbid_transport_base
  (U : Finset α)
  (Cbase : Finset (Finset α))
  (a : α)
  (Pcl : Finset α) : Finset (Finset α)

/--
移送の spec：
- 左：台 U、base Cbase、forbid {a} の “実際の族” は `Hole Cbase {a}`
- 右：台 U.erase a の base（transport_base）、forbid Pcl の “実際の族” は `Hole transport_base Pcl`
これらが（族として）一致する、という形で凍結する。

※「台が違うので族の等しさをどう読むか」は後で調整可能：
  いまは “Finset (Finset α) として同じ要素集合” という意味で固定しておく。
-/
axiom singleton_forbid_transport_spec
  (U : Finset α)
  (Cbase : Finset (Finset α))
  (a : α)
  (Pcl : Finset α) :
  Hole (α := α) Cbase ({a} : Finset α)
    = Hole (α := α) (singleton_forbid_transport_base (α := α) U Cbase a Pcl) Pcl

/--
(S2) NDSCorr の整合（凍結版）。

注意：ここは “台サイズ n の扱い” が絡むため、等式の形は最終設計で少し変える可能性がある。
しかし当面は、あなたの意図に沿って
- 左を `n = |U|`
- 右を `n' = |U.erase a|`
として、それぞれの `NDS_corr` が一致（あるいは簡単な差分で一致）する形を API として出す。

まずは “一致” を axiom で固定しておくのが安全。
-/
axiom NDS_corr_singleton_transport_eq
  (U : Finset α)
  (Cbase : Finset (Finset α))
  (a : α)
  (Pcl : Finset α) :
  let n  : Nat := U.card
  let n' : Nat := (U.erase a).card
  NDS_corr (α := α) n Cbase ({a} : Finset α)
    =
  NDS_corr (α := α) n' (singleton_forbid_transport_base (α := α) U Cbase a Pcl) Pcl

end Dr1nds
