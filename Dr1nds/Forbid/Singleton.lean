-- Dr1nds/Forbid/Singleton.lean
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs      -- Up, Hole, NDS, NDS_corr
import Dr1nds.Forbid.Basic     -- singleton lemmas for Up/Hole

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-!
# Forbid singleton (A = {a})

このファイルは Horn を使わず、
`Up`/`Hole`/`NDS_corr` の **singleton 展開**だけを theorem として固定する。

Horn + forbid の「表現の正規化」(A を前提に含む規則の削除など) は
このファイルでは扱わない（それは `Forbid/HornBridge.lean` 側で凍結する）。
-/

/- ============================================================
  2. |A|=1 ケースで必要になる「表現正規化」(Horn 側で埋める仕様)
     ここは “family-level” の statement として凍結するだけ。
============================================================ -/

/-!
あなたの自然言語の方針では、|A|=1 のときは

- 「A を前提に含む規則は意味がないので削除してよい」
- その削除で family は変わらず、NDS_corr も悪化しない（Up が減らない）

を使って分岐処理します。

ただしこれらは Horn ルールの意味論に依存するので、
このファイルでは **axiom として “仕様だけ” を凍結**し、
後で `Forbid/HornBridge.lean`（または Horn 側ファイル）で埋めます。
-/

/-- (SPEC) singleton forbid `A={a}` のとき、`A ⊆ prem` な規則を削除しても family は変わらない、という仕様。 -/
axiom singleton_forbid_drop_Aprem_rules_preserves_family
  (n : Nat)
  (C_before C_after : Finset (Finset α))
  (a : α) :
  True
  -- ここは後で Horn 側の「表現→family」定義が確定したら、
  -- `C_after = C_before` の形に置き換える。

/-- (SPEC) 上の削除で `NDS_corr` が悪化しない（= 値が増えない/減らないのどちらを採るかは後で固定）。 -/
axiom singleton_forbid_drop_Aprem_rules_ndscorr_monotone
  (n : Nat)
  (C_before C_after : Finset (Finset α))
  (a : α) :
  True
  -- ここも後で
  --   `NDS_corr n C_before {a} ≤ NDS_corr n C_after {a}`
  -- など、あなたの単調性の向きに合わせて確定させる。

/-- `NDS_corr n C {a}` の definitional 展開（Up/Hole をそのまま残す版）。 -/
lemma NDS_corr_singleton_unfold
  (n : Nat) (C : Finset (Finset α)) (a : α) :
  NDS_corr (α := α) n C ({a} : Finset α)
    = NDS (α := α) n (Hole (α := α) C ({a} : Finset α))
      + (Up (α := α) C ({a} : Finset α)).card := by
  simp [NDS_corr]

/-- `NDS_corr n C {a}` を filter だけで書き直す（完全に機械的）。 -/
lemma NDS_corr_singleton_rewrite
  (n : Nat) (C : Finset (Finset α)) (a : α) :
  NDS_corr (α := α) n C ({a} : Finset α)
    =
    NDS (α := α) n (C.filter (fun X => a ∉ X))
      + (C.filter (fun X => a ∈ X)).card := by
  classical
  -- unfold + rewrite Up/Hole using `Forbid/Basic.lean`
  simp [NDS_corr,
    Dr1nds.Hole_singleton_eq_filter_notmem (α := α),
    Dr1nds.Up_singleton_eq_filter_mem (α := α)]

end Dr1nds
