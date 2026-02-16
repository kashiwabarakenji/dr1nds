-- Dr1nds/Forbid/Monotonicity.lean
import Mathlib.Tactic

import Dr1nds.Forbid.Basic
import Dr1nds.S0_CoreDefs
--import Dr1nds.Accounting.NDS

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/-
NDScorr の単調性（contraction で非減少）を「言明として固定」
ここでの C は “forbid 表現から作られた family” を想定。
（どの C を使うか＝表現依存をなくす方針は、後で整理）
-/

axiom NDSCorr_monotone_under_contraction
  (n : Nat) (C : Finset (Finset α)) (A : Finset α) (h : α) :
  -- 「h はSC」など必要条件は後で追加
  True →
  NDS_corr (α := α) n C A ≤
    NDS_corr (α := α) (n-1) (con (α := α) h C) (A.erase h)

end Dr1nds
