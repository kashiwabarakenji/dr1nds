-- Dr1nds/Induction/Wiring.lean
import Mathlib.Tactic

import Dr1nds.Induction.Statements
import Dr1nds.Induction.LocalKernels

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/-
S10(wiring) 相当：
- case split だけする
- 中身は LocalKernels の API を呼ぶだけ
-/

theorem Q_step_wiring
  (n : Nat) (P : Pack0 (α := α)) :
  Q (α := α) n P → Q (α := α) (n+1) P :=
by
  intro hQ
  -- ここで「parallel か？」を判定し、分岐する（判定自体は後で実装）
  by_cases hPar : True
  · exact Q_of_parallel (α := α) (n := n+1) (P := P) (by trivial)
  ·
    -- no-parallel 側：SC を取る
    obtain ⟨h, hh⟩ := exists_SC_no_parallel (α := α) (P := P) (by trivial)
    -- ここから head/noHead, unary/nonUnary を場合分けして枝へ
    -- 今は全部 True のプレースホルダでよい
    -- （後で Horn 側のデータに接続）
    apply Q_branch_noHead (α := α) (n := n) (P := P) (h := h) (by trivial)
    simp_all only [not_true_eq_false]
    exact hQ


theorem Qcorr_step_wiring
  (n : Nat) (P : Pack1 (α := α)) :
  Qcorr (α := α) n P → Qcorr (α := α) (n+1) P :=
by
  intro hQ
  -- parallel 分岐（後で）
  by_cases hPar : True
  · exact Qcorr_of_parallel (α := α) (n := n + 1) (P := P) (by trivial)
  ·
    -- |A|=1 の special handling
    by_cases hA1 : (Pack1.A (α := α) P).card = 1
    · exact Qcorr_handle_A_singleton (α := α) (n := n) (P := P) hA1 hQ
    ·
      -- |A|≥2 側：forbid 内の SC を取って main branch
      obtain ⟨h, hhA⟩ := exists_SC_in_forbid (α := α) (P := P) (by trivial)
      apply Qcorr_branch_A_ge2 (α := α) (n := n) (P := P) (h := h) (by trivial)
      exact False.elim (hPar trivial)
      exact hQ

end Dr1nds
