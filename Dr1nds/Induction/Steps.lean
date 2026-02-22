-- Dr1nds/Induction/Steps.lean
import Mathlib.Tactic

import Dr1nds.Induction.Statements
import Dr1nds.Induction.LocalKernels
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.HornClosure

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/-
S10(wiring) 相当：
- case split と「どの局所核を呼ぶか」だけを書く
- 数学的な中身（局所核）は LocalKernels 側へ
-/

/- ============================================================
  (W0) forbid なし pack：SC 点 h に対する head-structure 3-way split

  NOTE (設計メモ / 凍結ポイント)
  - Steps(S10) は *wiring のみ* を書く方針。
    この 3-way split 自体は「分岐仕様」なので、最終的には
      (a) Induction/Statements.lean（仕様として凍結）
      または
      (b) Induction/LocalKernels.lean（局所核として供給）
    に移動するのが筋。

  - いまはコンパイルと全体配線の安定化を優先し、ここに axiom として置く。
============================================================ -/

axiom SC_head_cases0
  (P : Pack0 α) (h : α) :
  IsSC0 P h →
  (¬HasHead0 P h) ∨ (HasHead0 P h)

/- ============================================================
  (S10-0) Q-step (forbid-free)
============================================================ -/

/--
forbid なし版の帰納ステップ（構造のみ）：
Parallel なら独立核へ、NoParallel なら SC を取り 3-way split。
-/
theorem Q_step0
  (n : Nat):
   (∀ P : Pack0 α,Q n P) → (∀ P : Pack0 α,Q (n+1) P) := by
  intro hQ P
  classical
  by_cases hPar : Parallel0 P
  · -- parallel branch（独立核）
    exact Q_succ_of_parallel (α := α) (n := n) (P := P) hPar (hQ P)
  · -- no-parallel branch：SC を取って分岐
    have hNP : NoParallel0 P := by
      -- NOTE (設計メモ): 現在 NoParallel0 は abbrev True なので trivial。
      -- 将来 `NoParallel0 P := ¬ Parallel0 P` に差し替えたら、ここは `hPar` から構成する。
      trivial
    let h := choose_SC_no_parallel (α := α) P hNP
    have hSC : IsSC0 P h := choose_SC_no_parallel_spec (α := α) P hNP

    -- SC 点で head 構造を 3-way split
    have hcases : (¬HasHead0 P h) ∨ (HasHead0 P h) :=
      SC_head_cases0 (α := α) (P := P) (h := h) hSC

    cases hcases with
    | inl hNo =>
        -- head なし
        exact Q_branch_headFree (α := α) (n := n) (P := P) (h := h) hSC hNo hQ
    | inr hrest =>
        exact Q_branch_hasHead (α := α) (n := n) (P := P) (h := h) hSC hrest hQ

/- ============================================================
  (S10-1) Qcorr-step (with forbid A)
============================================================ -/

/--
forbid あり版の帰納ステップ（構造のみ）：
Parallel なら独立核へ、NoParallel なら
|A|=1 を専用核、|A|≥2 を “A 内 SC” で進める。
-/
noncomputable def Qcorr_Singleton_HasHead {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (heq: F.F = {a}) (hs:HasHead1 F a):
    ∃ F':HornWithForbid α , F'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr (F.H.U.card - 1)) ≤ (F'.NDS_corr F.H.U.card)
:= sorry

noncomputable def Qcorr_Singleton_NoHead {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (heq: F.F = {a}) (hs:¬HasHead1 F a):
    ∃ F':HornWithForbid α , F'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr (F.H.U.card - 1)) ≤ (F'.NDS_corr F.H.U.card)
:= sorry



theorem Qcorr_step1
  (n : Nat) :
  (∀ P: Pack0 α ,(P.H.U.card = n → Q n P)) → (∀ F: HornWithForbid α , (F.H.U.card = n → Qcorr (α := α) n F))
    →  (∀ F: HornWithForbid α , (F.H.U.card = n + 1 → Qcorr (α := α) (n+1) F)) := by
  intro hQ hQcorr
  classical
  intro F hn
  by_cases hPar : Parallel1 F
  · -- parallel branch（独立核）
    obtain ⟨F',hF⟩ := Qcorr_succ_of_parallel (α := α) (n := n + 1) F hn hPar
    sorry
  · -- no-parallel branch：A の大きさで分岐
    have hNP : NoParallel1 F := by
      exact hPar
    have hCardCases := card_cases (α := α) F.F  --ここではまだ閉包はとらない。
    rcases hCardCases with h0 | h1 | hge2
    · -- A.card=0（暫定：専用核）
      let fe :=F.F_nonempty
      exfalso
      simp_all only [not_false_eq_true, not_exists, ne_eq, not_and, Finset.card_eq_zero]
      simp [h0] at fe
    · -- A.card=1（専用核：台落ち）
      -- `A.card = 1` から代表元 `a` を取り、`A = {a}` を得る。
      obtain ⟨a, hAeq⟩ := Finset.card_eq_one.mp h1
      by_cases hs:HasHead1 F a
      · -- a がheadのルールがあるとき。
        obtain ⟨F',hF⟩ := Qcorr_Singleton_HasHead (α := α) F a hAeq hs
        dsimp [Qcorr]
        intro hf
        specialize hQcorr F'
        have : F'.H.U.card = n := by simp_all only [not_false_eq_true, not_exists, ne_eq,
          not_and, Finset.card_singleton, add_tsub_cancel_right, forall_const]
        specialize hQcorr this
        dsimp [Qcorr] at hQcorr
        specialize hQcorr this
        rw [this] at hF
        rw [hf] at hF
        simp at hF
        --片方が集合族のNDSで、片方が表示のNDSなので変換する必要がある。変換は定義を展開すればいい。
        dsimp [HornWithForbid.NDS_corr] at hF
        dsimp [HornWithForbid.BaseC] at hF
        search_proof





      · --  aがheadのルールがないとき。
        --ここで閉包をとりたい。
        obtain ⟨F',hF⟩ := Qcorr_Singleton_NoHead (α := α) F a  hAeq hs
        sorry
    · -- A.card≥2（A 内 SC を取って進める）
      ---禁止集合を閉集合に変えたものを作る必要がある。
      let h := choose_SC_in_forbid (α := α) F hNP
      have hmem : h ∈ F.F := choose_SC_in_forbid_mem (α := α) F
      have hSC : IsSC1 F h := choose_SC_in_forbid_spec (α := α) F
      by_cases hs:HasHead1 F h
      · exact Qcorr_ge2_HasHead (α := α) (n := n) (P := P) (h := h) hSC hmem hSC
      · exact Qcorr_ge2_NoHead (α := α) (n := n) (P := P) (h := h) hSC hmem hSC




end Dr1nds
