-- Dr1nds/Induction/Steps.lean
import Mathlib.Tactic

import Dr1nds.Induction.Statements
import Dr1nds.Induction.LocalKernels
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.HornClosure

namespace Dr1nds
variable {α : Type} [DecidableEq α]

/- ============================================================
  (S10-0) Q-step (forbid-free)
============================================================ -/

/--
forbid なし版の帰納ステップ（構造のみ）：
Parallel なら独立核へ、NoParallel なら SC を取り 3-way split。
-/
theorem Q_step0
  (n : Nat)(P : Pack0 α):
   (∀ P : Pack0 α,(P.H.U.card = n → Q n P)) →  (∀ F: HornWithForbid α , (F.H.U.card = n → Qcorr (α := α) n F))
    → P.H.U.card = n+1 → Q (n+1) P := by
  intro hQ hQcorr hn
  classical
  by_cases hPar : Parallel0 P
  · -- parallel branch（独立核）
     exact Q_of_parallel (α := α) (n := n) (P := P) hQ hn hPar

  · -- no-parallel branch：SC を取って分岐
    have hNP : NoParallel0 P := by
      -- NOTE (設計メモ): 現在 NoParallel0 は abbrev True なので trivial。
      -- 将来 `NoParallel0 P := ¬ Parallel0 P` に差し替えたら、ここは `hPar` から構成する。
      trivial
    have hU_nonempty : P.H.U.Nonempty := by
      have hpos : 0 < P.H.U.card := by omega
      exact Finset.card_pos.mp hpos
    let h := choose_SC_no_parallel (α := α) P hU_nonempty hNP
    have hSC : P.H.IsSC h := choose_SC_no_parallel_spec (α := α) P hU_nonempty hNP

    -- SC 点で head 構造を 3-way split
    have hcases : (¬P.H.hasHead h) ∨ (P.H.hasHead h) := by exact Decidable.not_or_of_imp fun a => a

    cases hcases with
    | inl hNo =>
        -- head なし
        exact Q_branch_headFree (α := α) (n := n) (P := P) (h := h) hQ hn hSC hNo
    | inr hrest =>
        exact Q_branch_hasHead (α := α) (n := n) (P := P) (h := h) hQ hQcorr hn hSC hrest

/- ============================================================
  (S10-1) Qcorr-step (with forbid A)
============================================================ -/

-----禁止集合がある場合。
theorem Qcorr_step1
  (n : Nat) :
  (∀ P: Pack0 α ,(P.H.U.card = n → Q n P)) → (∀ F: HornWithForbid α , (F.H.U.card = n → Qcorr (α := α) n F))
    →  (∀ F: HornWithForbid α , (F.H.U.card = n + 1 → Qcorr (α := α) (n+1) F)) := by
  intro hQ hQcorr
  classical
  intro F hn

  have hCardCases := card_cases (α := α) F.F  --ここではまだ閉包はとらない。
  rcases hCardCases with h0 | h1 | hge2
  · -- A.card=0（暫定：専用核）
    let fe :=F.F_nonempty
    exfalso
    simp_all only [Finset.card_eq_zero]
    simp [h0] at fe
  · -- A.card=1（専用核：台落ち）
    -- `A.card = 1` から代表元 `a` を取り、`A = {a}` を得る。
    obtain ⟨a, hAeq⟩ := Finset.card_eq_one.mp h1
    by_cases hs:HasHead1 F a
    · -- a がheadのルールがあるとき。
      obtain ⟨F',hF⟩ := Qcorr_singleton_hasHead_get (α := α) F a hAeq hs
      dsimp [Qcorr]
      intro hf
      specialize hQcorr F'
      have : F'.H.U.card = n := by simp_all only [Finset.card_singleton, add_tsub_cancel_right,
        forall_const]
      specialize hQcorr this
      dsimp [Qcorr] at hQcorr
      specialize hQcorr this
      rw [this] at hF
      rw [hf] at hF
      simp at hF
      --片方が集合族のNDSで、片方が表示のNDSなので変換する必要がある。変換は定義を展開すればいい。
      dsimp [HornWithForbid.NDS_corr] at hF
      dsimp [HornWithForbid.BaseC] at hF
      exact Int.le_trans hF hQcorr

    · --  aがheadのルールがないとき。
      have :¬HasHead1s F h1 := by
        intro h
        have :{a} = F.F := by
          simp_all only
        let hex : ∃ b, F.F = {b} := ⟨a, hAeq⟩
        have hspec := Classical.choose_spec hex  -- : F.F = {Classical.choose hex}
        have hchoose : Classical.choose hex = a := by
          have : {Classical.choose hex} = ({a} : Finset α) := by rw [← hspec, hAeq]
          exact Finset.singleton_injective this
        dsimp [HasHead1s] at h
        rw [hchoose] at h
        exact hs h

      exact Qcorr_singleton_headFree (α := α) n F hQ hn h1 this

  · -- A.card≥2（A 内 SC を取って進める）
    let Fclosed := HornNF.ClosureForbid F
    ---禁止集合を閉集合に変えたものを作る必要がある。
    -- この処理を行ったかどうかは先に伝える必要なし。SCさえ取れれば任務完了。
    suffices NDS_corr (n+1) Fclosed.H.FixSet Fclosed.F ≤ 0 from by
      dsimp [Qcorr]
      intro hn
      let cn := HornNF.closureForbid_NDS_corr_spec (n+1) F
      dsimp [Fclosed] at this
      rw [←cn] at this
      exact this

    by_cases hPar : Parallel1 Fclosed -- 禁止集合の大きさの分岐を先に変更する。
    · -- parallel branch（独立核）
      dsimp [Qcorr]
      exact Qcorr_ge_hasParallel (α := α) (n := n) Fclosed hQcorr hn hPar hn
    · -- no-parallel branch：A の大きさで分岐
      have hNP : NoParallel1 Fclosed := by
        dsimp [Fclosed]
        dsimp [NoParallel1]
        dsimp [Parallel1]
        simp_all only [not_exists, ne_eq, not_and, not_false_eq_true, implies_true, Fclosed]
      have hFclosed_closed : Fclosed.H.IsClosed Fclosed.F := by
        dsimp [Fclosed, HornNF.ClosureForbid]
        simpa using HornNF.closure_isClosed (H := F.H) (X := F.F)
      let a := choose_SC_in_forbid (α := α) Fclosed hFclosed_closed hNP
      have hmem : a ∈ Fclosed.F := choose_SC_in_forbid_mem (α := α) Fclosed hFclosed_closed hNP
      have hSC : IsSC1 Fclosed a := choose_SC_in_forbid_spec (α := α) Fclosed hFclosed_closed hNP
      have fs : ¬IsForbidSingleton Fclosed := by
        dsimp [IsForbidSingleton]
        dsimp [Fclosed]
        have: F.F ⊆ F.H.closure F.F := by
          have : F.F ⊆ F.H.toClosureOperator.cl F.F := by
            exact F.H.toClosureOperator.extensive F.F_subset_U
          exact this
        have : F.F.card ≤ (F.H.closure F.F).card := by
          exact Finset.card_le_card this
        have :F.F.card ≥ 2 := by simp_all only [choose_SC_in_forbid_mem, ge_iff_le, Fclosed, a]
        have :(F.H.closure F.F).card ≥ 2 := by
          (expose_names; exact Nat.le_trans hge2 this_2)
        exact Nat.ne_of_lt' this
      have : Fclosed.H.U.card = n + 1 := by
        simp_all [Fclosed, a]
        exact hn

      by_cases hs:HasHead1 F a
      · let qc := Qcorr_ge2_hasHead (α := α) (n := n) Fclosed (a := a) hmem hQcorr hn fs hSC hs
        dsimp [Qcorr] at qc
        specialize qc this
        exact qc
      · let qc := Qcorr_ge2_headFree (α := α) (n := n) Fclosed (a := a) hmem hQ hQcorr hn fs hSC hs
        dsimp [Qcorr] at qc
        specialize qc this
        exact qc

/- ============================================================
  (S10-2) Main Mutual Induction (Q / Qcorr)
============================================================ -/

/--
`Q`（forbidなし）と `Qcorr`（forbidあり）を同時に進めるメインの相互帰納法。

- 帰納の添字は `n` で、主張は「台集合サイズ `n+1` で成立」。
- Base (`n=0`) は `Q_base` / `Qcorr_base`（=サイズ1ケース）。
- Step は `Q_step0` / `Qcorr_step1` を直結している。
-/
theorem Q_Qcorr_main :
  ∀ n : Nat,
    (∀ P : Pack0 α, P.H.U.card = n + 1 → Q (n + 1) P) ∧
    (∀ F : HornWithForbid α, F.H.U.card = n + 1 → Qcorr (n + 1) F) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro P hcard
        have : Q 1 P := Q_base (α := α) P
        simpa using this
      · intro F hcard
        have : Qcorr 1 F := Qcorr_base (α := α) F
        simpa using this
  | succ n ih =>
      rcases ih with ⟨hQ, hQcorr⟩
      constructor
      · intro P hcard
        have hcard' : P.H.U.card = (n + 1) + 1 := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcard
        exact Q_step0 (α := α) (n := n + 1) (P := P) hQ hQcorr hcard'
      · intro F hcard
        have hcard' : F.H.U.card = (n + 1) + 1 := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcard
        exact Qcorr_step1 (α := α) (n := n + 1) hQ hQcorr F hcard'

/-- Convenience corollary: forbid-free branch at size `n+1`. -/
theorem Q_main
  (n : Nat) (P : Pack0 α) (hcard : P.H.U.card = n + 1) :
  Q (n + 1) P := by
  exact (Q_Qcorr_main (α := α) n).1 P hcard

/-- Convenience corollary: forbid branch at size `n+1`. -/
theorem Qcorr_main
  (n : Nat) (F : HornWithForbid α) (hcard : F.H.U.card = n + 1) :
  Qcorr (n + 1) F := by
  exact (Q_Qcorr_main (α := α) n).2 F hcard

end Dr1nds
