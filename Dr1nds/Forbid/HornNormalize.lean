import Mathlib.Data.Finset.Basic
import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornTrace
import Dr1nds.Forbid.Basic
import Dr1nds.Forbid.HornBridge
import Dr1nds.Forbid.HornWithForbid

namespace Dr1nds
namespace HornNF

variable {α : Type} [DecidableEq α]

/-- Premise-normalization: remove all premises that contain `a`. -/
def normalize (H : HornNF α) (a : α) : HornNF α :=
  { U := H.U
    prem := fun h => (H.prem h).filter (fun P => a ∉ P)
    prem_subset_U := fun {h P} hP => H.prem_subset_U (Finset.mem_filter.mp hP).1
    head_mem_U := fun {h} ⟨P, hP⟩ => H.head_mem_U ⟨P, (Finset.mem_filter.mp hP).1⟩
    nf := fun {h P} hP => H.nf (Finset.mem_filter.mp hP).1
  }

/-- Alias for normalize, emphasizing it acts on premises. -/
abbrev normalizePrem (H : HornNF α) (a : α) : HornNF α := normalize H a

/-- After normalization, no premise contains `a`. -/
lemma normalizePrem_noPremContains
  (H : HornNF α) (a : α) :
  ∀ {h : α} {Q : Finset α}, Q ∈ (normalizePrem H a).prem h → a ∉ Q := by
  intro h Q hQ
  simp [normalizePrem, normalize] at hQ
  exact hQ.2

/-- Normalization preserves DR1. -/
theorem normalizePreservesDR1
  (H : HornNF α) (a : α) (hDR1 : DR1 H) :
  DR1 (normalizePrem H a) := by
  intro h
  simp [normalizePrem, normalize]
  calc
    ((H.prem h).filter (fun P => a ∉ P)).card ≤ (H.prem h).card := Finset.card_filter_le _ _
    _ ≤ 1 := hDR1 h

/--
If head `a` is head-free (`prem a = ∅`), then normalizing at `a` does not change
the trace system at `a`.
-/
lemma trace_normalizePrem_eq_of_head_free
  (H : HornNF α) (a : α)
  (hfree : H.prem a = ∅) :
  (normalizePrem H a).trace a = H.trace a := by
  ext h
  · simp [normalizePrem, normalize, trace]
  · by_cases hEq : h = a
    · subst hEq
      simp [normalizePrem, normalize, trace, hfree]
    · simp [normalizePrem, normalize, trace, hfree, hEq]
      intro P
      constructor
      · intro hP
        rcases hP with ⟨P0, hP0, hmem⟩
        simp_all only [↓reduceIte, Finset.mem_singleton]
        subst hmem
        obtain ⟨left, right⟩ := hP0
        apply Exists.intro
        · split
          rename_i h_1
          on_goal 2 => rename_i h_1
          on_goal 2 => simp_all only [Finset.mem_singleton]
          on_goal 2 => apply And.intro
          on_goal 3 => { rfl
          }
          simp_all only [not_true_eq_false]
          · simp_all only [not_false_eq_true]
      · intro hP
        obtain ⟨w, h_1⟩ := hP
        obtain ⟨left, right⟩ := h_1
        split at right
        next h_1 => simp_all only [Finset.notMem_empty]
        next h_1 =>
          simp_all only [Finset.mem_singleton]
          subst right
          apply Exists.intro
          · split
            rename_i h_2
            on_goal 2 => rename_i h_2
            on_goal 2 => simp_all only [not_false_eq_true, and_true, Finset.mem_singleton]
            on_goal 2 => apply And.intro
            on_goal 3 => { rfl
            }
            simp_all only [not_true_eq_false]
            · simp_all only [not_false_eq_true]

/-- On singleton forbid, the Hole family is invariant under premise-normalization. -/
theorem hole_fixset_singleton_normalize_eq
  (H : HornNF α) (a : α) :
  Hole (α := α) (FixSet (normalizePrem H a)) ({a} : Finset α)
    =
  Hole (α := α) (FixSet H) ({a} : Finset α) := by
  ext X
  simp only [mem_Hole_iff, mem_FixSet_iff, singleton_subset_iff]
  constructor
  · rintro ⟨⟨hU, hCl_norm⟩, haX⟩
    constructor
    · dsimp [HornNF.IsClosed]
      constructor
      ·         --refine ⟨⟨hU, ?_⟩, haX⟩
        intro h P hP hsub
        by_cases haP : a ∈ P
        · exact absurd (hsub haP) haX
        · dsimp [HornNF.normalizePrem] at hCl_norm
          dsimp [HornNF.normalizePrem] at hU
          have :P ∈ (H.normalize a).prem h := by
            dsimp [HornNF.normalize]
            simp
            exact And.symm ⟨haP, hP⟩
          exact hU this hsub
      · exact hCl_norm
    · exact haX
  · rintro ⟨⟨hU, hCl⟩, haX⟩
    dsimp [HornNF.IsClosed]
    constructor
    · constructor
      · intro h P hP hsub
        simp [normalizePrem, normalize] at hP
        obtain ⟨left, right⟩ := hP
        exact hU left hsub
      · exact hCl
    · exact haX
/--
On singleton forbid, the `NDS_corr` of the original system is bounded by the normalized one.
-/
lemma ndscorr_singleton_normalize_le
  (k : Nat) (H : HornNF α) (a : α) :
  NDS_corr k (FixSet H) {a} ≤ NDS_corr k (FixSet (normalizePrem H a)) {a} := by
  have hHole : Hole (FixSet H) {a} = Hole (FixSet (normalizePrem H a)) {a} :=
    (hole_fixset_singleton_normalize_eq H a).symm
  have hCard : (Up (FixSet H) {a}).card ≤ (Up (FixSet (normalizePrem H a)) {a}).card := by
    apply Finset.card_le_card
    intro X hX
    simp [Up] at hX ⊢
    refine ⟨?_, hX.2⟩
    dsimp [HornNF.IsClosed]
    constructor
    · intro h P hP hsub
      simp [normalizePrem, normalize] at hP
      rcases hX with ⟨h1,h2⟩
      dsimp [HornNF.IsClosed] at h1
      simp_all only [Hole_singleton_eq_filter_notmem]
      obtain ⟨left, right⟩ := hP
      obtain ⟨left_1, right_1⟩ := h1
      exact left_1 left hsub
    · dsimp [HornNF.normalizePrem]
      dsimp [HornNF.normalize]
      dsimp [HornNF.IsClosed] at hX
      simp_all only [Hole_singleton_eq_filter_notmem]
  simp only [NDS_corr, hHole]
  linarith [Int.ofNat_le.mpr hCard]

/-!
## Inductive NDS Correlation

This section introduces theorems related to the inductive `NDS_corr` metric defined in
`S8_Statements`. These are essential for the main induction proof which proceeds on
the size of the universe. The logic is adapted from proofs in `Induction/LocalKernels.lean`.
-/
section InductiveNDSCorr

variable {α : Type} [DecidableEq α]

/--
This theorem formalizes the core inductive step for a singleton forbid set `{a}`
where `a` has a unique premise `Pprem` in the normalized system. It states that
the `NDS_corr` for `(U, {a})` can be bounded by the `NDS_corr` of a smaller
system on `U - α` with `Pprem` as the new forbid set.
-/
theorem nds_corr_singleton_hasHead_normalized_step
  (n : Nat) (F : HornWithForbid α) (a : α)
  (hA : F.F = {a})
  (Pprem : Finset α)
  (h_prem_normalized : (F.H.normalize a).prem a = {Pprem})
  (h_IH : Dr1nds.NDS_corr n (HornNF.FixSet ((F.H.normalize a).trace a)) Pprem ≤ 0) :
  Dr1nds.NDS_corr (n + 1) (HornNF.FixSet (F.H.normalize a)) {a} ≤ 0 := by
  let H_norm := F.H.normalize a
  -- This theorem is a wrapper around a more fundamental identity.
  -- The proof from the reference code applies `Qcorr_singleton_hasHead_of_Qcorr_traceP`.
  -- We apply it here with the necessary arguments.
  apply Qcorr_singleton_hasHead_of_Qcorr_traceP
  -- H_norm has DR1
  · exact normalizePreservesDR1 F.H a F.hDR1
  -- a ∈ H_norm.U
  · simp [normalize]
    apply F.F_subset_U
    simp_all only [Finset.mem_singleton]
  -- Pprem ∈ H_norm.prem a
  · rw [h_prem_normalized]
    exact Finset.mem_singleton.mpr rfl
  -- (H_norm.prem a).card = 1
  · rw [h_prem_normalized]
    exact Finset.card_singleton Pprem
  -- H_norm is a-normalized
  · exact normalizePrem_noPremContains F.H a
  -- The inductive hypothesis
  · exact h_IH

/--
A convenience wrapper combining the monotonicity of normalization and a hypothesis
on the normalized system to prove the goal for the original system. This corresponds
to `NDS_corr_le_of_normalized_le` in the original snippets.
-/
lemma nds_corr_le_of_normalized_le
  (n : Nat) (F : HornWithForbid α) (a : α) (hA : F.F = {a})
  (h_norm_goal_le_0 : Dr1nds.NDS_corr (n + 1) (HornNF.FixSet (F.H.normalize a)) {a} ≤ 0) :
  Dr1nds.NDS_corr (n + 1) (HornNF.FixSet F.H) F.F ≤ 0 := by
  rw [hA]
  -- Use the monotonicity of NDS_corr wrt normalization, which is proved in this file.
  have h_mono := ndscorr_singleton_normalize_le (n + 1) F.H a
  -- Chain the inequalities: NDS_corr(H) ≤ NDS_corr(normalize H) ≤ 0
  exact le_trans h_mono h_norm_goal_le_0

end InductiveNDSCorr

---------------------------------

noncomputable def ClosureForbid (F: HornWithForbid α) : HornWithForbid α where
  H := F.H
  hDR1 := F.hDR1
  hNEP := F.hNEP
  F := F.H.toClosureOperator.cl F.F
  F_subset_U := by
    unfold toClosureOperator
    exact closure_subset_U F.H F.F
  F_nonempty := by
    have :F.F ⊆ F.H.closure F.F := by
      apply subset_closure
      simp_all only [HornWithForbid.F_subset_U]
    have ne: F.F.Nonempty := by
      exact F.F_nonempty
    exact ne.mono this

theorem closureForbid_NDS_corr_spec (F: HornWithForbid α) :
  NDS_corr n (F.FixSet) ≤ NDS_corr n (ClosureForbid F).FixSet := by
  let F' := ClosureForbid F
  have eq : Hole F.H.FixSet F.F = Hole F'.H.FixSet F'.F := by
    -- Using simp_rw to unfold definitions. This is safer than dsimp/cases.
    simp_rw [Hole, F', ClosureForbid]
    ext X
    -- The goal is now `(IsClosed ∧ Disjoint) ↔ (IsClosed ∧ Disjoint_closure)`
    constructor
    · -- Direction `→`
      intro h
      -- Accessing parts of the conjunction with .1 and .2
      simp at h
      have hX_closed := h.1
      have hX_disjoint := h.2
      simp
      refine ⟨hX_closed, ?_⟩
      intro h
      have mono: F.F ⊆ F.H.toClosureOperator.cl F.F := by
        have :F.F ⊆ F.H.U := by exact F.F_subset_U
        exact F.H.toClosureOperator.extensive this
      have idem : X = F.H.toClosureOperator.cl X := by
        have mono2: X ⊆ F.H.U := by
          simp_all only [and_self, not_false_eq_true]
          intro y hy
          exact hX_closed.2 hy
        let fh := F.H.toClosureOperator.extensive mono2
        rcases hX_closed with ⟨h1,h2⟩
        dsimp [HornNF.toClosureOperator]
        dsimp [HornNF.closure]
        simp_all only [not_false_eq_true, and_true]
        ext a : 1
        simp_all only [Finset.mem_filter]
        apply Iff.intro
        · intro a_1
          apply And.intro
          · exact mono2 a_1
          · intro Y a_2 a_3
            apply a_3
            simp_all only
        · intro a_1
          simp_all only [subset_refl]




      have : F.F ⊆ X := by exact fun ⦃a⦄ a_1 => h (mono a_1)
      exact hX_disjoint this
    · -- Direction `←`
      intro h
      simp at h
      have hX_closed := h.1
      have hX_disjoint_closure := h.2
      simp
      refine ⟨hX_closed, ?_⟩

      --let fd := Finset.disjoint_of_subset_right
      intro half_le_self
      · -- `F.F` is a subset of its closure.
        have mono:F.H.toClosureOperator.cl F.F ⊆ F.H.toClosureOperator.cl X := by
          apply F.H.toClosureOperator.monotone
          dsimp [HornNF.toClosureOperator]
          exact F.F_subset_U
          dsimp [HornNF.toClosureOperator]
          dsimp [HornNF.IsClosed] at hX_closed
          simp_all only [not_false_eq_true, and_true]
          exact half_le_self
        have eq0: F.H.closure X = X := by
          exact (IsClosed_iff F.H X).mp hX_closed
        have eq:F.H.toClosureOperator.cl X = X := by
          dsimp [HornNF.toClosureOperator]
          exact eq0
        simp_all only [not_false_eq_true, and_self]

  dsimp [HornWithForbid.FixSet]
  simp
  exact ge_of_eq (congrArg (NDS_corr n) (id (Eq.symm eq)))





end HornNF
end Dr1nds
