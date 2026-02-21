import Mathlib.Data.Finset.Basic
import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornTrace
import Dr1nds.Forbid.Basic

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
  simp only [mem_Hole_iff, mem_FixSet_iff, Finset.mem_powerset, singleton_subset_iff]
  constructor
  · rintro ⟨⟨hU, hCl_norm⟩, haX⟩
    refine ⟨⟨hU, ?_⟩, haX⟩
    intro h P hP hsub
    by_cases haP : a ∈ P
    · exact absurd (hsub haP) haX
    · exact hCl_norm (Finset.mem_filter.mpr ⟨hP, haP⟩) hsub
  · rintro ⟨⟨hU, hCl⟩, haX⟩
    refine ⟨⟨hU, ?_⟩, haX⟩
    intro h P hP hsub
    simp [normalizePrem, normalize] at hP
    exact hCl hP.1 hsub

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
    refine ⟨hX.1.1, ?_⟩
    intro h P hP hsub
    simp [normalizePrem, normalize] at hP
    exact hX.1.2 hP.1 hsub
  simp only [NDS_corr, hHole]
  linarith [Int.ofNat_le.mpr hCard]

end HornNF
end Dr1nds
