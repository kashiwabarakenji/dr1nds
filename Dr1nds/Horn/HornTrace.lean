import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Dr1nds.Horn.Horn
import Dr1nds.ClosureSystem.Basic

/-
============================================================
  Trace and DR1 / Horn side (skeletons)
============================================================ -/
namespace Dr1nds
namespace HornNF

variable {α : Type} [DecidableEq α]

/--- Trace of HornNF at u (rule-level trace). -/
def trace (H : HornNF α) (u : α) : HornNF α :=
{ U := H.U.erase u
  prem := fun h =>
    if h = u then ∅
    else
      let S := H.prem h
      (S.biUnion (fun P =>
        if u ∈ P then
          (H.prem u).image (fun Pu => (P.erase u) ∪ Pu)
        else
          {P}
      )).filter (fun P => h ∉ P)
  prem_subset_U := by
    classical
    intro h P hP
    by_cases hh : h = u
    · simp [hh] at hP
    · simp [hh] at hP
      obtain ⟨⟨P₀, hP₀, hcase⟩, _hnotmem⟩ := hP
      by_cases hu : u ∈ P₀
      · simp [hu] at hcase
        rcases hcase with ⟨Pu, hPu, rfl⟩
        have hP0U := H.prem_subset_U hP₀
        have hPuU := H.prem_subset_U hPu
        intro x hx
        have hx' := Finset.mem_union.mp hx
        cases hx' with
        | inl hx₁ =>
            have hx₁' := (Finset.mem_erase.mp hx₁).2
            simp_all
            exact H.prem_subset_U hP₀ hx₁'
        | inr hx₂ =>
            simp_all
            constructor
            · have hnot : u ∉ Pu := H.nf hPu
              intro hx_eq
              subst hx_eq
              exact hnot hx₂
            · exact hPuU hx₂
      · simp [hu] at hcase
        have hP0U := H.prem_subset_U hP₀
        intro x hx
        simp_all
        constructor
        · exact ne_of_mem_of_not_mem hx hu
        · exact hP0U hx
  head_mem_U := by
    classical
    intro h hne
    by_cases hhu : h = u
    · subst hhu; simp at hne
    · have hne' : (H.prem h).Nonempty := by
        obtain ⟨P, hP⟩ := hne
        simp [hhu] at hP
        obtain ⟨⟨P₀, hP₀, _⟩, _⟩ := hP
        exact ⟨P₀, hP₀⟩
      exact Finset.mem_erase.mpr ⟨hhu, H.head_mem_U hne'⟩
  nf := by
    classical
    intro h P hP
    --unfold trace at hP
    by_cases hhu : h = u
    · simp [hhu] at hP
    · simp [hhu] at hP
      rcases hP with ⟨hmem, hnot⟩
      exact hnot
}

/-- DR1 property: each head has at most one premise. -/
def DR1 (H : HornNF α) : Prop :=
  ∀ h, (H.prem h).card ≤ 1

/-- Trace preserves DR1. -/
lemma trace_preserves_DR1
  (H : HornNF α) (u : α)
  (hDR1 : DR1 H) :
  DR1 (trace H u) :=
by
  classical
  intro h
  --unfold DR1
  unfold trace
  by_cases hhu : h = u
  · -- head = u: premises are empty
    subst hhu
    simp
  · -- head ≠ u
    have hcard_h := hDR1 h
    have hcard_u := hDR1 u
    simp [hhu]
    -- filter.card ≤ biUnion.card
    apply Nat.le_trans (Finset.card_filter_le _ _)
    -- Since H.prem h has card ≤ 1, it is either ∅ or a singleton
    rcases (H.prem h).eq_empty_or_nonempty with hempty | ⟨P₀, hP₀⟩
    · -- H.prem h = ∅ → biUnion = ∅
      simp [hempty]
    · -- H.prem h = {P₀} by DR1
      have hsingleton : H.prem h = {P₀} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hP₀, fun x hx => Finset.card_le_one.mp hcard_h x hx P₀ hP₀⟩
      simp only [hsingleton, Finset.singleton_biUnion]
      by_cases huP : u ∈ P₀
      · -- u ∈ P₀: image over H.prem u, card ≤ |H.prem u| ≤ 1
        simp [huP]
        exact Nat.le_trans Finset.card_image_le hcard_u
      · -- u ∉ P₀: result is {P₀}, card = 1 ≤ 1
        simp [huP]

/-- Trace preserves NEP (no empty premise created). -/
lemma trace_preserves_NEP
  (H : HornNF α) (u : α)
  (hnep : ∀ h P, P ∈ H.prem h → P.Nonempty) :
  ∀ h P, P ∈ (trace H u).prem h → P.Nonempty :=
by
  classical
  intro h P hP
  unfold trace at hP
  by_cases hh : h = u
  · simp [hh] at hP
  · simp [hh] at hP
    obtain ⟨⟨P₀, hP₀, hcase⟩, _hnotmem⟩ := hP
    by_cases hu : u ∈ P₀
    · simp [hu] at hcase
      rcases hcase with ⟨Pu, hPu, rfl⟩
      exact Finset.Nonempty.inr (hnep u Pu hPu)
    · simp [hu] at hcase
      simp_all
      exact hnep h P₀ hP₀


/--
Head-free simplification of trace premises.
If `H.prem v = ∅` and `h ≠ v`, then trace just filters
out premises containing `v`.
-/
lemma trace_prem_head_free
  (H : HornNF α)
  (v : α)
  (hfree : H.prem v = ∅)
  {h : α}
  (hneq : h ≠ v) :
  (H.trace v).prem h
    =
  (H.prem h).filter (fun P => v ∉ P) := by
  classical
  unfold HornNF.trace
  simp [hneq, hfree]
  ext X
  constructor
  · intro hX
    simp at hX
    simp
    constructor
    ·
      simp_all only [ne_eq]
      obtain ⟨left, right⟩ := hX
      obtain ⟨w, h_1⟩ := left
      obtain ⟨left, right_1⟩ := h_1
      split at right_1
      next h_1 => simp_all only [Finset.notMem_empty]
      next h_1 => simp_all only [Finset.mem_singleton]
    ·
      simp_all only [ne_eq]
      obtain ⟨left, right⟩ := hX
      obtain ⟨w, h_1⟩ := left
      obtain ⟨left, right_1⟩ := h_1
      apply Aesop.BuiltinRules.not_intro
      intro a
      split at right_1
      next h_1 => simp_all only [Finset.notMem_empty]
      next h_1 => simp_all only [Finset.mem_singleton]
  · intro hX
    simp at hX
    simp
    constructor
    · use X
      constructor
      · simp_all only [ne_eq]
      · simp_all only [ne_eq, ↓reduceIte, Finset.mem_singleton]
    · exact H.nf hX.1

lemma trace_isClosed_iff_head_free
  (H : HornNF α)
  (v : α)
  (hfree : H.prem v = ∅)
  {X : Finset α}
  (hvX : v ∉ X) :
  HornNF.IsClosed (H.trace v) X
    ↔
  HornNF.IsClosed H X :=
by
  classical
  unfold HornNF.IsClosed
  constructor

  ----------------------------------------------------------------
  -- → direction
  ----------------------------------------------------------------
  · intro htrace
    intro h P hP hsubset

    by_cases h_eq_v : h = v
    · subst h_eq_v
      -- H.prem v = ∅
      simp [hfree] at hP

    · -- use trace_prem_head_free
      have hmem_trace :
        P ∈ (H.trace v).prem h :=
      by
        -- rewrite trace premises in head-free case
        have := trace_prem_head_free H v hfree h_eq_v
        simp [this]
        -- goal becomes: P ∈ (H.prem h).filter (v ∉ ·)
        exact ⟨hP, by
          -- show v ∉ P
          intro hvP
          have : v ∈ X := hsubset hvP
          exact hvX this
        ⟩

      exact htrace hmem_trace hsubset


  ----------------------------------------------------------------
  -- ← direction
  ----------------------------------------------------------------
  · intro hH
    intro h P hP hsubset

    by_cases h_eq_v : h = v
    · subst h_eq_v
      -- trace prem at v is empty since H.prem v = ∅
      simp [HornNF.trace, hfree] at hP

    · -- unfold trace premise
      have :=
        trace_prem_head_free H v hfree h_eq_v
      simp [this] at hP
      rcases hP with ⟨hP, hvP⟩
      exact hH hP hsubset

/--
If no premise in `H` contains `v`, then in the trace world the premises for any head `h ≠ v`
are unchanged (the `biUnion` branch never fires).

This lemma is the key simplification used in the `|A|=1` has-head Up-card bijection.
-/
lemma trace_prem_eq_of_noPremContains
  (H : HornNF α)
  (v : α)
  (hNoPremV : ∀ {h : α} {P : Finset α}, P ∈ H.prem h → v ∉ P)
  {h : α}
  (hneq : h ≠ v) :
  (H.trace v).prem h = H.prem h := by
  classical
  -- unfold the trace definition at `h ≠ v`
  unfold HornNF.trace
  simp [hneq]
  -- abbreviate the original premise set
  set S : Finset (Finset α) := H.prem h
  -- the trace construction is `biUnion` (which collapses to `S`) followed by filtering `h ∉ P`
  ext Q
  constructor
  · intro hQ
    -- unpack membership in `filter`
    rcases (Finset.mem_filter.mp hQ) with ⟨hQbi, hnot⟩
    -- unpack membership in `biUnion`
    rcases (Finset.mem_biUnion.mp hQbi) with ⟨P, hP, hQP⟩
    -- since `v ∉ P`, the trace branch is the singleton `{P}`
    have hvP : v ∉ P := hNoPremV (h := h) (P := P) (by simpa [S] using hP)
    have hcase : (if v ∈ P then (H.prem v).image (fun Pu => (P.erase v) ∪ Pu) else ({P} : Finset (Finset α))) = {P} := by
      simp [hvP]
    -- so `Q ∈ {P}` implies `Q = P`
    have hQP' : Q = P := by
      simpa [hcase] using hQP
    subst hQP'
    -- conclude `P ∈ S` and rewrite `S`
    simpa [S] using hP
  · intro hQ
    -- show membership in the filtered `biUnion`
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · -- membership in `biUnion`: choose `P := Q`
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨Q, ?_, ?_⟩
      · simpa [S] using hQ
      · -- again, since `v ∉ Q`, the branch is `{Q}`
        have hvQ : v ∉ Q := hNoPremV (h := h) (P := Q) (by simpa [S] using hQ)
        simp [hvQ]
    · -- the final filter condition `h ∉ Q` holds by NF of `H`
      -- (every premise of head `h` avoids containing its head)
      exact H.nf (by simpa [S] using hQ)

/--
If no premise in `H` contains `v`, then adding `v` to a trace-closed set
preserves closedness in the original world.

This is the forward direction needed for the `|A|=1` has-head Up-card bijection:
`Y ∈ FixSet (trace v)` implies `Y ∪ {v} ∈ FixSet H` (after handling the subset-to-U part).
-/
lemma isClosed_union_singleton_of_noPremContains
  (H : HornNF α)
  (v : α)
  (hNoPremV : ∀ {h : α} {Q : Finset α}, Q ∈ H.prem h → v ∉ Q)
  {Y : Finset α}
  (hY : HornNF.IsClosed (H.trace v) Y) :
  HornNF.IsClosed H (Y ∪ ({v} : Finset α)) := by
  classical
  unfold HornNF.IsClosed at *
  intro h Q hQ hQsub
  by_cases h_eq_v : h = v
  · subst h_eq_v
    -- goal: v ∈ Y ∪ {v}
    simp
  ·
    -- show Q ⊆ Y (since v ∉ Q)
    have hQsubY : Q ⊆ Y := by
      intro x hxQ
      have hxIn : x ∈ Y ∪ ({v} : Finset α) := hQsub hxQ
      by_cases hxv : x = v
      · subst hxv
        exact False.elim ((hNoPremV (h := h) (Q := Q) hQ) hxQ)
      ·
        -- from hxIn : x ∈ Y ∪ {v} and x ≠ v, infer x ∈ Y
        have : x ∈ Y := by
          have hx : x ∈ Y ∨ x ∈ ({v} : Finset α) := by
            exact Finset.mem_union.mp (hQsub hxQ)
          cases hx with
          | inl hxy => exact hxy
          | inr hxsing =>
              have : x = v := by
                simpa [Finset.mem_singleton] using hxsing
              exact False.elim (hxv this)
        exact this
    -- rewrite premises for h ≠ v
    have hEq : (H.trace v).prem h = H.prem h :=
      trace_prem_eq_of_noPremContains H v (by
        intro h' P' hP'
        exact hNoPremV (h := h') (Q := P') hP'
      ) (h := h) h_eq_v
    have hQtrace : Q ∈ (H.trace v).prem h := by
      simpa [hEq] using hQ
    have hhY : h ∈ Y := hY hQtrace hQsubY
    -- conclude h ∈ Y ∪ {v}
    exact Finset.mem_union_left _ (by simpa using hhY)

/--
In the head-free case, closure for trace coincides with
closure for H on sets not containing v.
-/
theorem trace_fixset_head_free
  (H : HornNF α)
  (v : α)
  (hvU : v ∈ H.U)
  (hfree : H.prem v = ∅)
  :
  HornNF.FixSet (H.trace v)
    =
  (HornNF.FixSet H).image (fun X => X.erase v) :=
by
  classical
  ext X
  constructor

  ----------------------------------------------------------------
  -- → direction
  ----------------------------------------------------------------
  · intro hX

    -- unpack Fix(trace)
    have hx := (mem_FixSet_iff (H.trace v) X).1 hX
    rcases hx with ⟨hpow, hclosed_trace⟩

    -- from powerset obtain subset
    have hsub : X ⊆ H.U.erase v := by
      simpa using hpow

    -- v ∉ X
    have hvX : v ∉ X := by
      intro hv
      have := hsub hv
      simp_all only [mem_FixSet_iff, and_self, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false,
        and_true]

    -- lift subset to U
    have hsubU : X ⊆ H.U := by
      intro x hxmem
      have hx' := hsub hxmem
      exact (Finset.mem_of_mem_erase hx')

    -- closure equivalence
    have hclosed_H :
      HornNF.IsClosed H X :=
      (trace_isClosed_iff_head_free H v hfree hvX).1
        hclosed_trace

    -- X ∈ Fix(H)
    have hXfix :
      X ∈ HornNF.FixSet H :=
      (mem_FixSet_iff H X).2
        ⟨
          by simpa using hsubU,
          hclosed_H
        ⟩

    -- X = X.erase v
    have h_eq : X = X.erase v :=
      (Finset.erase_eq_of_notMem hvX).symm

    -- conclude
    refine Finset.mem_image.mpr ?_
    refine ⟨X, hXfix, ?_⟩
    exact h_eq.symm


  ----------------------------------------------------------------
  -- ← direction
  ----------------------------------------------------------------
  · intro hX
    rcases Finset.mem_image.mp hX with ⟨Y, hYfix, h_eq⟩

    -- unpack Y ∈ Fix(H)
    have hy := (mem_FixSet_iff H Y).1 hYfix
    rcases hy with ⟨hYpow, hYclosed⟩

    -- rewrite X
    subst h_eq

    ------------------------------------------------------------
    -- subset part
    ------------------------------------------------------------
    have hsub :
      Y.erase v ⊆ H.U.erase v :=
    by
      intro x hx
      have hxY := Finset.mem_of_mem_erase hx
      have hxU : x ∈ H.U := by
        have hsubY : Y ⊆ H.U := by simpa using hYpow
        exact hsubY hxY
      apply Finset.mem_erase.mpr
      simp_all only [mem_FixSet_iff, and_self, Finset.mem_powerset, Finset.mem_image, Finset.mem_erase, ne_eq, and_true,
        not_false_eq_true]

    have hpow :
      Y.erase v ∈ (H.trace v).U.powerset := by
      simpa using hsub

    ------------------------------------------------------------
    -- closure part
    ------------------------------------------------------------
    have hvX : v ∉ Y.erase v := by simp

    have hclosed_trace :
      HornNF.IsClosed (H.trace v) (Y.erase v) :=
      (trace_isClosed_iff_head_free H v hfree hvX).2
        (
          by
            intro h P hP hsubset

            -- lift subset to Y
            have hsubsetY : P ⊆ Y :=
            by
              intro x hxP
              have hxX := hsubset hxP
              exact Finset.mem_of_mem_erase hxX

            have h_in_Y : h ∈ Y :=
              hYclosed hP hsubsetY

            -- need h ∈ Y.erase v
            by_cases h_eq_v : h = v
            · subst h_eq_v
              -- but v ∉ Y.erase v
              simp at hvX
              simp_all only [mem_FixSet_iff, and_self, Finset.mem_powerset, Finset.notMem_empty]
            · exact Finset.mem_erase.mpr
                ⟨h_eq_v, h_in_Y⟩
        )

    -- conclude
    exact
      (mem_FixSet_iff (H.trace v) _).2
        ⟨hpow, hclosed_trace⟩


end HornNF
end Dr1nds
