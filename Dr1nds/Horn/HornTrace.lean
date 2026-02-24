import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornClosure
import Dr1nds.ClosureSystem.Basic
import Dr1nds.Forbid.Basic
import Dr1nds.SetFamily.CoreDefs

/-
============================================================
  Trace and DR1 / Horn side (skeletons)
============================================================ -/
namespace Dr1nds
namespace HornNF

variable {α : Type} [DecidableEq α]

@[ext] lemma ext {H1 H2 : HornNF α}
  (hU : H1.U = H2.U)
  (hPrem : H1.prem = H2.prem) : H1 = H2 := by
  cases H1
  cases H2
  cases hU
  cases hPrem
  simp

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

/-- Trace preserves DR1. 使われている -/
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

/-- Trace preserves NEP (no empty premise created). まだ使われてない -/
lemma trace_preserves_NEP'
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

lemma trace_preserves_NEP
  (H : HornNF α) (u : α)
  (hnep : H.IsNEP):
(trace H u).IsNEP := by
  classical
  intro x
  dsimp [HornNF.IsNEP] at hnep
  have : ∀ (h : α), ∀ P ∈ H.prem h, P.Nonempty := by
    intro h P hP
    dsimp [Finset.Nonempty]
    have :∅ ∉ H.prem h := by
      simp_all only [not_false_eq_true]
    have : P ≠ ∅ := by
      simp_all only [not_false_eq_true, ne_eq]
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only
    let ni :=Finset.nonempty_iff_ne_empty (s := P)
    simp_all only [not_false_eq_true, ne_eq]
    exact ni.2 this

  let tp := trace_preserves_NEP' H u this
  intro h
  specialize tp x
  specialize tp ∅ h
  simp_all only [Finset.not_nonempty_empty]

/--
Head-free simplification of trace premises.
If `H.prem v = ∅` and `h ≠ v`, then trace just filters
out premises containing `v`.
-/
private lemma trace_prem_head_free
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

-- 使われている HornBridgeから。
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
  ·
    intro htrace
    constructor
    ·
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

        exact htrace.1 hmem_trace hsubset
    · rcases htrace with ⟨htrace1,htrace2⟩
      dsimp [HornNF.trace] at htrace2
      rw [Finset.subset_erase] at htrace2
      exact htrace2.1

  ----------------------------------------------------------------
  -- ← direction
  ----------------------------------------------------------------
  · intro hH
    constructor
    · intro h P hP hsubset

      by_cases h_eq_v : h = v
      · subst h_eq_v
        -- trace prem at v is empty since H.prem v = ∅
        simp [HornNF.trace, hfree] at hP

      · -- unfold trace premise
        have :=
          trace_prem_head_free H v hfree h_eq_v
        simp [this] at hP
        rcases hP with ⟨hP, hvP⟩
        obtain ⟨left, right⟩ := hH
        exact left hP hsubset
    · dsimp [HornNF.trace]
      obtain ⟨left, right⟩ := hH
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq]
      apply And.intro
      · apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only
      · exact right hx

/--
If no premise in `H` contains `v`, then in the trace world the premises for any head `h ≠ v`
are unchanged (the `biUnion` branch never fires).

This lemma is the key simplification used in the `|A|=1` has-head Up-card bijection.
-- HornBridgeから使われている。hNoPremVは、normalizedの仮定と同じ。
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
Horn Bridgeから使われている。
-/
lemma isClosed_union_singleton_of_noPremContains
  (H : HornNF α)
  (hv: v ∈ H.U)
  (hNoPremV : ∀ {h : α} {Q : Finset α}, Q ∈ H.prem h → v ∉ Q)
  {Y : Finset α}
  (hY : HornNF.IsClosed (H.trace v) Y) :
  HornNF.IsClosed H (Y ∪ ({v} : Finset α)) := by
  classical
  unfold HornNF.IsClosed at *
  constructor
  · intro h Q hQ hQsub
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
      have hhY : h ∈ Y := by
        rcases hY with ⟨hY1,hY2⟩
        dsimp [HornNF.trace] at hY2
        rw [Finset.subset_erase] at hY2
        exact hY1 hQtrace hQsubY
      -- conclude h ∈ Y ∪ {v}
      exact Finset.mem_union_left _ hhY
  · rcases hY with ⟨hY, hvY⟩
    dsimp [HornNF.trace] at hvY
    rw [Finset.subset_erase] at hvY
    have hYU: Y ⊆ H.U := by exact hvY.1
    have hv :v ∈ H.U := by simp_all only
    simp_all only [true_and, Finset.union_singleton]
    rw [Finset.insert_subset_iff]
    simp_all only [and_self]



/--
If `P ∈ (H.trace v).prem h` then necessarily `v ∉ P` (since trace lives on `U.erase v`).
-/


lemma trace_prem_not_mem
  (H : HornNF α)
  (v : α)
  {h : α} {P : Finset α}
  (hP : P ∈ (H.trace v).prem h) :
  v ∉ P := by
  classical
  -- `prem_subset_U` in the trace world gives `P ⊆ H.U.erase v`
  have hsub : P ⊆ (H.U.erase v) := (H.trace v).prem_subset_U hP
  intro hvP
  have : v ∈ H.U.erase v := hsub hvP
  simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and]

/-- In the trace world at `a`, no premise contains `a` (binder name `Q`).
-/
lemma trace_noPremContains
  (H : HornNF α) (a : α) :
  ∀ {h : α} {Q : Finset α}, Q ∈ (H.trace a).prem h → a ∉ Q := by
  intro h Q hQ
  exact trace_prem_not_mem (H := H) (v := a) (h := h) (P := Q) hQ

/--
If `Pprem` is a premise of head `a` in `H`, then `Pprem` is contained in the universe
of the trace system `H.trace a`, i.e. in `H.U.erase a`.

This is the canonical way to produce the `hPsub` argument used when building
trace-world packs in the singleton-forbid / has-head branch.
-/
lemma prem_subset_traceU_of_mem_prem
  (H : HornNF α) {a : α} {Pprem : Finset α}
  (hmem : Pprem ∈ H.prem a) :
  Pprem ⊆ (H.trace a).U := by
  classical
  -- `(H.trace a).U` is definitionaly `H.U.erase a`.
  intro x hx
  have hxU : x ∈ H.U := H.prem_subset_U hmem hx
  have hxa : x ≠ a := by
    -- NF says `a ∉ Pprem` for `Pprem ∈ H.prem a`.
    have ha_not : a ∉ Pprem := H.nf hmem
    intro hEq
    subst hEq
    exact ha_not hx
  -- combine `x ∈ H.U` and `x ≠ a`.
  exact Finset.mem_erase.mpr ⟨hxa, hxU⟩


/-- `trace` does not create empty premises: `IsNEP` is preserved by trace. -/
lemma isNEP_trace_of_isNEP
  (H : HornNF α) (u : α)
  (hNEP : HornNF.IsNEP (α := α) H) :
  HornNF.IsNEP (α := α) (H.trace u) := by
  classical
  intro h
  by_cases hh : h = u
  · subst hh
    -- by definition, trace has no premises at the traced head
    simp [HornNF.trace]
  ·
    -- show `∅` is not in the filtered `biUnion`
    intro hempty
    -- unfold membership in `(H.trace u).prem h`
    simp [HornNF.trace, hh] at hempty
    cases hempty with
    | intro P0 hP0 =>
      -- hP0 : P0 ∈ H.prem h ∧ ∅ ∈ if u ∈ P0 then ... else {P0}
      have hP0mem : P0 ∈ H.prem h := hP0.1
      have hcase : (∅ : Finset α) ∈
          (if u ∈ P0 then
            Finset.image (fun Pu => P0.erase u ∪ Pu) (H.prem u)
           else ({P0} : Finset (Finset α))) := hP0.2
      by_cases hu : u ∈ P0
      · -- image branch
        have hcase' :
            (∅ : Finset α) ∈
              Finset.image (fun Pu => P0.erase u ∪ Pu) (H.prem u) := by
          simpa [hu] using hcase
        rcases Finset.mem_image.mp hcase' with ⟨Pu, hPu, hEq⟩
        have hPu0 : Pu = (∅ : Finset α) := by
          have hboth : P0.erase u = (∅ : Finset α) ∧ Pu = (∅ : Finset α) := by
            exact (Finset.union_eq_empty.mp hEq)
          exact hboth.2
        exact (hNEP (h := u)) (by simpa [hPu0] using hPu)
      · -- singleton branch
        have hcase' : (∅ : Finset α) ∈ ({P0} : Finset (Finset α)) := by
          simpa [hu] using hcase
        have hP0eq : P0 = (∅ : Finset α) := by
          let fm := Finset.mem_singleton.mp hcase'
          simp_all only [↓reduceIte, Finset.mem_singleton, and_self]
        exact (hNEP (h := h)) (by simpa [hP0eq] using hP0mem)


/-- If `∅` is a closed set of `H` (equivalently, `∅ ∈ FixSet H`), then it remains so after trace. -/
theorem empty_mem_fixset_trace_of_empty_mem_fixset
  (H : HornNF α) (u : α)
  (h0 : (∅ : Finset α) ∈ HornNF.FixSet (α := α) H) :
  (∅ : Finset α) ∈ HornNF.FixSet (α := α) (H.trace u) := by
  classical
  -- convert `∅ ∈ FixSet` to `IsNEP`, transport across trace, then convert back
  have hNEP : HornNF.IsNEP (α := α) H :=
    (isNEP_iff_empty_mem_FixSet (α := α) (H := H)).2 h0
  have hNEP' : HornNF.IsNEP (α := α) (H.trace u) :=
    isNEP_trace_of_isNEP (α := α) (H := H) (u := u) hNEP
  exact (isNEP_iff_empty_mem_FixSet (α := α) (H := H.trace u)).1 hNEP'


/-- The empty set always belongs to the Hole side for a singleton forbid `{a}`.

This is the basic NEP-transport fact used in singleton-forbid wiring:
adding a nonempty forbid set does not affect whether `∅` is present.
-/
lemma empty_mem_Hole_singleton_iff
  (C : Finset (Finset α)) (a : α) :
  ((∅ : Finset α) ∈ Hole (α := α) C ({a} : Finset α)) ↔ (∅ : Finset α) ∈ C := by
  classical
  -- unfold `Hole` and evaluate the predicate at `∅`
  -- Hole C {a} = C.filter (fun X => ¬({a} ⊆ X))
  -- and `{a} ⊆ ∅` is false, so membership reduces to `∅ ∈ C`.
  simp [Dr1nds.Hole]

/-- If `∅ ∈ C`, then also `∅ ∈ Hole C {a}` (the forward direction packaged).

This is often the exact shape needed by `have`-steps in `Induction/Main.lean`.
-/
lemma empty_mem_Hole_singleton_of_empty_mem
  (C : Finset (Finset α)) (a : α)
  (h0 : (∅ : Finset α) ∈ C) :
  (∅ : Finset α) ∈ Hole (α := α) C ({a} : Finset α) := by
  have h :
      ((∅ : Finset α) ∈ Hole (α := α) C ({a} : Finset α)) ↔ (∅ : Finset α) ∈ C :=
    empty_mem_Hole_singleton_iff (α := α) (C := C) (a := a)
  exact h.mpr h0

/-- The empty set is never in `Up C {a}` for a singleton forbid `{a}`. -/
lemma empty_not_mem_Up_singleton
  (C : Finset (Finset α)) (a : α) :
  (∅ : Finset α) ∉ Up (α := α) C ({a} : Finset α) := by
  classical
  simp [Dr1nds.Up]

/-- Under `hNoPremV`, trace and family-level `Tr` commute on fixed sets. -/
theorem fixset_trace_eq_Tr_fixset_of_noPremContains
  (H : HornNF α) (v : α)
  (hvU : v ∈ H.U)
  (hNoPremV : ∀ {h : α} {P : Finset α}, P ∈ H.prem h → v ∉ P) :
  HornNF.FixSet (H.trace v) = Tr v (HornNF.FixSet H) := by
  classical
  ext X
  constructor
  · intro hX
    have hXclosed : HornNF.IsClosed (H.trace v) X := (mem_FixSet_iff (H.trace v) X).1 hX
    have hvX : v ∉ X := by
      have hsub : X ⊆ (H.trace v).U := hXclosed.2
      intro hv
      have : v ∈ (H.trace v).U := hsub hv
      simp [HornNF.trace] at this
    have hInsClosed : HornNF.IsClosed H (X ∪ ({v} : Finset α)) :=
      isClosed_union_singleton_of_noPremContains
        (H := H) (v := v) (hv := hvU) (hNoPremV := hNoPremV) (hY := hXclosed)
    have hInsFix : X ∪ ({v} : Finset α) ∈ HornNF.FixSet H :=
      (mem_FixSet_iff H (X ∪ ({v} : Finset α))).2 hInsClosed
    refine Finset.mem_image.mpr ?_
    refine ⟨X ∪ ({v} : Finset α), hInsFix, ?_⟩
    simp [Finset.union_singleton, hvX]
  · intro hX
    rcases Finset.mem_image.mp hX with ⟨Y, hYfix, hYX⟩
    have hYclosed : HornNF.IsClosed H Y := (mem_FixSet_iff H Y).1 hYfix
    have hYsubU : Y ⊆ H.U := hYclosed.2
    have hsubUerase : Y.erase v ⊆ H.U.erase v := by
      intro x hx
      have hxY : x ∈ Y := Finset.mem_of_mem_erase hx
      have hxU : x ∈ H.U := hYsubU hxY
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hxU⟩
    have hclosedTrace : HornNF.IsClosed (H.trace v) (Y.erase v) := by
      constructor
      · intro h P hP hPsub
        by_cases hh : h = v
        · subst hh
          simp [HornNF.trace] at hP
        · have hPremEq : (H.trace v).prem h = H.prem h :=
            trace_prem_eq_of_noPremContains (H := H) (v := v)
              (hNoPremV := hNoPremV) (h := h) (hneq := hh)
          have hP' : P ∈ H.prem h := by
            simpa [hPremEq] using hP
          have hPsubY : P ⊆ Y := by
            intro x hxP
            have hxE : x ∈ Y.erase v := hPsub hxP
            exact Finset.mem_of_mem_erase hxE
          have hhY : h ∈ Y := hYclosed.1 hP' hPsubY
          exact Finset.mem_erase.mpr ⟨hh, hhY⟩
      · simpa [HornNF.trace] using hsubUerase
    have hXfix : Y.erase v ∈ HornNF.FixSet (H.trace v) :=
      (mem_FixSet_iff (H.trace v) (Y.erase v)).2 hclosedTrace
    simpa [hYX] using hXfix

/-- Head-free case: trace and `Tr` commute on fixed sets. -/
theorem fixset_trace_eq_Tr_fixset_of_head_free
  (H : HornNF α) (v : α)
  (hvU : v ∈ H.U)
  (hfree : H.prem v = ∅) :
  HornNF.FixSet (H.trace v) = Tr v (HornNF.FixSet H) := by
  classical
  ext X
  constructor
  · intro hX
    have hXclosed : HornNF.IsClosed (H.trace v) X := (mem_FixSet_iff (H.trace v) X).1 hX
    have hvX : v ∉ X := by
      have hsub : X ⊆ (H.trace v).U := hXclosed.2
      intro hv
      have : v ∈ (H.trace v).U := hsub hv
      simp [HornNF.trace] at this
    have hXclosedH : HornNF.IsClosed H X :=
      (trace_isClosed_iff_head_free (H := H) (v := v) (hfree := hfree) (hvX := hvX)).1 hXclosed
    have hXfix : X ∈ HornNF.FixSet H := (mem_FixSet_iff H X).2 hXclosedH
    refine Finset.mem_image.mpr ?_
    refine ⟨X, hXfix, ?_⟩
    simp [hvX]
  · intro hX
    rcases Finset.mem_image.mp hX with ⟨Y, hYfix, hYX⟩
    have hYclosed : HornNF.IsClosed H Y := (mem_FixSet_iff H Y).1 hYfix
    have hEraseClosedH : HornNF.IsClosed H (Y.erase v) := by
      constructor
      · intro h P hP hPsub
        by_cases hh : h = v
        · subst hh
          simp [hfree] at hP
        · have hPsubY : P ⊆ Y := by
            intro x hx
            exact Finset.mem_of_mem_erase (hPsub hx)
          have hhY : h ∈ Y := hYclosed.1 hP hPsubY
          exact Finset.mem_erase.mpr ⟨hh, hhY⟩
      · intro x hx
        exact hYclosed.2 (Finset.mem_of_mem_erase hx)
    have hEraseFix : Y.erase v ∈ HornNF.FixSet H := (mem_FixSet_iff H (Y.erase v)).2 hEraseClosedH
    have hvErase : v ∉ Y.erase v := by simp
    have hEraseClosedTrace : HornNF.IsClosed (H.trace v) (Y.erase v) :=
      (trace_isClosed_iff_head_free (H := H) (v := v) (hfree := hfree) (hvX := hvErase)).2 hEraseClosedH
    have hXfix : Y.erase v ∈ HornNF.FixSet (H.trace v) :=
      (mem_FixSet_iff (H.trace v) (Y.erase v)).2 hEraseClosedTrace
    simpa [hYX] using hXfix

/-- Head-free case: `FixSet (H.trace v)` is exactly family-level deletion on `FixSet H`. -/
theorem fixset_trace_eq_Del_fixset_of_head_free
  (H : HornNF α) (v : α)
  (_hvU : v ∈ H.U)
  (hfree : H.prem v = ∅) :
  HornNF.FixSet (H.trace v) = Del v (HornNF.FixSet H) := by
  classical
  ext X
  constructor
  · intro hX
    have hXclosed : HornNF.IsClosed (H.trace v) X := (mem_FixSet_iff (H.trace v) X).1 hX
    have hvX : v ∉ X := by
      have hsub : X ⊆ (H.trace v).U := hXclosed.2
      intro hv
      have : v ∈ (H.trace v).U := hsub hv
      simp [HornNF.trace] at this
    have hXclosedH : HornNF.IsClosed H X :=
      (trace_isClosed_iff_head_free (H := H) (v := v) (hfree := hfree) (hvX := hvX)).1 hXclosed
    have hXfix : X ∈ HornNF.FixSet H := (mem_FixSet_iff H X).2 hXclosedH
    exact Finset.mem_filter.mpr ⟨hXfix, hvX⟩
  · intro hX
    rcases Finset.mem_filter.mp hX with ⟨hXfix, hvX⟩
    have hXclosedH : HornNF.IsClosed H X := (mem_FixSet_iff H X).1 hXfix
    have hXclosedTrace : HornNF.IsClosed (H.trace v) X :=
      (trace_isClosed_iff_head_free (H := H) (v := v) (hfree := hfree) (hvX := hvX)).2 hXclosedH
    exact (mem_FixSet_iff (H.trace v) X).2 hXclosedTrace

/-- Head-free case: on `FixSet H`, trace-image and deletion coincide (`Tr v = Del v`). -/
theorem Tr_fixset_eq_Del_fixset_of_head_free
  (H : HornNF α) (v : α)
  (hvU : v ∈ H.U)
  (hfree : H.prem v = ∅) :
  Tr v (HornNF.FixSet H) = Del v (HornNF.FixSet H) := by
  calc
    Tr v (HornNF.FixSet H) = HornNF.FixSet (H.trace v) := by
      symm
      exact fixset_trace_eq_Tr_fixset_of_head_free (H := H) (v := v) (hvU := hvU) (hfree := hfree)
    _ = Del v (HornNF.FixSet H) :=
      fixset_trace_eq_Del_fixset_of_head_free (H := H) (v := v) (_hvU := hvU) (hfree := hfree)

/-- DR1 step version: trace and `Tr` commute on fixed sets. -/
theorem fixset_trace_eq_Tr_fixset_of_DR1
  (H : HornNF α) (_hDR1 : H.IsDR1) (v : α) (hvU : v ∈ H.U) :
  HornNF.FixSet (H.trace v) = Tr v (HornNF.FixSet H) := by
  classical
  ext X
  constructor
  · intro hX
    have hXclosed : HornNF.IsClosed (H.trace v) X := (mem_FixSet_iff (H.trace v) X).1 hX
    have hvX : v ∉ X := by
      have hsub : X ⊆ (H.trace v).U := hXclosed.2
      intro hv
      have : v ∈ (H.trace v).U := hsub hv
      simp [HornNF.trace] at this
    have hXsubU : X ⊆ H.U := by
      intro x hx
      exact (Finset.mem_erase.mp (hXclosed.2 hx)).2
    by_cases hTrig : ∃ Pu : Finset α, Pu ∈ H.prem v ∧ Pu ⊆ X
    · rcases hTrig with ⟨Pu0, hPu0, hPu0sub⟩
      have hInsClosed : HornNF.IsClosed H (insert v X) := by
        constructor
        · intro h P hP hPsub
          by_cases hEq : h = v
          · subst hEq
            simp
          · by_cases hvP : v ∈ P
            · have hQsubX : (P.erase v ∪ Pu0) ⊆ X := by
                intro x hx
                rcases Finset.mem_union.mp hx with hxE | hxPu
                · have hxP : x ∈ P := Finset.mem_of_mem_erase hxE
                  have hxIns : x ∈ insert v X := hPsub hxP
                  rcases Finset.mem_insert.mp hxIns with hxeq | hxX
                  · subst hxeq
                    exact False.elim ((Finset.mem_erase.mp hxE).1 rfl)
                  · exact hxX
                · exact hPu0sub hxPu
              by_cases hhQ : h ∈ (P.erase v ∪ Pu0)
              · exact Finset.mem_insert_of_mem (hQsubX hhQ)
              · have hQmem : (P.erase v ∪ Pu0) ∈ (H.trace v).prem h := by
                  unfold HornNF.trace
                  simp [hEq, hhQ]
                  refine ⟨P, hP, ?_⟩
                  simpa [hvP] using (Finset.mem_image.mpr ⟨Pu0, hPu0, rfl⟩)
                have hhX : h ∈ X := hXclosed.1 hQmem hQsubX
                exact Finset.mem_insert_of_mem hhX
            · by_cases hhP : h ∈ P
              · exact hPsub hhP
              · have hPsubX : P ⊆ X := by
                  intro x hx
                  have hxIns : x ∈ insert v X := hPsub hx
                  rcases Finset.mem_insert.mp hxIns with hxeq | hxX
                  · subst hxeq
                    exact False.elim (hvP hx)
                  · exact hxX
                have hPmemTrace : P ∈ (H.trace v).prem h := by
                  unfold HornNF.trace
                  simp [hEq, hhP]
                  refine ⟨P, hP, ?_⟩
                  simp [hvP]
                have hhX : h ∈ X := hXclosed.1 hPmemTrace hPsubX
                exact Finset.mem_insert_of_mem hhX
        · intro x hx
          rcases Finset.mem_insert.mp hx with hxeq | hxX
          · subst hxeq
            exact hvU
          · exact hXsubU hxX
      have hInsFix : insert v X ∈ HornNF.FixSet H :=
        (mem_FixSet_iff H (insert v X)).2 hInsClosed
      refine Finset.mem_image.mpr ?_
      refine ⟨insert v X, hInsFix, ?_⟩
      simp [hvX]
    · have hBaseClosed : HornNF.IsClosed H X := by
        constructor
        · intro h P hP hPsub
          by_cases hEq : h = v
          · subst hEq
            exfalso
            exact hTrig ⟨P, hP, hPsub⟩
          · by_cases hvP : v ∈ P
            · exfalso
              exact hvX (hPsub hvP)
            · have hPmemTrace : P ∈ (H.trace v).prem h := by
                unfold HornNF.trace
                simp [hEq, H.nf hP]
                refine ⟨P, hP, ?_⟩
                simp [hvP]
              exact hXclosed.1 hPmemTrace hPsub
        · exact hXsubU
      have hBaseFix : X ∈ HornNF.FixSet H := (mem_FixSet_iff H X).2 hBaseClosed
      refine Finset.mem_image.mpr ?_
      refine ⟨X, hBaseFix, ?_⟩
      simp [hvX]
  · intro hX
    rcases Finset.mem_image.mp hX with ⟨Y, hYfix, hYX⟩
    have hYclosed : HornNF.IsClosed H Y := (mem_FixSet_iff H Y).1 hYfix
    have hYsubU : Y ⊆ H.U := hYclosed.2
    have hClosedTrace : HornNF.IsClosed (H.trace v) (Y.erase v) := by
      constructor
      · intro h P hP hPsub
        by_cases hEq : h = v
        · subst hEq
          simp [HornNF.trace] at hP
        · simp [HornNF.trace, hEq] at hP
          rcases hP with ⟨⟨P0, hP0, hcase⟩, _⟩
          by_cases hvP0 : v ∈ P0
          · simp [hvP0] at hcase
            rcases hcase with ⟨Pu, hPu, hQeq⟩
            subst hQeq
            have hPuSubY : Pu ⊆ Y := by
              intro x hx
              exact Finset.mem_of_mem_erase (hPsub (Finset.mem_union.mpr (Or.inr hx)))
            have hvY : v ∈ Y := hYclosed.1 hPu hPuSubY
            have hP0SubY : P0 ⊆ Y := by
              intro x hx
              by_cases hxeq : x = v
              · subst hxeq
                exact hvY
              · have hxE : x ∈ P0.erase v := Finset.mem_erase.mpr ⟨hxeq, hx⟩
                exact Finset.mem_of_mem_erase (hPsub (Finset.mem_union.mpr (Or.inl hxE)))
            have hhY : h ∈ Y := hYclosed.1 hP0 hP0SubY
            exact Finset.mem_erase.mpr ⟨hEq, hhY⟩
          · simp [hvP0] at hcase
            subst hcase
            have hP0SubY : P ⊆ Y := by
              intro x hx
              exact Finset.mem_of_mem_erase (hPsub hx)
            have hhY : h ∈ Y := hYclosed.1 hP0 hP0SubY
            exact Finset.mem_erase.mpr ⟨hEq, hhY⟩
      · intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hYsubU (Finset.mem_of_mem_erase hx)⟩
    have hFixTrace : Y.erase v ∈ HornNF.FixSet (H.trace v) :=
      (mem_FixSet_iff (H.trace v) (Y.erase v)).2 hClosedTrace
    simpa [hYX] using hFixTrace

end HornNF
end Dr1nds
