
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Dr1nds.S0_CoreDefs
import Dr1nds.S1_Families
import Dr1nds.Horn.Horn   -- HornNF
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.HornClosure
import Dr1nds.Forbid.HornWithForbid

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/--
Trace a `HornWithForbid` system at a point `v`.

The new Horn system is `S.H.trace v`, and the new forbid set is `S.F.erase v`.
This operation is only defined when the resulting forbid set is non-empty,
which is equivalent to `S.F ≠ {v}`. The point `v` does not need to be in `F`
or be an SC point.
-/
def HornWithForbid.trace (S : HornWithForbid α) (v : α) (h_nonempty : (S.F.erase v).Nonempty) : HornWithForbid α :=
  { H := S.H.trace v
    hDR1 := HornNF.trace_preserves_DR1 S.H v S.hDR1
    hNEP := HornNF.trace_preserves_NEP' S.H v S.hNEP
    F := S.F.erase v
    F_subset_U := by
      dsimp [HornNF.trace]
      have : S.F ⊆ S.H.U := by simp_all only [F_subset_U]
      exact Finset.erase_subset_erase v this

    F_nonempty := h_nonempty
  }

@[simp] theorem trace_H (S : HornWithForbid α) (v : α) (h : (S.F.erase v).Nonempty) :
  (S.trace v h).H = S.H.trace v := rfl

@[simp] theorem trace_F (S : HornWithForbid α) (v : α) (h : (S.F.erase v).Nonempty) :
  (S.trace v h).F = S.F.erase v := rfl

/--
Trace the underlying Horn system at `a` and **replace** the forbid set by `Pprem`.

IMPORTANT:
`HornWithForbid` requires the forbid set to satisfy:
- `Pprem ⊆ (S.H.trace a).U`
- `Pprem.Nonempty`

So this constructor takes these obligations as explicit arguments.
This removes the need for axiom-level APIs.
-/
noncomputable def traceWithPrem
  (S : HornWithForbid α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (S.H.trace a).U)
  (hPne : Pprem.Nonempty) : HornWithForbid α :=
  { H := S.H.trace a
    hDR1 := by
      -- DR1 is preserved by trace (proved in the Horn layer).
      have hDR1' : HornNF.DR1 S.H := by
        simpa [HornNF.IsDR1, HornNF.DR1] using S.hDR1
      have hDR1'' : HornNF.DR1 (S.H.trace a) :=
        HornNF.trace_preserves_DR1 (H := S.H) (u := a) hDR1'
      simpa [HornNF.IsDR1, HornNF.DR1] using hDR1''
    hNEP := by
      -- NEP is preserved by trace (proved in the Horn layer).
      let tp := HornNF.trace_preserves_NEP' S.H a
      have :S.H.IsNEP := by
        dsimp [HornNF.IsNEP]
        simp [S.hNEP ]
      simp_all only
    F := Pprem
    F_subset_U := hPsub
    F_nonempty := hPne
  }

@[simp] theorem traceWithPrem_H
  (S : HornWithForbid α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (S.H.trace a).U)
  (hPne : Pprem.Nonempty) :
  (traceWithPrem (α := α) S a Pprem hPsub hPne).H = S.H.trace a := by
  rfl

@[simp] theorem traceWithPrem_F
  (S : HornWithForbid α) (a : α) (Pprem : Finset α)
  (hPsub : Pprem ⊆ (S.H.trace a).U)
  (hPne : Pprem.Nonempty) :
  (traceWithPrem (α := α) S a Pprem hPsub hPne).F = Pprem := by
  rfl


/-!
`HornWithForbid` requires the forbid set to be closed.

In the singleton-forbid has-head branch, the natural new forbid set is not the raw
premise `Praw` but its closure in the traced Horn system:

  `Pprem := closure_{S.H.trace a}(Praw)`.

This wrapper constructs the obligations internally.

NOTE: Replacing `Praw` by `closure(Praw)` does **not** change the resulting
forbid-family *when we filter a closed family* (e.g. `HornNF.FixSet`), because for
closed `X` we have `Praw ⊆ X ↔ closure(Praw) ⊆ X`. A lemma for this equivalence is
added below.
-/
noncomputable def traceWithPremClosure
  (S : HornWithForbid α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (S.H.trace a).U)
  (hPne : Praw.Nonempty) : HornWithForbid α := by
  classical
  let Pprem : Finset α := HornNF.closure (S.H.trace a) Praw

  -- closure is always inside the universe because it is defined by `U.filter _`
  have hPsub' : Pprem ⊆ (S.H.trace a).U := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1

  -- nonempty is preserved because `Praw ⊆ closure(Praw)` when `Praw ⊆ U`
  have hPne' : Pprem.Nonempty := by
    rcases hPne with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact (HornNF.subset_closure (H := (S.H.trace a)) (X := Praw) hPsub) hx

  exact traceWithPrem (α := α) S a Pprem hPsub' hPne'

@[simp] theorem traceWithPremClosure_H
  (S : HornWithForbid α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (S.H.trace a).U)
  (hPne : Praw.Nonempty) :
  (traceWithPremClosure (α := α) S a Praw hPsub hPne).H = S.H.trace a := by
  classical
  simp [traceWithPremClosure]

@[simp] theorem traceWithPremClosure_F
  (S : HornWithForbid α) (a : α) (Praw : Finset α)
  (hPsub : Praw ⊆ (S.H.trace a).U)
  (hPne : Praw.Nonempty) :
  (traceWithPremClosure (α := α) S a Praw hPsub hPne).F
    = HornNF.closure (S.H.trace a) Praw := by
  classical
  simp [traceWithPremClosure]

attribute [simp] traceWithPremClosure_H traceWithPremClosure_F


/-
============================================================
  Placeholder: deletion representation theorem

  これが最重要ブリッジ補題になる。
============================================================
-/


lemma deletion_filter_equiv
  (H : HornNF α)
  (hDR1 : H.IsDR1)
  (v : α)
  (P : Finset α)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  (X : Finset α) :
  X ∈ (HornNF.FixSet H).filter (fun X => v ∉ X)
  ↔
  X ∈ (H.trace v).FixSet ∧ ¬ P ⊆ X := by
  classical
  constructor

  ----------------------------------------------------------------
  -- → direction
  ----------------------------------------------------------------
  · intro h
    have hmem := Finset.mem_filter.mp h
    have hFix := hmem.1
    have hvX := hmem.2

    have hFix_data := (mem_FixSet_iff H X).mp hFix
    have hsubU := hFix_data.1
    have ⟨hsubU, hClosed⟩ := hFix_data

    --------------------------------------------------------------
    -- 1. ¬ P ⊆ X
    --------------------------------------------------------------
    have hNotP : ¬ P ⊆ X := by
      intro hPX
      have hv : v ∈ X := by
        apply hClosed
        · exact hP
        · exact hPX
      exact hvX hv

    --------------------------------------------------------------
    -- 2. trace で閉
    --------------------------------------------------------------
    have hTraceClosed :
      HornNF.IsClosed (H.trace v) X := by
      unfold HornNF.IsClosed
      intro h Q hQ hQsub

      by_cases h_eq_v : h = v
      · subst h_eq_v
        -- trace.prem v = ∅
        simp [HornNF.trace] at hQ

      · -- h ≠ v
        simp [HornNF.trace, h_eq_v] at hQ
        rcases hQ with ⟨⟨Q₀, hQ₀, hcase⟩, _⟩

        by_cases hvQ₀ : v ∈ Q₀
        · -- composite rule
          simp [hvQ₀] at hcase
          rcases hcase with ⟨Pu, hPu, hEq⟩
          subst hEq

          -- DR1 で Pu = P
          have h_single :
            ∀ Q ∈ H.prem v, Q = P := by
            have hcard := Finset.card_eq_one.mp hUnique
            intro Q hQv
            obtain ⟨a, ha⟩ := hcard
            have hQ' : Q = a := by simpa [ha] using hQv
            have hP' : P = a := by simpa [ha] using hP
            exact hQ'.trans hP'.symm

          have hPu_eq : Pu = P := h_single Pu hPu
          subst hPu_eq

          ------------------------------------------------------------
          -- Q₀.erase v ⊆ X
          ------------------------------------------------------------
          have hQ₀sub :
            Q₀.erase v ⊆ X := by
            intro x hx
            rename_i right
            simp_all only [Finset.mem_filter, not_false_eq_true, and_self, mem_FixSet_iff, Finset.mem_powerset,
              Finset.mem_union, Finset.mem_erase, ne_eq, true_and, not_or]
            obtain ⟨left, right⟩ := right
            obtain ⟨left_1, right_1⟩ := hx
            apply hQsub
            simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, not_false_eq_true, and_self, true_or]

          ------------------------------------------------------------
          -- Q₀ ⊆ X
          ------------------------------------------------------------
          have hQ₀sub_full :
            Q₀ ⊆ X := by
            intro x hxQ₀
            by_cases h_eq_v : h = v
            · cases h_eq_v
              -- v ∈ X を導いて矛盾
              have hv_mem : v ∈ X := by
                apply hClosed hQ₀
                intro y hy
                by_cases hyv : y = v
                · subst hyv
                  exact False.elim (h_eq_v rfl)
                · have hy' : y ∈ Q₀.erase v :=
                    Finset.mem_erase.mpr ⟨hyv, hy⟩
                  exact hQ₀sub hy'
              exact False.elim (hvX hv_mem)
            · have hx' : x ∈ Q₀.erase v := by
                apply Finset.mem_erase.mpr
                rw [← @Finset.notMem_singleton]
                simp
                constructor
                · show ¬x = v
                  intro hxv
                  subst hxv
                  exact hNotP (Finset.subset_union_right.trans hQsub)
                · simp_all only [Finset.mem_filter, not_false_eq_true, and_self, mem_FixSet_iff, Finset.mem_powerset,
                  Finset.mem_union, Finset.mem_erase, ne_eq, true_and, not_or]
                --   ⟨hxv, hxQ₀⟩
              exact hQ₀sub hx'

          ------------------------------------------------------------
          -- 閉性適用
          ------------------------------------------------------------
          exact hClosed hQ₀ hQ₀sub_full

        · -- ordinary rule
          simp [hvQ₀] at hcase
          subst hcase
          exact hClosed hQ₀ hQsub

    --------------------------------------------------------------
    -- universe 部分
    --------------------------------------------------------------
    have hsubU_pow := hFix_data.1
    have hsubU : X ⊆ H.U :=
      Finset.mem_powerset.mp hsubU_pow

    have hsubU' : X ⊆ (H.trace v).U := by
      intro x hx
      have hxU := hsubU hx
      have hxv : x ≠ v := by
        intro hxeq; subst hxeq; exact hvX hx
      simpa [HornNF.trace] using
        Finset.mem_erase.mpr ⟨hxv, hxU⟩

    have hTraceFix :
      X ∈ (H.trace v).FixSet := by
      apply (mem_FixSet_iff (H.trace v) X).mpr
      have hpow :
        X ∈ (H.trace v).U.powerset :=
        Finset.mem_powerset.mpr hsubU'
      exact ⟨hpow, hTraceClosed⟩

    exact ⟨hTraceFix, hNotP⟩

  ----------------------------------------------------------------
  -- ← direction
  ----------------------------------------------------------------
  · intro h
    have hTraceFix := h.1
    have hNotP := h.2

    have hTraceData :=
      (mem_FixSet_iff (H.trace v) X).mp hTraceFix
    have hsubU' := hTraceData.1
    have hTraceClosed :
      HornNF.IsClosed (H.trace v) X :=
      hTraceData.2

    --------------------------------------------------------------
    -- v ∉ X
    --------------------------------------------------------------
    have hvX : v ∉ X := by
      intro hv
      have := Finset.mem_powerset.mp hsubU' hv
      simp [HornNF.trace] at this


    --------------------------------------------------------------
    -- H で閉
    --------------------------------------------------------------
    have hClosed :
      HornNF.IsClosed H X := by
      unfold HornNF.IsClosed
      intro h Q hQ hQsub

      by_cases h_eq_v : h = v
      · --subst h_eq_v
        -- Q = P
        have h_single :
          ∀ Q ∈ H.prem v, Q = P := by
          have hcard := Finset.card_eq_one.mp hUnique
          intro Q hQv
          obtain ⟨a, ha⟩ := hcard
          have hQ' :
            Q = a := by
            simpa [ha] using hQv
          have hP' :
            P = a := by
            simpa [ha] using hP
          exact hQ'.trans hP'.symm

        have hQeq : Q = P := by
          subst h_eq_v
          simp_all only [not_false_eq_true]
        subst hQeq
        exfalso
        exact hNotP hQsub

      · -- h ≠ v
        have hQ_trace :
          Q ∈ (H.trace v).prem h := by
          simp [HornNF.trace, h_eq_v]
          by_cases hvQ : v ∈ Q
          · -- v ∈ Q and Q ⊆ X would give v ∈ X, contradicting hvX
            exfalso; exact hvX (hQsub hvQ)
          · -- v ∉ Q: Q is unchanged in trace, and h ∉ Q by NF
            exact ⟨⟨Q, hQ, by simp [hvQ]⟩, H.nf hQ⟩

        simp_all only [not_false_eq_true, and_self, mem_FixSet_iff, Finset.mem_powerset]
        apply hTraceClosed
        on_goal 2 => { exact hQsub
        }
        · simp_all only

    have hFix :
      X ∈ HornNF.FixSet H := by
      apply (mem_FixSet_iff H X).mpr
      have hsubU : X ⊆ H.U := by
        intro x hx
        have hsubU : X ⊆ H.U := by
          intro x hx
          have hxU : x ∈ (H.trace v).U :=
            Finset.mem_powerset.mp hsubU' hx
          exact (Finset.mem_erase.mp hxU).2
        exact hsubU hx

      have hpow :
        X ∈ H.U.powerset :=
        Finset.mem_powerset.mpr hsubU
      exact ⟨hpow, hClosed⟩

    apply Finset.mem_filter.mpr
    exact ⟨hFix, hvX⟩


/--
A usable (proved) version of `deletion_as_forbid`.

To build a `HornWithForbid` object we must supply the extra structure fields
for the forbid set `P` in the trace world (`P ⊆ (H.trace v).U`, `P.Nonempty`, and
`IsClosed (H.trace v) P`). In the singleton-proof wiring these are typically
provided from NF/DR1 lemmas and the chosen-premise facts.

This theorem is the *actual* bridge used to identify the deletion-filtered family
with the forbid FixSet in the trace world.
-/
theorem deletion_as_forbid'
  (H : HornNF α)
  (hDR1 : H.IsDR1)
  (hNEP: H.IsNEP)
  (v : α)
  (P : Finset α)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  (hPsub : P ⊆ (H.trace v).U)
  (hPne : P.Nonempty)
  :
  ∃ S : HornWithForbid α,
    S.H = H.trace v ∧
    S.F = P ∧
    S.FixSet = (HornNF.FixSet H).filter (fun X => v ∉ X) := by
  classical
  -- build the forbid structure on the trace world
  let S : HornWithForbid α :=
    { H := H.trace v
      hDR1 := by
        -- If you have a lemma `HornNF.trace_preserves_DR1`, replace this with it.
        -- For now we keep it as a local assumption via `hDR1` if needed.
        -- (Most developments already have `trace_preserves_DR1`.)
        let hn := HornNF.trace_preserves_DR1 (H := H) (hDR1 := hDR1)
        apply hn
      hNEP := by
        (expose_names; exact @HornNF.isNEP_trace_of_isNEP α inst H v hNEP)
      F := P
      F_subset_U := hPsub
      F_nonempty := hPne }

  refine ⟨S, rfl, rfl, ?_⟩

  -- Extensional equality using the membership characterization.
  ext X
  -- unfold `S.FixSet` and rewrite to the `deletion_filter_equiv` statement.
  have hdel :
    X ∈ (HornNF.FixSet H).filter (fun X => v ∉ X)
      ↔ X ∈ (H.trace v).FixSet ∧ ¬ P ⊆ X :=
    deletion_filter_equiv (α := α) (H := H) (hDR1 := hDR1)
      (v := v) (P := P) (hP := hP) (hUnique := hUnique) (X := X)

  -- `X ∈ S.FixSet` is `X ∈ FixSet(trace)` plus `¬P ⊆ X`.
  -- So both sides match by `hdel`.
  --
  -- Note: `S.FixSet` is `filter (¬ P ⊆ ·)` on `FixSet(trace)` by definition.
  simp [HornWithForbid.FixSet, S, hdel]



end Dr1nds
