import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Dr1nds.S0_CoreDefs
import Dr1nds.Horn.Horn   -- HornNF
import Dr1nds.Horn.HornTrace

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-
============================================================
  HornWithForbid (DR1 固定バージョン)

  意味：
    DR1 Horn 系 + ちょうど1つの forbid 閉集合
============================================================
-/

structure HornWithForbid (α : Type) [DecidableEq α] where
  H : HornNF α
  hDR1 : H.IsDR1

  F : Finset α                    -- forbid set

  F_subset_U : F ⊆ H.U
  F_nonempty : F.Nonempty
  F_closed : HornNF.IsClosed H F

attribute [simp] HornWithForbid.F_subset_U


/- ------------------------------------------------------------
  FixSet
------------------------------------------------------------ -/

noncomputable def HornWithForbid.FixSet
  (S : HornWithForbid α) :
  Finset (Finset α) :=
  (HornNF.FixSet S.H).filter
    (fun X => ¬ S.F ⊆ X)

@[simp] lemma mem_FixSet_withForbid_iff
  (S : HornWithForbid α)
  (X : Finset α) :
  X ∈ S.FixSet
  ↔
  X ∈ HornNF.FixSet S.H ∧ ¬ S.F ⊆ X := by
  classical
  simp [HornWithForbid.FixSet]

lemma mem_FixSet_withForbid_subset_U
  (S : HornWithForbid α)
  {X : Finset α}
  (hX : X ∈ S.FixSet) :
  X ⊆ S.H.U := by
  classical
  have h := (mem_FixSet_withForbid_iff S X).1 hX
  -- use underlying HornNF property
  exact mem_FixSet_subset_U S.H h.1


/- ------------------------------------------------------------
  基本補題
------------------------------------------------------------ -/



/-
============================================================
  NDS (for future use)
============================================================
-/

noncomputable def HornWithForbid.NDS
  (S : HornWithForbid α) : Int :=
  Dr1nds.NDS (α := α) S.H.U.card S.FixSet


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
Unique-head deletion can be represented as
trace + a single forbid set.

If `v` has exactly one premise `P`, then
the deletion of `v` from the closure system
of `H` is equivalent to the FixSet of the
trace system together with forbid `P`.

This is the core Del = Hole bridge in the DR1 world.
-/
theorem deletion_as_forbid
  (H : HornNF α)
  (hDR1 : H.IsDR1)
  (v : α)
  (P : Finset α)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  :
  ∃ S : HornWithForbid α,
    S.H = H.trace v ∧
    S.F = P ∧
    S.FixSet
      =
    (HornNF.FixSet H).filter (fun X => v ∉ X) := by
  sorry

end Dr1nds
