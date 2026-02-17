import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Dr1nds.Forbid.Basic
import Dr1nds.Horn.HornWithForbid
import Dr1nds.S6_ConDelNdegId
import Dr1nds.Horn.HornTrace
import LeanCopilot

namespace Dr1nds
open scoped BigOperators


variable {α : Type} [DecidableEq α]


/-- |A|=1（A={v}）かつ head=v の唯一前提が P のとき、
    Hole(Fix(H), {v}) は trace 世界の Hole へ移せる（P 版）。 -/
lemma hole_singleton_eq_hole_trace_prem
  (H : HornNF α) (hDR1 : H.IsDR1)
  (v : α) (P : Finset α)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1) :
  Hole (α := α) (HornNF.FixSet H) ({v} : Finset α)
    =
  Hole (α := α) ((H.trace v).FixSet) P := by
  classical
  ext X
  -- 左を filter に落として deletion_filter_equiv を当て、右を Hole に戻す
  -- ※ deletion_filter_equiv の名前空間は HornWithForbid 側に合わせて調整
  simp [Hole,
    deletion_filter_equiv (H := H) (hDR1 := hDR1) (v := v) (P := P) (hP := hP) (hUnique := hUnique)]


/-- |A|=1（A={v}）かつ head=v が存在しない（prem v = ∅）とき、
    Hole(Fix(H), {v}) は trace 世界の FixSet と一致する（Hole 側の等式）。

    ※Up 側（card の一致）には「v を前提に含む規則が無い」(NoPremContains v) の正規化仮定が必要なので、
      ここではまず Hole 側だけを確定させる。 -/
lemma hole_singleton_eq_fixset_trace_head_free
  (H : HornNF α)
  (v : α)
  (hvU : v ∈ H.U)
  (hfree : H.prem v = ∅) :
  Hole (α := α) (HornNF.FixSet H) ({v} : Finset α)
    =
  HornNF.FixSet (H.trace v) := by
  classical
  -- Hole(C,{v}) = filter (v ∉ ·)
  -- Fix(trace v) = image (erase v) = filter (v ∉ ·)  (head-free trace lemma)
  have hfix :
      HornNF.FixSet (H.trace v)
        =
      (HornNF.FixSet H).filter (fun X => v ∉ X) := by
    -- start from the image description
    simpa [HornNF.trace_fixset_head_free (H := H) (v := v) (hvU := hvU) (hfree := hfree)]
      using (by
        -- convert `image (erase v)` to `filter (v ∉ ·)` by ext
        ext X
        constructor
        · intro hX
          rcases Finset.mem_image.mp hX with ⟨Y, hY, hYX⟩
          subst hYX
          refine Finset.mem_filter.mpr ?_
          refine ⟨?_, Finset.notMem_erase v Y⟩
          -- show `Y.erase v ∈ FixSet H`
          -- unpack `hY : Y ∈ FixSet H` into subset/closed data
          have hYpow : Y ∈ H.U.powerset := (Finset.mem_filter.mp hY).1
          have hYsub : Y ⊆ H.U := Finset.mem_powerset.mp hYpow
          have hYclosed : H.IsClosed Y := (Finset.mem_filter.mp hY).2
          -- now prove `Y.erase v` is closed and still inside `U`
          refine Finset.mem_filter.mpr ?_
          refine ⟨?_, ?_⟩
          · -- `Y.erase v ⊆ U`
            rw [Finset.mem_powerset]
            intro x hx
            exact hYsub (Finset.mem_of_mem_erase hx)
          · -- `Y.erase v` is closed (head-free means no rule with head `v`)
            -- unfold the closure condition and use closedness of `Y`
            intro h Q hQ hQsub
            have hne : h ≠ v := by
              intro hEq
              subst hEq
              -- contradiction since `prem v = ∅`
              simp_all only [mem_FixSet_iff, and_self, Finset.mem_powerset, Finset.notMem_empty]
            have hQsubY : Q ⊆ Y := by
              intro x hx
              exact Finset.mem_of_mem_erase (hQsub hx)
            have hhY : h ∈ Y := by
              -- `hYclosed : H.IsClosed Y` expects the premise-membership proof first.
              exact hYclosed (h := h) hQ hQsubY

            -- push membership to `Y.erase v`
            have : h ∈ Y.erase v := by
              simp [Finset.mem_erase, hhY, hne]
            exact this
        · intro hX
          rcases Finset.mem_filter.mp hX with ⟨hY, hvX⟩
          refine Finset.mem_image.mpr ?_
          refine ⟨X, hY, ?_⟩
          simp [Finset.erase_eq_of_notMem hvX])

  -- now rewrite both sides to the common filter form
  calc
    Hole (α := α) (HornNF.FixSet H) ({v} : Finset α)
        = (HornNF.FixSet H).filter (fun X => v ∉ X) := by
            simp [Hole]
    _ = HornNF.FixSet (H.trace v) := by
         simp_all only

/-- head-free（prem v = ∅）かつ「v を前提に含む規則が無い」(正規化仮定) の下で
`Up(FixSet H,{v})` と `FixSet (H.trace v)` は `insert v` / `erase v` で双射。 -/
lemma card_up_fixset_eq_card_fixset_trace_head_free
  (H : HornNF α)
  (v : α)
  (hvU : v ∈ H.U)
  (hfree : H.prem v = ∅)
  (hNoPremV : ∀ {h : α} {P : Finset α}, P ∈ H.prem h → v ∉ P) :
  (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card
    =
  (HornNF.FixSet (H.trace v)).card := by
  classical

  -- 右 → 左 : X ∈ Fix(trace) ↦ insert v X ∈ Up(Fix(H),{v})
  have h_forw :
      ∀ {X : Finset α}, X ∈ HornNF.FixSet (H.trace v) →
        insert v X ∈ Up (HornNF.FixSet H) ({v} : Finset α) := by
    intro X hX
    have hXdata := Finset.mem_filter.mp hX
    have hXpow : X ∈ (H.trace v).U.powerset := hXdata.1
    have hXclosedTrace : (H.trace v).IsClosed X := hXdata.2
    have hXsubUerase : X ⊆ (H.trace v).U := Finset.mem_powerset.mp hXpow
    have hXsubUerase' : X ⊆ H.U.erase v := by
      simpa [HornNF.trace] using hXsubUerase

    have hvX : v ∉ X := by
      intro hv
      have := hXsubUerase' hv
      exact (Finset.mem_erase.mp this).1 rfl

    -- subset: insert v X ⊆ U
    have hsubU : insert v X ⊆ H.U := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxX
      · exact hvU
      · have hxUerase := hXsubUerase' hxX
        exact (Finset.mem_erase.mp hxUerase).2

    -- closedness of insert v X in H (uses hNoPremV)
    have hclosed_ins : HornNF.IsClosed H (insert v X) := by
      intro h P hP hPsub
      have hvP : v ∉ P := hNoPremV hP
      have hPsubX : P ⊆ X := by
        intro x hxP
        have hxIns : x ∈ insert v X := hPsub hxP
        rcases Finset.mem_insert.mp hxIns with rfl | hxX
        · exfalso; exact hvP hxP
        · exact hxX
      -- transfer closedness: trace and H coincide on sets not containing v
      have hclosedH_X : HornNF.IsClosed H X :=
        (HornNF.trace_isClosed_iff_head_free (H := H) (v := v) (hfree := hfree) (hvX := hvX)).1
          hXclosedTrace
      have hhX : h ∈ X := hclosedH_X hP hPsubX
      exact Finset.mem_insert_of_mem hhX

    have hFix : insert v X ∈ HornNF.FixSet H := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, hclosed_ins⟩
      exact Finset.mem_powerset.mpr hsubU

    -- membership in Up: (FixSet H).filter (v ∈ ·)
    exact Finset.mem_filter.mpr ⟨hFix, by
      simp_all only [mem_FixSet_iff, and_self, Finset.mem_powerset, Finset.singleton_subset_iff, Finset.mem_insert,
        or_false]
    ⟩

  -- 左 → 右 : Y ∈ Up ↦ erase v Y ∈ Fix(trace)
  have h_back :
      ∀ {Y : Finset α}, Y ∈ Up (HornNF.FixSet H) ({v} : Finset α) →
        Y.erase v ∈ HornNF.FixSet (H.trace v) := by
    intro Y hY
    rcases Finset.mem_filter.mp hY with ⟨hYfix, hvY⟩

    have hYdata := Finset.mem_filter.mp hYfix
    have hYpow : Y ∈ H.U.powerset := hYdata.1
    have hYclosed : H.IsClosed Y := hYdata.2
    have hYsubU : Y ⊆ H.U := Finset.mem_powerset.mp hYpow

    -- subset into U.erase v
    have hsubUerase : Y.erase v ⊆ H.U.erase v := by
      intro x hx
      have hxY : x ∈ Y := Finset.mem_of_mem_erase hx
      have hxU : x ∈ H.U := hYsubU hxY
      refine Finset.mem_erase.mpr ?_
      exact ⟨(Finset.mem_erase.mp hx).1, hxU⟩

    have hpow' : Y.erase v ∈ (H.trace v).U.powerset := by
      simpa [HornNF.trace] using (Finset.mem_powerset.mpr hsubUerase)

    have hvX : v ∉ Y.erase v := by simp

    -- show IsClosed H (Y.erase v) from IsClosed H Y
    have hclosedH : HornNF.IsClosed H (Y.erase v) := by
      intro h P hP hPsub
      have hPsubY : P ⊆ Y := by
        intro x hxP
        exact Finset.mem_of_mem_erase (hPsub hxP)
      have hhY : h ∈ Y := hYclosed hP hPsubY
      by_cases hEq : h = v
      · subst hEq
        simp_all only [mem_FixSet_iff, and_self, Finset.mem_powerset, Finset.notMem_empty]
      · exact Finset.mem_erase.mpr ⟨hEq, hhY⟩

    have hclosedTrace : HornNF.IsClosed (H.trace v) (Y.erase v) :=
      (HornNF.trace_isClosed_iff_head_free (H := H) (v := v) (hfree := hfree) (hvX := hvX)).2
        hclosedH

    refine Finset.mem_filter.mpr ?_
    refine ⟨hpow', hclosedTrace⟩

  -- card equality via a bijection (Finset.card_bij)
  have hcard : (HornNF.FixSet (H.trace v)).card =
      (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card := by
    classical
    refine Finset.card_bij
      (s := HornNF.FixSet (H.trace v))
      (t := Up (α := α) (HornNF.FixSet H) ({v} : Finset α))
      (i := fun X _ => insert v X)
      (hi := by
        intro X hX
        exact h_forw hX)
      (i_inj := by
        intro X hX X' hX' hEq
        -- erase cancels insert since v ∉ X, v ∉ X'
        have hvX : v ∉ X := by
          have hXpow : X ∈ (H.trace v).U.powerset := (Finset.mem_filter.mp hX).1
          have hXsub : X ⊆ (H.trace v).U := Finset.mem_powerset.mp hXpow
          have hXsub' : X ⊆ H.U.erase v := by
            simpa [HornNF.trace] using hXsub
          intro hv
          have := hXsub' hv
          exact (Finset.mem_erase.mp this).1 rfl
        have hvX' : v ∉ X' := by
          have hXpow : X' ∈ (H.trace v).U.powerset := (Finset.mem_filter.mp hX').1
          have hXsub : X' ⊆ (H.trace v).U := Finset.mem_powerset.mp hXpow
          have hXsub' : X' ⊆ H.U.erase v := by
            simpa [HornNF.trace] using hXsub
          intro hv
          have := hXsub' hv
          exact (Finset.mem_erase.mp this).1 rfl
        have := congrArg (fun Z => Z.erase v) hEq
        -- use erase_insert to cancel insert
        have hcancel : X = X' := by
          simpa [Finset.erase_insert, hvX, hvX'] using this
        exact hcancel)
      (i_surj := by
        intro Y hY
        refine ⟨Y.erase v, h_back hY, ?_⟩
        -- derive `v ∈ Y` from `{v} ⊆ Y`
        rcases Finset.mem_filter.mp hY with ⟨_, hvYsub⟩
        have hvYmem : v ∈ Y := by
          have : v ∈ ({v} : Finset α) := by simp
          exact hvYsub this
        -- now insert/erase cancels
        simp_all only [mem_FixSet_iff, Finset.mem_powerset, Up_singleton_eq_filter_mem, Finset.mem_filter,
          Finset.mem_insert, true_or, and_true, and_imp, Finset.singleton_subset_iff, Finset.insert_erase]
      )

  exact hcard.symm

/--
Head-free singleton bridge (equality):
  NDS_corr (n+1) (FixSet H) {v} = NDS n (FixSet (H.trace v)).
-/
lemma NDS_corr_singleton_head_free_eq
  (n : Nat)
  (H : HornNF α) (v : α)
  (hvU : v ∈ H.U)
  (hfree : H.prem v = ∅)
  (hNoPremV : ∀ {h : α} {P : Finset α}, P ∈ H.prem h → v ∉ P) :
  NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α)
    =
  NDS (α := α) n (HornNF.FixSet (H.trace v)) := by
  classical
  have hHole : Hole (α := α) (HornNF.FixSet H) ({v} : Finset α)
      = HornNF.FixSet (H.trace v) :=
    hole_singleton_eq_fixset_trace_head_free (α := α)
      (H := H) (v := v) (hvU := hvU) (hfree := hfree)

  have hUpCard : (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card
      = (HornNF.FixSet (H.trace v)).card :=
    card_up_fixset_eq_card_fixset_trace_head_free (α := α)
      (H := H) (v := v) (hvU := hvU) (hfree := hfree) (hNoPremV := hNoPremV)

  calc
    NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α)
        = NDS (α := α) n.succ (Hole (α := α) (HornNF.FixSet H) ({v} : Finset α))
            + (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card := by
          simp [Dr1nds.NDS_corr]
    _ = NDS (α := α) n.succ (HornNF.FixSet (H.trace v))
          + (HornNF.FixSet (H.trace v)).card := by
          simp [hHole]
          simp_all only [Hole_singleton_eq_filter_notmem, Up_singleton_eq_filter_mem]
    _ = (NDS (α := α) n (HornNF.FixSet (H.trace v))
          - ((HornNF.FixSet (H.trace v)).card : Int))
          + (HornNF.FixSet (H.trace v)).card := by
          -- NDS_succ was added in S6
          simp [Dr1nds.Accounting.NDS_succ]
    _ = NDS (α := α) n (HornNF.FixSet (H.trace v)) := by
          simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- head-free singleton: if the trace-world is ≤0 then the singleton-forbid world is ≤0. -/
lemma Qcorr_singleton_head_free_of_Q_trace
  (n : Nat)
  (H : HornNF α) (v : α)
  (hvU : v ∈ H.U)
  (hfree : H.prem v = ∅)
  (hNoPremV : ∀ {h : α} {P : Finset α}, P ∈ H.prem h → v ∉ P)
  (hQ : NDS (α := α) n (HornNF.FixSet (H.trace v)) ≤ 0) :
  NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α) ≤ 0 := by
  simpa [NDS_corr_singleton_head_free_eq (α := α)
    (n := n) (H := H) (v := v) (hvU := hvU) (hfree := hfree) (hNoPremV := hNoPremV)] using hQ

/--
(TODO) Has-head singleton: under the normalization `hNoPremV` (no premise contains `v`),
`Up(FixSet H,{v})` should be in bijection with `FixSet (H.trace v)`.

We postpone this because it needs a lemma relating `IsClosed H` and `IsClosed (H.trace v)` on sets not containing `v`
in the has-head case (i.e. without assuming `H.prem v = ∅`).
-/
lemma card_up_fixset_eq_card_fixset_trace_has_head
  (H : HornNF α)
  (v : α)
  (hvU : v ∈ H.U)
  (hNoPremV : ∀ {h : α} {P : Finset α}, P ∈ H.prem h → v ∉ P) :
  (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card
    =
  (HornNF.FixSet (H.trace v)).card := by
  classical

  -- Forward map: X ∈ Fix(trace v) ↦ insert v X ∈ Up(Fix(H), {v})
  have h_forw :
      ∀ {X : Finset α}, X ∈ HornNF.FixSet (H.trace v) →
        insert v X ∈ Up (α := α) (HornNF.FixSet H) ({v} : Finset α) := by
    intro X hX
    have hXdata := Finset.mem_filter.mp hX
    have hXpow : X ∈ (H.trace v).U.powerset := hXdata.1
    have hXclosedTrace : (H.trace v).IsClosed X := hXdata.2
    have hXsubUerase : X ⊆ (H.trace v).U := Finset.mem_powerset.mp hXpow
    have hXsubUerase' : X ⊆ H.U.erase v := by
      simpa [HornNF.trace] using hXsubUerase

    -- v ∉ X
    have hvX : v ∉ X := by
      intro hv
      have := hXsubUerase' hv
      exact (Finset.mem_erase.mp this).1 rfl

    -- subset: insert v X ⊆ U
    have hsubU : insert v X ⊆ H.U := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxX
      · exact hvU
      · have hxUerase := hXsubUerase' hxX
        exact (Finset.mem_erase.mp hxUerase).2

    -- closedness of insert v X in H (use the dedicated lemma from HornTrace)
    have hclosed_ins : HornNF.IsClosed H (insert v X) := by
      -- prove closedness for `X ∪ {v}` using the lemma in `HornTrace.lean`
      have hclosed_union : HornNF.IsClosed H (X ∪ ({v} : Finset α)) :=
        Dr1nds.HornNF.isClosed_union_singleton_of_noPremContains
          (H := H) (v := v)
          (hNoPremV := by
            intro h Q hQ
            exact hNoPremV (h := h) (P := Q) hQ)
          (Y := X) hXclosedTrace
      -- rewrite `insert v X` as `X ∪ {v}`
      simp_all only [mem_FixSet_iff, and_self, Finset.mem_powerset, Finset.union_singleton]

    have hFix : insert v X ∈ HornNF.FixSet H := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_powerset.mpr hsubU, hclosed_ins⟩

    -- membership in Up: filter ( {v} ⊆ · )
    refine Finset.mem_filter.mpr ?_
    refine ⟨hFix, ?_⟩
    -- {v} ⊆ insert v X
    intro x hx
    let fm := Finset.mem_insert_self v X
    simp_all only [mem_FixSet_iff, and_self, Finset.mem_powerset, Finset.mem_singleton]

  -- Backward map: Y ∈ Up(Fix(H), {v}) ↦ erase v Y ∈ Fix(trace v)
  have h_back :
      ∀ {Y : Finset α}, Y ∈ Up (α := α) (HornNF.FixSet H) ({v} : Finset α) →
        Y.erase v ∈ HornNF.FixSet (H.trace v) := by
    intro Y hY
    rcases Finset.mem_filter.mp hY with ⟨hYfix, hvYsub⟩

    have hYdata := Finset.mem_filter.mp hYfix
    have hYpow : Y ∈ H.U.powerset := hYdata.1
    have hYclosed : H.IsClosed Y := hYdata.2
    have hYsubU : Y ⊆ H.U := Finset.mem_powerset.mp hYpow

    -- subset into U.erase v
    have hsubUerase : Y.erase v ⊆ H.U.erase v := by
      intro x hx
      have hxY : x ∈ Y := Finset.mem_of_mem_erase hx
      have hxU : x ∈ H.U := hYsubU hxY
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hxU⟩

    have hpow' : Y.erase v ∈ (H.trace v).U.powerset := by
      simpa [HornNF.trace] using (Finset.mem_powerset.mpr hsubUerase)

    -- closedness in trace
    have hclosedTrace : HornNF.IsClosed (H.trace v) (Y.erase v) := by
      intro h P hP hPsub
      by_cases hh : h = v
      · subst hh
        -- trace prem at v is empty
        simp [HornNF.trace] at hP
      · -- h ≠ v
        have hPremEq : (H.trace v).prem h = H.prem h :=
          HornNF.trace_prem_eq_of_noPremContains (H := H) (v := v)
            (hNoPremV := by
              intro h' P' hP'
              exact hNoPremV (h := h') (P := P') hP')
            (hneq := hh)
        have hP' : P ∈ H.prem h := by
          simpa [hPremEq] using hP
        -- lift subset to Y (since v ∉ P)
        have hvP : v ∉ P := hNoPremV hP'
        have hPsubY : P ⊆ Y := by
          intro x hxP
          have hxE : x ∈ Y.erase v := hPsub hxP
          exact Finset.mem_of_mem_erase hxE
        have hhY : h ∈ Y := hYclosed (h := h) (P := P) hP' hPsubY
        exact Finset.mem_erase.mpr ⟨hh, hhY⟩

    exact Finset.mem_filter.mpr ⟨hpow', hclosedTrace⟩

  -- card equality via bijection between Fix(trace) and Up(Fix(H),{v})
  have hcard : (HornNF.FixSet (H.trace v)).card =
      (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card := by
    classical
    refine Finset.card_bij
      (s := HornNF.FixSet (H.trace v))
      (t := Up (α := α) (HornNF.FixSet H) ({v} : Finset α))
      (i := fun X _ => insert v X)
      (hi := by
        intro X hX
        exact h_forw hX)
      (i_inj := by
        intro X hX X' hX' hEq
        -- erase cancels insert since v ∉ X, v ∉ X'
        have hvX : v ∉ X := by
          have hXpow : X ∈ (H.trace v).U.powerset := (Finset.mem_filter.mp hX).1
          have hXsub : X ⊆ (H.trace v).U := Finset.mem_powerset.mp hXpow
          have hXsub' : X ⊆ H.U.erase v := by
            simpa [HornNF.trace] using hXsub
          intro hv
          have := hXsub' hv
          exact (Finset.mem_erase.mp this).1 rfl
        have hvX' : v ∉ X' := by
          have hXpow : X' ∈ (H.trace v).U.powerset := (Finset.mem_filter.mp hX').1
          have hXsub : X' ⊆ (H.trace v).U := Finset.mem_powerset.mp hXpow
          have hXsub' : X' ⊆ H.U.erase v := by
            simpa [HornNF.trace] using hXsub
          intro hv
          have := hXsub' hv
          exact (Finset.mem_erase.mp this).1 rfl
        have := congrArg (fun Z => Z.erase v) hEq
        have hcancel : X = X' := by
          simpa [Finset.erase_insert, hvX, hvX'] using this
        exact hcancel)
      (i_surj := by
        intro Y hY
        refine ⟨Y.erase v, h_back hY, ?_⟩
        -- derive `v ∈ Y` from `{v} ⊆ Y`
        rcases Finset.mem_filter.mp hY with ⟨_, hvYsub⟩
        have hvYmem : v ∈ Y := by
          have : v ∈ ({v} : Finset α) := by simp
          exact hvYsub this
        -- insert/erase cancels
        simp [Finset.insert_erase hvYmem])

  exact hcard.symm

namespace HornNF

/--
Alias (expected name): under the normalization assumption that no premise contains `v`,
`Up(FixSet H,{v})` has the same cardinality as `FixSet (H.trace v)`.

This is the has-head/general version (it does not assume `H.prem v = ∅`).
-/
lemma card_up_fixset_eq_card_fixset_trace
  (H : HornNF α)
  (v : α)
  (hvU : v ∈ H.U)
  (hNoPremV : ∀ {h : α} {P : Finset α}, P ∈ H.prem h → v ∉ P) :
  (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card
    =
  (HornNF.FixSet (H.trace v)).card := by
  simpa using
    (Dr1nds.card_up_fixset_eq_card_fixset_trace_has_head (α := α)
      (H := H) (v := v) (hvU := hvU) (hNoPremV := hNoPremV))

end HornNF

/--
(TODO) Has-head singleton bridge (equality, P-version):
  NDS_corr (n+1) (FixSet H) {v} = NDS_corr n (FixSet (H.trace v)) P.

This will be completed after the Up-card bridge above is proved.
-/
/-/
Has-head singleton bridge (equality, P-version):
  NDS_corr (n+1) (FixSet H) {v} = NDS_corr n (FixSet (H.trace v)) P.

This is proved from:
- `hole_singleton_eq_hole_trace_prem` (SHIFT1 / Hole transfer),
- `card_up_fixset_eq_card_fixset_trace_has_head` (the remaining Up-card kernel),
- the tautological partition `Up + Hole = all` inside the trace world,
- the accounting identity `NDS_succ` from S6.
-/
lemma NDS_corr_singleton_hasHead_P_eq
  (n : Nat)
  (H : HornNF α) (hDR1 : H.IsDR1)
  (v : α) (P : Finset α)
  (hvU : v ∈ H.U)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  (hNoPremV : ∀ {h : α} {Q : Finset α}, Q ∈ H.prem h → v ∉ Q) :
  NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α)
    =
  NDS_corr (α := α) n (HornNF.FixSet (H.trace v)) P := by
  classical

  -- SHIFT1 (Hole transfer)
  have hHole :
      Hole (α := α) (HornNF.FixSet H) ({v} : Finset α)
        =
      Hole (α := α) ((H.trace v).FixSet) P :=
    hole_singleton_eq_hole_trace_prem (α := α)
      (H := H) (hDR1 := hDR1) (v := v) (P := P)
      (hP := hP) (hUnique := hUnique)

  -- Up-card kernel (left Up equals total card of trace fixset)
  have hUpCard :
      (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card
        =
      (HornNF.FixSet (H.trace v)).card :=
    card_up_fixset_eq_card_fixset_trace_has_head (α := α)
      (H := H) (v := v) (hvU := hvU)
      (hNoPremV := by
        intro h Q hQ
        exact hNoPremV (h := h) (Q := Q) hQ)

  -- Tautological partition in the trace world: Up + Hole = all
  have hpart :
      (Up (α := α) (HornNF.FixSet (H.trace v)) P).card
        + (Hole (α := α) (HornNF.FixSet (H.trace v)) P).card
        = (HornNF.FixSet (H.trace v)).card := by
    classical
    -- `Up` and `Hole` are complementary filters on `FixSet (H.trace v)` for the predicate `P ⊆ ·`.
    simpa [Up, Hole, Finset.filter_filter, and_left_comm, and_assoc, and_comm]
      using (Finset.filter_card_add_filter_neg_card_eq_card
        (s := HornNF.FixSet (H.trace v))
        (p := fun X : Finset α => P ⊆ X))


  -- Now the accounting calculation
  calc
    NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α)
        = NDS (α := α) n.succ (Hole (α := α) (HornNF.FixSet H) ({v} : Finset α))
            + (Up (α := α) (HornNF.FixSet H) ({v} : Finset α)).card := by
          simp [Dr1nds.NDS_corr]
    _ = NDS (α := α) n.succ (Hole (α := α) ((H.trace v).FixSet) P)
          + (HornNF.FixSet (H.trace v)).card := by
          simp_all only [Hole_singleton_eq_filter_notmem, Up_singleton_eq_filter_mem, Nat.succ_eq_add_one]
    _ = (NDS (α := α) n (Hole (α := α) ((H.trace v).FixSet) P)
          - ((Hole (α := α) ((H.trace v).FixSet) P).card : Int))
          + (HornNF.FixSet (H.trace v)).card := by
          -- `NDS_succ` from S6: NDS (n+1) = NDS n - card
          simp [Dr1nds.Accounting.NDS_succ]
    _ = (NDS (α := α) n (Hole (α := α) ((H.trace v).FixSet) P)
          - ((Hole (α := α) ((H.trace v).FixSet) P).card : Int))
          + ((Up (α := α) (HornNF.FixSet (H.trace v)) P).card
             + (Hole (α := α) (HornNF.FixSet (H.trace v)) P).card) := by
          -- replace `FixSet.card` using the partition identity
          have hFixCardInt : (↑(HornNF.FixSet (H.trace v)).card : Int)
              = (↑(Up (α := α) (HornNF.FixSet (H.trace v)) P).card : Int)
                + (↑(Hole (α := α) (HornNF.FixSet (H.trace v)) P).card : Int) := by
            -- cast the Nat equality `hpart` into Int and rewrite `↑(a+b)`.
            have := congrArg (fun z : Nat => (z : Int)) hpart
            -- `this` has the form `↑(up + hole) = ↑fix`; rearrange.
            simpa [Int.natCast_add, add_comm, add_left_comm, add_assoc] using this.symm

          -- rewrite `FixSet.card` using the partition identity
          simp [hFixCardInt, add_left_comm, add_comm]
    _ = NDS (α := α) n (Hole (α := α) ((H.trace v).FixSet) P)
          + (Up (α := α) (HornNF.FixSet (H.trace v)) P).card := by
          -- cancel `- Hole.card` with `+ Hole.card`
          abel
    _ = NDS_corr (α := α) n (HornNF.FixSet (H.trace v)) P := by
          simp [Dr1nds.NDS_corr]


/-- has-head singleton: if the trace-world Qcorr holds, then the singleton-forbid world Qcorr holds.

This is the direct corollary of `NDS_corr_singleton_hasHead_P_eq`.
-/
lemma Qcorr_singleton_hasHead_of_Qcorr_traceP
  (n : Nat)
  (H : HornNF α) (hDR1 : H.IsDR1)
  (v : α) (P : Finset α)
  (hvU : v ∈ H.U)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  (hNoPremV : ∀ {h : α} {Q : Finset α}, Q ∈ H.prem h → v ∉ Q)
  (hQ : NDS_corr (α := α) n (HornNF.FixSet (H.trace v)) P ≤ 0) :
  NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α) ≤ 0 := by
  -- rewrite by the established equality and finish
  simpa [NDS_corr_singleton_hasHead_P_eq (α := α)
    (n := n) (H := H) (hDR1 := hDR1) (v := v) (P := P)
    (hvU := hvU) (hP := hP) (hUnique := hUnique) (hNoPremV := hNoPremV)] using hQ


/-- |A|=1 bridge, packaged as a two-case lemma.

If `prem v = ∅` (head-free) we reduce to `NDS ≤ 0` on the trace world.
If `prem v` is nonempty (has-head) we pick the unique premise `P` (using DR1) and reduce to
`NDS_corr ≤ 0` on the trace world with forbid `P`.

This lemma is intended as the *only* entry point used by `LocalKernels.lean` for the |A|=1 branch.

NOTE: the proof is provided as a skeleton because the case split and `P` selection policy may vary
in the project (e.g. you may want an explicit `P` parameter upstream). Replace the `sorry` blocks
once the upstream API is frozen.
-/
lemma Qcorr_singleton_by_trace_cases
  (n : Nat)
  (H : HornNF α)
  (hDR1 : H.IsDR1)
  (v : α)
  (hvU : v ∈ H.U)
  (hNoPremV : ∀ {h : α} {Q : Finset α}, Q ∈ H.prem h → v ∉ Q)
  (hQ_trace_NDS : NDS (α := α) n (HornNF.FixSet (H.trace v)) ≤ 0)
  (hQ_trace_Qcorr : ∀ (P : Finset α), P ∈ H.prem v →
      NDS_corr (α := α) n (HornNF.FixSet (H.trace v)) P ≤ 0) :
  NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α) ≤ 0 := by
  classical
  by_cases hfree : H.prem v = ∅
  · -- head-free branch
    exact Qcorr_singleton_head_free_of_Q_trace (α := α)
      (n := n) (H := H) (v := v) (hvU := hvU)
      (hfree := hfree) (hNoPremV := hNoPremV) (hQ := hQ_trace_NDS)
  · -- has-head branch: pick the unique premise P (DR1) and reduce to trace Qcorr(P)
    have hNonempty : (H.prem v).Nonempty := by
      -- `prem v ≠ ∅` is the definitional content of “has-head” on the premise-set level
      simpa [Finset.nonempty_iff_ne_empty] using hfree
    -- choose a witness `P` from `prem v`
    rcases hNonempty with ⟨P, hP⟩
    have hUnique : (H.prem v).card = 1 := by
      -- DR1 + nonempty
      exact prem_card_eq_one_of_DR1_of_ne_empty (H := H) (v := v) (hDR1 := hDR1)
        (by
          intro hEq
          exact hfree hEq)
    -- now discharge using the has-head bridge
    have hQp : NDS_corr (α := α) n (HornNF.FixSet (H.trace v)) P ≤ 0 :=
      hQ_trace_Qcorr P hP
    exact Qcorr_singleton_hasHead_of_Qcorr_traceP (α := α)
      (n := n) (H := H) (hDR1 := hDR1) (v := v) (P := P)
      (hvU := hvU) (hP := hP) (hUnique := hUnique) (hNoPremV := hNoPremV) (hQ := hQp)


/-- Convenience: the equality form of the has-head bridge rewritten as a `≤ 0` goal.

This is often the exact shape needed in `LocalKernels.lean`.
-/

lemma Qcorr_singleton_hasHead_P_of_Qcorr_traceP
  (n : Nat)
  (H : HornNF α) (hDR1 : H.IsDR1)
  (v : α) (P : Finset α)
  (hvU : v ∈ H.U)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  (hNoPremV : ∀ {h : α} {Q : Finset α}, Q ∈ H.prem h → v ∉ Q)
  (hQ : NDS_corr (α := α) n (HornNF.FixSet (H.trace v)) P ≤ 0) :
  NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α) ≤ 0 :=
by
  exact Qcorr_singleton_hasHead_of_Qcorr_traceP (α := α)
    (n := n) (H := H) (hDR1 := hDR1) (v := v) (P := P)
    (hvU := hvU) (hP := hP) (hUnique := hUnique) (hNoPremV := hNoPremV) (hQ := hQ)


/--
Kernel (singleton forbid, no-head case) in the *step* shape expected by the induction wiring:
if the trace-world is forbid-free and satisfies `NDS ≤ 0`, then the original singleton-forbid world
satisfies `NDS_corr ≤ 0`.

This is just a naming wrapper around `Qcorr_singleton_head_free_of_Q_trace`.
-/
lemma qcorr_singleton_noHead_step
  (n : Nat)
  (H : HornNF α)
  (v : α)
  (hvU : v ∈ H.U)
  (hfree : H.prem v = ∅)
  (hNoPremV : ∀ {h : α} {Q : Finset α}, Q ∈ H.prem h → v ∉ Q)
  (hQ_trace : NDS (α := α) n (HornNF.FixSet (H.trace v)) ≤ 0) :
  NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α) ≤ 0 := by
  exact Qcorr_singleton_head_free_of_Q_trace (α := α)
    (n := n) (H := H) (v := v) (hvU := hvU)
    (hfree := hfree) (hNoPremV := hNoPremV) (hQ := hQ_trace)


/--
Kernel (singleton forbid, has-head case) in the *step* shape expected by the induction wiring:
if the trace-world with forbid `P` satisfies `NDS_corr ≤ 0`, then the original singleton-forbid world
satisfies `NDS_corr ≤ 0`.

This is just a naming wrapper around `Qcorr_singleton_hasHead_of_Qcorr_traceP`.
-/
lemma qcorr_singleton_hasHead_P_step
  (n : Nat)
  (H : HornNF α) (hDR1 : H.IsDR1)
  (v : α) (P : Finset α)
  (hvU : v ∈ H.U)
  (hP : P ∈ H.prem v)
  (hUnique : (H.prem v).card = 1)
  (hNoPremV : ∀ {h : α} {Q : Finset α}, Q ∈ H.prem h → v ∉ Q)
  (hQ_trace : NDS_corr (α := α) n (HornNF.FixSet (H.trace v)) P ≤ 0) :
  NDS_corr (α := α) n.succ (HornNF.FixSet H) ({v} : Finset α) ≤ 0 := by
  exact Qcorr_singleton_hasHead_of_Qcorr_traceP (α := α)
    (n := n) (H := H) (hDR1 := hDR1)
    (v := v) (P := P)
    (hvU := hvU) (hP := hP) (hUnique := hUnique)
    (hNoPremV := hNoPremV) (hQ := hQ_trace)


#print axioms Dr1nds.NDS_corr_singleton_head_free_eq
#print axioms Dr1nds.NDS_corr_singleton_hasHead_P_eq
#print axioms Dr1nds.HornNF.card_up_fixset_eq_card_fixset_trace

end Dr1nds
