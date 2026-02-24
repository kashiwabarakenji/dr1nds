import Dr1nds.SetFamily.CoreDefs
import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornClosure
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.Parallel
import Dr1nds.Forbid.HornWithForbid
import Dr1nds.Induction.Statements
import Dr1nds.SetFamily.ConDelNdegId
import Mathlib.Tactic

namespace Dr1nds

variable {α : Type} [DecidableEq α]

-- =====================================
-- (0) parallel / no-parallel 分岐（独立核）
-- =====================================

/- Parallel / NoParallel for forbid-free packs. -/
abbrev Parallel0 (P : Pack0 α) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ P.H.closure {v} ∧ v ∈ P.H.closure {u}
abbrev NoParallel0 (P : Pack0 α) : Prop := ¬ Parallel0 P

/-- Parallel / NoParallel for forbid packs. 禁止集合の中にパラレルがあるかどうか。-/
abbrev Parallel1 (F: HornWithForbid α) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ F.F ∧ v ∈ F.F ∧ u ∈ F.H.closure {v} ∧ v ∈ F.H.closure {u}
abbrev NoParallel1  (F: HornWithForbid α): Prop := ¬ Parallel1 F

--使わないかも。
def HasParallel0 (P : Pack0 α) (v:α) :=
  ∃ u, u ≠ v ∧ u ∈ P.H.closure {v} ∧ v ∈ P.H.closure {u}

def HasParallel1 (F : HornWithForbid α) (v:α) :=
  ∃ u, u ≠ v ∧ u ∈ F.H.closure {v} ∧ v ∈ F.H.closure {u}

---ほかの言明に合わせて2段階にする。getのほうは、頂点をtraceしたものがNDSが大きくなくて、Packの条件を満たすというもの。頂点を引数に入れる。
---上のほうの言明は、帰納法の仮定を仮定すると、Q n が成り立つというもの。
/-- Wiring helper: advance one step under the parallel-branch (forbid-free). -/
noncomputable def Q_of_parallel_get
  (P : Pack0 α) (v : α) : Pack0 α where
  H := P.H.trace v
  hDR1 := P.H.trace_preserves_DR1 v P.hDR1
  hNEP := P.H.trace_preserves_NEP v P.hNEP

theorem Q_of_parallel_get_spec
  (n : Nat) (P : Pack0 α) (hn : P.H.U.card = n) (hn1 : 1 ≤ n)
  (v : α) (hvU : v ∈ P.H.U) (hParV : HasParallel0 P v) :
  (Q_of_parallel_get P v).H.U.card = n - 1 ∧
    NDS n (P.H.FixSet) ≤ NDS (n - 1) ((Q_of_parallel_get P v).H.FixSet) := by
  classical
  rcases hParV with ⟨u, huv_ne, hu_clv, hv_clu⟩
  have hParCl : P.H.IsParallelByClosure u v := ⟨huv_ne, hu_clv, hv_clu⟩
  have hParCl_symm : P.H.IsParallelByClosure v u := ⟨huv_ne.symm, hv_clu, hu_clv⟩
  have hRare : P.H.rare v :=
    HornNF.rare_of_hasParallel_of_DR1 (H := P.H) (hDR1 := P.hDR1) (hNEP := P.hNEP)
      (u := v) (hPar := ⟨u, hParCl_symm⟩)
  have hndeg_nonpos : ndeg (P.H.FixSet) v ≤ 0 := by
    simpa [HornNF.rare] using hRare
  have hPairEmpty : PairTr v (P.H.FixSet) = ∅ :=
    HornNF.PairTr_fixset_eq_empty_of_parallel (H := P.H) (u := u) (v := v) hParCl
  have hPairNDS0 : NDS (n - 1) (PairTr v (P.H.FixSet)) = 0 := by
    simp [hPairEmpty, NDS]
  have hTraceID :
      NDS n (P.H.FixSet)
        =
      NDS (n - 1) (Tr v (P.H.FixSet))
        + NDS (n - 1) (PairTr v (P.H.FixSet))
        + ndeg (P.H.FixSet) v := by
    simpa using
      (Accounting.TRACE_ID (α := α) (n := n) (hn := hn1) (C := P.H.FixSet) (u := v))
  have hNDSleTr : NDS n (P.H.FixSet) ≤ NDS (n - 1) (Tr v (P.H.FixSet)) := by
    rw [hTraceID, hPairNDS0]
    linarith
  have hFixTrace :
      (Q_of_parallel_get P v).H.FixSet = Tr v (P.H.FixSet) := by
    dsimp [Q_of_parallel_get]
    exact HornNF.fixset_trace_eq_Tr_fixset_of_DR1 (H := P.H) P.hDR1 v hvU
  refine ⟨?_, ?_⟩
  · dsimp [Q_of_parallel_get, HornNF.trace]
    calc
      (P.H.U.erase v).card = P.H.U.card - 1 := Finset.card_erase_of_mem hvU
      _ = n - 1 := by simpa [hn]
  · simpa [hFixTrace] using hNDSleTr

/-- Parallel-branch (forbid-free): if `Parallel0 P` holds, we can close `Q n P` by the trace reduction core. -/
theorem Q_of_parallel
  (n : Nat) (P : Pack0 α) : (∀ P':Pack0 α, P'.H.U.card = n → Q n P') →
  P.H.U.card = n + 1 →
  Parallel0 P → Q (n+1) P := by
  classical
  intro hQ hn hPar
  rcases hPar with ⟨u, v, huv_ne, hu_clv, hv_clu⟩
  have hvU : v ∈ P.H.U := (Finset.mem_filter.mp hv_clu).1
  have hParV : HasParallel0 P v := ⟨u, huv_ne, hu_clv, hv_clu⟩
  have hStep :=
    Q_of_parallel_get_spec (α := α) (n := n + 1) (P := P) (hn := hn) (hn1 := by omega)
      (v := v) (hvU := hvU) (hParV := hParV)
  let P' : Pack0 α := Q_of_parallel_get P v
  have hP'card : P'.H.U.card = n := by
    have hP'card' : P'.H.U.card = (n + 1) - 1 := by
      simpa [P'] using hStep.1
    omega
  have hQ' : Q n P' := hQ P' hP'card
  dsimp [Q]
  intro _hn'
  have hMain : NDS (n + 1) (P.H.FixSet) ≤ NDS n (P'.H.FixSet) := by
    simpa [P'] using hStep.2
  have hNDSnonpos : NDS n (P'.H.FixSet) ≤ 0 := by
    dsimp [Q] at hQ'
    exact hQ' hP'card
  exact Int.le_trans hMain hNDSnonpos

/-- Monotonicity of `PairTr` under family inclusion. -/
lemma PairTr_subset_of_subset
  (v : α) {C D : Finset (Finset α)} (hCD : C ⊆ D) :
  PairTr v C ⊆ PairTr v D := by
  intro X hX
  rcases Finset.mem_filter.mp hX with ⟨hXC, hcond⟩
  rcases hcond with ⟨hvX, hXinsC⟩
  refine Finset.mem_filter.mpr ?_
  refine ⟨hCD hXC, ⟨hvX, hCD hXinsC⟩⟩

/-- If `u ∈ A`, then tracing the hole at `v` is the same as hole after tracing.
This uses the parallel biconditional `u ∈ X ↔ v ∈ X` on the base family `C`. -/
lemma Tr_Hole_eq_Hole_Tr_erase_of_parallel
  (C : Finset (Finset α)) (A : Finset α) {u v : α}
  (huv_ne : u ≠ v) (huA : u ∈ A)
  (hiff : ∀ X : Finset α, X ∈ C → (u ∈ X ↔ v ∈ X)) :
  Tr v (Hole C A) = Hole (Tr v C) (A.erase v) := by
  classical
  ext X
  constructor
  · intro hX
    rcases Finset.mem_image.mp hX with ⟨Y, hYhole, rfl⟩
    rcases (mem_Hole_iff (α := α) (C := C) (A := A) (X := Y)).1 hYhole with ⟨hYC, hnotA⟩
    refine (mem_Hole_iff (α := α) (C := Tr v C) (A := A.erase v) (X := Y.erase v)).2 ?_
    refine ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨Y, hYC, rfl⟩
    · intro hsub
      have huErase : u ∈ A.erase v := Finset.mem_erase.mpr ⟨huv_ne, huA⟩
      have huYerase : u ∈ Y.erase v := hsub huErase
      have huY : u ∈ Y := (Finset.mem_erase.mp huYerase).2
      have hvY : v ∈ Y := (hiff Y hYC).1 huY
      have hAsubY : A ⊆ Y := by
        intro a haA
        by_cases hav : a = v
        · simpa [hav] using hvY
        · have haErase : a ∈ A.erase v := Finset.mem_erase.mpr ⟨hav, haA⟩
          exact (Finset.mem_erase.mp (hsub haErase)).2
      exact hnotA hAsubY
  · intro hX
    rcases (mem_Hole_iff (α := α) (C := Tr v C) (A := A.erase v) (X := X)).1 hX with
      ⟨hXTr, hnotErase⟩
    rcases Finset.mem_image.mp hXTr with ⟨Y, hYC, hYeq⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨Y, ?_, hYeq⟩
    refine (mem_Hole_iff (α := α) (C := C) (A := A) (X := Y)).2 ?_
    refine ⟨hYC, ?_⟩
    intro hAsubY
    apply hnotErase
    intro a haErase
    have haY : a ∈ Y := hAsubY (Finset.mem_of_mem_erase haErase)
    have hav : a ≠ v := (Finset.mem_erase.mp haErase).1
    have haYerase : a ∈ Y.erase v := Finset.mem_erase.mpr ⟨hav, haY⟩
    simpa [hYeq] using haYerase

/-- Degree transfer across Hole/Up for vertices inside the forbid set. -/
lemma ndeg_hole_add_up_eq_ndeg_of_mem_parallel
  (C : Finset (Finset α)) (A : Finset α) (a : α)
  (ha : a ∈ A) :
  ndeg (Hole C A) a + (Up C A).card = ndeg C a := by
  classical
  have hUpSubsetDeg :
      (Up (α := α) C A).card ≤ deg (α := α) C a := by
    refine Finset.card_le_card ?_
    intro X hX
    rcases Finset.mem_filter.mp hX with ⟨hXC, hAX⟩
    exact Finset.mem_filter.mpr ⟨hXC, hAX ha⟩
  have hDegSplit :
      deg (α := α) C a
        =
      (Up (α := α) C A).card + deg (α := α) (Hole (α := α) C A) a := by
    have hpart := Finset.filter_card_add_filter_neg_card_eq_card
      (s := C.filter (fun X => a ∈ X))
      (p := fun X : Finset α => A ⊆ X)
    have hUpEq :
        (C.filter (fun X => a ∈ X)).filter (fun X => A ⊆ X)
          =
        Up (α := α) C A := by
      ext X; constructor
      · intro hX
        rcases Finset.mem_filter.mp hX with ⟨hXaC, hAX⟩
        rcases Finset.mem_filter.mp hXaC with ⟨hXC, _⟩
        exact Finset.mem_filter.mpr ⟨hXC, hAX⟩
      · intro hX
        rcases Finset.mem_filter.mp hX with ⟨hXC, hAX⟩
        refine Finset.mem_filter.mpr ?_
        refine ⟨Finset.mem_filter.mpr ⟨hXC, hAX ha⟩, hAX⟩
    have hHoleEq :
        (C.filter (fun X => a ∈ X)).filter (fun X => ¬ A ⊆ X)
          =
        (Hole (α := α) C A).filter (fun X => a ∈ X) := by
      ext X; constructor <;> intro hX
      · rcases Finset.mem_filter.mp hX with ⟨hXaC, hNotAX⟩
        rcases Finset.mem_filter.mp hXaC with ⟨hXC, hXa⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hXC, hNotAX⟩, hXa⟩
      · rcases Finset.mem_filter.mp hX with ⟨hXHole, hXa⟩
        rcases Finset.mem_filter.mp hXHole with ⟨hXC, hNotAX⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hXC, hXa⟩, hNotAX⟩
    have hpart' :
        (Up (α := α) C A).card
          + deg (α := α) (Hole (α := α) C A) a
          =
        deg (α := α) C a := by
      simpa [deg, hUpEq, hHoleEq] using hpart
    exact eq_comm.mp hpart'
  have hHoleCard :
      (Hole (α := α) C A).card = C.card - (Up (α := α) C A).card := by
    have hpart := card_Up_add_card_Hole (α := α) C A
    exact Nat.eq_sub_of_add_eq (by simpa [add_comm] using hpart)
  have hDegNat :
      deg (α := α) (Hole (α := α) C A) a
        =
      deg (α := α) C a - (Up (α := α) C A).card := by
    exact Nat.eq_sub_of_add_eq (by simpa [add_comm] using hDegSplit.symm)
  calc
    ndeg (α := α) (Hole (α := α) C A) a + (Up (α := α) C A).card
        =
      ((2 : Int) * (deg (α := α) (Hole (α := α) C A) a : Int)
        - ((Hole (α := α) C A).card : Int))
      + (Up (α := α) C A).card := by
          simp [ndeg]
    _ =
      ((2 : Int) * ((deg (α := α) C a - (Up (α := α) C A).card : Nat) : Int)
        - ((C.card - (Up (α := α) C A).card : Nat) : Int))
      + (Up (α := α) C A).card := by
          rw [hDegNat, hHoleCard]
    _ = (2 : Int) * (deg (α := α) C a : Int) - (C.card : Int) := by
          have h1 : (Up (α := α) C A).card ≤ deg (α := α) C a := hUpSubsetDeg
          have h2 : (Up (α := α) C A).card ≤ C.card := by
            exact Finset.card_le_card (by intro X hX; exact (Finset.mem_filter.mp hX).1)
          simp [Int.ofNat_sub h1, Int.ofNat_sub h2]
          ring
    _ = ndeg (α := α) C a := by
          simp [ndeg]

/-- Trace step object for the parallel branch in the forbid world. -/
noncomputable def Qcorr_of_parallel_get
  (F : HornWithForbid α) (v : α) (_hvF : v ∈ F.F)
  (hFne : (F.F.erase v).Nonempty) : HornWithForbid α where
  H := F.H.trace v
  hDR1 := F.H.trace_preserves_DR1 v F.hDR1
  hNEP := F.H.trace_preserves_NEP v F.hNEP
  F := F.F.erase v
  F_subset_U := by
    dsimp [HornNF.trace]
    exact Finset.erase_subset_erase v F.F_subset_U
  F_nonempty := hFne

/-- Spec of `Qcorr_of_parallel_get`: card drops by one and `NDS_corr` does not worsen. -/
theorem Qcorr_of_parallel_get_spec
  (n : Nat) (F : HornWithForbid α) (hn : F.H.U.card = n) (hn1 : 1 ≤ n)
  (hPar : Parallel1 F) :
  ∃ v : α, ∃ hvF : v ∈ F.F, ∃ hFne : (F.F.erase v).Nonempty,
    (Qcorr_of_parallel_get F v hvF hFne).H.U.card = n - 1 ∧
      F.NDS_corr n ≤ (Qcorr_of_parallel_get F v hvF hFne).NDS_corr (n - 1) := by
  classical
  rcases hPar with ⟨u, v, huv_ne, huF, hvF, hu_clv, hv_clu⟩
  let hFne : (F.F.erase v).Nonempty := by
    refine ⟨u, ?_⟩
    exact Finset.mem_erase.mpr ⟨huv_ne, huF⟩
  let F' : HornWithForbid α := Qcorr_of_parallel_get F v hvF hFne
  have hvU : v ∈ F.H.U := F.F_subset_U hvF
  have hParFix :
      F.H.IsParallelByFixSet u v := by
    exact (HornNF.parallel_closure_iff_parallel_fixset (H := F.H) (u := u) (v := v)).1
      ⟨huv_ne, hu_clv, hv_clu⟩
  have hiff : ∀ X : Finset α, X ∈ F.H.FixSet → (u ∈ X ↔ v ∈ X) := hParFix.2.2.2
  have hPairBaseEmpty : PairTr v (F.H.FixSet) = ∅ :=
    HornNF.PairTr_fixset_eq_empty_of_parallel (H := F.H) (u := u) (v := v)
      ⟨huv_ne, hu_clv, hv_clu⟩
  have hHoleSubsetBase : Hole (F.H.FixSet) F.F ⊆ F.H.FixSet := by
    intro X hX
    exact (mem_Hole_iff (α := α) (C := F.H.FixSet) (A := F.F) (X := X)).1 hX |>.1
  have hPairHoleEmpty : PairTr v (Hole (F.H.FixSet) F.F) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro X hX
    have hXbase : X ∈ PairTr v (F.H.FixSet) :=
      PairTr_subset_of_subset (v := v) (C := Hole (F.H.FixSet) F.F) (D := F.H.FixSet) hHoleSubsetBase hX
    simpa [hPairBaseEmpty] using hXbase
  have hPairHoleNDS0 : NDS (n - 1) (PairTr v (Hole (F.H.FixSet) F.F)) = 0 := by
    simp [hPairHoleEmpty, NDS]
  have hRare : F.H.rare v :=
    HornNF.rare_of_hasParallel_of_DR1 (H := F.H) (hDR1 := F.hDR1) (hNEP := F.hNEP)
      (u := v) (hPar := ⟨u, ⟨huv_ne.symm, hv_clu, hu_clv⟩⟩)
  have hndeg_nonpos : ndeg (F.H.FixSet) v ≤ 0 := by
    simpa [HornNF.rare] using hRare
  have hNdegCorr :
      ndeg (Hole (F.H.FixSet) F.F) v + (Up (F.H.FixSet) F.F).card
        = ndeg (F.H.FixSet) v := by
    exact ndeg_hole_add_up_eq_ndeg_of_mem_parallel
      (C := F.H.FixSet) (A := F.F) (a := v) hvF
  have hTraceID :
      NDS n (Hole (F.H.FixSet) F.F)
        =
      NDS (n - 1) (Tr v (Hole (F.H.FixSet) F.F))
        + NDS (n - 1) (PairTr v (Hole (F.H.FixSet) F.F))
        + ndeg (Hole (F.H.FixSet) F.F) v := by
    simpa using
      (Accounting.TRACE_ID (α := α) (n := n) (hn := hn1)
        (C := Hole (F.H.FixSet) F.F) (u := v))
  have hCorrLeTr :
      NDS_corr n (F.H.FixSet) F.F
        ≤ NDS (n - 1) (Tr v (Hole (F.H.FixSet) F.F)) := by
    have hMain :
        NDS_corr n (F.H.FixSet) F.F
          =
        NDS (n - 1) (Tr v (Hole (F.H.FixSet) F.F))
          + NDS (n - 1) (PairTr v (Hole (F.H.FixSet) F.F))
          + (ndeg (Hole (F.H.FixSet) F.F) v + (Up (F.H.FixSet) F.F).card) := by
      calc
        NDS_corr n (F.H.FixSet) F.F
            = NDS n (Hole (F.H.FixSet) F.F) + (Up (F.H.FixSet) F.F).card := by
                simp [NDS_corr]
        _ =
          (NDS (n - 1) (Tr v (Hole (F.H.FixSet) F.F))
            + NDS (n - 1) (PairTr v (Hole (F.H.FixSet) F.F))
            + ndeg (Hole (F.H.FixSet) F.F) v)
            + (Up (F.H.FixSet) F.F).card := by
              rw [hTraceID]
        _ =
          NDS (n - 1) (Tr v (Hole (F.H.FixSet) F.F))
            + NDS (n - 1) (PairTr v (Hole (F.H.FixSet) F.F))
            + (ndeg (Hole (F.H.FixSet) F.F) v + (Up (F.H.FixSet) F.F).card) := by
              ring
    rw [hMain, hPairHoleNDS0, hNdegCorr]
    linarith
  have hTrHoleEq :
      Tr v (Hole (F.H.FixSet) F.F)
        =
      Hole (Tr v (F.H.FixSet)) (F.F.erase v) := by
    exact Tr_Hole_eq_Hole_Tr_erase_of_parallel
      (C := F.H.FixSet) (A := F.F) (u := u) (v := v)
      (huv_ne := huv_ne) (huA := huF) (hiff := hiff)
  have hFixTrace :
      HornNF.FixSet (F.H.trace v) = Tr v (F.H.FixSet) := by
    exact HornNF.fixset_trace_eq_Tr_fixset_of_DR1 (H := F.H) F.hDR1 v hvU
  have hCardF' : F'.H.U.card = n - 1 := by
    dsimp [F', Qcorr_of_parallel_get, HornNF.trace]
    calc
      (F.H.U.erase v).card = F.H.U.card - 1 := Finset.card_erase_of_mem hvU
      _ = n - 1 := by simpa [hn]
  have hLeF' : F.NDS_corr n ≤ F'.NDS_corr (n - 1) := by
    have hHoleLe :
        NDS_corr n (F.H.FixSet) F.F
          ≤ NDS (n - 1) (Hole (HornNF.FixSet (F.H.trace v)) (F.F.erase v)) := by
      calc
        NDS_corr n (F.H.FixSet) F.F
            ≤ NDS (n - 1) (Tr v (Hole (F.H.FixSet) F.F)) := hCorrLeTr
        _ = NDS (n - 1) (Hole (Tr v (F.H.FixSet)) (F.F.erase v)) := by
              rw [hTrHoleEq]
        _ = NDS (n - 1) (Hole (HornNF.FixSet (F.H.trace v)) (F.F.erase v)) := by
              simp [hFixTrace]
    have hUpNonneg :
        (0 : Int) ≤ (Up (HornNF.FixSet (F.H.trace v)) (F.F.erase v)).card :=
      Up_card_nonneg (α := α) (C := HornNF.FixSet (F.H.trace v)) (A := F.F.erase v)
    have hHoleLeCorr :
        NDS (n - 1) (Hole (HornNF.FixSet (F.H.trace v)) (F.F.erase v))
          ≤
        NDS_corr (n - 1) (HornNF.FixSet (F.H.trace v)) (F.F.erase v) := by
      simpa [NDS_corr] using (le_add_of_nonneg_right hUpNonneg)
    have hBase : F.NDS_corr n = NDS_corr n (F.H.FixSet) F.F := by
      simp [HornWithForbid.NDS_corr, HornWithForbid.BaseC]
    have hTarget :
        F'.NDS_corr (n - 1)
          = NDS_corr (n - 1) (HornNF.FixSet (F.H.trace v)) (F.F.erase v) := by
      simp [F', Qcorr_of_parallel_get, HornWithForbid.NDS_corr, HornWithForbid.BaseC]
    rw [hBase, hTarget]
    exact Int.le_trans hHoleLe hHoleLeCorr
  refine ⟨v, hvF, hFne, hCardF', hLeF'⟩

/-- Wiring helper: advance one step under the parallel-branch (with forbid). -/
theorem Qcorr_ge_hasParallel
  (n : Nat) (F : HornWithForbid α) :
  (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') → F.H.U.card = n + 1 → Parallel1 F →
  Qcorr (n+1) F := by
  intro hQcorr hn hPar
  obtain ⟨v, hvF, hFne, hCardStep, hStep⟩ :=
    Qcorr_of_parallel_get_spec (α := α) (n := n + 1) (F := F) (hn := hn) (hn1 := by omega) hPar
  let F' : HornWithForbid α := Qcorr_of_parallel_get F v hvF hFne
  have hF'card : F'.H.U.card = n := by
    have : F'.H.U.card = (n + 1) - 1 := by simpa [F'] using hCardStep
    omega
  have hQF' : Qcorr n F' := hQcorr F' hF'card
  have hQF'nonpos : F'.NDS_corr n ≤ 0 := by
    dsimp [Qcorr] at hQF'
    have hBase : NDS_corr n F'.H.FixSet F'.F ≤ 0 := hQF' hF'card
    simpa [HornWithForbid.NDS_corr, HornWithForbid.BaseC] using hBase
  have hStep' : F.NDS_corr (n + 1) ≤ F'.NDS_corr n := by
    have hFcard : F.H.U.card = n + 1 := hn
    simpa [hFcard, hF'card] using hStep
  have hFinal : F.NDS_corr (n + 1) ≤ 0 := Int.le_trans hStep' hQF'nonpos
  dsimp [Qcorr]
  intro _hn'
  simpa [HornWithForbid.NDS_corr, HornWithForbid.BaseC] using hFinal

end Dr1nds
