-- Dr1nds/Induction/LocalKernels.lean
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Tactic
import Dr1nds.Horn.HornTrace
import Dr1nds.Horn.HornContraction
import Dr1nds.Forbid.Basic
import Dr1nds.Forbid.HornWithForbid
import Dr1nds.Forbid.HornBridge
import Dr1nds.Forbid.Singleton
import Dr1nds.Forbid.HornNormalize
import Dr1nds.Induction.Statements
import Dr1nds.SetFamily.ConDelNdegId
import Dr1nds.Induction.Parallel
set_option maxHeartbeats 10000000

namespace Dr1nds
variable {α : Type} [DecidableEq α]



---------------------------------------------
---これは、Hornレベルで定義することではないのか。HornNF.IsSCを定義した。今後は、P.H.IsSCを使う。
--abbrev IsSC0 (P : Pack0 α) (h : α) : Prop :=
--  P.H.closure {h} = {h}

/-- SC / head-structure predicates for forbid packs. -/
abbrev IsSC1 (F: HornWithForbid α) (h : α) : Prop :=
  F.H.closure {h} = {h}

lemma isSC1_singleton_mem_baseFixSet
  (F : HornWithForbid α) (a : α)
  (hSC : IsSC1 F a) :
  ({a} : Finset α) ∈ HornNF.FixSet F.H := by
  exact (SC_closure_singleton F.H a).mpr hSC

/--
No-parallel (forbid-free) ⇒ existence of an SC point.
This is the entry point to the SC-based induction branch.
-/
theorem exists_SC_no_parallel
  (P : Pack0 α) (hU : P.H.U.Nonempty) :
  NoParallel0 P → ∃ h : α, P.H.IsSC h := by
  classical
  intro hNP
  let S : Finset (Finset α) := P.H.FixSet.filter (fun X => X.Nonempty)
  have hUfix : P.H.U ∈ P.H.FixSet := by
    refine (mem_FixSet_iff (H := P.H) (X := P.H.U)).2 ?_
    refine ⟨?_, subset_rfl⟩
    intro h Pprem hPrem hsub
    exact P.H.head_mem_U ⟨Pprem, hPrem⟩
  have hSnonempty : S.Nonempty := by
    refine ⟨P.H.U, Finset.mem_filter.mpr ?_⟩
    exact ⟨hUfix, hU⟩
  obtain ⟨M, hMS, hMmin⟩ := Finset.exists_min_image S Finset.card hSnonempty
  have hMfix : M ∈ P.H.FixSet := (Finset.mem_filter.mp hMS).1
  have hMnonempty : M.Nonempty := (Finset.mem_filter.mp hMS).2
  have hMsubsetU : M ⊆ P.H.U := mem_FixSet_subset_U (H := P.H) hMfix
  have hMnotTwo : ¬ 2 ≤ M.card := by
    intro hMge2
    have hMgt1 : 1 < M.card := by omega
    rcases (Finset.one_lt_card.mp hMgt1) with ⟨u, huM, v, hvM, huv_ne⟩
    have huU : u ∈ P.H.U := hMsubsetU huM
    have hvU : v ∈ P.H.U := hMsubsetU hvM
    have hsub_u : ({u} : Finset α) ⊆ M := Finset.singleton_subset_iff.mpr huM
    have hsub_v : ({v} : Finset α) ⊆ M := Finset.singleton_subset_iff.mpr hvM
    have hMclosed : P.H.IsClosed M := (mem_FixSet_iff (H := P.H) (X := M)).1 hMfix
    have hclu_sub_M : P.H.closure ({u} : Finset α) ⊆ M :=
      HornNF.closure_subset_of_subset_isClosed (H := P.H) (hXY := hsub_u) (hY := hMclosed)
    have hclv_sub_M : P.H.closure ({v} : Finset α) ⊆ M :=
      HornNF.closure_subset_of_subset_isClosed (H := P.H) (hXY := hsub_v) (hY := hMclosed)
    have hu_in_clu : u ∈ P.H.closure ({u} : Finset α) := by
      have hsingletonU : ({u} : Finset α) ⊆ P.H.U := Finset.singleton_subset_iff.mpr huU
      exact (HornNF.subset_closure (H := P.H) (X := ({u} : Finset α)) hsingletonU) (by simp)
    have hv_in_clv : v ∈ P.H.closure ({v} : Finset α) := by
      have hsingletonU : ({v} : Finset α) ⊆ P.H.U := Finset.singleton_subset_iff.mpr hvU
      exact (HornNF.subset_closure (H := P.H) (X := ({v} : Finset α)) hsingletonU) (by simp)
    have hclu_fix : P.H.closure ({u} : Finset α) ∈ P.H.FixSet := by
      exact (mem_FixSet_iff (H := P.H) (X := P.H.closure ({u} : Finset α))).2
        (HornNF.closure_isClosed (H := P.H) (X := ({u} : Finset α)))
    have hclv_fix : P.H.closure ({v} : Finset α) ∈ P.H.FixSet := by
      exact (mem_FixSet_iff (H := P.H) (X := P.H.closure ({v} : Finset α))).2
        (HornNF.closure_isClosed (H := P.H) (X := ({v} : Finset α)))
    have hclu_nonempty : (P.H.closure ({u} : Finset α)).Nonempty := ⟨u, hu_in_clu⟩
    have hclv_nonempty : (P.H.closure ({v} : Finset α)).Nonempty := ⟨v, hv_in_clv⟩
    have hcluS : P.H.closure ({u} : Finset α) ∈ S := Finset.mem_filter.mpr ⟨hclu_fix, hclu_nonempty⟩
    have hclvS : P.H.closure ({v} : Finset α) ∈ S := Finset.mem_filter.mpr ⟨hclv_fix, hclv_nonempty⟩
    have hMle_clu : M.card ≤ (P.H.closure ({u} : Finset α)).card := hMmin _ hcluS
    have hMle_clv : M.card ≤ (P.H.closure ({v} : Finset α)).card := hMmin _ hclvS
    have hclu_eq_M : P.H.closure ({u} : Finset α) = M :=
      Finset.eq_of_subset_of_card_le hclu_sub_M hMle_clu
    have hclv_eq_M : P.H.closure ({v} : Finset α) = M :=
      Finset.eq_of_subset_of_card_le hclv_sub_M hMle_clv
    have hu_in_clv : u ∈ P.H.closure ({v} : Finset α) := by simpa [hclv_eq_M] using huM
    have hv_in_clu : v ∈ P.H.closure ({u} : Finset α) := by simpa [hclu_eq_M] using hvM
    have hPar : Parallel0 P := ⟨u, v, huv_ne, hu_in_clv, hv_in_clu⟩
    exact hNP hPar
  have hMcard_one : M.card = 1 := by
    have hMpos : 0 < M.card := Finset.card_pos.mpr hMnonempty
    omega
  obtain ⟨a, hMa⟩ := Finset.card_eq_one.mp hMcard_one
  refine ⟨a, ?_⟩
  have hsingle_fix : ({a} : Finset α) ∈ P.H.FixSet := by
    simpa [hMa] using hMfix
  exact (SC_closure_singleton P.H a).1 hsingle_fix

/-- Noncomputably pick an SC point from `exists_SC_no_parallel`. -/
noncomputable def choose_SC_no_parallel
  (P : Pack0 α) (hU : P.H.U.Nonempty) (hNP : NoParallel0 P) : α :=
  Classical.choose (exists_SC_no_parallel (α := α) P hU hNP)

@[simp] theorem choose_SC_no_parallel_spec
  (P : Pack0 α) (hU : P.H.U.Nonempty) (hNP : NoParallel0 P) :
  P.H.IsSC (choose_SC_no_parallel (α := α) P hU hNP) :=
  Classical.choose_spec (exists_SC_no_parallel (α := α) P hU hNP)
------------------------------------------------

/- No-parallel (with forbid) implies existence of an SC point *inside* the forbid set `A`.
    Picking `h ∈ A` is crucial: it prevents the forbid-update from introducing a second forbid set. -/

axiom exists_SC_in_forbid
  (F : HornWithForbid α) :
  NoParallel1 P → ∃ h : α, h ∈ F.F ∧ IsSC1 P h

/-- Noncomputably pick an SC point inside `A` from `exists_SC_in_forbid`. -/
noncomputable def choose_SC_in_forbid
  (F : HornWithForbid α) (hNP : NoParallel1 F) : α :=
  Classical.choose (exists_SC_in_forbid (α := α) F hNP)

@[simp] theorem choose_SC_in_forbid_mem
  (F : HornWithForbid α) (hNP : NoParallel1 F) :
  choose_SC_in_forbid (α := α) F hNP ∈ F.F :=
by
  simpa [choose_SC_in_forbid] using (Classical.choose_spec (exists_SC_in_forbid (α := α) F hNP)).1

@[simp] theorem choose_SC_in_forbid_spec
(F : HornWithForbid α) (hNP : NoParallel1 F) :
  IsSC1 F (choose_SC_in_forbid (α := α) F hNP) :=
by
  simpa [choose_SC_in_forbid] using (Classical.choose_spec (exists_SC_in_forbid (α := α) F hNP)).2

-----------------------------------------------------
-- Headがあるかないかの分岐。



--HornWithForbidに移動しても良いし、ここでもよい。
def HasHead1 (F :HornWithForbid  α) (h : α) : Prop :=
  (F.H.prem h).Nonempty

def IsForbidSingleton (F :HornWithForbid  α): Prop :=
  F.F.card = 1

lemma erase_nonempty_of_mem_not_singleton
  (F : HornWithForbid α) (a : α)
  (ha : a ∈ F.F)
  (hns : ¬ IsForbidSingleton F) :
  (F.F.erase a).Nonempty := by
  have hcard_erase : (F.F.erase a).card = F.F.card - 1 := Finset.card_erase_of_mem ha
  have hge2 : 2 ≤ F.F.card := by
    by_contra hlt2
    have hle1 : F.F.card ≤ 1 := by omega
    have hcard1 : F.F.card = 1 := by
      have hpos : 0 < F.F.card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    exact hns hcard1
  have hpos : 0 < (F.F.erase a).card := by
    rw [hcard_erase]
    omega
  exact Finset.card_pos.mp hpos

lemma not_subset_singleton_of_mem_not_singleton
  (F : HornWithForbid α) (a : α)
  (ha : a ∈ F.F)
  (hns : ¬ IsForbidSingleton F) :
  ¬ F.F ⊆ ({a} : Finset α) := by
  intro hsub
  have hle1 : F.F.card ≤ 1 := by
    exact Finset.card_le_card hsub
  have hpos : 0 < F.F.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hcard1 : F.F.card = 1 := by omega
  exact hns hcard1

lemma card_ge_two_of_mem_not_singleton
  (F : HornWithForbid α) (a : α)
  (ha : a ∈ F.F)
  (hns : ¬ IsForbidSingleton F) :
  2 ≤ F.F.card := by
  have hpos : 0 < F.F.card := Finset.card_pos.mpr ⟨a, ha⟩
  by_contra hlt2
  have hle1 : F.F.card ≤ 1 := by omega
  have hcard1 : F.F.card = 1 := by omega
  exact hns hcard1

--シングルトンの禁止集合を与えたときに、headがあるかどうか。
def HasHead1s (F :HornWithForbid  α) (fs: IsForbidSingleton F):Prop := by
  let h := Classical.choose (Finset.card_eq_one.mp fs)
  exact (F.H.prem h).Nonempty



-----------------------------------------------------
--新しいローカルカーネル

---contractionでは、閉集合族が閉集合族に。
noncomputable def Q_contraction  {α :Type} [DecidableEq α](P : Pack0 α) (a: α) (hSC: P.H.IsSC a): Pack0 α where
  H := P.H.contraction a
  hDR1 := by exact P.H.contraction_preserves_DR1 P.hDR1 a
  hNEP := by exact contraction_SC_NEP P.H a hSC

---head freeのdeletionは、traceと同じ。だったら最初からtraceと言ってもいい気もするが。
noncomputable def Q_trace {α :Type} [DecidableEq α](P : Pack0 α) (a: α) : Pack0 α where
  H := P.H.trace a
  hDR1 := by exact P.H.trace_preserves_DR1 a P.hDR1
  hNEP :=  P.H.trace_preserves_NEP a P.hNEP

noncomputable def Q_deletion_head {α :Type} [DecidableEq α](P : Pack0 α) (a: α) (hasHead: P.H.hasHead a):HornWithForbid α where
  H := P.H.trace a
  hDR1 := P.H.trace_preserves_DR1 a P.hDR1
  hNEP := P.H.trace_preserves_NEP a P.hNEP
  F := Classical.choose (exists_unique_prem_of_DR1_of_nonempty P.H a P.hDR1 hasHead)  --- headを持つ唯一のルールのpremiseを入れる。
  F_subset_U := by
    let F := Classical.choose (exists_unique_prem_of_DR1_of_nonempty P.H a P.hDR1 hasHead)
    have h_mem : F ∈ P.H.prem a := (Classical.choose_spec (exists_unique_prem_of_DR1_of_nonempty P.H a P.hDR1 hasHead)).1
    exact HornNF.prem_subset_traceU_of_mem_prem P.H h_mem
  F_nonempty := by
    let F := Classical.choose (exists_unique_prem_of_DR1_of_nonempty P.H a P.hDR1 hasHead)
    have h_mem : F ∈ P.H.prem a := (Classical.choose_spec (exists_unique_prem_of_DR1_of_nonempty P.H a P.hDR1 hasHead)).1
    have :F.Nonempty := by
      let ph := P.hNEP (h := a)
      suffices F ≠ ∅ from by
        exact Finset.nonempty_iff_ne_empty.mpr this
      intro h
      rw [h] at h_mem
      exact ph h_mem
    simp_all only [F]

/-- In the has-head branch, rule-level deletion matches family-level `Del` on `FixSet`. -/
theorem Q_deletion_head_fixset_eq_Del
  (P : Pack0 α) (a : α) (hasHead : P.H.hasHead a) :
  (Q_deletion_head P a hasHead).FixSet = Del a (HornNF.FixSet P.H) := by
  classical
  let Pprem := Classical.choose (exists_unique_prem_of_DR1_of_nonempty P.H a P.hDR1 hasHead)
  have hP : Pprem ∈ P.H.prem a :=
    (Classical.choose_spec (exists_unique_prem_of_DR1_of_nonempty P.H a P.hDR1 hasHead)).1
  have hUnique : (P.H.prem a).card = 1 := by
    exact prem_card_eq_one_of_DR1_of_ne_empty (H := P.H) (v := a) (hDR1 := P.hDR1) hasHead
  have hHole :=
    hole_singleton_eq_hole_trace_prem (α := α)
      (H := P.H) (hDR1 := P.hDR1) (v := a) (P := Pprem)
      (hP := hP) (hUnique := hUnique)
  have hQhole :
      (Q_deletion_head P a hasHead).FixSet
        = Hole (α := α) (HornNF.FixSet (P.H.trace a)) Pprem := by
    simpa [Q_deletion_head, Pprem] using
      (FixSet_eq_Hole_FixSet (α := α) (S := Q_deletion_head P a hasHead))
  calc
    (Q_deletion_head P a hasHead).FixSet
        = Hole (α := α) (HornNF.FixSet (P.H.trace a)) Pprem := hQhole
    _ = Hole (α := α) (HornNF.FixSet P.H) ({a} : Finset α) := hHole.symm
    _ = Del a (HornNF.FixSet P.H) := by
      simp [Del]

-- 新しいローカルカーネル Qcorr編

--禁止集合のサイズが2以上の場合に使われる。
noncomputable def Qcorr_contraction {α :Type} [DecidableEq α] (F: HornWithForbid α) (a: α) (hSC:F.H.IsSC a) (hA: a ∈ F.F) (geq2: F.F.card ≥ 2):
   HornWithForbid α where
  H := F.H.contraction a
  hDR1 := F.H.contraction_preserves_DR1 F.hDR1 a
  hNEP := contraction_SC_NEP F.H a hSC
  F := F.F.erase a
  F_subset_U := by
    simp_all only [ge_iff_le, contraction_U]
    gcongr
    simp_all only [HornWithForbid.F_subset_U]
  F_nonempty := by
    have hcard : (F.F.erase a).card = F.F.card - 1 :=
    Finset.card_erase_of_mem hA
    -- 2. card ≥ 2 より card - 1 ≥ 1
    have hpos : (F.F.erase a).card > 0 := by
      rw [hcard]
      exact Nat.sub_pos_of_lt geq2   -- または omega / linarith
      -- 3. card > 0 なら Nonempty
    exact Finset.card_pos.mp hpos

theorem Qcorr_contraction_fixset_eq_Con
  (F : HornWithForbid α) (a : α)
  (hSC : F.H.IsSC a) (hA : a ∈ F.F) (geq2 : F.F.card ≥ 2) :
  (Qcorr_contraction F a hSC hA geq2).FixSet = Con a F.FixSet := by
  classical
  have hne : (F.F.erase a).Nonempty := by
    have hcard : (F.F.erase a).card = F.F.card - 1 := Finset.card_erase_of_mem hA
    have hpos : 0 < (F.F.erase a).card := by
      rw [hcard]
      exact Nat.sub_pos_of_lt geq2
    exact Finset.card_pos.mp hpos
  have hsc_mem : ({a} : Finset α) ∈ F.FixSet := by
    refine (HornWithForbid.mem_FixSet_withForbid_iff F {a}).2 ?_
    refine ⟨(SC_closure_singleton F.H a).mpr hSC, ?_⟩
    exact not_subset_singleton_of_mem_not_singleton
      (F := F) (a := a) (ha := hA)
      (hns := by
        intro hs
        have : F.F.card ≤ 1 := by simpa [IsForbidSingleton] using hs.le
        omega)
  simpa [Qcorr_contraction] using contract_FixSet_eq F a hne hsc_mem

lemma qcorr_contraction_card
  (F : HornWithForbid α) (a : α)
  (hSC : F.H.IsSC a) (hA : a ∈ F.F) (geq2 : F.F.card ≥ 2) :
  (Qcorr_contraction F a hSC hA geq2).H.U.card = F.H.U.card - 1 := by
  dsimp [Qcorr_contraction]
  have haU : a ∈ F.H.U := F.F_subset_U hA
  rw [contraction_U, Finset.card_erase_of_mem haU]

lemma Del_Hole_eq_Del_of_mem
  (C : Finset (Finset α)) (A : Finset α) (a : α)
  (ha : a ∈ A) :
  Del a (Hole (α := α) C A) = Del a C := by
  ext X
  constructor
  · intro hX
    rcases Finset.mem_filter.mp hX with ⟨hXHole, hXa⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hXHole).1, hXa⟩
  · intro hX
    rcases Finset.mem_filter.mp hX with ⟨hXC, hXa⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, hXa⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨hXC, ?_⟩
    intro hAX
    exact hXa (hAX ha)

lemma nds_del_add_ndeg_eq_nds_corr_singleton
  (n : Nat) (C : Finset (Finset α)) (a : α) :
  NDS (α := α) n (Del a C) + ndeg (α := α) C a
    =
  NDS_corr (α := α) (n + 1) C ({a} : Finset α) := by
  have hcard : (Up (α := α) C ({a} : Finset α)).card + (Hole (α := α) C ({a} : Finset α)).card = C.card := by
    exact card_Up_add_card_Hole (α := α) C ({a} : Finset α)
  have hndeg :
      ndeg (α := α) C a
        = (((Up (α := α) C ({a} : Finset α)).card : Int)
            - (Hole (α := α) C ({a} : Finset α)).card) := by
    have hcardInt :
        (C.card : Int)
          = ((Up (α := α) C ({a} : Finset α)).card : Int)
            + (Hole (α := α) C ({a} : Finset α)).card := by
      have := congrArg (fun t : Nat => (t : Int)) hcard
      simpa [Int.natCast_add, add_comm, add_left_comm, add_assoc] using this.symm
    calc
      ndeg (α := α) C a = (2 : Int) * (deg (α := α) C a : Int) - (C.card : Int) := by
        rfl
      _ = (2 : Int) * ((Up (α := α) C ({a} : Finset α)).card : Int) - (C.card : Int) := by
        simp [deg, Up]
      _ = (2 : Int) * ((Up (α := α) C ({a} : Finset α)).card : Int)
            - (((Up (α := α) C ({a} : Finset α)).card : Int)
              + (Hole (α := α) C ({a} : Finset α)).card) := by
            rw [hcardInt]
      _ = (((Up (α := α) C ({a} : Finset α)).card : Int)
            - (Hole (α := α) C ({a} : Finset α)).card) := by
            ring
  calc
    NDS (α := α) n (Del a C) + ndeg (α := α) C a
        = NDS (α := α) n (Hole (α := α) C ({a} : Finset α))
          + (((Up (α := α) C ({a} : Finset α)).card : Int)
              - (Hole (α := α) C ({a} : Finset α)).card) := by
            simp [Del, Hole, hndeg]
    _ = (NDS (α := α) n (Hole (α := α) C ({a} : Finset α))
          - (Hole (α := α) C ({a} : Finset α)).card)
        + (Up (α := α) C ({a} : Finset α)).card := by
          ring
    _ = NDS (α := α) (n + 1) (Hole (α := α) C ({a} : Finset α))
        + (Up (α := α) C ({a} : Finset α)).card := by
          simp [Accounting.NDS_succ]
    _ = NDS_corr (α := α) (n + 1) C ({a} : Finset α) := by
          simp [NDS_corr]

lemma subset_iff_erase_subset_of_mem
  (A X : Finset α) (a : α)
  (haA : a ∈ A) (haX : a ∈ X) :
  A ⊆ X ↔ A.erase a ⊆ X.erase a := by
  constructor
  · intro h z hz
    have hzA : z ∈ A := Finset.mem_of_mem_erase hz
    have hzX : z ∈ X := h hzA
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1, hzX⟩
  · intro h z hzA
    by_cases hza : z = a
    · subst hza
      exact haX
    · have hzAe : z ∈ A.erase a := Finset.mem_erase.mpr ⟨hza, hzA⟩
      exact (Finset.mem_erase.mp (h hzAe)).2

lemma Con_Hole_eq_Hole_Con_erase
  (C : Finset (Finset α)) (A : Finset α) (a : α)
  (haA : a ∈ A) :
  Con (α := α) a (Hole (α := α) C A)
    =
  Hole (α := α) (Con (α := α) a C) (A.erase a) := by
  classical
  ext Y
  constructor
  · intro hY
    rcases Finset.mem_image.mp hY with ⟨X, hXf, hYX⟩
    rcases Finset.mem_filter.mp hXf with ⟨hXHole, haX⟩
    rcases Finset.mem_filter.mp hXHole with ⟨hXC, hnotAX⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨X, Finset.mem_filter.mpr ⟨hXC, haX⟩, hYX⟩
    · intro hsub
      have hAX : A ⊆ X := by
        have hEq := (subset_iff_erase_subset_of_mem (A := A) (X := X) (a := a) haA haX)
        exact hEq.mpr (by simpa [hYX] using hsub)
      exact hnotAX hAX
  · intro hY
    rcases Finset.mem_filter.mp hY with ⟨hYcon, hnotSub⟩
    rcases Finset.mem_image.mp hYcon with ⟨X, hXf, hYX⟩
    rcases Finset.mem_filter.mp hXf with ⟨hXC, haX⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨X, ?_, hYX⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_filter.mpr ⟨hXC, ?_⟩, haX⟩
    intro hAX
    apply hnotSub
    have hEq := (subset_iff_erase_subset_of_mem (A := A) (X := X) (a := a) haA haX)
    exact by simpa [hYX] using hEq.mp hAX

lemma ndeg_hole_add_up_eq_ndeg_of_mem
  (C : Finset (Finset α)) (A : Finset α) (a : α)
  (haA : a ∈ A) :
  ndeg (α := α) (Hole (α := α) C A) a + (Up (α := α) C A).card
    =
  ndeg (α := α) C a := by
  classical
  have hUpSubsetDeg :
      (Up (α := α) C A).card ≤ deg (α := α) C a := by
    refine Finset.card_le_card ?_
    intro X hX
    rcases Finset.mem_filter.mp hX with ⟨hXC, hAX⟩
    exact Finset.mem_filter.mpr ⟨hXC, hAX haA⟩
  have hDegSplit :
      deg (α := α) C a
        =
      (Up (α := α) C A).card + deg (α := α) (Hole (α := α) C A) a := by
    -- partition `C.filter (a ∈ ·)` by `A ⊆ ·`
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
        refine ⟨Finset.mem_filter.mpr ⟨hXC, hAX haA⟩, hAX⟩
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

---禁止集合の大きさが2以上でパラレルの場合に使われる。HornWithForbidになるもの。禁止集合がなくなるtraceは、Qcorr_singleton_deletion_free
noncomputable def Qcorr_trace {α :Type} [DecidableEq α] (F: HornWithForbid α) (a: α)  (hA: a ∈ F.F) (geq2: F.F.card ≥ 2):
   HornWithForbid α where
  H := F.H.trace a
  hDR1 := F.H.trace_preserves_DR1 a F.hDR1
  hNEP := F.H.trace_preserves_NEP a F.hNEP
  F := F.F.erase a
  F_subset_U := by
    dsimp [HornNF.trace]
    have : F.F ⊆ F.H.U := by exact F.F_subset_U
    exact Finset.erase_subset_erase a this
  F_nonempty := by
    have hcard : (F.F.erase a).card = F.F.card - 1 :=
    Finset.card_erase_of_mem hA
    -- 2. card ≥ 2 より card - 1 ≥ 1
    have hpos : (F.F.erase a).card > 0 := by
      rw [hcard]
      exact Nat.sub_pos_of_lt geq2   -- または omega / linarith
      -- 3. card > 0 なら Nonempty
    exact Finset.card_pos.mp hpos

-- (hA: a ∈ F.F) (geq2: F.F.card ≥ 2)の場合に使われるが、マイナーの構成には使わないのか。すると、F.F.card = 1の場合もこれでOKか。
noncomputable def Qcorr_deletion_head  {α :Type} [DecidableEq α] (F: HornWithForbid α) (a: α)  (hasHead: F.H.hasHead a) :
   HornWithForbid α where
  H := F.H.trace a
  hDR1 := F.H.trace_preserves_DR1 a F.hDR1
  hNEP := F.H.trace_preserves_NEP a F.hNEP
  F := Classical.choose (exists_unique_prem_of_DR1_of_nonempty F.H a F.hDR1 hasHead)  --- headを持つ唯一のルールのpremiseを入れる。
  F_subset_U := by
    let FF := Classical.choose (exists_unique_prem_of_DR1_of_nonempty F.H a F.hDR1 hasHead)
    have h_mem : FF ∈ F.H.prem a := (Classical.choose_spec (exists_unique_prem_of_DR1_of_nonempty F.H a F.hDR1 hasHead)).1
    exact HornNF.prem_subset_traceU_of_mem_prem F.H h_mem
  F_nonempty := by
    let FF := Classical.choose (exists_unique_prem_of_DR1_of_nonempty F.H a F.hDR1 hasHead)
    have h_mem : FF ∈ F.H.prem a := (Classical.choose_spec (exists_unique_prem_of_DR1_of_nonempty F.H a F.hDR1 hasHead)).1
    have :FF.Nonempty := by
      let ph := F.hNEP (h := a)
      suffices FF ≠ ∅ from by
        exact Finset.nonempty_iff_ne_empty.mpr this
      intro h
      rw [h] at h_mem
      exact ph h_mem
    simp_all only [FF]

lemma qcorr_deletion_head_card
  (F : HornWithForbid α) (a : α) (hasHead : F.H.hasHead a) :
  (Qcorr_deletion_head F a hasHead).H.U.card = F.H.U.card - 1 := by
  dsimp [Qcorr_deletion_head, HornNF.trace]
  have haU : a ∈ F.H.U := F.H.head_mem_U hasHead
  simpa using Finset.card_erase_of_mem haU

/-- In the has-head branch, `Qcorr_deletion_head` realizes family-level deletion on the base fixset. -/
theorem Qcorr_deletion_head_fixset_eq_Del
  (F : HornWithForbid α) (a : α) (hasHead : F.H.hasHead a) :
  (Qcorr_deletion_head F a hasHead).FixSet = Del a (HornNF.FixSet F.H) := by
  classical
  let Pprem := Classical.choose (exists_unique_prem_of_DR1_of_nonempty F.H a F.hDR1 hasHead)
  have hP : Pprem ∈ F.H.prem a :=
    (Classical.choose_spec (exists_unique_prem_of_DR1_of_nonempty F.H a F.hDR1 hasHead)).1
  have hUnique : (F.H.prem a).card = 1 := by
    exact prem_card_eq_one_of_DR1_of_ne_empty (H := F.H) (v := a) (hDR1 := F.hDR1) hasHead
  have hHole :=
    hole_singleton_eq_hole_trace_prem (α := α)
      (H := F.H) (hDR1 := F.hDR1) (v := a) (P := Pprem)
      (hP := hP) (hUnique := hUnique)
  have hQhole :
      (Qcorr_deletion_head F a hasHead).FixSet
        = Hole (α := α) (HornNF.FixSet (F.H.trace a)) Pprem := by
    simpa [Qcorr_deletion_head, Pprem] using
      (FixSet_eq_Hole_FixSet (α := α) (S := Qcorr_deletion_head F a hasHead))
  calc
    (Qcorr_deletion_head F a hasHead).FixSet
        = Hole (α := α) (HornNF.FixSet (F.H.trace a)) Pprem := hQhole
    _ = Hole (α := α) (HornNF.FixSet F.H) ({a} : Finset α) := hHole.symm
    _ = Del a (HornNF.FixSet F.H) := by
      simp [Del]

lemma ndiscorr_nonpos_of_Qcorr
  (n : Nat) (F : HornWithForbid α)
  (hQcorr : Qcorr n F)
  (hcard : F.H.U.card = n) :
  F.NDS_corr n ≤ 0 := by
  dsimp [Qcorr] at hQcorr
  simpa [HornWithForbid.NDS_corr, HornWithForbid.BaseC] using hQcorr hcard

lemma hole_nonpos_of_Qcorr
  (n : Nat) (F : HornWithForbid α)
  (hQcorr : Qcorr n F)
  (hcard : F.H.U.card = n) :
  NDS (α := α) n F.FixSet ≤ 0 := by
  have hcorr : F.NDS_corr n ≤ 0 := ndiscorr_nonpos_of_Qcorr (n := n) (F := F) hQcorr hcard
  simpa [HornWithForbid.NDS_corr, HornWithForbid.BaseC, FixSet_eq_Hole_FixSet] using
    (corr_implies_hole_bound (α := α) (n := n) (C := HornNF.FixSet F.H) (A := F.F) hcorr)

--  (hA: {a} = F.F) (hs:IsForbidSingleton F) の状況下で使うが、マイナーの定義には出てこない。型的には禁止集合を無視したtrace。
-- Normalizeも行っていることになる。Head freeの状態だと、Normalizeとはただのtraceになる。NDSの非減少は別途考える。
noncomputable def Qcorr_singleton_deletion_free {α :Type} [DecidableEq α] (F: HornWithForbid α) (a: α) :
   Pack0 α where
  H := F.H.trace a
  hDR1 := F.H.trace_preserves_DR1 a F.hDR1
  hNEP := F.H.trace_preserves_NEP a F.hNEP


------------------------------------------------------
--古いけど再利用可能なもの。

--ここでNDSの計算を行う。
noncomputable def Qcorr_singleton_hasHead_get {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (heq: F.F = {a}) (hs:HasHead1 F a):
    ∃ F':HornWithForbid α , F'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr F.H.U.card) ≤ (F'.NDS_corr (F.H.U.card - 1))
:= by
  have ainU:a ∈ F.H.U := by exact F.H.head_mem_U hs
  let Hnorm : HornNF α := F.H.normalize a
  obtain ⟨Pprem, hPprem_orig⟩ := hs
  have hPprem_not_a : a ∉ Pprem := F.H.nf hPprem_orig
  have hPprem_norm : Pprem ∈ Hnorm.prem a := by
    dsimp [Hnorm, HornNF.normalize]
    exact Finset.mem_filter.mpr ⟨hPprem_orig, hPprem_not_a⟩
  have hs_norm : Hnorm.hasHead a := ⟨Pprem, hPprem_norm⟩
  have hDR1_norm : HornNF.DR1 Hnorm := by
    exact HornNF.normalizePreservesDR1 F.H a F.hDR1
  have hUnique_norm : (Hnorm.prem a).card = 1 := by
    exact prem_card_eq_one_of_DR1_of_ne_empty Hnorm a hDR1_norm hs_norm
  have hNEP_norm : Hnorm.IsNEP := by
    intro h hempty
    have hmem_filter : (∅ : Finset α) ∈ (F.H.prem h).filter (fun Q => a ∉ Q) := by
      simpa [Hnorm, HornNF.normalize] using hempty
    have hmem : (∅ : Finset α) ∈ F.H.prem h := (Finset.mem_filter.mp hmem_filter).1
    exact (F.hNEP (h := h)) hmem
  let F' : HornWithForbid α := {
    H := Hnorm.trace a
    hDR1 := Hnorm.trace_preserves_DR1 a hDR1_norm
    hNEP := Hnorm.trace_preserves_NEP a hNEP_norm
    F := Pprem
    F_subset_U := by
      exact HornNF.prem_subset_traceU_of_mem_prem (H := Hnorm) hPprem_norm
    F_nonempty := by
      have hne : Pprem ≠ ∅ := by
        intro h0
        rw [h0] at hPprem_orig
        exact (F.hNEP (h := a)) hPprem_orig
      exact Finset.nonempty_iff_ne_empty.mpr hne
  }
  refine ⟨F', ?_⟩
  constructor
  · have hainU_norm : a ∈ Hnorm.U := by
      simpa [Hnorm, HornNF.normalize] using ainU
    dsimp [F', Hnorm]
    dsimp [HornNF.trace]
    simpa [HornNF.normalize] using Finset.card_erase_of_mem hainU_norm
  · dsimp [HornWithForbid.NDS_corr, HornWithForbid.BaseC, F']
    rw [heq]
    have hmono :
      NDS_corr (F.H.U.card) (HornNF.FixSet F.H) ({a} : Finset α)
        ≤
      NDS_corr (F.H.U.card) (HornNF.FixSet Hnorm) ({a} : Finset α) := by
      exact HornNF.ndscorr_singleton_normalize_le (k := F.H.U.card) (H := F.H) (a := a)
    have hEq_norm :
      NDS_corr (F.H.U.card) (HornNF.FixSet Hnorm) ({a} : Finset α)
        =
      NDS_corr (F.H.U.card - 1) (HornNF.FixSet (Hnorm.trace a)) Pprem := by
      have hpos : 0 < F.H.U.card := Finset.card_pos.mpr ⟨a, ainU⟩
      have hsubadd : F.H.U.card - 1 + 1 = F.H.U.card := by
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
      have hEq_raw :=
        Dr1nds.NDS_corr_singleton_hasHead_P_eq
          (α := α) (n := F.H.U.card - 1)
          (H := Hnorm) (hDR1 := hDR1_norm)
          (v := a) (P := Pprem)
          (hvU := by simpa [Hnorm, HornNF.normalize] using ainU)
          (hP := hPprem_norm)
          (hUnique := hUnique_norm)
          (hNoPremV := by
            intro h Q hQ
            have hQ' : Q ∈ (HornNF.normalizePrem F.H a).prem h := by
              simpa [Hnorm, HornNF.normalizePrem] using hQ
            exact HornNF.normalizePrem_noPremContains (H := F.H) (a := a) hQ')
      simpa [Nat.succ_eq_add_one, hsubadd] using hEq_raw
    exact le_trans hmono (le_of_eq hEq_norm)

theorem Qcorr_singleton_hasHead
  (n : Nat) (F : HornWithForbid α) :
   (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  F.H.U.card = n + 1 → (fb:IsForbidSingleton F) → HasHead1s F fb→
   Qcorr (n+1) F := by
  intro hQcorr hn hSC hh
  dsimp [IsForbidSingleton] at hSC
  have :∃ a , F.F = {a} := by exact Finset.card_eq_one.mp hSC
  obtain ⟨a,ha⟩ := this
  have : HasHead1 F a := by
    dsimp [HasHead1s] at hh
    simp_all only [Finset.singleton_inj, Classical.choose_eq']
    simp_all only [Finset.card_singleton]
    exact hh
  obtain ⟨F',hF'⟩ := Qcorr_singleton_hasHead_get F a ha this
  dsimp [Qcorr]
  intro hn
  specialize hQcorr F'
  have :F'.H.U.card = n := by
    simp_all only [add_tsub_cancel_right, forall_const]
  specialize hQcorr this
  dsimp [Qcorr] at hQcorr
  specialize hQcorr this
  rw [←hn]
  rw [←this] at hQcorr
  rcases hF' with ⟨h1,h2⟩
  dsimp [HornWithForbid.NDS_corr] at h2
  dsimp [HornWithForbid.BaseC] at h2
  rw [h1] at hQcorr
  --dsimp [HornNF.FixSet] at hQcorr
  --dsimp [HornNF.FixSet] at h2
  exact Int.le_trans h2 hQcorr

---ここでNDSの計算を行う。
noncomputable def Qcorr_singleton_headFree_get {α :Type} [DecidableEq α](F : HornWithForbid α) (a: α) (heq: F.F = {a}) (hs:¬HasHead1 F a):
    ∃ P':Pack0 α , P'.H.U.card = F.H.U.card - 1 ∧ (F.NDS_corr F.H.U.card) ≤ (NDS P'.H.U.card P'.H.FixSet)
:= by
  have ainU : a ∈ F.H.U := by
    have haF : a ∈ F.F := by simp [heq]
    exact F.F_subset_U haF
  have hfree : F.H.prem a = ∅ := by
    by_contra hne
    exact hs (Finset.nonempty_iff_ne_empty.mpr hne)
  let Hnorm : HornNF α := F.H.normalize a
  have hmono :
    NDS_corr (F.H.U.card) (HornNF.FixSet F.H) ({a} : Finset α)
      ≤
    NDS_corr (F.H.U.card) (HornNF.FixSet Hnorm) ({a} : Finset α) := by
    exact HornNF.ndscorr_singleton_normalize_le (k := F.H.U.card) (H := F.H) (a := a)
  have hheadfree_norm :
    NDS_corr (F.H.U.card) (HornNF.FixSet Hnorm) ({a} : Finset α)
      =
    NDS (F.H.U.card - 1) (HornNF.FixSet (Hnorm.trace a)) := by
    have hpos : 0 < F.H.U.card := Finset.card_pos.mpr ⟨a, ainU⟩
    have hsubadd : F.H.U.card - 1 + 1 = F.H.U.card := by
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    have hEq_raw :=
      Dr1nds.NDS_corr_singleton_head_free_eq
        (α := α) (n := F.H.U.card - 1)
        (H := Hnorm) (v := a)
        (hvU := by simpa [Hnorm, HornNF.normalize] using ainU)
        (hfree := by
          simp [Hnorm, HornNF.normalize, hfree])
        (hNoPremV := by
          intro h Q hQ
          have hQ' : Q ∈ (HornNF.normalizePrem F.H a).prem h := by
            simpa [Hnorm, HornNF.normalizePrem] using hQ
          exact HornNF.normalizePrem_noPremContains (H := F.H) (a := a) hQ')
    simpa [Nat.succ_eq_add_one, hsubadd] using hEq_raw
  have htrace_eq : Hnorm.trace a = F.H.trace a := by
    exact HornNF.trace_normalizePrem_eq_of_head_free (H := F.H) (a := a) hfree
  have hineq :
    NDS_corr (F.H.U.card) (HornNF.FixSet F.H) ({a} : Finset α)
      ≤
    NDS (F.H.U.card - 1) (HornNF.FixSet (F.H.trace a)) := by
    calc
      NDS_corr (F.H.U.card) (HornNF.FixSet F.H) ({a} : Finset α)
          ≤
        NDS_corr (F.H.U.card) (HornNF.FixSet Hnorm) ({a} : Finset α) := hmono
      _ = NDS (F.H.U.card - 1) (HornNF.FixSet (Hnorm.trace a)) := hheadfree_norm
      _ = NDS (F.H.U.card - 1) (HornNF.FixSet (F.H.trace a)) := by simp [htrace_eq]
  refine ⟨Qcorr_singleton_deletion_free F a, ?_⟩
  constructor
  · dsimp [Qcorr_singleton_deletion_free]
    dsimp [HornNF.trace]
    exact Finset.card_erase_of_mem ainU
  · dsimp [HornWithForbid.NDS_corr, HornWithForbid.BaseC]
    rw [heq]
    dsimp [Qcorr_singleton_deletion_free]
    rw [show (F.H.trace a).U.card = F.H.U.card - 1 by
      dsimp [HornNF.trace]
      exact Finset.card_erase_of_mem ainU]
    exact hineq

theorem Qcorr_singleton_headFree
  (n : Nat) (F : HornWithForbid α)  :
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) →
  F.H.U.card = n + 1 → (fb:IsForbidSingleton F) → ¬HasHead1s F fb→
   Qcorr (n+1) F := by
  intro hQ hn hSC hh
  dsimp [IsForbidSingleton] at hSC
  have :∃ a , F.F = {a} := by exact Finset.card_eq_one.mp hSC
  obtain ⟨a,ha⟩ := this
  have : ¬HasHead1 F a := by
    dsimp [HasHead1s] at hh
    simp_all only [Finset.singleton_inj, Classical.choose_eq']
    simp_all only [Finset.card_singleton]
    dsimp [HasHead1]
    exact hh
  obtain ⟨P',hP'⟩ := Qcorr_singleton_headFree_get F a ha this
  dsimp [Qcorr]
  intro hn
  specialize hQ P'
  have :P'.H.U.card = n := by
    simp_all only [add_tsub_cancel_right, forall_const]
  specialize hQ this
  dsimp [Q] at hQ
  specialize hQ this
  rw [←hn]
  rw [←this] at hQ
  rcases hP' with ⟨h1,h2⟩
  dsimp [HornWithForbid.NDS_corr] at h2
  dsimp [HornWithForbid.BaseC] at h2
  rw [h1] at hQ
  rw [h1] at h2
  exact Int.le_trans h2 hQ

-----------------------------------------------------


theorem Q_branch_headFree
  (n : Nat) (P : Pack0 α) (h : α) :
  (∀ P':Pack0 α, P'.H.U.card = n → Q n P') →
  P.H.U.card = n + 1 → P.H.IsSC h → ¬P.H.hasHead h →
   Q (n+1) P := by
  intro hIH hn hSC hNoHead
  dsimp [Q]
  intro _hn
  have hhU : h ∈ P.H.U := by
    have hFixSingle : ({h} : Finset α) ∈ P.H.FixSet :=
      (SC_closure_singleton P.H h).mpr hSC
    have hClosedSingle : HornNF.IsClosed P.H ({h} : Finset α) :=
      (mem_FixSet_iff P.H ({h} : Finset α)).1 hFixSingle
    exact hClosedSingle.2 (by simp)
  have hfree : P.H.prem h = ∅ := by
    by_cases hp : P.H.prem h = ∅
    · exact hp
    · exfalso
      exact hNoHead (Finset.nonempty_iff_ne_empty.mpr hp)
  have hConCard : (Q_contraction P h hSC).H.U.card = n := by
    dsimp [Q_contraction]
    rw [contraction_U, Finset.card_erase_of_mem hhU]
    omega
  have hTraceCard : (Q_trace P h).H.U.card = n := by
    dsimp [Q_trace, HornNF.trace]
    rw [Finset.card_erase_of_mem hhU]
    omega
  have hConQ : Q n (Q_contraction P h hSC) := hIH (Q_contraction P h hSC) hConCard
  have hTraceQ : Q n (Q_trace P h) := hIH (Q_trace P h) hTraceCard
  have hCon_nonpos : NDS n (Con h (HornNF.FixSet P.H)) ≤ 0 := by
    have h0 : NDS n ((Q_contraction P h hSC).H.FixSet) ≤ 0 := hConQ hConCard
    have hFixEq : (Q_contraction P h hSC).H.FixSet = Con h (HornNF.FixSet P.H) := by
      dsimp [Q_contraction]
      exact contraction_fix_equiv P.H h hhU
    simpa [hFixEq] using h0
  have hDel_nonpos : NDS n (Del h (HornNF.FixSet P.H)) ≤ 0 := by
    have h0 : NDS n ((Q_trace P h).H.FixSet) ≤ 0 := hTraceQ hTraceCard
    have hFixEq : (Q_trace P h).H.FixSet = Del h (HornNF.FixSet P.H) := by
      dsimp [Q_trace]
      calc
        HornNF.FixSet (P.H.trace h)
            = Hole (α := α) (HornNF.FixSet P.H) ({h} : Finset α) := by
              symm
              exact hole_singleton_eq_fixset_trace_head_free
                (H := P.H) (v := h) (hvU := hhU) (hfree := hfree)
        _ = Del h (HornNF.FixSet P.H) := by
              simp [Del, Hole]
    simpa [hFixEq] using h0
  have hRare : HornNF.rare P.H h := HornNF.rare_of_not_hasHead P.H h hNoHead
  have hndeg_nonpos : ndeg (HornNF.FixSet P.H) h ≤ 0 := by
    simpa [HornNF.rare] using hRare
  have hID :
      NDS (n + 1) (HornNF.FixSet P.H)
        =
      NDS n (Con h (HornNF.FixSet P.H))
        + (NDS n (Del h (HornNF.FixSet P.H)) + ndeg (HornNF.FixSet P.H) h) := by
    simpa using
      (Accounting.CON_ID_assoc (α := α) (n := n + 1) (hn := by omega)
        (C := HornNF.FixSet P.H) (u := h))
  rw [hID]
  linarith

theorem Q_branch_hasHead
  (n : Nat) (P : Pack0 α) (h : α) :
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) → (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  P.H.U.card = n + 1 → P.H.IsSC h → P.H.hasHead h →
  Q (n+1) P := by
  intro hIH hIHcorr hn hSC hHasHead
  dsimp [Q]
  intro _hn
  have hhU : h ∈ P.H.U := by
    have hFixSingle : ({h} : Finset α) ∈ P.H.FixSet :=
      (SC_closure_singleton P.H h).mpr hSC
    have hClosedSingle : HornNF.IsClosed P.H ({h} : Finset α) :=
      (mem_FixSet_iff P.H ({h} : Finset α)).1 hFixSingle
    exact hClosedSingle.2 (by simp)
  have hConCard : (Q_contraction P h hSC).H.U.card = n := by
    dsimp [Q_contraction]
    rw [contraction_U, Finset.card_erase_of_mem hhU]
    omega
  have hConQ : Q n (Q_contraction P h hSC) := hIH (Q_contraction P h hSC) hConCard
  have hCon_nonpos : NDS n (Con h (HornNF.FixSet P.H)) ≤ 0 := by
    have h0 : NDS n ((Q_contraction P h hSC).H.FixSet) ≤ 0 := hConQ hConCard
    have hFixEq : (Q_contraction P h hSC).H.FixSet = Con h (HornNF.FixSet P.H) := by
      dsimp [Q_contraction]
      exact contraction_fix_equiv P.H h hhU
    simpa [hFixEq] using h0
  let F0 : HornWithForbid α := {
    H := P.H
    hDR1 := P.hDR1
    hNEP := P.hNEP
    F := ({h} : Finset α)
    F_subset_U := by
      intro x hx
      simpa using (Finset.mem_singleton.mp hx ▸ hhU)
    F_nonempty := by simp
  }
  have hHasHead1 : HasHead1 F0 h := by
    simpa [HasHead1, F0] using hHasHead
  obtain ⟨F', hF'⟩ := Qcorr_singleton_hasHead_get (α := α) F0 h rfl hHasHead1
  have hF'card_n : F'.H.U.card = n := by
    rcases hF' with ⟨hcard, _⟩
    have : F0.H.U.card = n + 1 := by simpa [F0] using hn
    omega
  have hQcorrF' : Qcorr n F' := hIHcorr F' hF'card_n
  have hF'nonpos : F'.NDS_corr n ≤ 0 := by
    dsimp [Qcorr] at hQcorrF'
    exact hQcorrF' hF'card_n
  have hSingletonCorr_nonpos : NDS_corr (n + 1) (HornNF.FixSet P.H) ({h} : Finset α) ≤ 0 := by
    rcases hF' with ⟨hcard, hineq⟩
    have hineq' : F0.NDS_corr (n + 1) ≤ F'.NDS_corr n := by
      have h0card : F0.H.U.card = n + 1 := by simpa [F0] using hn
      have h1card : F'.H.U.card = n := by
        have : F0.H.U.card = n + 1 := by simpa [F0] using hn
        omega
      simpa [h0card, h1card] using hineq
    have hF0_nonpos : F0.NDS_corr (n + 1) ≤ 0 := le_trans hineq' hF'nonpos
    simpa [HornWithForbid.NDS_corr, HornWithForbid.BaseC, F0] using hF0_nonpos
  have hDelNdeg_eq_corr :
      NDS n (Del h (HornNF.FixSet P.H)) + ndeg (HornNF.FixSet P.H) h
        =
      NDS_corr (n + 1) (HornNF.FixSet P.H) ({h} : Finset α) := by
    let C : Finset (Finset α) := HornNF.FixSet P.H
    have hcard : (Up (α := α) C ({h} : Finset α)).card + (Hole (α := α) C ({h} : Finset α)).card = C.card := by
      exact card_Up_add_card_Hole (α := α) C ({h} : Finset α)
    have hndeg :
        ndeg C h
          = (((Up (α := α) C ({h} : Finset α)).card : Int)
              - (Hole (α := α) C ({h} : Finset α)).card) := by
      have hcardInt :
          (C.card : Int)
            = ((Up (α := α) C ({h} : Finset α)).card : Int)
              + (Hole (α := α) C ({h} : Finset α)).card := by
        have := congrArg (fun t : Nat => (t : Int)) hcard
        simpa [Int.natCast_add, add_comm, add_left_comm, add_assoc] using this.symm
      calc
        ndeg C h = (2 : Int) * (deg (α := α) C h : Int) - (C.card : Int) := by
          rfl
        _ = (2 : Int) * ((Up (α := α) C ({h} : Finset α)).card : Int) - (C.card : Int) := by
          simp [deg, Up]
        _ = (2 : Int) * ((Up (α := α) C ({h} : Finset α)).card : Int)
              - (((Up (α := α) C ({h} : Finset α)).card : Int)
                + (Hole (α := α) C ({h} : Finset α)).card) := by
              rw [hcardInt]
        _ = (((Up (α := α) C ({h} : Finset α)).card : Int)
              - (Hole (α := α) C ({h} : Finset α)).card) := by
              ring
    calc
      NDS n (Del h C) + ndeg C h
          = NDS n (Hole (α := α) C ({h} : Finset α))
            + (((Up (α := α) C ({h} : Finset α)).card : Int)
                - (Hole (α := α) C ({h} : Finset α)).card) := by
              simp [Del, Hole, hndeg]
      _ = (NDS n (Hole (α := α) C ({h} : Finset α))
            - (Hole (α := α) C ({h} : Finset α)).card)
          + (Up (α := α) C ({h} : Finset α)).card := by
            ring
      _ = NDS (n + 1) (Hole (α := α) C ({h} : Finset α))
          + (Up (α := α) C ({h} : Finset α)).card := by
            simp [Accounting.NDS_succ]
      _ = NDS_corr (n + 1) C ({h} : Finset α) := by
            simp [NDS_corr]
  have hDelNdeg_nonpos :
      NDS n (Del h (HornNF.FixSet P.H)) + ndeg (HornNF.FixSet P.H) h ≤ 0 := by
    rw [hDelNdeg_eq_corr]
    exact hSingletonCorr_nonpos
  have hID :
      NDS (n + 1) (HornNF.FixSet P.H)
        =
      NDS n (Con h (HornNF.FixSet P.H))
        + (NDS n (Del h (HornNF.FixSet P.H)) + ndeg (HornNF.FixSet P.H) h) := by
    simpa using
      (Accounting.CON_ID_assoc (α := α) (n := n + 1) (hn := by omega)
        (C := HornNF.FixSet P.H) (u := h))
  rw [hID]
  linarith

theorem Qcorr_ge2_hasHead
  (n : Nat) (F : HornWithForbid α) (a : α) (hh : a ∈ F.F):
   (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  F.H.U.card = n + 1 → ¬IsForbidSingleton F → IsSC1 F a → HasHead1 F a →
   Qcorr (n+1) F
:= by
  intro hIHcorr hn hNotSing hSC1 hHasHead1
  dsimp [Qcorr]
  intro _hn
  have hge2 : 2 ≤ F.F.card :=
    card_ge_two_of_mem_not_singleton (F := F) (a := a) (ha := hh) (hns := hNotSing)
  have hSC : F.H.IsSC a := hSC1
  have hHasHead : F.H.hasHead a := by
    simpa [HasHead1] using hHasHead1

  -- Contraction branch (ge2 world)
  let Fc : HornWithForbid α := Qcorr_contraction F a hSC hh hge2
  have hFc_card : Fc.H.U.card = n := by
    have hcardm1 : Fc.H.U.card = F.H.U.card - 1 := by
      simpa [Fc] using qcorr_contraction_card (F := F) (a := a) (hSC := hSC) (hA := hh) (geq2 := hge2)
    rw [hn] at hcardm1
    omega
  have hQFc : Qcorr n Fc := hIHcorr Fc hFc_card
  have hConHole_nonpos :
      NDS (α := α) n (Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a)) ≤ 0 := by
    have hFcHole_nonpos : NDS (α := α) n Fc.FixSet ≤ 0 :=
      hole_nonpos_of_Qcorr (n := n) (F := Fc) hQFc hFc_card
    have hFcFix :
        Fc.FixSet
          = Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a) := by
      calc
        Fc.FixSet
            = Con (α := α) a F.FixSet := by
                simpa [Fc] using
                  Qcorr_contraction_fixset_eq_Con (F := F) (a := a) (hSC := hSC) (hA := hh) (geq2 := hge2)
        _ = Con (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F) := by
                simp [FixSet_eq_Hole_FixSet]
        _ = Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a) := by
                exact Con_Hole_eq_Hole_Con_erase (α := α) (C := HornNF.FixSet F.H) (A := F.F) (a := a) hh
    simpa [hFcFix] using hFcHole_nonpos

  -- Deletion-head branch (trace + forbid replacement by premise P)
  let Fd : HornWithForbid α := Qcorr_deletion_head F a hHasHead
  have hFd_card : Fd.H.U.card = n := by
    have hcardm1 : Fd.H.U.card = F.H.U.card - 1 := by
      simpa [Fd] using qcorr_deletion_head_card (F := F) (a := a) (hasHead := hHasHead)
    rw [hn] at hcardm1
    omega
  have hQFd : Qcorr n Fd := hIHcorr Fd hFd_card
  have hDel_nonpos :
      NDS (α := α) n (Del (α := α) a (HornNF.FixSet F.H)) ≤ 0 := by
    have hFdHole_nonpos : NDS (α := α) n Fd.FixSet ≤ 0 :=
      hole_nonpos_of_Qcorr (n := n) (F := Fd) hQFd hFd_card
    have hFdFix : Fd.FixSet = Del (α := α) a (HornNF.FixSet F.H) := by
      simpa [Fd] using Qcorr_deletion_head_fixset_eq_Del (F := F) (a := a) (hasHead := hHasHead)
    simpa [hFdFix] using hFdHole_nonpos

  -- Singleton-hasHead reduction on the same Horn base: obtains `NDS Del + ndeg ≤ 0`
  let F0 : HornWithForbid α := {
    H := F.H
    hDR1 := F.hDR1
    hNEP := F.hNEP
    F := ({a} : Finset α)
    F_subset_U := by
      intro x hx
      have haU : a ∈ F.H.U := F.F_subset_U hh
      simpa using (Finset.mem_singleton.mp hx ▸ haU)
    F_nonempty := by simp
  }
  have hHasHead1_F0 : HasHead1 F0 a := by
    simpa [HasHead1, F0] using hHasHead1
  obtain ⟨Fs, hFs⟩ := Qcorr_singleton_hasHead_get (α := α) F0 a rfl hHasHead1_F0
  have hFs_card : Fs.H.U.card = n := by
    rcases hFs with ⟨hcard, _⟩
    have hF0card : F0.H.U.card = n + 1 := by simpa [F0] using hn
    rw [hF0card] at hcard
    omega
  have hQFs : Qcorr n Fs := hIHcorr Fs hFs_card
  have hFs_nonpos : Fs.NDS_corr n ≤ 0 := by
    exact ndiscorr_nonpos_of_Qcorr (n := n) (F := Fs) hQFs hFs_card
  have hSingletonCorr_nonpos :
      NDS_corr (α := α) (n + 1) (HornNF.FixSet F.H) ({a} : Finset α) ≤ 0 := by
    rcases hFs with ⟨hcard, hineq⟩
    have hineq' : F0.NDS_corr (n + 1) ≤ Fs.NDS_corr n := by
      have h0card : F0.H.U.card = n + 1 := by simpa [F0] using hn
      have h1card : Fs.H.U.card = n := hFs_card
      simpa [h0card, h1card] using hineq
    have hF0_nonpos : F0.NDS_corr (n + 1) ≤ 0 := le_trans hineq' hFs_nonpos
    simpa [HornWithForbid.NDS_corr, HornWithForbid.BaseC, F0] using hF0_nonpos
  have hDelNdeg_nonpos :
      NDS (α := α) n (Del (α := α) a (HornNF.FixSet F.H)) + ndeg (α := α) (HornNF.FixSet F.H) a ≤ 0 := by
    rw [nds_del_add_ndeg_eq_nds_corr_singleton (α := α) (n := n) (C := HornNF.FixSet F.H) (a := a)]
    exact hSingletonCorr_nonpos

  -- Final accounting on `Hole(Fix(H), F.F)`
  have hMainEq :
      NDS_corr (α := α) (n + 1) (HornNF.FixSet F.H) F.F
        =
      NDS (α := α) n (Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a))
        + (NDS (α := α) n (Del (α := α) a (HornNF.FixSet F.H))
            + ndeg (α := α) (HornNF.FixSet F.H) a) := by
    have hID :=
      Accounting.CON_ID_assoc (α := α) (n := n + 1) (hn := by omega)
        (C := Hole (α := α) (HornNF.FixSet F.H) F.F) (u := a)
    have hID' :
        NDS (α := α) (n + 1) (Hole (α := α) (HornNF.FixSet F.H) F.F)
          =
        NDS (α := α) n (Con (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F))
          + (NDS (α := α) n (Del (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F))
              + ndeg (α := α) (Hole (α := α) (HornNF.FixSet F.H) F.F) a) := by
      simpa using hID
    calc
      NDS_corr (α := α) (n + 1) (HornNF.FixSet F.H) F.F
          =
        NDS (α := α) (n + 1) (Hole (α := α) (HornNF.FixSet F.H) F.F)
          + (Up (α := α) (HornNF.FixSet F.H) F.F).card := by
            simp [NDS_corr]
      _ =
        (NDS (α := α) n (Con (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F))
          + (NDS (α := α) n (Del (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F))
              + ndeg (α := α) (Hole (α := α) (HornNF.FixSet F.H) F.F) a))
          + (Up (α := α) (HornNF.FixSet F.H) F.F).card := by
            rw [hID']
      _ =
        NDS (α := α) n (Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a))
          + (NDS (α := α) n (Del (α := α) a (HornNF.FixSet F.H))
              + ndeg (α := α) (HornNF.FixSet F.H) a) := by
            have hConEq :
                Con (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F)
                  =
                Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a) :=
              Con_Hole_eq_Hole_Con_erase (α := α) (C := HornNF.FixSet F.H) (A := F.F) (a := a) hh
            have hDelEq :
                Del (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F)
                  =
                Del (α := α) a (HornNF.FixSet F.H) :=
              Del_Hole_eq_Del_of_mem (α := α) (C := HornNF.FixSet F.H) (A := F.F) (a := a) hh
            have hNdegEq :
                ndeg (α := α) (Hole (α := α) (HornNF.FixSet F.H) F.F) a
                  + (Up (α := α) (HornNF.FixSet F.H) F.F).card
                  =
                ndeg (α := α) (HornNF.FixSet F.H) a :=
              ndeg_hole_add_up_eq_ndeg_of_mem (α := α) (C := HornNF.FixSet F.H) (A := F.F) (a := a) hh
            rw [hConEq, hDelEq]
            linarith [hNdegEq]
  rw [hMainEq]
  linarith [hConHole_nonpos, hDelNdeg_nonpos]

theorem Qcorr_ge2_headFree
  (n : Nat) (F : HornWithForbid α) (a : α) (ha : a ∈ F.F):
  (∀ P:Pack0 α, P.H.U.card = n → Q n P) →
  (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') →
  F.H.U.card = n + 1 → ¬IsForbidSingleton F → IsSC1 F a → ¬HasHead1 F a →
  Qcorr (n+1) F := by
  intro hIH hIHcorr hn hNotSing hSC1 hNoHead1
  dsimp [Qcorr]
  intro _hn
  have hge2 : 2 ≤ F.F.card :=
    card_ge_two_of_mem_not_singleton (F := F) (a := a) (ha := ha) (hns := hNotSing)
  have hSC : F.H.IsSC a := hSC1
  have haU : a ∈ F.H.U := F.F_subset_U ha
  have hfree : F.H.prem a = ∅ := by
    simpa [HasHead1] using hNoHead1
  have hNoHead : ¬F.H.hasHead a := by
    simp [HornNF.hasHead, hfree]

  -- Contraction branch (ge2 world)
  let Fc : HornWithForbid α := Qcorr_contraction F a hSC ha hge2
  have hFc_card : Fc.H.U.card = n := by
    have hcardm1 : Fc.H.U.card = F.H.U.card - 1 := by
      simpa [Fc] using
        qcorr_contraction_card (F := F) (a := a) (hSC := hSC) (hA := ha) (geq2 := hge2)
    rw [hn] at hcardm1
    omega
  have hQFc : Qcorr n Fc := hIHcorr Fc hFc_card
  have hConHole_nonpos :
      NDS (α := α) n (Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a)) ≤ 0 := by
    have hFcHole_nonpos : NDS (α := α) n Fc.FixSet ≤ 0 :=
      hole_nonpos_of_Qcorr (n := n) (F := Fc) hQFc hFc_card
    have hFcFix :
        Fc.FixSet
          = Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a) := by
      calc
        Fc.FixSet
            = Con (α := α) a F.FixSet := by
                simpa [Fc] using
                  Qcorr_contraction_fixset_eq_Con (F := F) (a := a) (hSC := hSC) (hA := ha) (geq2 := hge2)
        _ = Con (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F) := by
                simp [FixSet_eq_Hole_FixSet]
        _ = Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a) := by
                exact Con_Hole_eq_Hole_Con_erase (α := α) (C := HornNF.FixSet F.H) (A := F.F) (a := a) ha
    simpa [hFcFix] using hFcHole_nonpos

  -- Trace branch in head-free case gives `Del`, then combine with `rare` (`ndeg ≤ 0`)
  let Pt : Pack0 α := Qcorr_singleton_deletion_free F a
  have hPt_card : Pt.H.U.card = n := by
    have hcardm1 : Pt.H.U.card = F.H.U.card - 1 := by
      dsimp [Pt, Qcorr_singleton_deletion_free, HornNF.trace]
      exact Finset.card_erase_of_mem haU
    rw [hn] at hcardm1
    omega
  have hQPt : Q n Pt := hIH Pt hPt_card
  have hDel_nonpos :
      NDS (α := α) n (Del (α := α) a (HornNF.FixSet F.H)) ≤ 0 := by
    have hPt_nonpos : NDS (α := α) n Pt.H.FixSet ≤ 0 := by
      dsimp [Q] at hQPt
      exact hQPt hPt_card
    have hPtFix : Pt.H.FixSet = Del (α := α) a (HornNF.FixSet F.H) := by
      dsimp [Pt, Qcorr_singleton_deletion_free]
      calc
        HornNF.FixSet (F.H.trace a)
            = Hole (α := α) (HornNF.FixSet F.H) ({a} : Finset α) := by
              symm
              exact hole_singleton_eq_fixset_trace_head_free
                (H := F.H) (v := a) (hvU := haU) (hfree := hfree)
        _ = Del (α := α) a (HornNF.FixSet F.H) := by
              simp [Del, Hole]
    simpa [hPtFix] using hPt_nonpos
  have hRare : HornNF.rare F.H a := HornNF.rare_of_not_hasHead F.H a hNoHead
  have hndeg_nonpos : ndeg (α := α) (HornNF.FixSet F.H) a ≤ 0 := by
    simpa [HornNF.rare] using hRare
  have hDelNdeg_nonpos :
      NDS (α := α) n (Del (α := α) a (HornNF.FixSet F.H))
        + ndeg (α := α) (HornNF.FixSet F.H) a ≤ 0 := by
    linarith [hDel_nonpos, hndeg_nonpos]

  -- Final accounting on `Hole(Fix(H), F.F)`
  have hMainEq :
      NDS_corr (α := α) (n + 1) (HornNF.FixSet F.H) F.F
        =
      NDS (α := α) n (Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a))
        + (NDS (α := α) n (Del (α := α) a (HornNF.FixSet F.H))
            + ndeg (α := α) (HornNF.FixSet F.H) a) := by
    have hID :=
      Accounting.CON_ID_assoc (α := α) (n := n + 1) (hn := by omega)
        (C := Hole (α := α) (HornNF.FixSet F.H) F.F) (u := a)
    have hID' :
        NDS (α := α) (n + 1) (Hole (α := α) (HornNF.FixSet F.H) F.F)
          =
        NDS (α := α) n (Con (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F))
          + (NDS (α := α) n (Del (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F))
              + ndeg (α := α) (Hole (α := α) (HornNF.FixSet F.H) F.F) a) := by
      simpa using hID
    calc
      NDS_corr (α := α) (n + 1) (HornNF.FixSet F.H) F.F
          =
        NDS (α := α) (n + 1) (Hole (α := α) (HornNF.FixSet F.H) F.F)
          + (Up (α := α) (HornNF.FixSet F.H) F.F).card := by
            simp [NDS_corr]
      _ =
        (NDS (α := α) n (Con (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F))
          + (NDS (α := α) n (Del (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F))
              + ndeg (α := α) (Hole (α := α) (HornNF.FixSet F.H) F.F) a))
          + (Up (α := α) (HornNF.FixSet F.H) F.F).card := by
            rw [hID']
      _ =
        NDS (α := α) n (Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a))
          + (NDS (α := α) n (Del (α := α) a (HornNF.FixSet F.H))
              + ndeg (α := α) (HornNF.FixSet F.H) a) := by
            have hConEq :
                Con (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F)
                  =
                Hole (α := α) (Con (α := α) a (HornNF.FixSet F.H)) (F.F.erase a) :=
              Con_Hole_eq_Hole_Con_erase (α := α) (C := HornNF.FixSet F.H) (A := F.F) (a := a) ha
            have hDelEq :
                Del (α := α) a (Hole (α := α) (HornNF.FixSet F.H) F.F)
                  =
                Del (α := α) a (HornNF.FixSet F.H) :=
              Del_Hole_eq_Del_of_mem (α := α) (C := HornNF.FixSet F.H) (A := F.F) (a := a) ha
            have hNdegEq :
                ndeg (α := α) (Hole (α := α) (HornNF.FixSet F.H) F.F) a
                  + (Up (α := α) (HornNF.FixSet F.H) F.F).card
                  =
                ndeg (α := α) (HornNF.FixSet F.H) a :=
              ndeg_hole_add_up_eq_ndeg_of_mem (α := α) (C := HornNF.FixSet F.H) (A := F.F) (a := a) ha
            rw [hConEq, hDelEq]
            linarith [hNdegEq]
  rw [hMainEq]
  linarith [hConHole_nonpos, hDelNdeg_nonpos]

omit [DecidableEq α] in
/-- Card-split helper: any finite set has either card = 0, card = 1, or card ≥ 2.
Stepsで使っている
-/
lemma card_cases
  (A : Finset α) :
  A.card = 0 ∨ A.card = 1 ∨ 2 ≤ A.card := by
  classical
  have h : A.card = 0 ∨ A.card = 1 ∨ 2 ≤ A.card := by
    omega
  exact h

end Dr1nds
