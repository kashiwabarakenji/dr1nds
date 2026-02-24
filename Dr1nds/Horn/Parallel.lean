import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornClosure

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- Parallel relation on two vertices (Horn-closure presentation). -/
def HornNF.IsParallelByClosure (H : HornNF α) (u v : α) : Prop :=
  u ≠ v ∧ u ∈ H.closure {v} ∧ v ∈ H.closure {u}

/- Parallel relation on two vertices (closed-family presentation). -/
def HornNF.IsParallelByFixSet (H : HornNF α) (u v : α) : Prop :=
  u ≠ v ∧ u ∈ H.U ∧ v ∈ H.U ∧
    ∀ X : Finset α, X ∈ H.FixSet → (u ∈ X ↔ v ∈ X)

lemma HornNF.mem_closure_singleton_iff
  (H : HornNF α) (u v : α) :
  u ∈ H.closure {v} ↔
    u ∈ H.U ∧ ∀ X : Finset α, X ∈ H.FixSet → v ∈ X → u ∈ X := by
  classical
  constructor
  · intro hu
    refine ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp hu).1
    · intro X hX hvX
      have hXclosed : H.IsClosed X := (mem_FixSet_iff (H := H) (X := X)).1 hX
      exact (Finset.mem_filter.mp hu).2 X hXclosed (Finset.singleton_subset_iff.mpr hvX)
  · intro h
    rcases h with ⟨huU, hforall⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨huU, ?_⟩
    intro X hXclosed hsub
    have hvX : v ∈ X := hsub (by simp)
    exact hforall X ((mem_FixSet_iff (H := H) (X := X)).2 hXclosed) hvX

theorem HornNF.parallel_closure_iff_parallel_fixset
  (H : HornNF α) (u v : α) :
  H.IsParallelByClosure u v ↔ H.IsParallelByFixSet u v := by
  classical
  constructor
  · intro hPar
    rcases hPar with ⟨hne, huv, hvu⟩
    rcases (HornNF.mem_closure_singleton_iff (H := H) (u := u) (v := v)).1 huv with ⟨huU, huAll⟩
    rcases (HornNF.mem_closure_singleton_iff (H := H) (u := v) (v := u)).1 hvu with ⟨hvU, hvAll⟩
    refine ⟨hne, huU, hvU, ?_⟩
    intro X hX
    constructor
    · intro huX
      exact hvAll X hX huX
    · intro hvX
      exact huAll X hX hvX
  · intro hPar
    rcases hPar with ⟨hne, huU, hvU, hiff⟩
    refine ⟨hne, ?_, ?_⟩
    · exact (HornNF.mem_closure_singleton_iff (H := H) (u := u) (v := v)).2
        ⟨huU, by
          intro X hX hvX
          exact (hiff X hX).2 hvX⟩
    · exact (HornNF.mem_closure_singleton_iff (H := H) (u := v) (v := u)).2
        ⟨hvU, by
          intro X hX huX
          exact (hiff X hX).1 huX⟩

lemma HornNF.prem_subset_closure_singleton_of_mem_closure
  (H : HornNF α) (hDR1 : H.IsDR1)
  (u h : α) (hh_ne : h ≠ u) {P : Finset α}
  (huS : u ∈ H.closure ({u} : Finset α))
  (hP : P ∈ H.prem h) :
  h ∈ H.closure ({u} : Finset α) → P ⊆ H.closure ({u} : Finset α) := by
  classical
  intro hhcl
  by_contra hnot
  rcases Finset.not_subset.mp hnot with ⟨p, hpP, hpnotS⟩
  let S : Finset α := H.closure ({u} : Finset α)
  let Y : Finset α := S.erase h
  have huS' : u ∈ S := by simpa [S] using huS
  have huY : u ∈ Y := by
    refine Finset.mem_erase.mpr ?_
    exact ⟨hh_ne.symm, huS'⟩
  have hYclosed : H.IsClosed Y := by
    constructor
    · intro k Q hQ hQsub
      by_cases hk : k = h
      · have hPk : P ∈ H.prem k := by simpa [hk] using hP
        have hQeq : Q = P := prem_eq_of_mem_of_mem (H := H) (v := k) (hDR1 := hDR1) hQ hPk
        have hpQ : p ∈ Q := by simpa [hQeq] using hpP
        have hpY : p ∈ Y := hQsub hpQ
        have hpS : p ∈ S := Finset.mem_of_mem_erase hpY
        exact False.elim (hpnotS hpS)
      · have hQsubS : Q ⊆ S := by
          exact fun x hx => Finset.mem_of_mem_erase (hQsub hx)
        have hSclosed : H.IsClosed S := HornNF.closure_isClosed (H := H) (X := ({u} : Finset α))
        have hkS : k ∈ S := hSclosed.1 hQ hQsubS
        exact Finset.mem_erase.mpr ⟨hk, hkS⟩
    · intro x hx
      exact HornNF.closure_subset_U (H := H) (X := ({u} : Finset α)) (Finset.mem_of_mem_erase hx)
  have hu_sub_Y : ({u} : Finset α) ⊆ Y := Finset.singleton_subset_iff.mpr huY
  have hhY : h ∈ Y := (Finset.mem_filter.mp hhcl).2 Y hYclosed hu_sub_Y
  have : h ∉ Y := by simp [Y]
  exact this hhY

lemma HornNF.prem_inter_closure_singleton_nonempty_of_parallel
  (H : HornNF α) (hDR1 : H.IsDR1) (hNEP : H.IsNEP)
  {u v : α} (hPar : H.IsParallelByClosure u v) {P : Finset α}
  (hP : P ∈ H.prem u) :
  (P ∩ H.closure ({u} : Finset α)).Nonempty := by
  classical
  rcases hPar with ⟨huv_ne, hu_in_clv, hv_in_clu⟩
  by_contra hEmpty
  have hEmpty' : P ∩ H.closure ({u} : Finset α) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
  let S : Finset α := H.closure ({u} : Finset α)
  let T : Finset α := S.erase u
  have hPnonempty : P.Nonempty := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro hPe
    have : (∅ : Finset α) ∈ H.prem u := by simpa [hPe] using hP
    exact hNEP this
  have hPsubsetNotS : ∀ x ∈ P, x ∉ S := by
    intro x hxP hxS
    have hxPS : x ∈ P ∩ H.closure ({u} : Finset α) := Finset.mem_inter.mpr ⟨hxP, hxS⟩
    have hcontra : x ∈ (∅ : Finset α) := by
      rw [hEmpty'] at hxPS
      exact hxPS
    exact (Finset.notMem_empty x) hcontra
  have hTclosed : H.IsClosed T := by
    constructor
    · intro h Q hQ hQsub
      by_cases hh : h = u
      · have hPu : P ∈ H.prem h := by simpa [hh] using hP
        have hQeq : Q = P := prem_eq_of_mem_of_mem (H := H) (v := h) (hDR1 := hDR1) hQ hPu
        rcases hPnonempty with ⟨x, hxP⟩
        have hxQ : x ∈ Q := by simpa [hQeq] using hxP
        have hxT : x ∈ T := hQsub hxQ
        have hxS : x ∈ S := Finset.mem_of_mem_erase hxT
        have hxNotS : x ∉ S := hPsubsetNotS x hxP
        exact False.elim (hxNotS hxS)
      · have hQsubS : Q ⊆ S := by
          exact fun x hx => Finset.mem_of_mem_erase (hQsub hx)
        have hSclosed : H.IsClosed S := HornNF.closure_isClosed (H := H) (X := ({u} : Finset α))
        have hhS : h ∈ S := hSclosed.1 hQ hQsubS
        exact Finset.mem_erase.mpr ⟨hh, hhS⟩
    · intro x hx
      exact HornNF.closure_subset_U (H := H) (X := ({u} : Finset α)) (Finset.mem_of_mem_erase hx)
  have hvT : v ∈ T := by
    refine Finset.mem_erase.mpr ?_
    exact ⟨huv_ne.symm, hv_in_clu⟩
  have hv_sub_T : ({v} : Finset α) ⊆ T := Finset.singleton_subset_iff.mpr hvT
  have huT : u ∈ T := (Finset.mem_filter.mp hu_in_clv).2 T hTclosed hv_sub_T
  have : u ∉ T := by simp [T]
  exact this huT

theorem HornNF.rare_of_hasParallel_of_DR1
  (H : HornNF α) (hDR1 : H.IsDR1) (hNEP : H.IsNEP)
  {u : α} (hPar : ∃ v : α, H.IsParallelByClosure u v) :
  H.rare u := by
  classical
  rcases hPar with ⟨v, huvPar⟩
  let C : Finset (Finset α) := H.FixSet
  let A : Finset (Finset α) := C.filter (fun X => u ∈ X)
  let B : Finset (Finset α) := C.filter (fun X => u ∉ X)
  let S : Finset α := H.closure ({u} : Finset α)
  let f : Finset α → Finset α := fun X => X \ S
  have hmap_to_B : ∀ {X : Finset α}, X ∈ A → f X ∈ B := by
    intro X hX
    have hXfix : X ∈ C := (Finset.mem_filter.mp hX).1
    have huX : u ∈ X := (Finset.mem_filter.mp hX).2
    have hXclosed : H.IsClosed X := by
      simpa [C] using (mem_FixSet_iff (H := H) (X := X)).1 hXfix
    have hSX : S ⊆ X := by
      have huU : u ∈ H.U := (mem_FixSet_subset_U (H := H) hXfix) huX
      have huSub : ({u} : Finset α) ⊆ X := Finset.singleton_subset_iff.mpr huX
      exact HornNF.closure_subset_of_subset_isClosed (H := H) (hXY := huSub) (hY := hXclosed)
    have huS : u ∈ S := by
      have huU : u ∈ H.U := (mem_FixSet_subset_U (H := H) hXfix) huX
      have huSubU : ({u} : Finset α) ⊆ H.U := Finset.singleton_subset_iff.mpr huU
      have huInCl : u ∈ H.closure ({u} : Finset α) :=
        (HornNF.subset_closure (H := H) (X := ({u} : Finset α)) (hX := huSubU)) (by simp)
      simpa [S] using huInCl
    have hDiffClosed : H.IsClosed (X \ S) := by
      constructor
      · intro h P hP hPsub
        have hhX : h ∈ X := hXclosed.1 hP (by
          intro x hx
          exact (Finset.mem_sdiff.mp (hPsub hx)).1)
        have hhNotS : h ∉ S := by
          intro hhS
          by_cases hhu : h = u
          · subst hhu
            have hIntNonempty :
                (P ∩ S).Nonempty :=
              HornNF.prem_inter_closure_singleton_nonempty_of_parallel
                (H := H) (hDR1 := hDR1) (hNEP := hNEP) (hPar := huvPar) (hP := hP)
            rcases hIntNonempty with ⟨x, hxInt⟩
            have hxP : x ∈ P := (Finset.mem_inter.mp hxInt).1
            have hxS : x ∈ S := (Finset.mem_inter.mp hxInt).2
            have hxDiff : x ∈ X \ S := hPsub hxP
            exact (Finset.mem_sdiff.mp hxDiff).2 hxS
          · have hPS : P ⊆ S :=
              HornNF.prem_subset_closure_singleton_of_mem_closure
                (H := H) (hDR1 := hDR1) (u := u) (h := h) (hh_ne := hhu)
                (huS := huS)
                (hP := hP) hhS
            have hPnonempty : P.Nonempty := by
              by_contra hPn
              have hPe : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPn
              have hEmptyPrem : (∅ : Finset α) ∈ H.prem h := by simpa [hPe] using hP
              exact hNEP hEmptyPrem
            rcases hPnonempty with ⟨x, hxP⟩
            have hxS : x ∈ S := hPS hxP
            have hxDiff : x ∈ X \ S := hPsub hxP
            exact (Finset.mem_sdiff.mp hxDiff).2 hxS
        exact Finset.mem_sdiff.mpr ⟨hhX, hhNotS⟩
      · intro x hx
        exact (hXclosed.2) ((Finset.mem_sdiff.mp hx).1)
    have hDiffFix : X \ S ∈ C := by
      simpa [C] using (mem_FixSet_iff (H := H) (X := X \ S)).2 hDiffClosed
    exact Finset.mem_filter.mpr ⟨hDiffFix, by
      intro huDiff
      exact (Finset.mem_sdiff.mp huDiff).2 huS⟩
  have hInj : ∀ {X Y : Finset α}, X ∈ A → Y ∈ A → f X = f Y → X = Y := by
    intro X Y hX hY hEq
    have hXfix : X ∈ C := (Finset.mem_filter.mp hX).1
    have huX : u ∈ X := (Finset.mem_filter.mp hX).2
    have hYfix : Y ∈ C := (Finset.mem_filter.mp hY).1
    have huY : u ∈ Y := (Finset.mem_filter.mp hY).2
    have hXclosed : H.IsClosed X := by
      simpa [C] using (mem_FixSet_iff (H := H) (X := X)).1 hXfix
    have hYclosed : H.IsClosed Y := by
      simpa [C] using (mem_FixSet_iff (H := H) (X := Y)).1 hYfix
    have hSX : S ⊆ X := by
      have huSub : ({u} : Finset α) ⊆ X := Finset.singleton_subset_iff.mpr huX
      exact HornNF.closure_subset_of_subset_isClosed (H := H) (hXY := huSub) (hY := hXclosed)
    have hSY : S ⊆ Y := by
      have huSub : ({u} : Finset α) ⊆ Y := Finset.singleton_subset_iff.mpr huY
      exact HornNF.closure_subset_of_subset_isClosed (H := H) (hXY := huSub) (hY := hYclosed)
    apply Finset.Subset.antisymm
    · intro z hzX
      by_cases hzS : z ∈ S
      · exact hSY hzS
      · have hzDiff : z ∈ X \ S := Finset.mem_sdiff.mpr ⟨hzX, hzS⟩
        have hzFX : z ∈ f X := by simpa [f] using hzDiff
        have hzFY : z ∈ f Y := by simpa [hEq] using hzFX
        have : z ∈ Y \ S := by simpa [f] using hzFY
        exact (Finset.mem_sdiff.mp this).1
    · intro z hzY
      by_cases hzS : z ∈ S
      · exact hSX hzS
      · have hzDiff : z ∈ Y \ S := Finset.mem_sdiff.mpr ⟨hzY, hzS⟩
        have hzFY : z ∈ f Y := by simpa [f] using hzDiff
        have hzFX : z ∈ f X := by simpa [hEq] using hzFY
        have : z ∈ X \ S := by simpa [f] using hzFX
        exact (Finset.mem_sdiff.mp this).1
  have hAcard_image : A.card = (A.image f).card := by
    refine Finset.card_bij
      (s := A) (t := A.image f)
      (i := fun X _ => f X)
      (hi := by
        intro X hX
        exact Finset.mem_image_of_mem f hX)
      (i_inj := by
        intro X hX Y hY hEq
        exact hInj hX hY hEq)
      (i_surj := by
        intro Y hY
        rcases Finset.mem_image.mp hY with ⟨X, hX, rfl⟩
        exact ⟨X, hX, rfl⟩)
  have hImageSubset : A.image f ⊆ B := by
    intro Y hY
    rcases Finset.mem_image.mp hY with ⟨X, hX, rfl⟩
    exact hmap_to_B hX
  have hAleB : A.card ≤ B.card := by
    calc
      A.card = (A.image f).card := hAcard_image
      _ ≤ B.card := Finset.card_le_card hImageSubset
  have hCardSplit : A.card + B.card = C.card := by
    simpa [A, B, C] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := H.FixSet) (p := fun X : Finset α => u ∈ X))
  have hndegAB : ndeg (α := α) C u = (A.card : Int) - (B.card : Int) := by
    have hCardNat : C.card = A.card + B.card := hCardSplit.symm
    calc
      ndeg (α := α) C u
          = (2 : Int) * (A.card : Int) - (C.card : Int) := by
              simp [ndeg, deg, A, C]
      _ = (2 : Int) * (A.card : Int) - ((A.card + B.card : Nat) : Int) := by
              rw [hCardNat]
      _ = (A.card : Int) - (B.card : Int) := by
              calc
                (2 : Int) * (A.card : Int) - ((A.card + B.card : Nat) : Int)
                    = ((A.card : Int) + (A.card : Int)) - ((A.card : Int) + (B.card : Int)) := by
                        simp [Nat.cast_add, two_mul]
                _ = (A.card : Int) - (B.card : Int) := by
                        abel
  have hRareInt : (A.card : Int) - (B.card : Int) ≤ 0 := by
    exact sub_nonpos.mpr (Int.ofNat_le.mpr hAleB)
  dsimp [HornNF.rare]
  simpa [C, hndegAB] using hRareInt

lemma HornNF.PairTr_fixset_eq_empty_of_parallel
  (H : HornNF α) {u v : α} (hPar : H.IsParallelByClosure u v) :
  PairTr (α := α) v (H.FixSet) = ∅ := by
  classical
  rcases (HornNF.parallel_closure_iff_parallel_fixset (H := H) (u := u) (v := v)).1 hPar with
    ⟨huv_ne, _huU, _hvU, hiff⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro X hX
  rcases Finset.mem_filter.mp hX with ⟨hXfix, hXpair⟩
  rcases hXpair with ⟨hvNotX, hXuvFix⟩
  have huNotX : u ∉ X := by
    intro huX
    exact hvNotX ((hiff X hXfix).1 huX)
  have huInXuv : u ∈ X ∪ ({v} : Finset α) := by
    have hvInXuv : v ∈ X ∪ ({v} : Finset α) :=
      Finset.mem_union_right X (Finset.mem_singleton.mpr rfl)
    exact (hiff (X ∪ ({v} : Finset α)) hXuvFix).2 hvInXuv
  have huInX : u ∈ X := by
    rcases Finset.mem_union.mp huInXuv with huX | huV
    · exact huX
    · exfalso
      exact huv_ne (Finset.mem_singleton.mp huV)
  exact huNotX huInX

end Dr1nds
