import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

import Dr1nds.Forbid.Basic
import Dr1nds.SetFamily.ConDelNdegId

namespace Dr1nds

variable {α : Type} [DecidableEq α]

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

end Dr1nds

