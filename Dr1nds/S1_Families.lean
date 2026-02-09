import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import LeanCopilot

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/--
A plain finite family of subsets of U.
This does NOT require `U ∈ C` (needed for "holey families", deletions, forbids, ...).
-/
structure SetFamily (α : Type) [DecidableEq α] where
  U : Finset α
  C : Finset (Finset α)
  subset_univ : ∀ {X : Finset α}, X ∈ C → X ⊆ U

namespace SetFamily

@[simp] lemma subset_univ_of_mem (F : SetFamily α) {X : Finset α} (hX : X ∈ F.C) :
    X ⊆ F.U :=
  F.subset_univ hX

@[simp] lemma mem_imp_subset_univ (F : SetFamily α) {X : Finset α} :
    X ∈ F.C → X ⊆ F.U :=
  fun h => F.subset_univ h

end SetFamily


/--
A closure system on U (finite):
- contains U
- closed under binary intersection
(we keep it minimal; add `∅ ∈ C` later if you want)
-/
structure ClosureSystem (α : Type) [DecidableEq α] extends SetFamily α where
  top_mem : U ∈ C
  inter_mem : ∀ {X Y : Finset α}, X ∈ C → Y ∈ C → (X ∩ Y) ∈ C

namespace ClosureSystem

@[simp] lemma mem_top (CS : ClosureSystem α) : CS.U ∈ CS.C :=
  CS.top_mem

lemma mem_inter (CS : ClosureSystem α) {X Y : Finset α}
    (hX : X ∈ CS.C) (hY : Y ∈ CS.C) : (X ∩ Y) ∈ CS.C :=
  CS.inter_mem hX hY

@[simp] lemma subset_univ_of_mem (CS : ClosureSystem α) {X : Finset α} (hX : X ∈ CS.C) :
    X ⊆ CS.U :=
  CS.toSetFamily.subset_univ hX


/- ============================================================
  Iterated intersection (NO fold)
============================================================ -/

/--
iterated intersection (logical, NO fold):
`iterInter CS S` = { a ∈ U | ∀ X ∈ S, a ∈ X } as a finset.
-/
noncomputable def iterInter (CS : ClosureSystem α) (S : Finset (Finset α)) : Finset α :=
  CS.U.filter (fun a => ∀ X : Finset α, X ∈ S → a ∈ X)

@[simp] lemma mem_iterInter_iff (CS : ClosureSystem α) (S : Finset (Finset α)) (a : α) :
    a ∈ CS.iterInter S ↔ (a ∈ CS.U ∧ ∀ X : Finset α, X ∈ S → a ∈ X) := by
  classical
  simp [iterInter]


@[simp] lemma iterInter_subset_univ (CS : ClosureSystem α) (S : Finset (Finset α)) :
    CS.iterInter S ⊆ CS.U := by
  classical
  intro a ha
  exact (CS.mem_iterInter_iff S a).1 ha |>.1

/-- If `X ∈ S`, then `iterInter S ⊆ X`. -/
lemma iterInter_subset_of_mem
    (CS : ClosureSystem α) (S : Finset (Finset α)) {X : Finset α}
    (hX : X ∈ S) :
    CS.iterInter S ⊆ X := by
  classical
  intro a ha
  exact (CS.mem_iterInter_iff S a).1 ha |>.2 X hX

/-- Base case: `iterInter ∅ = U`. -/
@[simp] lemma iterInter_empty (CS : ClosureSystem α) :
    CS.iterInter (∅ : Finset (Finset α)) = CS.U := by
  classical
  ext a
  simp [iterInter]


/--
Insert step characterization:
`iterInter (insert X S) = X ∩ iterInter S`.
-/
lemma iterInter_insert (CS : ClosureSystem α) (S : Finset (Finset α)) (X : Finset α) :
    CS.iterInter (insert X S) = X ∩ CS.iterInter S := by
  classical
  ext a
  constructor
  · intro ha
    have haU : a ∈ CS.U := (CS.mem_iterInter_iff (insert X S) a).1 ha |>.1
    have hall : ∀ Y : Finset α, Y ∈ insert X S → a ∈ Y :=
      (CS.mem_iterInter_iff (insert X S) a).1 ha |>.2
    have haX : a ∈ X := hall X (by simp)
    have haIt : a ∈ CS.iterInter S := by
      -- show a∈U and ∀Y∈S, a∈Y
      apply (CS.mem_iterInter_iff S a).2
      refine ⟨haU, ?_⟩
      intro Y hY
      exact hall Y (by simp [hY])
    exact by
      simp [Finset.mem_inter, haX, haIt]
  · intro ha
    have haX : a ∈ X := by
      simp_all only [Finset.mem_inter, mem_iterInter_iff]

    have haIt : a ∈ CS.iterInter S := by
      simp_all only [Finset.mem_inter, mem_iterInter_iff, true_and, implies_true, and_self]
    have haU : a ∈ CS.U := (CS.mem_iterInter_iff S a).1 haIt |>.1
    have hallS : ∀ Y : Finset α, Y ∈ S → a ∈ Y :=
      (CS.mem_iterInter_iff S a).1 haIt |>.2
    -- now show a ∈ iterInter (insert X S)
    apply (CS.mem_iterInter_iff (insert X S) a).2
    refine ⟨haU, ?_⟩
    intro Y hY
    -- Y=X or Y∈S
    have : Y = X ∨ Y ∈ S := by
      simpa [Finset.mem_insert] using hY
    cases this with
    | inl hYX => simpa [hYX] using haX
    | inr hYS => exact hallS Y hYS

/-- `iterInter` is closed if all members of `S` are closed (uses Prop-induction only). -/
lemma iterInter_mem
    (CS : ClosureSystem α) (S : Finset (Finset α))
    (hS : ∀ {X : Finset α}, X ∈ S → X ∈ CS.C) :
    CS.iterInter S ∈ CS.C := by
  classical

  -- 強い主張で帰納して、最後に与えられた hS を流し込む
  have hStrong :
      (∀ {S : Finset (Finset α)},
          (∀ {X : Finset α}, X ∈ S → X ∈ CS.C) → CS.iterInter S ∈ CS.C) := by
    intro S
    -- Finset.induction_on を「関数を返す」形で使う
    exact
      Finset.induction_on S
        (motive := fun S =>
          (∀ {X : Finset α}, X ∈ S → X ∈ CS.C) → CS.iterInter S ∈ CS.C)
        (by
          intro _
          -- base: S = ∅
          -- iterInter ∅ = U
          simp_all only [iterInter_empty, mem_top]
        )
        (fun X S hXnot ih => by
          intro hXS
          -- hXS : ∀ {Y}, Y ∈ insert X S → Y ∈ CS.C

          have hXmem : X ∈ CS.C := by
            -- X ∈ insert X S は simp
            exact hXS (by simp)

          have hSmem : ∀ {Y : Finset α}, Y ∈ S → Y ∈ CS.C := by
            intro Y hY
            -- Y ∈ S ⇒ Y ∈ insert X S
            exact hXS (by simp [hY])

          have ih' : CS.iterInter S ∈ CS.C := by
            exact ih hSmem

          -- iterInter (insert X S) = X ∩ iterInter S
          -- intersection-closed で閉
          simpa [iterInter_insert] using CS.mem_inter hXmem ih'
        )

  -- 最後に元の hS を適用
  exact hStrong (S := S) hS

end ClosureSystem

/-- Singleton-Closed point (C-based): the singleton `{v}` belongs to the family `C`. -/
def SC (C : Finset (Finset α)) (v : α) : Prop :=
  ({v} : Finset α) ∈ C

/-- Unfolding lemma for `SC`. -/
@[simp] lemma SC_def (C : Finset (Finset α)) (v : α) :
  SC (α := α) C v ↔ (({v} : Finset α) ∈ C) := by
  rfl

/-- Convenience: if `{v} ∈ C` then `SC C v`. -/
lemma SC_of_mem {C : Finset (Finset α)} {v : α}
  (h : ({v} : Finset α) ∈ C) : SC (α := α) C v := by
  exact h

/-- Convenience: if `SC C v` then `{v} ∈ C`. -/
lemma mem_of_SC {C : Finset (Finset α)} {v : α}
  (h : SC (α := α) C v) : ({v} : Finset α) ∈ C := by
  exact h

@[simp] lemma mem_singleton_iff {v x : α} :
  x ∈ ({v} : Finset α) ↔ x = v := by
  simp

lemma SC_iff_singleton_mem (C : Finset (Finset α)) (v : α) :
  SC (α := α) C v ↔ (({v} : Finset α) ∈ C) := by
  rfl

end Dr1nds
