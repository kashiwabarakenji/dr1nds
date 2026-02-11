import Mathlib.Data.Finset.Basic
import Dr1nds.ClosureSystem.Basic
import LeanCopilot

namespace Dr1nds

variable {α : Type} [Fintype α] [DecidableEq α]

/--
有限個の集合の共通部分を取る反復演算。
空の場合は univ。
-/
noncomputable def iterInter
  (CS : ClosureSystem α) (S : Finset (Finset α)) : Finset α :=
  CS.U.filter (fun a => ∀ X ∈ S, a ∈ X)


@[simp] lemma iterInter_empty (CS : ClosureSystem α) :
  iterInter CS ∅ = CS.U := by
  dsimp [iterInter]
  simp_all only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true]


@[simp] lemma iterInter_insert
  (CS : ClosureSystem α) (X : Finset α) (S : Finset (Finset α)) :
  iterInter CS (insert X S) = X ∩ iterInter CS S := by
  classical
  ext a
  constructor
  · -- → direction
    intro ha
    have hU : a ∈ CS.U := by
      dsimp [iterInter] at ha
      exact Finset.mem_of_mem_filter a ha


    have hall :
        ∀ Y ∈ insert X S, a ∈ Y := by
      dsimp [iterInter] at ha
      intro Y a_1
      simp_all only [Finset.mem_insert, forall_eq_or_imp, Finset.mem_filter, true_and]
      obtain ⟨left, right⟩ := ha
      cases a_1 with
      | inl h =>
        subst h
        simp_all only
      | inr h_1 => simp_all only

    have hX : a ∈ X := hall X (by simp)
    have hS : a ∈ iterInter CS S := by
      refine ?_
      simp [iterInter, hU]
      intro Y hY
      exact hall Y (by simp [hY])

    simp [Finset.mem_inter, hX, hS]

  · -- ← direction
    intro ha
    rcases Finset.mem_inter.mp ha with ⟨hX, hIt⟩
    have hU : a ∈ CS.U := by
      dsimp [iterInter] at hIt
      exact Finset.mem_of_mem_filter a hIt

    refine ?_
    simp [iterInter, hU]
    constructor
    . simp_all only [Finset.mem_inter, and_self]
    · intro Y hY

      have : Y = X ∨ Y ∈ S := by
        simp_all only [Finset.mem_inter, and_self, or_true]
      cases this with
      | inl hYX =>
          simpa [hYX] using hX
      | inr hYS =>
          have : a ∈ iterInter CS S := hIt
          dsimp [iterInter] at this
          simp_all only [Finset.mem_inter, and_self, Finset.mem_filter, true_and]




/--
iterInter の値は ClosureSystem に属する。

※ 重要：
  - simp にしない
  - 明示的に使う補題
-/
lemma iterInter_mem
  (CS : ClosureSystem α)
  (S : Finset (Finset α))
  (hS : ∀ {X : Finset α}, X ∈ S → X ∈ CS.C) :
  iterInter CS S ∈ CS.C := by
  classical
  -- 強化した主張で帰納する
  refine
    Finset.induction_on S
      (motive := fun S =>
        (∀ {X : Finset α}, X ∈ S → X ∈ CS.C) →
        iterInter CS S ∈ CS.C)
      ?base
      ?step
      hS

  · -- base: S = ∅
    intro _
    simp [iterInter_empty]
    exact CS.top_mem

  · -- step: S = insert X SS
    intro X SS hXnot ih hSS

    -- X ∈ insert X SS
    have hXmem : X ∈ CS.C := by
      apply hSS
      simp

    -- SS ⊆ S なので制限した仮定を作る
    have hSS' : ∀ {Y : Finset α}, Y ∈ SS → Y ∈ CS.C := by
      intro Y hY
      apply hSS
      simp [hY]

    have ih' : iterInter CS SS ∈ CS.C :=
      ih hSS'

    -- 交わり閉性
    simpa [iterInter_insert] using CS.mem_inter hXmem ih'

end Dr1nds
