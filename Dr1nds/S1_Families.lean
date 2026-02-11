import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanCopilot

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/-!
S1_Families.lean

目的（凍結）：
- 有限集合族 C : Finset (Finset α) を「会計の母体」として扱うための
  最小限の定義・補題を与える。
- Horn / forbid / con / trace には立ち入らない。
- 交わり・最小閉集合は **論理的定義のみ** を使う。
- 以後の S2–S11 は、このファイルの定義を前提に構成される。
-/

/- ============================================================
  1. 基本：集合族と台
============================================================ -/

/--
有限集合族 C と、その台集合 U。
※ U ∈ C を仮定しない（Hole / Del 用）。
-/
structure SetFamily (α : Type) [DecidableEq α] where
  U : Finset α
  C : Finset (Finset α)
  subset_univ : ∀ {X : Finset α}, X ∈ C → X ⊆ U

namespace SetFamily

@[simp] lemma subset_univ_of_mem
  (F : SetFamily α) {X : Finset α} (hX : X ∈ F.C) : X ⊆ F.U :=
F.subset_univ hX

end SetFamily


/- ============================================================
  2. 閉集合族（Closure System）
============================================================ -/

/-
閉集合族（closure system）の最小定義：
- 台 U を含む
- ∩ に閉じている
-/
--削る予定。ClosureSystemにすでに定義がある。
/-
structure ClosureSystem (α : Type) [DecidableEq α]
  extends SetFamily α where
  top_mem : U ∈ C
  inter_mem :
    ∀ {X Y : Finset α}, X ∈ C → Y ∈ C → (X ∩ Y) ∈ C

namespace ClosureSystem

@[simp] lemma mem_top (CS : ClosureSystem α) : CS.U ∈ CS.C :=
CS.top_mem

lemma mem_inter
  (CS : ClosureSystem α) {X Y : Finset α}
  (hX : X ∈ CS.C) (hY : Y ∈ CS.C) :
  (X ∩ Y) ∈ CS.C :=
CS.inter_mem hX hY

@[simp] lemma subset_univ_of_mem
  (CS : ClosureSystem α) {X : Finset α} (hX : X ∈ CS.C) :
  X ⊆ CS.U :=
CS.toSetFamily.subset_univ hX

end ClosureSystem


/- ============================================================
  3. 論理的交わり（fold 不使用）
============================================================ -/

/--
論理的交わり（fold 不使用）：
  iterInter CS S
= { a ∈ U | ∀ X∈S, a∈X }
-/
noncomputable def iterInter
  (CS : ClosureSystem α) (S : Finset (Finset α)) : Finset α :=
CS.U.filter (fun a => ∀ X ∈ S, a ∈ X)

@[simp] lemma mem_iterInter_iff
  (CS : ClosureSystem α) (S : Finset (Finset α)) (a : α) :
  a ∈ iterInter CS S ↔
    (a ∈ CS.U ∧ ∀ X ∈ S, a ∈ X) := by
  classical
  simp [iterInter]

@[simp] lemma iterInter_empty
  (CS : ClosureSystem α) :
  iterInter CS (∅ : Finset (Finset α)) = CS.U := by
  classical
  ext a
  simp [iterInter]

/--
挿入ステップ：
  iterInter (insert X S) = X ∩ iterInter S
-/
lemma iterInter_insert
  (CS : ClosureSystem α)
  (S : Finset (Finset α)) (X : Finset α) :
  iterInter CS (insert X S) = X ∩ iterInter CS S := by
  classical
  ext a
  constructor
  · intro ha
    have h := (mem_iterInter_iff CS (insert X S) a).1 ha
    refine Finset.mem_inter.mpr ?_
    constructor
    · exact h.2 X (by simp)
    · refine (mem_iterInter_iff CS S a).2 ?_
      refine ⟨h.1, ?_⟩
      intro Y hY
      exact h.2 Y (by simp [hY])
  · intro ha
    have hX : a ∈ X := (Finset.mem_inter.mp ha).1
    have hI : a ∈ iterInter CS S := (Finset.mem_inter.mp ha).2
    have hIU := (mem_iterInter_iff CS S a).1 hI
    refine (mem_iterInter_iff CS (insert X S) a).2 ?_
    refine ⟨hIU.1, ?_⟩
    intro Y hY
    have : Y = X ∨ Y ∈ S := by
      simpa [Finset.mem_insert] using hY
    cases this with
    | inl hYX => simpa [hYX] using hX
    | inr hYS => exact hIU.2 Y hYS

/--
S の全要素が閉なら、iterInter S も閉。
（fold を使わない Finset.induction）
-/
lemma iterInter_mem
  (CS : ClosureSystem α)
  (S : Finset (Finset α))
  (hS : ∀ {X : Finset α}, X ∈ S → X ∈ CS.C) :
  iterInter CS S ∈ CS.C := by
  classical
  -- S に依存する強い主張で帰納
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
    simp [iterInter_empty, CS.mem_top]
  · -- step: S = insert X SS
    intro X SS hXnot ih hXS
    -- X ∈ CS.C
    have hXmem : X ∈ CS.C := by
      apply hXS
      simp
    -- SS ⊆ CS.C
    have hSSmem : ∀ {Y : Finset α}, Y ∈ SS → Y ∈ CS.C := by
      intro Y hY
      apply hXS
      simp [hY]
    -- 帰納法の仮定を適用
    have ih' : iterInter CS SS ∈ CS.C :=
      ih hSSmem
    -- insert の場合の計算
    simpa [iterInter_insert] using CS.mem_inter hXmem ih'
-/
/- ============================================================
  4. SC（singleton-closed）
============================================================ -/

/--
SC(x) :⇔ {x} ∈ C
-/
def SC (C : Finset (Finset α)) (x : α) : Prop :=
  ({x} : Finset α) ∈ C

omit [DecidableEq α] in
@[simp] lemma SC_iff
  (C : Finset (Finset α)) (x : α) :
  SC C x ↔ ({x} : Finset α) ∈ C := by
  rfl

end Dr1nds
