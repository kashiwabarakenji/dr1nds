import Mathlib.Data.Finset.Basic
import Dr1nds.ClosureSystem.Basic

namespace Dr1nds

variable {α : Type} [Fintype α] [DecidableEq α]

/--
有限個の集合の共通部分（Finset 版）。

定義は「CS.U の要素 a が、S のすべての集合 X に入っている」ことで与える。
空集合族のときは CS.U になる。
-/
noncomputable def iterInter
  (CS : ClosureSystem α) (S : Finset (Finset α)) : Finset α :=
  CS.U.filter (fun a => ∀ X ∈ S, a ∈ X)

@[simp] lemma iterInter_def
  (CS : ClosureSystem α) (S : Finset (Finset α)) :
  iterInter (α := α) CS S = CS.U.filter (fun a => ∀ X ∈ S, a ∈ X) := by
  rfl

@[simp] lemma mem_iterInter
  (CS : ClosureSystem α) (S : Finset (Finset α)) {a : α} :
  a ∈ iterInter (α := α) CS S ↔ (a ∈ CS.U ∧ ∀ X ∈ S, a ∈ X) := by
  simp [iterInter]

@[simp] lemma iterInter_empty (CS : ClosureSystem α) :
  iterInter (α := α) CS ∅ = CS.U := by
  classical
  ext a
  simp [iterInter]

@[simp] lemma iterInter_insert
  (CS : ClosureSystem α) (X : Finset α) (S : Finset (Finset α)) :
  iterInter (α := α) CS (insert X S) = X ∩ iterInter (α := α) CS S := by
  classical
  ext a
  constructor
  · intro ha
    have hU : a ∈ CS.U := (mem_iterInter (CS := CS) (S := insert X S)).1 ha |>.1
    have hall : ∀ Y ∈ insert X S, a ∈ Y := (mem_iterInter (CS := CS) (S := insert X S)).1 ha |>.2
    have hX : a ∈ X := hall X (by simp)
    have hIt : a ∈ iterInter (α := α) CS S := by
      -- show membership by unfolding iterInter
      have : (a ∈ CS.U ∧ ∀ Y ∈ S, a ∈ Y) := by
        refine And.intro hU ?_
        intro Y hY
        exact hall Y (by simp [hY])
      exact (mem_iterInter (CS := CS) (S := S)).2 this
    exact Finset.mem_inter.2 ⟨hX, hIt⟩
  · intro ha
    rcases Finset.mem_inter.1 ha with ⟨hX, hIt⟩
    have hU : a ∈ CS.U := (mem_iterInter (CS := CS) (S := S)).1 hIt |>.1
    have hallS : ∀ Y ∈ S, a ∈ Y := (mem_iterInter (CS := CS) (S := S)).1 hIt |>.2
    -- now prove membership in iterInter of insert
    refine (mem_iterInter (CS := CS) (S := insert X S)).2 ?_
    refine And.intro hU ?_
    intro Y hY
    have : Y = X ∨ Y ∈ S := by
      simpa [Finset.mem_insert] using hY
    cases this with
    | inl hYX => simpa [hYX] using hX
    | inr hYS => exact hallS Y hYS

/--
`iterInter CS S` は `CS.C` に属する（有限交差で閉じている）。

`Finset.fold` を使わず、`Finset.induction_on` による帰納で示す。
-/
lemma iterInter_mem
  (CS : ClosureSystem α)
  (S : Finset (Finset α))
  (hS : ∀ {X : Finset α}, X ∈ S → X ∈ CS.C) :
  iterInter (α := α) CS S ∈ CS.C := by
  classical
  -- 帰納
  refine Finset.induction_on S (motive := fun S =>
    (∀ {X : Finset α}, X ∈ S → X ∈ CS.C) → iterInter (α := α) CS S ∈ CS.C) ?base ?step hS
  · intro _
    simpa using CS.top_mem
  · intro X S hXnot ih hXS
    have hXmem : X ∈ CS.C := hXS (by simp)
    have hSmem : iterInter (α := α) CS S ∈ CS.C := by
      apply ih
      intro Y hY
      apply hXS
      simp [hY]
    -- insert case reduces to intersection
    let csm := CS.mem_inter hXmem hSmem
    simp
    dsimp [iterInter] at csm
    dsimp [iterInter] at hSmem
    convert csm using 1
    ext x
    simp
    tauto

end Dr1nds
