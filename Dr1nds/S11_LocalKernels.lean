-- Dr1nds/S11_LocalKernels.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S8_Statements
import Dr1nds.S9_IH_Unpack
import Dr1nds.S1_Families  -- SC はここに残す方針

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ============================================================
  S11 : Local kernels (SKELETON)
  目的：
    - S10 のステップで必要な「v の選択」「局所評価」を全部ここに集約
    - “どの理論核で v を選ぶか” は後で差し替え可能にする（API固定）
============================================================ -/

/- TODO:
  - This file is API-only.
  - Each axiom is intended to be discharged by specific later modules:
    * `exists_goodV_for_Q`, `ndeg_hole_le_zero_of_choice` via SC/rare selection kernels (S7+)
    * `Del_bound`, `Del_hole_bound` via Del-branch accounting bounds (S6 + local kernels)
    * `IH_Q_gives_con_bound` via S8.Q definition + IH unpack
-/

namespace Local

/--
Q_step で使う「良い v」のパッケージ。
最小限として `ndeg P.C v ≤ 0` だけを持つ（選び方は後で確定）。
-/
structure GoodV_for_Q (n : Nat) (P : HypPack (α := α)) where
  v : α
  hndeg : ndeg (α := α) P.C v ≤ 0

/-- Q_step で使う「良い v」：パッケージ版（推奨 API）
    `Nonempty` で返す。 -/
axiom exists_goodV_for_Q
  (n : Nat) (P : HypPack (α := α)) :
  Nonempty (GoodV_for_Q (α := α) n P)

/-- 互換 API：従来どおり `∃ v, ndeg ≤ 0` を返す。 -/
theorem exists_good_v_for_Q
  (n : Nat) (P : HypPack (α := α)) :
  ∃ v : α, ndeg (α := α) P.C v ≤ 0 := by
  classical
  let gv : GoodV_for_Q (α := α) n P := Classical.choice (exists_goodV_for_Q (α := α) n P)
  exact ⟨gv.v, gv.hndeg⟩

/-- Compatibility: turn `Nonempty (GoodV_for_Q n P)` into an existential witness. -/
theorem exists_goodV_for_Q_exists
  (n : Nat) (P : HypPack (α := α)) :
  ∃ gv : GoodV_for_Q (α := α) n P, True := by
  classical
  refine ⟨Classical.choice (exists_goodV_for_Q (α := α) n P), True.intro⟩

/-- Convenience: choose a good witness `gv : GoodV_for_Q n P` (data, not a Prop). -/
noncomputable def choose_goodV_for_Q
  (n : Nat) (P : HypPack (α := α)) : GoodV_for_Q (α := α) n P :=
  Classical.choice (exists_goodV_for_Q (α := α) n P)

@[simp] theorem goodV_ndeg
  {n : Nat} {P : HypPack (α := α)} (gv : GoodV_for_Q (α := α) n P) :
  ndeg (α := α) P.C gv.v ≤ 0 :=
  gv.hndeg

/-
Q_step の con-branch 用（最小口）：
IH: Q(n-1) P から、con 側の NDS ≤ 0 が取れる。

実体は `S9_IH_Unpack` に置いた IH-unpack（`IH.Q_con`）に委譲する。
-/
theorem IH_Q_gives_con_bound
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0 := by
  intro ih
  exact IH.Q_con (α := α) n P v ih

/--
Q_step の con-branch 用：
選んだ v に対し、HypPack を con 側へ押し出せる（台・条件を保つ）
（実装：ConHypPack のような構造を作るか、必要条件だけ返すかは後で確定）
-/
axiom con_pack_of_good_v
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  -- “con 側でも Q (n-1) を適用できる形” を返す
  -- ここは運用に合わせて差し替え可：いったん HypPack を返す
  HypPack (α := α)

/--
Q_step の Del-branch 用（最小口）：
IH とは独立に、Del 側の NDS ≤ 0 を出す局所核（S10 側でも placeholder を置いた）
-/
axiom Del_bound
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0


/- ------------------------------------------------------------
  forbid 側（Qcorr_step）で必要な v 選択と case 分岐
------------------------------------------------------------ -/

/--
forbid 付きステップで v を A から選ぶ核：
ForbidOK P A から v∈A を与える。
（ForbidOK が A.Nonempty を含むので、これは定理として出せる）
-/
theorem choose_v_in_A
  (P : HypPack (α := α)) (A : Finset α) :
  ForbidOK (α := α) P A →
  ∃ v : α, v ∈ A := by
  classical
  intro hOK
  have hne : A.Nonempty := ForbidOK.nonempty (P := P) (A := A) hOK
  exact hne

/--
Case 分岐核：
v∈A のとき (A.erase v = ∅) ∨ (A.erase v).Nonempty
（`by_cases` と `nonempty_iff_ne_empty` で定理として出せる）
-/
theorem erase_empty_or_nonempty
  (A : Finset α) (v : α) :
  v ∈ A →
  (A.erase v = ∅) ∨ (A.erase v).Nonempty := by
  classical
  intro _hv
  by_cases h : A.erase v = ∅
  · exact Or.inl h
  · exact Or.inr (Finset.nonempty_iff_ne_empty.2 h)

/--
forbid 側の局所 ndeg 評価核：
D := Hole(C,A) に対して、選んだ v の ndeg_D(v) ≤ 0 を出す。
（どの核で出すか：SC / rare / NoParallelStopSC などは S7/S12 で確定）
-/
axiom ndeg_hole_le_zero_of_choice
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A →
  v ∈ A →
  ndeg (α := α) (Hole (α := α) P.C A) v ≤ 0

/--
forbid 側の Del-branch 用：
D := Hole(C,A) に対して Del_v(D) の会計を閉じるための上界（≤0）。
（本体は S6 の CON_ID + S5 の forbid 互換の後、S7系ローカル核で埋める）
-/

axiom Del_hole_bound
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A →
  v ∈ A →
  NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A)) ≤ 0

/--
forbid 側 Case1（`A.erase v = ∅`）を一撃で閉じる核。

設計意図：
- `A.erase v = ∅` は通常 `A = {v}`（singleton forbid）を表す。
- この場合は「con 側に落として IH を当てる」ルートが破綻しやすいので、
  ローカル核として独立に閉じる API を用意する。
- 実装元は S7 系（SC/NoParallelStopSC など）に差し替え可能。
- S10 の `Qcorr_case1` から呼ばれる想定。
-/
axiom Qcorr_case1_singleton
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A →
  v ∈ A →
  A.erase v = ∅ →
  NDS_corr (α := α) n P.C A ≤ 0

end Local

end Dr1nds
