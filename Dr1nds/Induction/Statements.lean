import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornClosure
import Dr1nds.Forbid.HornWithForbid
import Dr1nds.SetFamily.CoreDefs
import Mathlib.Tactic


set_option autoImplicit false

/-
============================================================
  Induction Statements (FREEZE SPEC)
  目的：
    - 帰納法で運ぶ命題 Q / Qcorr の「型」と「入出力」を凍結する
    - 証明は S10(wiring) と S11(local kernels) へ分離
  方針：
    - ここでは数学的中身を一切書かない（すべて Prop の仕様として固定）
    - forbid あり/なしを混ぜない
    - |A|=1 も許す（ただし次のステップの取り扱いは別分岐にする）
============================================================
-/

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ------------------------------------------------------------
  0. パック型（必要最小限）
  ここは後で自由に変えてよい。
  「何を帰納法の入力に取るか」を固定する役目だけ。
------------------------------------------------------------ -/

-- forbid なし世界：DR1(+NEP+NF) HornNF と、その閉集合族 C = FixSet
structure Pack0 (α : Type) [DecidableEq α] where
  H : _root_.Dr1nds.HornNF α
  hDR1 : H.IsDR1
  hNEP : H.IsNEP
  -- hNF  : H.IsNF

/- ------------------------------------------------------------
  1'. 帰納法で運ぶ命題 Q / Qcorr（定義固定）

  方針（親スレ合意）：
  - Q / Qcorr は「評価命題」そのものに固定する。
  - これにより |A|=1 分岐のような “等式で評価を落として IH を当てる” 型のステップが
    そのまま Lean で閉じられる。
------------------------------------------------------------ -/

-- forbid なし世界（Pack0）での主命題：`NDS ≤ 0`。
def Q (n : Nat) (P : Pack0 α) : Prop :=
  P.H.U.card = n → NDS n P.H.FixSet ≤ 0

-- forbid あり世界（Pack1）での主命題：`NDS_corr ≤ 0`。
-- 注意：forbid は常に `Pack1.A = closure(Araw)` を用いる。

def Qcorr (n : Nat) (F : HornWithForbid α) : Prop :=
  F.H.U.card = n → NDS_corr n F.H.FixSet F.F ≤ 0

/-
Set-family level NEP: the family contains the empty set.

We keep NEP at the *family* level so it can be shared across the Horn/ClosureSystem/WithForbid worlds.
In this project we will apply it primarily to the *base* family `Pack*.C` (not Hole-filtered families),
so it does not conflict with the “no double Hole” convention for `NDS_corr`.
-/
-- def NEP (C : Finset (Finset α)) : Prop :=
--   (∅ : Finset α) ∈ C

/- ------------------------------------------------------------
  3. Base case（独立核として凍結）
  ここは後で埋める。
------------------------------------------------------------ -/

lemma fixset_eq_pair_empty_U_of_card_one
  (H : HornNF α) (hNEP : H.IsNEP) (hcardU : H.U.card = 1) :
  H.FixSet = ({(∅ : Finset α), H.U} : Finset (Finset α)) := by
  classical
  have hempty : (∅ : Finset α) ∈ H.FixSet :=
    HornNF.empty_mem_FixSet_of_isNEP (H := H) hNEP
  have hUmem : H.U ∈ H.FixSet := by
    refine (mem_FixSet_iff (H := H) (X := H.U)).2 ?_
    refine ⟨?_, subset_rfl⟩
    intro h P hP hsub
    exact H.head_mem_U ⟨P, hP⟩
  apply Finset.ext
  intro X
  constructor
  · intro hX
    by_cases hX0 : X = ∅
    · simp [hX0]
    · have hXsubU : X ⊆ H.U := mem_FixSet_subset_U (H := H) hX
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcardU
      have hXsub : X ⊆ ({u} : Finset α) := by simpa [hu] using hXsubU
      have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX0
      rcases hXne with ⟨x, hxX⟩
      have hxu : x = u := by
        have hxS : x ∈ ({u} : Finset α) := hXsub hxX
        simpa using hxS
      have huX : u ∈ X := by simpa [← hxu] using hxX
      have hXeq : X = ({u} : Finset α) := by
        apply Finset.Subset.antisymm
        · exact hXsub
        · intro y hy
          have hyu : y = u := by simpa using hy
          simpa [hyu] using huX
      simp [hu, hXeq]
  · intro hX
    rcases Finset.mem_insert.1 hX with hX0 | hXU
    · simpa [hX0] using hempty
    · rcases Finset.mem_singleton.1 hXU with hXU'
      simpa [hXU'] using hUmem

lemma forbid_eq_U_of_card_one
  (F : HornWithForbid α) (hcardU : F.H.U.card = 1) :
  F.F = F.H.U := by
  classical
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcardU
  have hFsub : F.F ⊆ ({u} : Finset α) := by
    simpa [hu] using F.F_subset_U
  rcases F.F_nonempty with ⟨x, hxF⟩
  have hxu : x = u := by
    have hxS : x ∈ ({u} : Finset α) := hFsub hxF
    simpa using hxS
  have huF : u ∈ F.F := by simpa [← hxu] using hxF
  have hFeq : F.F = ({u} : Finset α) := by
    apply Finset.Subset.antisymm
    · exact hFsub
    · intro y hy
      have hyu : y = u := by simpa using hy
      simpa [hyu] using huF
  simpa [hu] using hFeq

theorem Q_base (P : Pack0 α) : Q 1 P := by
  intro hcardU
  have hFix :
      P.H.FixSet = ({(∅ : Finset α), P.H.U} : Finset (Finset α)) :=
    fixset_eq_pair_empty_U_of_card_one (H := P.H) (hNEP := P.hNEP) (hcardU := hcardU)
  have hNDS0 : NDS 1 P.H.FixSet = 0 := by
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcardU
    calc
      NDS 1 P.H.FixSet = NDS 1 ({(∅ : Finset α), P.H.U} : Finset (Finset α)) := by simp [hFix]
      _ = 0 := by simp [NDS, w, hu]
  simp [hNDS0]

theorem Qcorr_base (F : HornWithForbid α) : Qcorr 1 F := by
  intro hcardU
  have hFix :
      F.H.FixSet = ({(∅ : Finset α), F.H.U} : Finset (Finset α)) :=
    fixset_eq_pair_empty_U_of_card_one (H := F.H) (hNEP := F.hNEP) (hcardU := hcardU)
  have hFU : F.F = F.H.U := forbid_eq_U_of_card_one (F := F) (hcardU := hcardU)
  have hCorr0 : NDS_corr 1 F.H.FixSet F.F = 0 := by
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcardU
    have hHole :
        Hole (α := α) ({(∅ : Finset α), ({u} : Finset α)} : Finset (Finset α)) ({u} : Finset α)
          =
        ({(∅ : Finset α)} : Finset (Finset α)) := by
      ext X
      constructor
      · intro hX
        rcases Finset.mem_filter.1 hX with ⟨hXin, hnot⟩
        rcases Finset.mem_insert.1 hXin with hX0 | hX1
        · exact Finset.mem_singleton.2 hX0
        · exfalso
          apply hnot
          intro y hy
          have hXe : X = ({u} : Finset α) := Finset.mem_singleton.1 hX1
          have hyu : y = u := Finset.mem_singleton.1 hy
          simp [hXe, hyu]
      · intro hX
        have hX0 : X = ∅ := Finset.mem_singleton.1 hX
        refine Finset.mem_filter.2 ?_
        refine ⟨?_, ?_⟩
        · exact Finset.mem_insert.2 (Or.inl hX0)
        · intro hsub
          have hu_single : u ∈ ({u} : Finset α) := by simp
          have : u ∈ (∅ : Finset α) := by simpa [hX0] using hsub hu_single
          simpa using this
    have hUp :
        Up (α := α) ({(∅ : Finset α), ({u} : Finset α)} : Finset (Finset α)) ({u} : Finset α)
          =
        ({({u} : Finset α)} : Finset (Finset α)) := by
      ext X
      constructor
      · intro hX
        rcases Finset.mem_filter.1 hX with ⟨hXin, hsub⟩
        rcases Finset.mem_insert.1 hXin with hX0 | hX1
        · exfalso
          have hu_single : u ∈ ({u} : Finset α) := by simp
          have : u ∈ (∅ : Finset α) := by simpa [hX0] using hsub hu_single
          simpa using this
        · exact Finset.mem_singleton.2 (Finset.mem_singleton.1 hX1)
      · intro hX
        have hXu : X = ({u} : Finset α) := Finset.mem_singleton.1 hX
        refine Finset.mem_filter.2 ?_
        refine ⟨?_, ?_⟩
        · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 hXu))
        · intro y hy
          simpa [hXu] using hy
    calc
      NDS_corr 1 F.H.FixSet F.F = NDS_corr 1 ({(∅ : Finset α), F.H.U} : Finset (Finset α)) F.H.U := by
        simp [hFix, hFU]
      _ = 0 := by
        rw [hu]
        simp [NDS_corr, NDS, w, hHole, hUp]
  simp [hCorr0]

end Dr1nds
