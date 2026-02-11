-- Dr1nds/S8_Statements.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S2_HornNF
import Dr1nds.S4_FixFamily
import Dr1nds.S6_ConDelNdegId
import Dr1nds.S7_SC_Local  -- SC など（必要なら）

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

/- ============================================================
  S8 : Statements / API (SKELETON, FROZEN)
  - HypPack: closed-family enumeration + HornNF hypotheses
  - Goals: Q / Qcorr
  - IH: mutual induction interfaces
  - Step: main step interfaces (proof later)
============================================================ -/

/- ------------------------------------------------------------
  0. Hypothesis pack (finite enumeration of FixSet)
------------------------------------------------------------ -/

/--
HypPack = ClosedPack + HornNF hypotheses on U.

- `ClosedPack` は S4_FixFamily にある：
    U : Finset α
    H : HornNF α
    C : Finset (Finset α)
    mem_iff : X ∈ C ↔ (X ⊆ U ∧ X ∈ H.FixSet U)   （※あなたの現行定義に合わせて）
-/
structure HypPack (α : Type) [DecidableEq α] extends ClosedPack (α := α) where
  hornOn : HornNF.HornOn (α := α) H U
  dr1    : HornNF.IsDR1  (α := α) H
  nep    : HornNF.IsNEP  (α := α) H
  nf     : HornNF.IsNF   (α := α) H

namespace HypPack
variable (P : HypPack α)

@[simp] lemma hornOn' : HornNF.HornOn (α := α) P.H P.U := P.hornOn
@[simp] lemma dr1'    : HornNF.IsDR1  (α := α) P.H := P.dr1
@[simp] lemma nep'    : HornNF.IsNEP  (α := α) P.H := P.nep
@[simp] lemma nf'     : HornNF.IsNF   (α := α) P.H := P.nf

-- 便利：P.C の membership spec をそのまま取り出す
@[simp] theorem mem_iff' (X : Finset α) :
    X ∈ P.C ↔ X ⊆ P.U ∧ X ∈ (HornNF.FixSet (α := α) P.H P.U) := by
  simpa [HornNF.FixSet] using (P.mem_iff X)

end HypPack


/- ------------------------------------------------------------
  1. Goal predicates: Q / Qcorr
------------------------------------------------------------ -/

/--
Q(n,P): 通常会計の目標。
（P は有限列挙された閉集合族）
-/
def Q (n : Nat) (P : HypPack α) : Prop :=
  NDS (α := α) n P.C ≤ 0

/--
Qcorr(n,P,A): forbid 付き会計の目標。

注意：
- forbid A は「Hole(P.C,A)」という像（穴あき族）として扱う方針。
- A は *閉集合* として扱う（このプロジェクトのテンプレに合わせる）。
- 実運用では |A|≥2 を想定することが多いが、ここでは条件として引数で管理する。
-/
def Qcorr (n : Nat) (P : HypPack α) (A : Finset α) : Prop :=
  NDS_corr (α := α) n P.C A ≤ 0

/-
------------------------------------------------------------
  2. Accounting identities exposed at the API level
------------------------------------------------------------ -/

/--
通常会計（CON_ID）を「pack 上の形」で使えるように露出する。
S6_ConDelNdegId の `CON_ID` を呼ぶときのブリッジ。
-/
axiom CON_ID_pack
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack α) (v : α) :
  NDS (α := α) n P.C
    =
  NDS (α := α) (n - 1) (con (α := α) v P.C)
    +
  NDS (α := α) (n - 1) (Del (α := α) v P.C)
    +
  ndeg (α := α) P.C v

/--
forbid 付き会計（CON_ID_corr）の最終形を pack 上で露出する。
実体の証明は S5_Forbid_Compat / S5_ForbidConLemmas 側で行う。
-/
axiom CON_ID_corr_pack
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack α) (A : Finset α) (v : α) :
  NDS_corr (α := α) n P.C A
    =
  NDS_corr (α := α) (n - 1) (con (α := α) v P.C) (A.erase v)
    +
  (NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A))
      + ndeg (α := α) (Hole (α := α) P.C A) v)

/- ------------------------------------------------------------
  3. Mutual IH interfaces (axioms for now)
------------------------------------------------------------ -/
/- ------------------------------------------------------------
  1. forbid 側の前提（A に課す条件）を固定
------------------------------------------------------------ -/

/--
ForbidOK(P,A):
- A ⊆ U
- A は非空
- （用途では |A|≥2 を要求することが多いのでここで固定しておく）
-/
def ForbidOK (P : HypPack α) (A : Finset α) : Prop :=
  A ⊆ P.U ∧ A.Nonempty ∧ (2 ≤ A.card)

namespace ForbidOK

@[simp] lemma subset_univ {P : HypPack α} {A : Finset α} :
    ForbidOK (α := α) P A → A ⊆ P.U := by
  intro h; exact h.1

@[simp] lemma nonempty {P : HypPack α} {A : Finset α} :
    ForbidOK (α := α) P A → A.Nonempty := by
  intro h; exact h.2.1

@[simp] lemma card_ge_two {P : HypPack α} {A : Finset α} :
    ForbidOK (α := α) P A → 2 ≤ A.card := by
  intro h; exact h.2.2

end ForbidOK

/--
Bundled induction hypothesis at level `n`.

`IH n P` contains:
- the usual goal `Q n P`, and
- all forbid goals `Qcorr n P A` for admissible `A` (w.r.t. `ForbidOK`).

This is the Lean-friendly interface recommended for later S9/S11 re-wiring.
-/
def IH (n : Nat) (P : HypPack α) : Prop :=
  Q (α := α) n P ∧ (∀ A : Finset α, ForbidOK (α := α) P A → Qcorr (α := α) n P A)

/-- Bundled IH provided by the global induction skeleton (axiom for now). -/
axiom IH_pack
  (n : Nat) (P : HypPack α) :
  IH (α := α) (n - 1) P

/-- Projection: IH gives the usual goal at level `n-1`. -/
theorem IH_Q
  (n : Nat) (P : HypPack α) :
  Q (α := α) (n - 1) P :=
  (IH_pack (α := α) n P).1

/-- Projection: IH gives the forbid goals at level `n-1`. -/
theorem IH_Qcorr
  (n : Nat) (P : HypPack α) (A : Finset α) :
  ForbidOK (α := α) P A →
  Qcorr (α := α) (n - 1) P A :=
by
  intro hOK
  exact (IH_pack (α := α) n P).2 A hOK



/--
B2（A.erase v 非空）の Case2 用にあなたが欲しがっていた IH 形。

※これは「con を取った世界」に落として IH を当てるタイプ。
※ここでも A の良さ条件をまとめて受けるようにしておくと後で楽。
-/
axiom IH_corr_con_pack
  (n : Nat)
  (P : HypPack α)
  (A : Finset α)
  (v : α) :
  Q (α := α) (n - 1) P →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1)
    (con (α := α) v P.C)
    (A.erase v) ≤ 0

/--
Preferred IH-based interface for the con-branch in forbid case2.
This matches the bundled IH design.
-/
axiom IH_corr_con_pack_IH
  (n : Nat)
  (P : HypPack α)
  (A : Finset α)
  (v : α) :
  IH (α := α) (n - 1) P →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1)
    (con (α := α) v P.C)
    (A.erase v) ≤ 0

/-- Wrapper: the IH-based interface implies the legacy one by projecting `Q (n-1) P`. -/
lemma IH_corr_con_pack_of_IH
  (n : Nat)
  (P : HypPack α)
  (A : Finset α)
  (v : α) :
  IH (α := α) (n - 1) P →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1)
    (con (α := α) v P.C)
    (A.erase v) ≤ 0 := by
  intro hIH hvA hNE
  exact IH_corr_con_pack_IH (α := α) n P A v hIH hvA hNE


/- ------------------------------------------------------------
  4. Step interfaces (proof skeleton only)
------------------------------------------------------------ -/

/--
Q_step で使う「良い v」の最小 API。
現状は会計側（CON_ID）に直接刺さる形として
  ndeg(P.C,v) ≤ 0
だけを要求する。
（将来、SC / NoParallel / rare などで `∃ v` を構成する。）
-/
def GoodV_for_Q (P : HypPack α) (v : α) : Prop :=
  ndeg (α := α) P.C v ≤ 0

/--
通常ステップ：
`∃ v, GoodV_for_Q P v` が与えられれば Q(n,P) を閉じる、という形に固定。
-/
axiom Q_step
  (n : Nat) (P : HypPack α) :
  (∃ v : α, GoodV_for_Q (α := α) P v) →
  Q (α := α) n P

/-- 互換：従来形 `∃ v, ndeg ≤ 0` から `∃ v, GoodV_for_Q` へ。 -/
lemma exists_goodV_for_Q_of_exists_ndeg
  (P : HypPack α) :
  (∃ v : α, ndeg (α := α) P.C v ≤ 0) →
  (∃ v : α, GoodV_for_Q (α := α) P v) := by
  intro h
  simpa [GoodV_for_Q] using h

/--
forbid ステップ（例）：
GoodA2 の A に対し、ある v∈A を選んで CON_ID_corr を使い Qcorr(n) を閉じる。
-/
axiom Qcorr_step
  (n : Nat) (P : HypPack α) (A : Finset α) :
  ForbidOK (α := α) P A →
  Qcorr (α := α) n P A


/- ------------------------------------------------------------
  5. Optional: SC predicate reference point
------------------------------------------------------------ -/

-- SC は S1_Families の定義を使う、という現方針ならここは触れない。
-- もし “P.C 上の SC” を使うなら、補題は S7_SC_Local 側に置くのを推奨。



end Dr1nds
