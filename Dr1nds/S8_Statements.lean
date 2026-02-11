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

  目的：
  - HypPack : 「有限列挙された閉集合族」+ HornNF 仮定
  - 目標命題 : Q / Qcorr
  - 帰納IH  : bundled 形（Lean で扱いやすい）
  - Step    : Q_step / Qcorr_step（中身は S10/S11 側）

  方針：
  - “定義・言明の接続層”として、ここは基本 API を固定する。
  - 証明の中身（選点・局所評価・del 上界など）は S10/S11 に寄せる。
============================================================ -/

/- ------------------------------------------------------------
  0. Hypothesis pack (finite enumeration of FixSet)
------------------------------------------------------------ -/

/--
HypPack = ClosedPack + HornNF hypotheses on U.

`ClosedPack` は S4_FixFamily にある：
  U : Finset α
  H : HornNF α
  C : Finset (Finset α)
  mem_iff : X ∈ C ↔ (X ⊆ U ∧ X ∈ H.FixSet U)
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

/-- Convenience: membership spec for `P.C`. -/
@[simp] theorem mem_iff' (X : Finset α) :
    X ∈ P.C ↔ X ⊆ P.U ∧ X ∈ (HornNF.FixSet (α := α) P.H P.U) := by
  simpa [HornNF.FixSet] using (P.mem_iff X)

end HypPack


/- ------------------------------------------------------------
  1. Goal predicates: Q / Qcorr
------------------------------------------------------------ -/

/-- Q(n,P): 通常会計の目標。 -/
def Q (n : Nat) (P : HypPack α) : Prop :=
  NDS (α := α) n P.C ≤ 0

/-- Qcorr(n,P,A): forbid 付き会計の目標（forbid は Hole(P.C,A) を像として扱う）。 -/
def Qcorr (n : Nat) (P : HypPack α) (A : Finset α) : Prop :=
  NDS_corr (α := α) n P.C A ≤ 0


/- ------------------------------------------------------------
  2. Forbid-side admissibility predicate (A に課す条件)
------------------------------------------------------------ -/

/--
ForbidOK(P,A):
- A ⊆ U
- A.Nonempty
- 2 ≤ A.card

（A を「閉集合である」とする条件は、現行設計では必須にしていない。
  必要になったら別名で追加し、S10/S11 側で使う。）
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


/- ------------------------------------------------------------
  3. Accounting identities exposed at the API level
------------------------------------------------------------ -/

/--
通常会計（CON_ID）を pack 上で使える形に露出する。
（S6_ConDelNdegId の CON_ID を呼ぶためのブリッジ）
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
（実体の証明は S5_Forbid_Compat / S5_ForbidConLemmas 側で行う。）
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
  4. Bundled IH interfaces (recommended)
------------------------------------------------------------ -/

/--
Bundled induction hypothesis at level `n`.

`IH n P` contains:
- the usual goal `Q n P`, and
- all forbid goals `Qcorr n P A` for admissible `A`.
-/
def IH (n : Nat) (P : HypPack α) : Prop :=
  Q (α := α) n P ∧ (∀ A : Finset α, ForbidOK (α := α) P A → Qcorr (α := α) n P A)

/-- Bundled IH provided by the global induction skeleton (axiom for now). -/
axiom IH_pack
  (n : Nat) (P : HypPack α) :
  IH (α := α) (n - 1) P

/-- Projection: IH gives the usual goal at level `n-1`. -/
theorem IH_Q (n : Nat) (P : HypPack α) :
  Q (α := α) (n - 1) P :=
  (IH_pack (α := α) n P).1

/-- Projection: IH gives the forbid goals at level `n-1`. -/
theorem IH_Qcorr (n : Nat) (P : HypPack α) (A : Finset α) :
  ForbidOK (α := α) P A →
  Qcorr (α := α) (n - 1) P A := by
  intro hOK
  exact (IH_pack (α := α) n P).2 A hOK


/--
B2（A.erase v 非空）の forbid Case2 用：IH（bundled）から con-branch の上界を引き出す API。

（ここは “unary head 問題” や “選点戦略” の影響を受けやすいので、当面 axiom にしておく。）
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

/-- Wrapper: legacy-style interface (only assumes `Q (n-1) P`). -/
lemma IH_corr_con_pack
  (n : Nat)
  (P : HypPack α)
  (A : Finset α)
  (v : α) :
  Q (α := α) (n - 1) P →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1)
    (con (α := α) v P.C)
    (A.erase v) ≤ 0 := by
  intro hQ hvA hNE
  have hIH : IH (α := α) (n - 1) P := by
    refine ⟨hQ, ?_⟩
    intro A' hOK
    -- forbid 側の IH は bundled から引くのが基本設計。
    -- ここは S9 の skeleton（IH_pack）に寄せるため、いったん IH_Qcorr を経由する。
    exact IH_Qcorr (α := α) n P A' hOK
  exact IH_corr_con_pack_IH (α := α) n P A v hIH hvA hNE


/- ------------------------------------------------------------
  5. Step interfaces (proof skeleton only)
------------------------------------------------------------ -/

/-- Q_step で使う「良い v」：最小 API（ndeg ≤ 0）。 -/
def GoodV_for_Q (P : HypPack α) (v : α) : Prop :=
  ndeg (α := α) P.C v ≤ 0

/--
通常ステップ：`∃ v, GoodV_for_Q P v` が与えられれば `Q n P` を閉じる。
（選点は S11 側で作り、ここは受け口だけを固定する。）
-/
axiom Q_step
  (n : Nat) (P : HypPack α) :
  (∃ v : α, GoodV_for_Q (α := α) P v) →
  Q (α := α) n P

/-- 互換：`∃ v, ndeg ≤ 0` から `∃ v, GoodV_for_Q` へ。 -/
lemma exists_goodV_for_Q_of_exists_ndeg (P : HypPack α) :
  (∃ v : α, ndeg (α := α) P.C v ≤ 0) →
  (∃ v : α, GoodV_for_Q (α := α) P v) := by
  intro h
  simpa [GoodV_for_Q] using h

/--
forbid ステップ：ForbidOK(P,A) の下で `Qcorr n P A` を閉じる。
（実体は S10/S11 で組む。）
-/
axiom Qcorr_step
  (n : Nat) (P : HypPack α) (A : Finset α) :
  ForbidOK (α := α) P A →
  Qcorr (α := α) n P A


/- ------------------------------------------------------------
  6. Notes
------------------------------------------------------------ -/

-- SC は S1_Families の定義を使う方針なら、ここで再定義しない。
-- “P.C 上の SC” の補題は S7_SC_Local 側に置く。

end Dr1nds
