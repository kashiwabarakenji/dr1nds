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

  /- ROADMAP (how axioms will be discharged) -/
  - S8 は API 層のみを担い、ここで宣言する axiom は下流の特定ファイルで証明・実装される予定。
  - CON_ID_pack は S6_ConDelNdegId で証明される。
  - CON_ID_corr_pack は S5_Forbid_Compat および S5_ForbidConLemmas で扱う。
  - Q_step, Qcorr_step などの選点・局所評価に関わる axiom は S10/S11 で構成される。
  - IH_pack はグローバル帰納法の仮置きであり、最終的には S11/S12（または適切な集約ファイル）での最終定理証明により削除される。

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
  dr1    : HornNF.IsDR1  (α := α) H
  nep    : HornNF.IsNEP  (α := α) H
  nf     : HornNF.IsNF   (α := α) H

namespace HypPack

variable (P : HypPack α)

@[simp] lemma dr1'    : HornNF.IsDR1  (α := α) P.H := P.dr1
@[simp] lemma nep'    : HornNF.IsNEP  (α := α) P.H := P.nep
@[simp] lemma nf'     : HornNF.IsNF   (α := α) P.H := P.nf

/-- Convenience: membership spec for `P.C`. -/
@[simp] theorem mem_iff' (X : Finset α) :
    X ∈ P.C ↔ X ∈ HornNF.FixSet (α := α) P.H := by
  simp_all only [ClosedPack.mem_iff']

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
Forbid 側で許す forbid 集合 `A` の条件。

**凍結（重要）**：S10 側の分岐設計に合わせ、`singleton` を射程外に出すため
`2 ≤ A.card` を採用する。

- `A.Nonempty` は `2 ≤ A.card` から従うので入れない（冗長・simp 事故源）。
- `A ⊆ P.H.U` は台集合整合のため必須。
- `A.erase v` の非空性などは、必要な箇所で補題として引き出す。
-/
def ForbidOK (P : HypPack α) (A : Finset α) : Prop :=
  A ⊆ P.H.U ∧ (2 ≤ A.card)

namespace ForbidOK

@[simp] lemma subset_univ {P : HypPack α} {A : Finset α} :
    ForbidOK (α := α) P A → A ⊆ P.H.U := by
  intro h; exact h.1

@[simp] lemma card_ge_two {P : HypPack α} {A : Finset α} :
    ForbidOK (α := α) P A → 2 ≤ A.card := by
  intro h; exact h.2

/-- `ForbidOK` から `A.Nonempty` を取り出す（`2 ≤ card` なので自動）。 -/
lemma nonempty {P : HypPack α} {A : Finset α} :
    ForbidOK (α := α) P A → A.Nonempty := by
  intro h
  -- `2 ≤ card` なら `card ≠ 0` なので nonempty
  dsimp [ForbidOK] at h
  obtain ⟨left, right⟩ := h
  contrapose! right
  subst right
  simp_all only [Finset.empty_subset, Finset.card_empty, Nat.zero_lt_succ]

end ForbidOK


/- ------------------------------------------------------------
  3. Accounting identities exposed at the API level
------------------------------------------------------------ -/

/--
/--
(1) 通常会計の基本恒等式（CON_ID）を HypPack 上で使いやすい形に露出する。
(2) S6_ConDelNdegId で証明されるべき事実である。
(3) 長期的には S6_ConDelNdegId に置き、ここでは axiom として仮置きする。
(4) 仮定として n ≥ 1, P : HypPack α, v : α を必要とする。
-/
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
/--
(1) forbid 付き会計の基本恒等式（CON_ID_corr）の最終形を HypPack 上で露出する。
(2) S5_Forbid_Compat および S5_ForbidConLemmas で証明されるべき事実である。
(3) 長期的には S5 系のファイルに置き、ここでは axiom として仮置きする。
(4) 仮定として n ≥ 1, P : HypPack α, A : Finset α, v : α を必要とする。
-/
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
  Local kernel / selection API

  方針：
  - S8 は「仕様・命題・等式」を凍結する層。
  - 選点（good v）・representability（con/del pack の存在）・Del-bound などの
    “局所核” は最終的に S11_LocalKernels 側へ集約したい。

  現時点では、依存関係を壊さないために **S8 内に置きつつ** `namespace Local`
  に隔離し、旧名は `abbrev` で互換を維持する。

  TODO（整理段階で実施）:
  - S11 側に実装が揃ったら、ここ（S8）の `abbrev` を削除し、参照側を
    `Dr1nds.Local.*` もしくは `S11_LocalKernels` の定義に統一する。
------------------------------------------------------------ -/
namespace Local

/--
(1) con 分岐の構成可能性（representability）。
(2) `Pc.U = P.U.erase v` かつ `Pc.C = con v P.C` を満たす `HypPack` の存在。
(3) 実装（もしくは構成の公理化）は最終的に S11_LocalKernels へ。
-/
axiom exists_con_pack
  (P : HypPack α) (v : α) :
  ∃ Pc : HypPack α,
    Pc.H.U = P.H.U.erase v ∧
    Pc.C = con (α := α) v P.C

/-- del 分岐の構成可能性（representability）。最終的に S11 へ。 -/
axiom exists_del_pack
  (P : HypPack α) (v : α) :
  ∃ Pd : HypPack α,
    Pd.H.U = P.H.U.erase v ∧
    Pd.C = Del (α := α) v P.C

/--
Del-branch 上界（通常会計）。

注意：これは「クラス閉性」ではなく、IH を当てるための局所構成を前提にした
Del-bound 核をまとめた入口。
-/
axiom del_bound_pack
  (n : Nat) (P : HypPack α) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0

/--
Del-branch 上界（forbid 側：Hole 上の Del）。

方針C（Del-as-Hole + Qcorr IH + 符号）で閉じる予定。
-/
axiom del_bound_hole_pack
  (n : Nat) (P : HypPack α) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A →
  Qcorr (α := α) (n - 1) P A →
  NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A)) ≤ 0

end Local

-- 互換 alias（参照側を壊さないために当面残す。最終的に削除予定）
abbrev exists_con_pack := Local.exists_con_pack (α := α)
abbrev exists_del_pack := Local.exists_del_pack (α := α)
abbrev del_bound_pack := Local.del_bound_pack (α := α)
abbrev del_bound_hole_pack := Local.del_bound_hole_pack (α := α)


/- ------------------------------------------------------------
  4. Bundled IH interfaces (recommended)
------------------------------------------------------------ -/

/--
(1) グローバル帰納法の仮置きとしての bundled IH を定義する。
(2) IH n P は通常の目標 Q n P と、ForbidOK な A に対する Qcorr n P A を同時に含む。
-/
def IH (n : Nat) (P : HypPack α) : Prop :=
  Q (α := α) n P ∧ (∀ A : Finset α, ForbidOK (α := α) P A → Qcorr (α := α) n P A)

/--
(1) グローバル帰納法のドライバとしての IH_pack は仮置きの axiom である。
(2) 本来は S11/S12 などの最終的な証明ファイルで構成され、ここでは暫定的に宣言している。
(3) 仮定として n : Nat, P : HypPack α を必要とする。
-/
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


/-
(1) B2（A.erase v 非空）の forbid Case2 用に、bundled IH から con-branch の上界を引き出す API。
(2) unary head 問題や選点戦略の影響を受けやすいため、暫定的に axiom としている。
(3) 仮定として IH (n-1) P, v ∈ A, (A.erase v).Nonempty を要求する。
-/
/-
NOTE:
`IH_corr_con_pack_IH` とその派生（legacy wrapper）は S9_IH_Unpack.lean 側で
実際に `theorem` として実装する。
S8_Statements.lean では「必要になる命題の形」を固定する役割に徹し、
同名の axiom を置かない（名前衝突・二重管理の原因になるため）。
-/


/- ------------------------------------------------------------
  5. Step interfaces (proof skeleton only)

  ここも「局所核」なので、将来的には S11 側へ寄せたい。
  ただし現状は依存関係を壊さないため S8 内に残し、`namespace Local` に隔離する。
------------------------------------------------------------ -/

namespace Local

/--
(1) 通常ステップで使う「良い v」の最小 API。`ndeg ≤ 0` のみを要求する。
(2) 選点は S11 側で構成し、ここは受け口のみ固定する。
-/
def GoodV_for_Q (P : HypPack α) (v : α) : Prop :=
  ndeg (α := α) P.C v ≤ 0

/--
(1) 通常ステップ：`∃ v, GoodV_for_Q P v` が与えられれば `Q n P` を閉じる。
(2) 実体は S11（S10 経由）で構成される。
-/
axiom Q_step
  (n : Nat) (P : HypPack α) :
  (∃ v : α, GoodV_for_Q (α := α) P v) →
  Q (α := α) n P

/-- forbid ステップ：ForbidOK(P,A) の下で Qcorr n P A を閉じる。 -/
axiom Qcorr_step
  (n : Nat) (P : HypPack α) (A : Finset α) :
  ForbidOK (α := α) P A →
  Qcorr (α := α) n P A

end Local

-- 互換 alias（参照側を壊さないために当面残す。最終的に削除予定）
abbrev GoodV_for_Q := Local.GoodV_for_Q (α := α)
abbrev Q_step := Local.Q_step (α := α)
abbrev Qcorr_step := Local.Qcorr_step (α := α)

/-- 互換：`∃ v, ndeg ≤ 0` から `∃ v, GoodV_for_Q` へ。 -/
lemma exists_goodV_for_Q_of_exists_ndeg (P : HypPack α) :
  (∃ v : α, ndeg (α := α) P.C v ≤ 0) →
  (∃ v : α, GoodV_for_Q (α := α) P v) := by
  intro h
  -- `GoodV_for_Q` は定義的に `ndeg ≤ 0`
  simpa [GoodV_for_Q] using h


/- ------------------------------------------------------------
  6. Notes
------------------------------------------------------------ -/

-- SC は S1_Families の定義を使う方針なら、ここで再定義しない。
-- “P.C 上の SC” の補題は S7_SC_Local 側に置く。

end Dr1nds
