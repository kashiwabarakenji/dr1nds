-- Dr1nds/S7_SC_Local.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S1_Families
import Dr1nds.S6_ConDelNdegId  -- Accounting.CON_ID を使う側になるので依存を固定

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]

open SetFamily

/- ============================================================
  S7 : Local inequality at an SC point (FROZEN I/O, skeleton)
  Policy:
    * base defs: S0_CoreDefs
    * no global Horn/DR1 assumptions here (pure family-level lemma)
    * provide only the exact I/O used by S10/Q-step and T-step
============================================================ -/

/-!
# このファイルの役割（S7 / UC-S7）

- ここは **「局所核のI/Oを凍結する場所」** です。
  実際の証明はまだ入れず、`axiom` として形だけを固定します。
- S10 の forbid-step（`Qcorr_step`）では、会計等式 `CON_ID_corr` を展開すると

    `NDS (n-1) (Del_s (Hole C A)) + ndeg (Hole C A) s`

  の形の *局所項* が必ず出てきます。これを **SC 点 s** で ≤0 に落とすのが UC-S7。
- 重要：ここで仮定する `SC` は **base family `F` に対して** であり、
  `Hole F.C A` で SC を仮定しません（後者は一般に壊れるので仮定しない）。
- forbid 側は `ForbidOK` を `2 ≤ A.card` に凍結しているので、
  singleton forbid（`A.card = 1`）の分岐は S10 側で別扱い（または射程外）です。

## `axiom` の今後

- これらの `axiom` は **最終的には `S11_LocalKernels.lean` で証明に置き換える** 想定です。
- その際、このファイルには
  - `axiom` を削除して `theorem/lemma` に置き換える
  - あるいは `S11` で証明した定理を `import` してここでは `abbrev/lemma` で再公開する
  のどちらかに整理します。
- いまは「S10 配線が依存する形」を先に固め、上位層の議論がブレないようにしています。
-/

namespace S7

/- ------------------------------------------------------------
  0. SC predicate (family-level)
------------------------------------------------------------ -/

/- SC point in a family C: singleton {s} is in C. -/
--def SC (C : Finset (Finset α)) (s : α) : Prop :=
--  ({s} : Finset α) ∈ C

--omit [DecidableEq α] in
--@[simp] lemma SC_iff (C : Finset (Finset α)) (s : α) :
--  SC (α := α) C s ↔ ({s} : Finset α) ∈ C := by
--  rfl

/- ------------------------------------------------------------
  1. The local target inequality (the exact shape used downstream)
------------------------------------------------------------ -/

/--
(UC-S7 / 局所核：SC 点での Del+ndeg の非正)

- **一次仕様（最も強い形）**：S10 の `CON_ID_corr` 展開後に現れる局所項

    `NDS (n-1) (Del s (Hole C A)) + ndeg (Hole C A) s`

  を `≤ 0` に落とす。
- ここでの `SC F s` は *base family* `F` に対する仮定。
  `Hole F.C A` 側で SC を仮定しない点が重要。
- `2 ≤ A.card` は forbid 側の射程（ForbidOK）を反映。

今後：この `axiom` は `S11_LocalKernels.lean` で証明に置き換える。
証明が入ったら、下の「投影版」(Del-branch だけ / ndeg だけ) は
この一次仕様から導出する形に整理するのが理想。
-/
axiom local_SC_del_ndeg_le_zero
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α) :
  (2 ≤ A.card) →
  SC F s →
  (NDS (n - 1) (Del s (Hole F.C A))
      +
    ndeg (Hole F.C A) s
  ≤ 0)

/- ------------------------------------------------------------
  2. Convenience wrappers (to reduce rewriting noise)
------------------------------------------------------------ -/

/-- A named abbreviation for D := Hole(C,A). -/
def D (F : SetFamily α) (A : Finset α) : Finset (Finset α) :=
  Hole F.C A

/-- Same inequality, written with D := Hole(C,A). -/
lemma local_SC_del_ndeg_le_zero'
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α)
  (hA : 2 ≤ A.card)
  (hSC : SC F s) :
  (NDS (n - 1) (Del s (D F A))
      +
    ndeg (D F A) s
  ≤ 0) := by
  -- purely a wrapper
  simpa [D] using local_SC_del_ndeg_le_zero n F A s hA hSC

/- ------------------------------------------------------------
  3. Projected bounds used by forbid-step (still skeleton)
------------------------------------------------------------ -/

/-!
投影版（ndeg だけ）

S10 側では局所項をまとめて扱うよりも、
- Del-branch の上界
- ndeg の上界
を別々に呼ぶ方が `simp/rw/linarith` が安定する場面がある。

最終的には `local_SC_del_ndeg_le_zero` から導出できる形に寄せたいが、
Lean 実装の初期段階では「配線の安定」を優先して独立 `axiom` として置く。
-/
axiom local_SC_ndeg_hole_le_zero
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α) :
  (2 ≤ A.card) →
  SC F s →
  ndeg (Hole F.C A) s ≤ 0

/-!
投影版（Del-branch だけ）

こちらも S10 wiring の都合で単独の API として公開している。
最終整理では
- `local_SC_del_ndeg_le_zero`（一次仕様）
- `local_SC_Del_hole_bound` / `local_SC_ndeg_hole_le_zero`（投影）
のどちらを残すかを決め、冗長性を解消する。
-/
axiom local_SC_Del_hole_bound
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α) :
  (2 ≤ A.card) →
  SC F s →
  NDS (n - 1) (Del s (Hole F.C A)) ≤ 0

/-- Same as `local_SC_Del_hole_bound`, written with `D := Hole(C,A)` to reduce rewriting noise. -/
lemma local_SC_Del_D_bound'
  (n : Nat)
  (F : SetFamily α)
  (A : Finset α)
  (s : α)
  (hA : 2 ≤ A.card)
  (hSC : SC F s) :
  NDS (n - 1) (Del s (D F A)) ≤ 0 := by
  simpa [D] using local_SC_Del_hole_bound n F A s hA hSC

/-!
## 将来のリファクタ目標（導出関係のスケルトン）

現状は配線を安定させるために 3 本を `axiom` として並立させているが、
理想的には一次仕様 `local_SC_del_ndeg_le_zero` から投影版を導出して冗長性を消す。

下の 2 本は、その「最終的にこう整理したい」という形だけを先に凍結しておく。
（いまは証明を書かない：S11 で証明が入ったタイミングで差し替える。）
-/


end S7

end Dr1nds
