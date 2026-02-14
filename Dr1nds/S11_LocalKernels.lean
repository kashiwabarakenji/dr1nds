-- Dr1nds/S11_LocalKernels.lean
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

import Dr1nds.S0_CoreDefs
import Dr1nds.S8_Statements
import Dr1nds.S9_IH_Unpack

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/- ============================================================
  S11 : Local kernels (SKELETON)
  目的：S10_Steps から呼ばれる「局所核 API」を一本化する。
  方針：骨格優先。中身は axiom/sorry で後回し。

  注意：このファイルは *S10_Steps を import しない*（循環依存を避ける）。
============================================================ -/

/-!
# S11 ROADMAP（凍結 API と今後の埋め方）

このファイルは **S10_Steps が唯一 import する「局所核 API 集約」** です。
重要方針：**S10 は wiring に徹し、数学的に重い部分はすべて S11 側の API（lemma/axiom）として切り出す。**

## ここで「証明済み」になっているもの
- `Up_card_nonneg`
- `corr_implies_hole_bound`（`NDS_corr ≤ 0` から `NDS(Hole) ≤ 0` への符号処理）

## ここで「axiom として凍結」しているもの（後でどこで埋めるか）

### (S7) good vertex の存在
- `exists_good_v_for_Q`（`∃ v, ndeg ≤ 0` の供給）
- これは **選点（good v）供給の中核**。NoParallel→SC→goodV などのルートで埋める。

### (S5/S6) representability（IH を当てるための pack 供給）
- `exists_con_pack`：`con v P.C` を列挙する `HypPack` の存在（※S8 側で定義済）
- `choose_con_pack` / `choose_con_pack_C`：上の存在から noncomputable に選ぶ
- `IH_Q_gives_con_bound_pack`：`Q(n-1,P)` から con-branch を `≤0` で抑える（representability で得た pack を介する版）
- `exists_del_base_pack` / `del_as_hole` / `con_pack_universe`：Del-as-Hole ルートの表現核

### (S2 など) DR1/NEP 由来の軽い選択補題
- `choose_prem_of_hasHead` / `pick_prem_mem`

### (S5/S6) Del-bound（方針C）
- 推奨 API は `Del_branch_bound`。
  `Qcorr(n-1, Pc, Pv.erase v)` から `NDS(Del v P.C) ≤ 0` を出す、という形に固定してある。

## レガシー（削除予定）
- `Qcorr_case1_singleton`：`ForbidOK` を `2 ≤ A.card` に凍結している限り singleton 分岐は起きない。
  まだ S10 側に古い分岐が残る場合だけの互換用。最終的に削除する。

※注意：このファイルは **S10_Steps を import しない**（循環依存回避）。
-/

/-
====================
S11 棚卸しメモ（親スレ用）
====================

S11 は「S10 が呼ぶ局所核 API の集約点」。このファイル内の宣言は次の3種類に分類する。

(A) 完全に確定した plumbing（theorem）
    - 純粋に定義展開＋算術で閉じるもの。
    - 例: `Up_card_nonneg`, `corr_implies_hole_bound`, `Del_eq_Hole_singleton`。

(B) “軽い representability”
    - `choose_*` で pack を選び、`*.C = ...` で書き戻すだけのもの。
    - 例: `choose_con_pack`, `choose_con_pack_C_eq`。
    - これは IH を当てるための配線であり、数学的核ではない。

(C) “重い核”（axiom のまま凍結しているもの）
    - good v の供給（S7）: `exists_good_v_for_Q`
    - Del-bound（方針C）: `Del_branch_bound`（＋必要なら `del_eq_hole` など）
    - premise choice（S2/HornNF）: `choose_prem_of_hasHead` など

運用ルール：
  * S10 は wiring のみ。中身が重い議論は S11 の axiom/theorem に切り出し、S10 を増やさない。
  * 置換の順序は「呼び出し側を変えずに中身を theorem 化」：
      1) `Del_bound` を直接使わず `Del_bound_of_Q` へ寄せる
      2) `Del_bound_of_Q` の実装を `Del_bound_from_branch` 経由へ差し替える
      3) 最後に `Del_bound`（axiom）自体を削除

注意：`prem_contains_head_choice` は NF 方針（head ∉ prem）と整合しない可能性がある。
  - ここは “prem の意味” を S8 側の仕様に合わせて最終決定する。
  - NF を常時仮定する設計なら、むしろ `v ∉ Pv` が欲しい（＝ここは差し替え候補）。
-/

/- ============================================================
  (A) Proven arithmetic/definition lemmas
============================================================ -/

/-- Up-cardinality is always nonnegative (as an Int). -/
lemma Up_card_nonneg
  (C : Finset (Finset α)) (A : Finset α) :
  (0 : Int) ≤ (Up (α := α) C A).card := by
  -- `card` is a Nat; its coercion to Int is nonnegative.
  simp_all only [Nat.cast_nonneg]

/-- From a corrected bound we can drop the nonnegative `Up` term
    and obtain the plain `Hole` bound. -/
lemma corr_implies_hole_bound
  (n : Nat)
  (C : Finset (Finset α))
  (A : Finset α)
  (h : NDS_corr (α := α) n C A ≤ 0) :
  NDS (α := α) n (Hole (α := α) C A) ≤ 0 := by
  classical
  -- unfold the definition of NDS_corr
  -- NDS_corr n C A = NDS n (Hole C A) + (Up C A).card
  have h' :
      NDS (α := α) n (Hole (α := α) C A)
        + (Up (α := α) C A).card ≤ 0 := by
    simpa [NDS_corr] using h
  -- the Up-card term is nonnegative
  have hup : (0 : Int) ≤ (Up (α := α) C A).card :=
    Up_card_nonneg (α := α) C A
  -- so we can drop it from the left-hand side
  have : NDS (α := α) n (Hole (α := α) C A) ≤ 0 := by
    -- a + b ≤ 0 and 0 ≤ b  ⇒  a ≤ 0
    linarith
  exact this

/--
Canonical singleton Del-as-Hole equality.

This uses only the definitions from S0:
  Del v C      = C.filter (fun X => v ∉ X)
  Hole C {v}   = C.filter (fun X => ¬ ({v} ⊆ X))

Since `{v} ⊆ X` is definitionally equivalent to `v ∈ X`,
the two filters coincide.
-/
lemma Del_eq_Hole_singleton
  (C : Finset (Finset α)) (v : α) :
  Del v C = Hole C ({v} : Finset α) := by
  classical
  unfold Del Hole
  apply Finset.ext
  intro X
  simp [Finset.mem_filter]


/-
============================================================
  (A2) Del-as-Hole for HornNF.FixSet (ported from vPATCH-DEL-AS-HOLE-ADMIT0-1.0c)

  位置づけ：
  - HypPack レベルの `del_as_hole`（axiom）とは別物。
  - こちらは HornNF の closure system と FixSet（閉集合族）だけで完結する
    「Del = Hole(削除世界, Pv)」の表現補題。

  注意：
  - ここで使う `HornNF.del` は filter 型（prem の filter + U.erase）を想定。
  - DR1（prem v の一意性）を使う。
  - 既存の API 名が違う場合は、このブロックだけを S2 側の実名に合わせて rename してください。
============================================================ -/

namespace HornNF

variable (H : HornNF α)

/-- Membership in `FixSet` can be expressed as `X ⊆ U` plus closure. -/
lemma mem_FixSet_iff (X : Finset α) :
    X ∈ HornNF.FixSet H ↔ X ⊆ H.U ∧ H.IsClosed X := by
  -- `FixSet := U.powerset.filter IsClosed`
  -- `X ∈ U.powerset` is definitional to `X ⊆ U`.
  simp [HornNF.FixSet, Finset.mem_powerset]

/-- Elements of `FixSet` are subsets of the universe `U`. -/
lemma mem_FixSet_subset_U {X : Finset α}
    (hX : X ∈ HornNF.FixSet H) : X ⊆ H.U :=
  (mem_FixSet_iff (H := H) (X := X)).1 hX |>.1

/-- DR1 uniqueness: if `P,Q ∈ prem v` then `P = Q`. -/
lemma prem_eq_of_mem_of_mem
    (v : α)
    (hDR1 : HornNF.IsDR1 H)
    {P Q : Finset α}
    (hP : P ∈ H.prem v) (hQ : Q ∈ H.prem v) :
    P = Q := by
  have hcard : (H.prem v).card ≤ 1 := hDR1 v
  -- `Finset.card_le_one.mp` produces the uniqueness function, but we pass args explicitly
  -- to avoid Lean mis-inferring `hP` as the element.
  have hunique := Finset.card_le_one.mp hcard
  exact hunique (a := P) (b := Q) hP hQ

/-- Del-as-Hole (case R1): head=v に premise Pv があるとき

`Del v (FixSet H) = Hole (FixSet (H.del v)) Pv`.

(移植版)
-/
theorem del_as_hole_caseR1
    (v : α)
    (hDR1 : HornNF.IsDR1 H)
    (Pv : Finset α) (hPv : Pv ∈ H.prem v) :
    Del v (HornNF.FixSet H)
      =
    Hole (HornNF.FixSet (HornNF.del H v)) Pv :=
by
  classical
  ext X
  -- Del/Hole だけを展開して、FixSet の中身（powerset/filter）は必要な箇所でだけ展開する。
  simp [Del, Hole]
  constructor
  · -- (⇒)
    rintro ⟨hXFix, hvX⟩
    -- `simp [Del, Hole]` により、`hXFix` は既に `X ∈ FixSet H` の形で来ることもあれば
    -- `X ⊆ H.U ∧ H.IsClosed X` にまで展開されて来ることもある。
    -- どちらでも扱えるように、ここでは一度 `hXFix' : X ⊆ H.U ∧ H.IsClosed X` を作る。
    have hXFix' : X ⊆ H.U ∧ H.IsClosed X := by
      -- もし `hXFix` が membership なら `mem_FixSet_iff` で、
      -- もし既に pair ならそのまま。
      first
        | exact (mem_FixSet_iff (H := H) (X := X)).1 hXFix
        | exact hXFix

    refine And.intro ?hXFixDel ?hNotPv
    · -- X ∈ FixSet (H.del v)
      have hXU : X ⊆ H.U := hXFix'.1
      have hXU' : X ⊆ H.U.erase v := by
        intro x hxX
        have hxU : x ∈ H.U := hXU hxX
        have hxne : x ≠ v := by
          intro hxeq; subst hxeq; exact hvX hxX
        exact Finset.mem_erase.mpr ⟨hxne, hxU⟩

      have hClosedH : H.IsClosed X := hXFix'.2

      have hClosedDel : (HornNF.del H v).IsClosed X := by
        intro h P hPdel hPX
        by_cases hh : h = v
        · subst hh
          -- prem_del(v)=∅
          simp_all only [and_self, del_prem_self, Finset.notMem_empty]
        · -- h≠v: prem_del(h) is a filter of `H.prem h`
          have hP : P ∈ H.prem h := by
            have : P ∈ (H.prem h).filter (fun Q => v ∉ Q) := by
              -- ここは `simp` の方が頑丈
              simp [HornNF.del, hh] at hPdel
              -- `hPdel : P ∈ H.prem h ∧ v ∉ P`
              exact Finset.mem_filter.mpr ⟨hPdel.1, hPdel.2⟩
            exact (Finset.mem_filter.mp this).1
          exact hClosedH (h := h) (P := P) hP hPX

      -- FixSet の membership を組み立てる
      have : X ∈ HornNF.FixSet (HornNF.del H v) := by
        -- `(H.del v).U` は definitional に `H.U.erase v`
        -- ここでだけ FixSet を展開
        have : X ⊆ (HornNF.del H v).U ∧ (HornNF.del H v).IsClosed X := by
          simp_all only [and_self, del_U]
        exact (mem_FixSet_iff (H := HornNF.del H v) (X := X)).2 this
      simp_all only [and_self, Dr1nds.mem_FixSet_iff, del_U, Finset.mem_powerset]

    · -- ¬Pv ⊆ X
      intro hPvX
      have hClosedH : H.IsClosed X := hXFix'.2
      have : v ∈ X := hClosedH (h := v) (P := Pv) hPv hPvX
      exact hvX this

  · -- (⇐)
    rintro ⟨hXFixDel, hNotPvX⟩
    -- 同様に、`hXFixDel` を pair 形式に正規化
    have hXFixDel' : X ⊆ (HornNF.del H v).U ∧ (HornNF.del H v).IsClosed X := by
      first
        | exact (mem_FixSet_iff (H := HornNF.del H v) (X := X)).1 hXFixDel
        | exact hXFixDel

    refine And.intro ?hXFix ?hvX

    · -- X ∈ FixSet H
      have hXU' : X ⊆ (HornNF.del H v).U := hXFixDel'.1
      have hClosedDel : (HornNF.del H v).IsClosed X := hXFixDel'.2

      have hvX : v ∉ X := by
        intro hvX'
        have : v ∈ (HornNF.del H v).U := hXU' hvX'
        have : v ∈ H.U.erase v := by
          simp_all only [and_true, del_U, and_self, Finset.mem_erase, ne_eq, not_true_eq_false, false_and]
        exact (Finset.notMem_erase v H.U) this

      have hXU : X ⊆ H.U := by
        intro x hxX
        have : x ∈ (HornNF.del H v).U := hXU' hxX
        have : x ∈ H.U.erase v := by
          simpa [HornNF.del] using this
        exact (Finset.mem_erase.mp this).2

      have hClosedH : H.IsClosed X := by
        intro h P hP hPX
        by_cases hh : h = v
        · subst hh
          have hPeq : P = Pv := by
            apply prem_eq_of_mem_of_mem (H := H)
            simp_all only [and_true, del_U, and_self]
            exact hP
            exact hPv
          subst hPeq
          exfalso
          exact hNotPvX hPX
        · by_cases hvP : v ∈ P
          · exfalso
            exact hvX (hPX hvP)
          · have hPdel : P ∈ (HornNF.del H v).prem h := by
              have : P ∈ (H.prem h).filter (fun Q => v ∉ Q) :=
                Finset.mem_filter.mpr ⟨hP, hvP⟩
              simpa [HornNF.del, hh] using this
            exact hClosedDel (h := h) (P := P) hPdel hPX

      -- FixSet membership
      have : X ∈ HornNF.FixSet H :=
        (mem_FixSet_iff (H := H) (X := X)).2 ⟨hXU, hClosedH⟩
      simp_all only [and_true, del_U, and_self, Dr1nds.mem_FixSet_iff, Finset.mem_powerset]

    · -- v ∉ X
      have hXU' : X ⊆ (HornNF.del H v).U := hXFixDel'.1
      intro hvX'
      have : v ∈ (HornNF.del H v).U := hXU' hvX'
      have : v ∈ H.U.erase v := by
        simp_all only [and_true, del_U, true_and, Finset.mem_erase, ne_eq, not_true_eq_false, false_and]
      exact (Finset.notMem_erase v H.U) this

end HornNF


/- ============================================================
  (B) good vertex 供給（S7 の責務）

  NOTE:
  `GoodV_for_Q` の引数順や依存（`n` を取るかどうか）が S8 側で変わりうるため、
  S11 ではそれに直接依存しない。

  S10 が本当に必要なのは「`ndeg ≤ 0` を満たす頂点が 1 つ取れる」ことだけなので、
  ここでは最小形 `∃ v, ndeg ≤ 0` を axiom として凍結する。
============================================================ -/

/--
(Purpose)
S10 needs *some* vertex `v` with `ndeg(P.C,v) ≤ 0` to run the main induction step.

(Intended proof location)
S7（NoParallel→SC→good vertex など）で埋める。
-/
axiom exists_good_v_for_Q
  (n : Nat) (P : HypPack α) :
  ∃ v : α, ndeg (α := α) P.C v ≤ 0

/-- Noncomputably pick a good vertex from `exists_good_v_for_Q`. -/
noncomputable def choose_good_v_for_Q
  (n : Nat) (P : HypPack α) : α :=
  Classical.choose (exists_good_v_for_Q (α := α) n P)


@[simp] theorem choose_good_v_for_Q_spec
  (n : Nat) (P : HypPack α) :
  ndeg (α := α) P.C (choose_good_v_for_Q (α := α) n P) ≤ 0 :=
  Classical.choose_spec (exists_good_v_for_Q (α := α) n P)




/- ============================================================
  (C) Representability for IH targets (con-pack / del-pack)
============================================================ -/

-- NOTE: exists_con_pack は S8_Statements.lean 側で定義済み。S11 で再定義すると衝突するので、ここでは S8 のものを利用する。

/- Noncomputably choose a con-pack. -/
noncomputable def choose_con_pack
  (P : HypPack α) (v : α) : HypPack α :=
  Classical.choose (exists_con_pack (α := α) (P := P) (v := v))

-- NOTE:
-- `choose_con_pack_C_eq` を本体として置き、`choose_con_pack_C` を simp-lemma として別名で出す。
-- 以前 `@[simp]` のみで運用すると、文脈によっては `simp` が等式を `True` に潰してしまい
-- `by simpa using ...` が意図と違う型で通る事故が起きたため、両方を残す。
/-- Spec lemma (non-simp): the chosen pack enumerates `con v P.C`.

NOTE: We deliberately do **not** tag this lemma with `[simp]` because `simp` can rewrite
`t = t` to `True` via `eq_self_iff_true`, and then `by simpa using ...` could typecheck
against `True` rather than the intended equality.
-/

theorem choose_con_pack_C_eq
  (P : HypPack α) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).C = con (α := α) v P.C := by
  exact (Classical.choose_spec (exists_con_pack (α := α) (P := P) (v := v))).2

/-- Spec lemma (non-simp): the chosen con-pack has universe `P.H.U.erase v`.

NOTE: We deliberately do **not** tag this lemma with `[simp]` for the same reason as
`choose_con_pack_C_eq`: avoiding accidental rewriting of goals into `True` via `eq_self_iff_true`.
-/
theorem choose_con_pack_U_eq
  (P : HypPack α) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).H.U = P.H.U.erase v := by
  exact (Classical.choose_spec (exists_con_pack (α := α) (P := P) (v := v))).1

/-- Simp lemma: rewrite the chosen con-pack universe. -/
@[simp] theorem choose_con_pack_U
  (P : HypPack α) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).H.U = P.H.U.erase v := by
  exact choose_con_pack_U_eq (α := α) (P := P) (v := v)

/-- Alias simp-lemma (kept for backward compatibility with earlier code). -/
@[simp] theorem choose_con_pack_U'
  (P : HypPack α) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).H.U = P.H.U.erase v := by
  exact choose_con_pack_U_eq (α := α) (P := P) (v := v)

/-- Simp lemma: rewrite the chosen con-pack family. -/
@[simp] theorem choose_con_pack_C
  (P : HypPack α) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).C = con (α := α) v P.C := by
  exact choose_con_pack_C_eq (α := α) (P := P) (v := v)

/-- Alias simp-lemma (kept for backward compatibility with earlier S10 code). -/
@[simp] theorem choose_con_pack_C'
  (P : HypPack α) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).C = con (α := α) v P.C := by
  exact choose_con_pack_C_eq (α := α) (P := P) (v := v)

/-/ === (C) Representability for IH targets (del-pack) === -/

/-- Noncomputably choose a del-pack. -/
noncomputable def choose_del_pack
  (P : HypPack α) (v : α) : HypPack α :=
  Classical.choose (exists_del_pack (α := α) (P := P) (v := v))

/-- Spec lemma (non-simp): the chosen pack enumerates `Del v P.C`. -/
theorem choose_del_pack_C_eq
  (P : HypPack α) (v : α) :
  (choose_del_pack (α := α) (P := P) (v := v)).C = Del (α := α) v P.C := by
  exact (Classical.choose_spec (exists_del_pack (α := α) (P := P) (v := v))).2

/-- Simp lemma: rewrite the chosen del-pack family. -/
@[simp] theorem choose_del_pack_C
  (P : HypPack α) (v : α) :
  (choose_del_pack (α := α) (P := P) (v := v)).C = Del (α := α) v P.C := by
  exact choose_del_pack_C_eq (α := α) (P := P) (v := v)

/--
(Purpose)
S10 の con-branch を抑えるための「配線用」補題。

ポイント：これは重い核ではなく、S9 側にある `IH_Q_gives_con_bound`（= con-family へ IH を当てるための公理/補題）
から **ただちに導ける** ので、S11 では axiom にせず theorem として固定する。

注意：ここで `Pc` は representability により供給された pack で、家族の等式 `hPcC` により
`Pc.C` を `con v P.C` に書き換えて閉じる。
-/
theorem IH_Q_gives_con_bound_pack
  (n : Nat) (P : HypPack α) (v : α)
  (Pc : HypPack α) (hPcC : Pc.C = con (α := α) v P.C) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) Pc.C ≤ 0
:= by
  intro hQ
  -- S9_IH_Unpack には「Q(n-1,P) から con-branch を抑える」定理がすでにある。
  -- ここでは representability で得た等式 `hPcC` を使って `Pc.C` を `con v P.C` に書き換えるだけ。
  have hcon : NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0 :=
    IH_Q_gives_con_bound (α := α) (n := n) (P := P) (v := v) hQ
  simpa [hPcC] using hcon

/-- Backward-compatibility: old name (non-pack) lived in S9; the pack version lives in S11. -/
@[simp] theorem IH_Q_gives_con_bound'
  (n : Nat) (P : HypPack α) (v : α)
  (Pc : HypPack α) (hPcC : Pc.C = con (α := α) v P.C) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) Pc.C ≤ 0 :=
by
  intro hQ
  exact IH_Q_gives_con_bound_pack (α := α) (n := n) (P := P) (v := v) (Pc := Pc) hPcC hQ

/- ============================================================
  (D) Del-bound kernels (C-route via Qcorr)
============================================================ -/

/--
 (S11 kernel) Del-bound when `prem v` is empty.

 Design note: S10 is pure wiring; the mathematical content for this branch
 is handled in S11.
-/
axiom Del_bound_of_Q_empty
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack α)
  (v : α)
  (hPrem : ¬ (P.H.prem v).Nonempty)
  (hQ : Q (α := α) (n - 1) P) :
  NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0




/-
(Purpose)
DR1 implies `prem v` has at most one element; when it is nonempty we can pick the unique premise.
S10 uses this to extract the premise for the Del-branch.

(Intended proof location)
S2_HornNF or S1_HornNF (premise choice facts).
-/

/-
(Purpose)
Pick a premise `Pv ∈ prem v` from nonemptiness.

Design note:
This is a pure choice lemma; DR1 uniqueness is not required for existence.
-/
noncomputable def choose_prem_of_hasHead
  (P : HypPack α) (v : α)
  (hne : (P.H.prem v).Nonempty) :
  { Pv : Finset α // Pv ∈ P.H.prem v } :=
  by
    classical
    refine ⟨Classical.choose hne, ?_⟩
    exact Classical.choose_spec hne


/-- Noncomputably pick `Pv` from `prem v` when nonempty. -/
noncomputable def pick_prem
  (P : HypPack α) (v : α) (h : (P.H.prem v).Nonempty) : Finset α :=
  (choose_prem_of_hasHead (α := α) (P := P) (v := v) h).1

@[simp] theorem pick_prem_mem
  (P : HypPack α) (v : α) (h : (P.H.prem v).Nonempty) :
  pick_prem (α := α) P v h ∈ P.H.prem v :=
  Classical.choose_spec h

/--
 (S11 kernel) Del-bound when `prem v` is nonempty but the chosen premise has card < 2.

 In the intended design this covers the singleton-prem branch.
-/
axiom Del_bound_of_Q_singleton
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack α)
  (v : α)
  (hPrem : (P.H.prem v).Nonempty)
  (hCard : ¬ 2 ≤ (pick_prem  P v hPrem).card)
  (hQ : Q (α := α) (n - 1) P) :
  NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0
/-/
Kernel: supply the specific `Qcorr` fact needed by the Del-branch when `prem v` is nonempty.

This is expected to be proved in S5/S6 using the Del-as-Hole identification on the deletion world,
then applying the global IH on the appropriate pack.

We keep it as an axiom for now so that `Del_bound_of_Q` can be implemented via the branch route
without changing any call sites.
-/



/--
Kernel: supply the specific `Qcorr` fact needed by the Del-branch when `prem v` is nonempty
and the chosen premise has size at least 2.

This is the intended non-singleton API; singleton (`card = 1`) is handled by a separate route.
-/
/-
Kernel: supply the specific `Qcorr` fact needed by the Del-branch when `prem v` is nonempty
and the chosen premise has size at least 2.

This is the intended non-singleton API; singleton (`card = 1`) is handled by a separate route.

Implementation note:
We apply `IH_Qcorr` *directly* to the con-pack, after constructing `ForbidOK`.
This avoids any Del→con transport.
-/
theorem prem_erase_Qcorr_ge2
  (n : Nat) (_hn : 1 ≤ n)
  (P : HypPack α) (v : α)
  (hPrem : (P.H.prem v).Nonempty)
  (hCard : 2 ≤ (pick_prem (α := α) P v hPrem).card) :
  Qcorr (α := α)
    (n - 1)
    (choose_con_pack (α := α) (P := P) (v := v))
    ((pick_prem (α := α) P v hPrem).erase v)
:= by
  classical

  -- Fix names
  let Pv := pick_prem (α := α) P v hPrem
  have hmem : Pv ∈ P.H.prem v := by
    simp_all only [pick_prem_mem, Pv]

  -- NF: head is not in its premise
  have hv_not : v ∉ Pv := by
    simpa [Pv] using P.H.nf hmem

  -- card condition survives erase (since v ∉ Pv)
  have hCard' : 2 ≤ (Pv.erase v).card := by
    simpa [Pv, Finset.erase_eq_of_notMem hv_not] using hCard

  -- inclusion into the con-pack universe
  have hsubset :
      Pv.erase v ⊆
        (choose_con_pack (α := α) (P := P) (v := v)).H.U := by
    intro x hx
    have hxne : x ≠ v := (Finset.mem_erase.mp hx).1
    have hxPv : x ∈ Pv := (Finset.mem_erase.mp hx).2
    have hxU : x ∈ P.H.U :=
      P.H.prem_subset_U hmem hxPv
    have hUeq :
      (choose_con_pack (α := α) (P := P) (v := v)).H.U = P.H.U.erase v :=
      choose_con_pack_U_eq (α := α) (P := P) (v := v)
    -- move to `P.H.U.erase v` and rewrite the target universe
    have : x ∈ P.H.U.erase v := Finset.mem_erase.mpr ⟨hxne, hxU⟩
    simpa [hUeq] using this

  -- build ForbidOK and apply IH_Qcorr directly on the con-pack
  have hForbid :
      ForbidOK (α := α)
        (choose_con_pack (α := α) (P := P) (v := v))
        (Pv.erase v) := by
    exact And.intro hsubset hCard'

  exact
    IH_Qcorr
      (α := α)
      (n := n)
      (P := choose_con_pack (α := α) (P := P) (v := v))
      (A := Pv.erase v)
      hForbid

/--
Pd-based version of prem_erase_Qcorr_ge2.

This supplies the Qcorr fact directly on the deletion-world pack.
For now we keep it as an axiom; it will later be proved via IH_Qcorr
applied to the deletion base pack.
-/

theorem prem_erase_Qcorr_ge2_Pd
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack α) (v : α)
  (hPrem : (P.H.prem v).Nonempty)
  (hCard : 2 ≤ (pick_prem (α := α) P v hPrem).card)
  (Pd : HypPack α)
  (hPdU : Pd.H.U = P.H.U.erase v)
  (hPdC : Pd.C = Del (α := α) v P.C) :
  Qcorr (α := α)
    (n - 1)
    Pd
    ((pick_prem (α := α) P v hPrem).erase v)
:= by
  classical
  let Pv := pick_prem (α := α) P v hPrem

  have hmem : Pv ∈ P.H.prem v := by
    simp [Pv]

  -- NF: head is not in its premise
  have hv_not : v ∉ Pv := by
    simpa [Pv] using P.H.nf hmem

  -- card condition survives erase
  have hCard' : 2 ≤ (Pv.erase v).card := by
    simpa [Pv, Finset.erase_eq_of_notMem hv_not] using hCard

  -- inclusion into deletion-world universe
  have hsubset :
      Pv.erase v ⊆ Pd.H.U := by
    intro x hx
    have hxne : x ≠ v := (Finset.mem_erase.mp hx).1
    have hxPv : x ∈ Pv := (Finset.mem_erase.mp hx).2
    have hxU : x ∈ P.H.U :=
      P.H.prem_subset_U hmem hxPv
    have : x ∈ P.H.U.erase v :=
      Finset.mem_erase.mpr ⟨hxne, hxU⟩
    simpa [hPdU] using this

  -- build ForbidOK on Pd
  have hForbid :
      ForbidOK (α := α) Pd (Pv.erase v) :=
    And.intro hsubset hCard'

  -- apply IH_Qcorr directly on Pd
  exact
    IH_Qcorr
      (α := α)
      (n := n)
      (P := Pd)
      (A := Pv.erase v)
      hForbid


/-/
(Del-as-Hole) 仕様の置き場所（台=U.erase v を明示した版）

ここで固定したい設計は次の通り：
- `Del v P.C` は “削除世界（台 `P.U.erase v`）” の family として扱う。
- したがって Del-as-Hole は **削除世界の base pack** `Pd` 上で述べる。

このファイル（S11）では呼び出し口の安定が最優先なので、
実体は当面 axiom として置き、後で S5/S6 で theorem 化する。

注意：以前の暫定 `Hole P.C (pick_prem ...)` は、母体 family の台が `U` のまま
の可能性があり、`U.erase v` 固定設計と整合しないため削除した。
-/
theorem exists_del_base_pack
  (P : HypPack α) (v : α) :
  ∃ Pd : HypPack α,
    Pd.H.U = P.H.U.erase v ∧ Pd.C = Del (α := α) v P.C := by
  -- Reuse the representability lemma provided in S8.
  simpa using (exists_del_pack (α := α) (P := P) (v := v))

/-
Del-as-Hole（削除世界 base pack 版）

`prem v` が nonempty のとき、唯一前提 `Pv` を取り、
削除世界 base pack `Pd` の上で
  `Pd.C = Hole Pd.C (Pv.erase v)`
を与える。

※ここでは `Pd` の取り方を `exists_del_base_pack` によって固定する。
-/
/-
Del-as-Hole（削除世界 base pack 版）

`prem v` が nonempty のとき、唯一前提 `Pv` を取り、
削除世界 base pack `Pd`（`Pd.H.U = P.H.U.erase v` かつ `Pd.C = Del v P.C`）の上で
  `Pd.C = Hole Pd.C (Pv.erase v)`
を与える。

※ここでは `Pd` の取り方を `exists_del_base_pack` によって固定する。
-/

/--
Del-as-Hole（削除世界 base pack 版）

`prem v` が nonempty のとき、唯一前提 `Pv` を取り、
削除世界 base pack `Pd`（`Pd.H.U = P.H.U.erase v` かつ `Pd.C = Del v P.C`）の上で
  `Pd.C = Hole Pd.C (Pv.erase v)`
を与える。
-/
theorem del_as_hole
  (P : HypPack α)
  (v : α)
  (hPrem : (P.H.prem v).Nonempty) :
  ∃ Pd : HypPack α,
    Pd.H.U = P.H.U.erase v ∧
    Pd.C = Del (α := α) v P.C ∧
    (let Pv := pick_prem (α := α) P v hPrem
     Pd.C = Hole (α := α) Pd.C (Pv.erase v))
:= by
  classical
  obtain ⟨Pd, hU, hC⟩ :=
    exists_del_base_pack (α := α) (P := P) (v := v)

  let Pv := pick_prem (α := α) P v hPrem
  have hPv : Pv ∈ P.H.prem v := by
    simp_all only [pick_prem_mem, Pv]

  have hv_not : v ∉ Pv := by
    simpa using P.H.nf hPv

  refine ⟨Pd, hU, hC, ?_⟩

  -- FixSet-level Del-as-Hole
  have hFixSet :
      Del v (HornNF.FixSet P.H)
        = Hole (HornNF.FixSet (HornNF.del P.H v)) Pv :=
    HornNF.del_as_hole_caseR1
      (H := P.H)
      (v := v)
      (hDR1 := P.dr1)
      (Pv := Pv)
      (hPv := hPv)

  -- First show: Del v P.C = Del v (FixSet P.H)
  have hDel_eq : Del v P.C = Del v (HornNF.FixSet P.H) := by
    -- P.C = FixSet P.H via P.mem_iff'
    have hPC : P.C = HornNF.FixSet P.H := by
      ext X
      simp_all only [pick_prem_mem, ClosedPack.mem_iff', mem_FixSet_iff, Finset.mem_powerset, Pv]
    rw [hPC]

  -- Combine with hFixSet
  have hFix :
      Del v P.C
        = Hole (HornNF.FixSet (HornNF.del P.H v)) Pv := by
    rw [hDel_eq]
    exact hFixSet

  -- Return to Pd-level and convert Pv to Pv.erase v
  have hFinal :
      Pd.C = Hole Pd.C (Pv.erase v) := by
    -- rewrite Pd.C to Del v P.C
    rw [hC]
    -- rewrite Del v P.C using hFix
    rw [hFix]
    -- replace Pv.erase v with Pv (since v ∉ Pv)
    have hErase : Pv.erase v = Pv :=
      Finset.erase_eq_of_notMem hv_not
    rw [hErase]
    -- now we need: Hole F Pv = Hole (Hole F Pv) Pv
    -- this is idempotence of filtering with the same predicate
    apply Finset.ext
    intro X
    unfold Hole
    simp

  exact hFinal

/-- Noncomputably choose a del base pack as in del_as_hole. -/
noncomputable def choose_del_base_pack
  (P : HypPack α) (v : α)
  (hPrem : (P.H.prem v).Nonempty) : HypPack α :=
  (del_as_hole P v hPrem).choose

@[simp] theorem choose_del_base_pack_spec_U
  (P : HypPack α) (v : α) (hPrem : (P.H.prem v).Nonempty) :
  (choose_del_base_pack (α := α) (P := P) (v := v) (hPrem := hPrem)).H.U = P.H.U.erase v := by
  have h := Classical.choose_spec (del_as_hole (α := α) (P := P) (v := v) (hPrem := hPrem))
  exact h.1

@[simp] theorem choose_del_base_pack_spec_C
  (P : HypPack α) (v : α) (hPrem : (P.H.prem v).Nonempty) :
  (choose_del_base_pack (α := α) (P := P) (v := v) (hPrem := hPrem)).C = Del (α := α) v P.C := by
  have h := Classical.choose_spec (del_as_hole (α := α) (P := P) (v := v) (hPrem := hPrem))
  exact h.2.1

theorem choose_del_base_pack_spec_hole
  (P : HypPack α) (v : α) (hPrem : (P.H.prem v).Nonempty) :
  let Pv := pick_prem (α := α) P v hPrem
  (choose_del_base_pack (α := α) (P := P) (v := v) (hPrem := hPrem)).C
    = Hole (α := α)
        (choose_del_base_pack (α := α) (P := P) (v := v) (hPrem := hPrem)).C
        (Pv.erase v)
:= by
  classical
  -- Unpack the spec coming from `del_as_hole`.
  have hs :=
    Classical.choose_spec
      (del_as_hole (α := α) (P := P) (v := v) (hPrem := hPrem))
  -- `hs.2.2` is exactly the Hole-equality, but written for `Classical.choose ...`.
  -- Rewrite `Classical.choose ...` as `choose_del_base_pack ...`.
  simpa [choose_del_base_pack] using hs.2.2


/--
Del-bound（方針C）の最終 API。

Proof idea (future, S5/S6):
  1) DR1/NEP から head v の唯一前提 `Pv` を抽出（S2 の choose_prem 系）。
  2) `Del v P.C` を `Hole(Del_base(P,v), Pv)` と同一視（del_as_hole）。
  3) `Qcorr(n-1, Pc, Pv.erase v)` と `corr_implies_hole_bound` で Hole の NDS を落とす。
  4) Hole=Del の同一視で結論へ。
-/
theorem Del_branch_bound_Pd
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack α)
  (v : α)
  (Pd : HypPack α)
  (hPdU : Pd.H.U = P.H.U.erase v)
  (hPdC : Pd.C = Del (α := α) v P.C)
  (A : Finset α)
  (hHoleEq : Pd.C = Hole (α := α) Pd.C A) :
  Qcorr (α := α) (n - 1) Pd A →
  NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0
:= by
  classical
  intro hQcorr

  -- Step 1: unfold Qcorr to get the corrected bound
  have hCorr :
      NDS_corr (α := α) (n - 1) Pd.C A ≤ 0 := by
    simpa [Qcorr] using hQcorr

  -- Step 2: drop the Up-term to get a Hole-bound
  have hHole :
      NDS (α := α) (n - 1) (Hole (α := α) Pd.C A) ≤ 0 :=
    corr_implies_hole_bound
      (α := α)
      (n := n - 1)
      (C := Pd.C)
      (A := A)
      hCorr

  -- Step 3: rewrite Hole Pd.C A back to Pd.C
  have hPd :
      NDS (α := α) (n - 1) Pd.C ≤ 0 := by
    exact le_of_eq_of_le (congrArg (NDS (n - 1)) hHoleEq) hHole


  -- Step 4: rewrite Pd.C to Del v P.C
  simpa [hPdC] using hPd

/--
Bridge lemma: derive the plain Del-bound from the branch-style API.

This is the first step toward eliminating the axiom `Del_bound`.
It uses:
  - representability of `con` via `choose_con_pack`
  - `Del_branch_bound`
and packages them into a direct bound on `Del v P.C`.
-/
theorem Del_bound_from_branch
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack α)
  (v : α)
  (hPrem : (P.H.prem v).Nonempty)
  (hQcorr :
    Qcorr (α := α)
      (n - 1)
      (choose_del_base_pack P v hPrem)
      ((pick_prem P v hPrem).erase v)
  ) :
  NDS (α := α) (n - 1) (Del v P.C) ≤ 0 :=
by
  classical
  let Pd :=
    choose_del_base_pack P v hPrem

  have hPdU :
      Pd.H.U = P.H.U.erase v :=
    choose_del_base_pack_spec_U (α := α) (P := P) (v := v) (hPrem := hPrem)

  have hPdC :
      Pd.C = Del (α := α) v P.C :=
    choose_del_base_pack_spec_C (α := α) (P := P) (v := v) (hPrem := hPrem)

  let Pv := pick_prem P v hPrem

  have hDel :=
    Del_branch_bound_Pd
      (α := α)
      (n := n)
      (hn := hn)
      (P := P)
      (v := v)
      (Pd := Pd)
      (hPdU := hPdU)
      (hPdC := hPdC)
      (A := Pv.erase v)
  -- supply the Hole-equality coming from del_as_hole
  have hHoleEq :
      Pd.C = Hole (α := α) Pd.C (Pv.erase v) :=
    choose_del_base_pack_spec_hole
      (α := α) (P := P) (v := v) (hPrem := hPrem)

  exact hDel hHoleEq hQcorr


/-/
-- Branch-only Del-bound (nonempty + card ≥ 2 route).
--
-- This version matches the S10 wiring:
--   - hPrem : prem v is nonempty
--   - hCard : 2 ≤ Pv.card
--   - hQ    : Q (n-1) P
--
-- Singleton / empty cases are handled upstream in S10.
-/
theorem Del_bound_of_Q
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack α)
  (v : α)
  (hPrem : (P.H.prem v).Nonempty)
  (hCard : 2 ≤ (pick_prem (α := α) P v hPrem).card)
  (hQ : Q (α := α) (n - 1) P) :
  NDS (α := α) (n - 1) (Del v P.C) ≤ 0 :=
by
  classical

  let Pd := choose_del_base_pack P v hPrem
  have hPdU :
      Pd.H.U = P.H.U.erase v :=
    choose_del_base_pack_spec_U (α := α) (P := P) (v := v) (hPrem := hPrem)

  have hPdC :
      Pd.C = Del (α := α) v P.C :=
    choose_del_base_pack_spec_C (α := α) (P := P) (v := v) (hPrem := hPrem)

  -- supply Qcorr on the deletion-world pack
  have hQcorrPd :=
    prem_erase_Qcorr_ge2_Pd
      (α := α)
      (n := n)
      (hn := hn)
      (P := P)
      (v := v)
      (hPrem := hPrem)
      (hCard := hCard)
      (Pd := Pd)
      (hPdU := hPdU)
      (hPdC := hPdC)

  -- conclude via the branch API
  exact
    Del_bound_from_branch
      (α := α)
      (n := n)
      (hn := hn)
      (P := P)
      (v := v)
      (hPrem := hPrem)
      hQcorrPd


/- ============================================================
  (E) Forbid helpers / small finset lemmas
============================================================ -/

/-- Choose an element of `A` from `ForbidOK P A` (uses `A.Nonempty`). -/
theorem choose_v_in_A
  (P : HypPack α) (A : Finset α) :
  ForbidOK (α := α) P A → ∃ v : α, v ∈ A := by
  intro hOK
  have hne : A.Nonempty := ForbidOK.nonempty (α := α) (P := P) (A := A) hOK
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, hv⟩

/-- Noncomputably pick an element `v ∈ A` from `ForbidOK P A`. -/
noncomputable def pick_v_in_A
  (P : HypPack α) (A : Finset α) (hOK : ForbidOK (α := α) P A) : α :=
  Classical.choose (choose_v_in_A (α := α) (P := P) (A := A) hOK)

@[simp] theorem pick_v_in_A_mem
  (P : HypPack α) (A : Finset α) (hOK : ForbidOK (α := α) P A) :
  pick_v_in_A (α := α) P A hOK ∈ A :=
  Classical.choose_spec (choose_v_in_A (α := α) (P := P) (A := A) hOK)

/-- From `ForbidOK` we can always extract `A.Nonempty` (helper for case splits). -/
theorem forbidOK_nonempty (P : HypPack α) (A : Finset α) :
    ForbidOK (α := α) P A → A.Nonempty := by
  intro h
  exact (ForbidOK.nonempty (α := α) (P := P) (A := A) h)

/-- Case split helper for `A.erase v`: either empty or nonempty. -/
theorem erase_empty_or_nonempty
  (A : Finset α) (v : α) : v ∈ A → ((A.erase v) = ∅ ∨ (A.erase v).Nonempty) := by
  intro _hv
  classical
  by_cases h : A.erase v = ∅
  · exact Or.inl h
  · exact Or.inr (Finset.nonempty_iff_ne_empty.2 h)


/- ============================================================
  (F) Legacy / expected-to-be-removed axioms
============================================================ -/

/--
====================
削除予定（cleanup）
====================

- `Del_hole_bound`, `ndeg_hole_le_zero_of_choice`：方針Cが `Del_branch_bound` に集約できたら削除候補。

S11 は「呼び出し口の安定」が最優先なので、削除は S10/S9 が落ちないことを確認してから行う。
-/


/-
(LEGACY)
Del-hole bound used in the Del-bound step.

(Intended proof location)
S5/S6 (Del-world representability + sign bookkeeping).
-/
axiom Del_hole_bound
  (n : Nat) (P : HypPack α) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A → v ∈ A →
  NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A)) ≤ 0

/--
(LEGACY)
Bound on `ndeg` for hole families at the chosen vertex.

(Intended proof location)
S5/S6 (Del-world representability + sign bookkeeping).
-/
axiom ndeg_hole_le_zero_of_choice
  (n : Nat) (P : HypPack α) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A → v ∈ A →
  ndeg (α := α) (Hole (α := α) P.C A) v ≤ 0

end Dr1nds
