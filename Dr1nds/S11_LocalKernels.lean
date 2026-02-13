-- Dr1nds/S11_LocalKernels.lean
import Mathlib.Data.Int.Basic
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
- `choose_prem_of_hasHead` / `prem_contains_head_choice`

### (S5/S6) Del-bound（方針C）
- 推奨 API は `Del_branch_bound`。
  `Qcorr(n-1, Pc, Pv.erase v)` から `NDS(Del v P.C) ≤ 0` を出す、という形に固定してある。

## レガシー（削除予定）
- `Qcorr_case1_singleton`：`ForbidOK` を `2 ≤ A.card` に凍結している限り singleton 分岐は起きない。
  まだ S10 側に古い分岐が残る場合だけの互換用。最終的に削除する。

※注意：このファイルは **S10_Steps を import しない**（循環依存回避）。
-/


/- ============================================================
  (A) Proven arithmetic/definition lemmas
============================================================ -/

/-- Up-cardinality is always nonnegative (as an Int). -/
lemma Up_card_nonneg
  (C : Finset (Finset α)) (A : Finset α) :
  (0 : Int) ≤ (Up (α := α) C A).card := by
  -- `card` is a Nat; its coercion to Int is nonnegative.
  simpa using Int.ofNat_nonneg (Up (α := α) C A).card

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
  -- unfold both sides to `filter`
  unfold Del Hole
  -- it suffices to show the predicates coincide pointwise
  apply Finset.ext
  intro X
  simp [Finset.mem_filter]

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
  (n : Nat) (P : HypPack (α := α)) :
  ∃ v : α, ndeg (α := α) P.C v ≤ 0

/-- Noncomputably pick a good vertex from `exists_good_v_for_Q`. -/
noncomputable def choose_good_v_for_Q
  (n : Nat) (P : HypPack (α := α)) : α :=
  Classical.choose (exists_good_v_for_Q (α := α) n P)

@[simp] theorem choose_good_v_for_Q_spec
  (n : Nat) (P : HypPack (α := α)) :
  ndeg (α := α) P.C (choose_good_v_for_Q (α := α) n P) ≤ 0 :=
  Classical.choose_spec (exists_good_v_for_Q (α := α) n P)


/- ============================================================
  (C) Representability for IH targets (con-pack / del-pack)
============================================================ -/

-- NOTE: exists_con_pack は S8_Statements.lean 側で定義済み。S11 で再定義すると衝突するので、ここでは S8 のものを利用する。

/-- Noncomputably choose a con-pack. -/
noncomputable def choose_con_pack
  (P : HypPack (α := α)) (v : α) : HypPack (α := α) :=
  Classical.choose (exists_con_pack (α := α) (P := P) (v := v))

/-- Spec lemma: the chosen pack enumerates `con v P.C`. -/
@[simp] theorem choose_con_pack_C
  (P : HypPack (α := α)) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).C = con (α := α) v P.C := by
  -- `exists_con_pack` now returns both universe compatibility and the family equality.
  -- We only need the `.C` component here.
  exact (Classical.choose_spec (exists_con_pack (α := α) (P := P) (v := v))).2

/-- Alias simp-lemma (kept for backward compatibility with earlier S10 code). -/
@[simp] theorem choose_con_pack_C'
  (P : HypPack (α := α)) (v : α) :
  (choose_con_pack (α := α) (P := P) (v := v)).C = con (α := α) v P.C := by
  simpa using (choose_con_pack_C (α := α) (P := P) (v := v))

/--
(Purpose)
S10 の con-branch を抑えるための「配線用」補題。

ポイント：これは重い核ではなく、S9 側にある `IH_Q_gives_con_bound`（= con-family へ IH を当てるための公理/補題）
から **ただちに導ける** ので、S11 では axiom にせず theorem として固定する。

注意：ここで `Pc` は representability により供給された pack で、家族の等式 `hPcC` により
`Pc.C` を `con v P.C` に書き換えて閉じる。
-/
theorem IH_Q_gives_con_bound_pack
  (n : Nat) (P : HypPack (α := α)) (v : α)
  (Pc : HypPack (α := α)) (hPcC : Pc.C = con (α := α) v P.C) :
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
  (n : Nat) (P : HypPack (α := α)) (v : α)
  (Pc : HypPack (α := α)) (hPcC : Pc.C = con (α := α) v P.C) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) Pc.C ≤ 0 :=
by
  intro hQ
  exact IH_Q_gives_con_bound_pack (α := α) (n := n) (P := P) (v := v) (Pc := Pc) hPcC hQ

/- ============================================================
  (D) Del-bound kernels (C-route via Qcorr)
============================================================ -/

/-
  (Normal Del-bound for Q_step)

  Used in S10.Q_step.
  This is the non-forbid version:
    Q(n-1,P) ⇒ NDS(n-1)(Del v P.C) ≤ 0.

  This will later be proved via the Del-as-Hole route
  and Qcorr induction, but for wiring we freeze it here.
  -/

axiom Del_bound
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α))
  (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (Del v P.C) ≤ 0

/--
Wrapper lemma for the plain Del-bound.

This is currently just a thin layer over the axiom `Del_bound`,
but it gives S10 (and future refactors) a stable theorem name
that can later be reimplemented via `Del_bound_from_branch`
without changing call sites.
-/
theorem Del_bound_of_Q
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α))
  (v : α)
  (hQ : Q (α := α) (n - 1) P) :
  NDS (α := α) (n - 1) (Del v P.C) ≤ 0 :=
by
  exact Del_bound (α := α) (n := n) (hn := hn) (P := P) (v := v) hQ

/--
(Purpose)
DR1 implies `prem v` has at most one element; when it is nonempty we can pick the unique premise.
S10 uses this to extract the premise for the Del-branch.

(Intended proof location)
S2_HornNF or S1_HornNF (premise choice facts).
-/
axiom choose_prem_of_hasHead
  (P : HypPack (α := α)) (v : α) :
  (P.H.prem v).Nonempty →
  { Pv : Finset α // Pv ∈ P.H.prem v }

/--
(Optional strengthening)
選ばれた `Pv` が head `v` を含む、という形を後で使いたい場合の補助。
-/
axiom prem_contains_head_choice
  (P : HypPack (α := α)) (v : α)
  (h : (P.H.prem v).Nonempty) :
  let Pv := (choose_prem_of_hasHead (α := α) (P := P) (v := v) h).1
  v ∈ Pv

/-- Noncomputably pick `Pv` from `prem v` when nonempty. -/
noncomputable def pick_prem
  (P : HypPack (α := α)) (v : α) (h : (P.H.prem v).Nonempty) : Finset α :=
  (choose_prem_of_hasHead (α := α) (P := P) (v := v) h).1

@[simp] theorem pick_prem_mem
  (P : HypPack (α := α)) (v : α) (h : (P.H.prem v).Nonempty) :
  pick_prem (α := α) P v h ∈ P.H.prem v :=
  (choose_prem_of_hasHead (α := α) (P := P) (v := v) h).2

@[simp] theorem pick_prem_contains_head
  (P : HypPack (α := α)) (v : α) (h : (P.H.prem v).Nonempty) :
  v ∈ pick_prem (α := α) P v h := by
  simpa [pick_prem] using (prem_contains_head_choice (α := α) (P := P) (v := v) h)

/--
(New primary Del-as-Hole API — preferred over `exists_del_base_pack` / `del_as_hole`.)

Canonical Del-as-Hole formulation (moved here so that `pick_prem` is already defined).
-/
axiom del_eq_hole
  (P : HypPack (α := α))
  (v : α)
  (h : (P.H.prem v).Nonempty) :
  Del v P.C
    =
  Hole P.C
    (pick_prem P v h)

/--
Del-bound（方針C）の最終 API。

Proof idea (future, S5/S6):
  1) DR1/NEP から head v の唯一前提 `Pv` を抽出（S2 の choose_prem 系）。
  2) `Del v P.C` を `Hole(Del_base(P,v), Pv)` と同一視（del_as_hole）。
  3) `Qcorr(n-1, Pc, Pv.erase v)` と `corr_implies_hole_bound` で Hole の NDS を落とす。
  4) Hole=Del の同一視で結論へ。
-/
axiom Del_branch_bound
  (n : Nat) (hn : 1 ≤ n)
  (P : HypPack (α := α))
  (v : α)
  (Pc : HypPack (α := α))
  (hPcC : Pc.C = con (α := α) v P.C)
  (Pv : Finset α) :
  (v ∈ Pv) →
  Qcorr (α := α) (n - 1) Pc (Pv.erase v) →
  NDS (α := α) (n - 1) (Del (α := α) v P.C) ≤ 0

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
  (P : HypPack (α := α))
  (v : α)
  (hPrem : (P.H.prem v).Nonempty)
  (hQprev : Q (α := α) (n - 1) P)
  (hQcorr :
    Qcorr (α := α)
      (n - 1)
      (choose_con_pack (α := α) (P := P) (v := v))
      ((pick_prem (α := α) P v hPrem).erase v)
  ) :
  NDS (α := α) (n - 1) (Del v P.C) ≤ 0 :=
by
  classical
  -- representability: Pc enumerates con v P.C
  let Pc :=
    choose_con_pack (α := α) (P := P) (v := v)
  have hPcC :
      Pc.C = con (α := α) v P.C :=
    choose_con_pack_C (α := α) (P := P) (v := v)

  -- extract Pv from prem
  let Pv := pick_prem (α := α) P v hPrem
  have hvPv : v ∈ Pv :=
    pick_prem_contains_head (α := α) (P := P) (v := v) hPrem

  -- apply branch-style Del bound
  have hDel :=
    Del_branch_bound
      (α := α)
      (n := n)
      (hn := hn)
      (P := P)
      (v := v)
      (Pc := Pc)
      (hPcC := hPcC)
      (Pv := Pv)
      hvPv
      hQcorr

  exact hDel


/- ============================================================
  (E) Forbid helpers / small finset lemmas
============================================================ -/

/-- Choose an element of `A` from `ForbidOK P A` (uses `A.Nonempty`). -/
theorem choose_v_in_A
  (P : HypPack (α := α)) (A : Finset α) :
  ForbidOK (α := α) P A → ∃ v : α, v ∈ A := by
  intro hOK
  have hne : A.Nonempty := ForbidOK.nonempty (α := α) (P := P) (A := A) hOK
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, hv⟩

/-- Noncomputably pick an element `v ∈ A` from `ForbidOK P A`. -/
noncomputable def pick_v_in_A
  (P : HypPack (α := α)) (A : Finset α) (hOK : ForbidOK (α := α) P A) : α :=
  Classical.choose (choose_v_in_A (α := α) (P := P) (A := A) hOK)

@[simp] theorem pick_v_in_A_mem
  (P : HypPack (α := α)) (A : Finset α) (hOK : ForbidOK (α := α) P A) :
  pick_v_in_A (α := α) P A hOK ∈ A :=
  Classical.choose_spec (choose_v_in_A (α := α) (P := P) (A := A) hOK)

/-- From `ForbidOK` we can always extract `A.Nonempty` (helper for case splits). -/
theorem forbidOK_nonempty (P : HypPack (α := α)) (A : Finset α) :
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
(LEGACY)
ForbidOK を `2 ≤ A.card` に凍結している限り singleton 分岐は本来起きない。
S10 側に古い分岐が残る場合だけの互換用。最終的に削除する。
-/
axiom Qcorr_case1_singleton
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A → v ∈ A → (A.erase v) = ∅ →
  NDS_corr (α := α) n P.C A ≤ 0

/--
(LEGACY)
Del-hole bound used in the Del-bound step.

(Intended proof location)
S5/S6 (Del-world representability + sign bookkeeping).
-/
axiom Del_hole_bound
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A → v ∈ A →
  NDS (α := α) (n - 1) (Del (α := α) v (Hole (α := α) P.C A)) ≤ 0

/--
(LEGACY)
Bound on `ndeg` for hole families at the chosen vertex.

(Intended proof location)
S5/S6 (Del-world representability + sign bookkeeping).
-/
axiom ndeg_hole_le_zero_of_choice
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A → v ∈ A →
  ndeg (α := α) (Hole (α := α) P.C A) v ≤ 0

end Dr1nds
