-- Dr1nds/S9_IH_Unpack.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Dr1nds.S0_CoreDefs
import Dr1nds.S8_Statements

namespace Dr1nds

open scoped BigOperators
variable {α : Type} [DecidableEq α]
set_option linter.deprecated false

/- ============================================================
  S9 : IH unpack / bridge (SKELETON, FROZEN)

  本ファイルは暫定的な「IH ブリッジAPI」層として機能する。
  目的は、S10/S11 の骨格で必要になる IH の呼び出し口だけを固定し、
  実際の pack 構成（HypPack の縮小版を構成し、Q や Qcorr を適用する証明）を後回しにすることにある。

  最終的には、以下のように axioms を排除することを目指す：
    - con の場合は、P から P_con : HypPack を構成し、P_con.C = con v P.C となるようにする。
    - forbid 付きの場合（corr）は、P から Pcorr_con : HypPack を構成し、宇宙は P.U.erase v、forbid 集合は A.erase v とする。
    - これらの HypPack に対して Q や Qcorr を適用し、必要な不等式を証明する。

  依存関係としては、
    - S10_Steps はこのブリッジAPIのみに依存し、axioms に直接依存しないこと。
    - S11_LocalKernels はこの axioms を直接使わず、より具体的な pack の構成を使うこと。

  代表的な構成課題：
    - P_con : HypPack を作り、P_con.C = con v P.C となることを示す。
    - Pcorr_con : HypPack を作り、forbid 設定付きで同様の関係を示す。

============================================================ -/

/--
TODO: Q_con の代わりに以下のような補題を証明することを目指す。

  lemma exists_con_pack
    (n : Nat) (P : HypPack) (v : α) :
    ∃ Pcon : HypPack, Pcon.IsNEP ∧ Pcon.C = con v P.C ∧ Pcon.U < P.U

  lemma Q_to_con_bound
    (n : Nat) (P : HypPack) (v : α) :
    Q (n - 1) Pcon → NDS (n - 1) (con v P.C) ≤ 0

証明方針：
  - con v P.C に対応する小さな universe の pack Pcon を構成し、
  - Pcon の IsNEP（または Q で使われる family-NEP 性質）を証明し、
  - Q (n-1) Pcon を仮定して結論を導く。

現在は、pack 構成や transport を省略し、axiom として固定している。

-/
/-
(LEGACY)
This axiom is kept only for backward compatibility with older S10 wiring.
Prefer `con_bound_of_IH_all` / `con_bound_of_IH_all_pack` (∀P-style IH) below.
-/
@[deprecated "Use con_bound_of_IH_all (or con_bound_of_IH_all_pack) with ∀P-style IH instead."]
axiom Q_con
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0

/-- Compatibility name used by older skeletons (e.g. S11). -/
/-
(LEGACY)
Compatibility wrapper around `Q_con`.
Prefer `con_bound_of_IH_all` once S10 is fully switched to the ∀P-style IH.
-/
@[deprecated "Use con_bound_of_IH_all (or con_bound_of_IH_all_pack) with ∀P-style IH instead."]
theorem IH_Q_gives_con_bound
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0 :=
by
  intro ih
  exact Q_con (α := α) n P v ih


/--
TODO: Qcorr_con_case2 の代わりに以下のような補題を証明することを目指す。

  lemma exists_corr_con_pack
    (n : Nat) (P : HypPack) (A : Finset α) (v : α)
    (hv : v ∈ A) (hne : (A.erase v).Nonempty) :
    ∃ Pcorr_con : HypPack,
      Pcorr_con.IsNEP ∧
      Pcorr_con.U = P.U.erase v ∧
      Pcorr_con.forbid_set = A.erase v ∧
      ...

  lemma Qcorr_to_con_bound_case2
    (n : Nat) (P : HypPack) (A : Finset α) (v : α)
    (hv : v ∈ A) (hne : (A.erase v).Nonempty) :
    Q (n - 1) Pcorr_con →
    NDS_corr (n - 1) (con v P.C) (A.erase v) ≤ 0

証明方針：
  - forbid 側の pack を構成し、forbid 設定を A.erase v に変更し、
  - その pack に対して Qcorr を適用し、
  - IH は bundled な形（Q ∧ ∀A, ForbidOK → Qcorr）を仮定する形にする予定。

現状は axioms として固定し、pack 構成や bundled IH は後回しにしている。

-/
/-
(LEGACY)
This axiom is kept only for backward compatibility with older S10 wiring.
Once a corr-con representability lemma is in place, replace uses by a ∀P-style proof.
-/
@[deprecated "Legacy bridge. Replace by a ∀P-style corr-con bound once representability is formalized."]
axiom Qcorr_con_case2
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  Q (α := α) (n - 1) P →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1) (con (α := α) v P.C) (A.erase v) ≤ 0


/--
IH を引数に取る版（S8 側の `IH_corr_con_pack` から呼ばれる想定）。

この層ではまだ pack 構成をしていないため、結局は `Qcorr_con_case2`（暫定 axiom）を呼ぶだけ。
将来的には `Qcorr_con_case2` を排除し、この定理の本体で
"con に対応する forbid-pack を構成して Qcorr を適用する" 形に置換する。
-/
/-
(LEGACY)
Compatibility wrapper around `Qcorr_con_case2`.
-/
@[deprecated "Legacy bridge. Replace by a ∀P-style corr-con bound once representability is formalized."]
theorem IH_corr_con_pack
  (n : Nat) (P : HypPack (α := α)) (A : Finset α) (v : α) :
  IH (α := α) (n - 1) P →
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1)
    (con (α := α) v P.C)
    (A.erase v) ≤ 0 :=
by
  intro hIH hv hne
  -- bundled IH の通常側 Q だけを取り出して、暫定 axiom に流す
  have hQ : Q (α := α) (n - 1) P := hIH.1
  exact Qcorr_con_case2 (α := α) n P A v hQ hv hne


/--
Preferred (stable) name for the corr-con bound obtained from a ∀P-style IH.

NOTE: At the moment this is still proved via the legacy axiom `Qcorr_con_case2`.
Once corr-con representability is formalized, this theorem should be updated to
avoid `Qcorr_con_case2` without changing its statement.
-/
theorem corr_con_bound_of_IH_all
  (n : Nat)
  (ihAll : ∀ P : HypPack (α := α), IH (α := α) (n - 1) P)
  (P : HypPack (α := α)) (A : Finset α) (v : α) :
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1)
    (con (α := α) v P.C)
    (A.erase v) ≤ 0 :=
by
  intro hv hne
  have hQ : Q (α := α) (n - 1) P := (ihAll P).1
  exact Qcorr_con_case2 (α := α) n P A v hQ hv hne

/--
Pack-level variant of `corr_con_bound_of_IH_all`.

This lets later wiring keep a locally-chosen representable pack `Pc` and rewrite via `hPcC`.
At the moment it still relies on the legacy axiom `Qcorr_con_case2` through
`corr_con_bound_of_IH_all`.
-/
theorem corr_con_bound_of_IH_all_pack
  (n : Nat)
  (ihAll : ∀ P : HypPack (α := α), IH (α := α) (n - 1) P)
  (P : HypPack (α := α)) (A : Finset α) (v : α)
  (Pc : HypPack (α := α)) (hPcC : Pc.C = con (α := α) v P.C) :
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1) Pc.C (A.erase v) ≤ 0 :=
by
  intro hv hne
  have hcon : NDS_corr (α := α) (n - 1)
      (con (α := α) v P.C) (A.erase v) ≤ 0 :=
    corr_con_bound_of_IH_all (α := α) (n := n) (ihAll := ihAll) (P := P) (A := A) (v := v) hv hne
  simpa [hPcC] using hcon

/-- A convenience alias: same conclusion as `corr_con_bound_of_IH_all_pack`, but without keeping `Pc` in the goal. -/
theorem corr_con_bound_of_IH_all'
  (n : Nat)
  (ihAll : ∀ P : HypPack (α := α), IH (α := α) (n - 1) P)
  (P : HypPack (α := α)) (A : Finset α) (v : α)
  (Pc : HypPack (α := α)) (hPcC : Pc.C = con (α := α) v P.C) :
  v ∈ A →
  (A.erase v).Nonempty →
  NDS_corr (α := α) (n - 1) (con (α := α) v P.C) (A.erase v) ≤ 0 :=
by
  intro hv hne
  -- rewrite the pack bound back to the concrete family
  have hPc : NDS_corr (α := α) (n - 1) Pc.C (A.erase v) ≤ 0 :=
    corr_con_bound_of_IH_all_pack (α := α) (n := n) (ihAll := ihAll)
      (P := P) (A := A) (v := v) (Pc := Pc) hPcC hv hne
  simpa [hPcC] using hPc

/--
`ForbidOK P A := A ⊆ P.H.U ∧ 2 ≤ A.card` のもとで、`v ∈ A` なら `A.erase v` は非空。

※ `ForbidOK` の定義を今後さらに調整する場合（例えば追加条件を入れる等）は、
この補題もそれに合わせて見直す。
-/
theorem forbidOK_erase_nonempty
  (P : HypPack (α := α)) (A : Finset α) (v : α) :
  ForbidOK (α := α) P A →
  v ∈ A →
  (A.erase v).Nonempty := by
  classical
  intro hOK hv
  rcases hOK with ⟨_hAU, hAcard⟩
  -- ForbidOK は `2 ≤ A.card` を仮定しているので、`v ∈ A` から `A.erase v` は非空。
  have hlt : 1 < A.card := lt_of_lt_of_le (Nat.one_lt_two) hAcard
  have hpos : 0 < A.card - 1 := Nat.sub_pos_of_lt hlt
  have hpos' : 0 < (A.erase v).card := by
    simpa [Finset.card_erase_of_mem hv] using hpos
  exact Finset.card_pos.1 hpos'

/-- Unpack `Q n P` into the concrete NDS bound on `P.C`.
    This isolates the definitional dependency on how `Q` is defined in `S8_Statements`. -/
theorem Q_implies_NDS
  (n : Nat) (P : HypPack (α := α)) :
  Q (α := α) n P → NDS (α := α) n P.C ≤ 0 := by
  intro hQ
  simpa [Q] using hQ

/- ============================================================
  NOTE (migration status)

  After the S9_InductionSkeleton refactor (IH as `∀ P, IH (n-1) P`), the preferred
  way to obtain con-branch bounds is `con_bound_of_IH_all` below.

  The older bridge axioms
    * `Q_con` / `IH_Q_gives_con_bound`
    * `Qcorr_con_case2` / `IH_corr_con_pack`
  are kept temporarily for backward compatibility with older S10 wiring.
  Once S10 is fully switched to the ∀P-style IH, these legacy axioms should be
  removed and their uses replaced by the ∀P-style lemmas.
============================================================ -/

/- ============================================================
  NEW (post-refactor helper): using ∀ P-style IH

  After the S9_InductionSkeleton refactor, the main IH is obtained as

    ihAll : ∀ P, IH (n-1) P

  Then con-branch bounds can be obtained *without* a dedicated transport axiom:
  we pick a representable con-pack `Pc` using `exists_con_pack` (from S8),
  apply `ihAll Pc`, and rewrite via `Pc.C = con v P.C`.

  NOTE: We keep the legacy axiom `Q_con` / theorem `IH_Q_gives_con_bound` for
  backward compatibility with older S10 wiring. The lemma below is the
  preferred replacement once S10 is switched to the ∀P-style IH.
============================================================ -/

/--
Pack-level con-branch bound: same as `con_bound_of_IH_all_pack`, but returns the inequality on `Pc.C`
without rewriting. This is convenient for S11-style local representability where `Pc` is already in hand.
-/
theorem con_pack_bound_of_IH_all
  (n : Nat)
  (ihAll : ∀ P : HypPack (α := α), IH (α := α) (n - 1) P)
  (Pc : HypPack (α := α)) :
  NDS (α := α) (n - 1) Pc.C ≤ 0
:= by
  have hQPc : Q (α := α) (n - 1) Pc := (ihAll Pc).1
  exact Q_implies_NDS (α := α) (n := n - 1) (P := Pc) hQPc

/--
Preferred con-branch bound (pack form): once IH is available as `∀ P, IH (n-1) P`,
we can apply IH to any representable con-pack `Pc` and rewrite back.

This is the form that S11 can use to keep all noncomputable choices local.
-/
theorem con_bound_of_IH_all_pack
  (n : Nat)
  (ihAll : ∀ P : HypPack (α := α), IH (α := α) (n - 1) P)
  (P : HypPack (α := α)) (v : α)
  (Pc : HypPack (α := α)) (hPcC : Pc.C = con (α := α) v P.C) :
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0
:= by
  have hPcCnd : NDS (α := α) (n - 1) Pc.C ≤ 0 :=
    con_pack_bound_of_IH_all (α := α) (n := n) (ihAll := ihAll) (Pc := Pc)
  simpa [hPcC] using hPcCnd

/--
If two packs enumerate the same `con v P.C`, then their `.C` fields are equal.

This is a small rewiring helper: in S10/S11 you sometimes have a locally named pack `Pc`
(and separately `choose_con_pack P v`) and want to identify their families without changing
any surrounding code.
-/
theorem eq_C_of_eq_con
  (P : HypPack (α := α)) (v : α)
  (Pc Pc' : HypPack (α := α))
  (hPc  : Pc.C  = con (α := α) v P.C)
  (hPc' : Pc'.C = con (α := α) v P.C) :
  Pc.C = Pc'.C := by
  simpa [hPc, hPc']

/-- Pack-form con-bound derived directly from a ∀P-style IH and a con-pack existence proof. -/
theorem con_bound_of_IH_all_via_choose
  (n : Nat)
  (ihAll : ∀ P : HypPack (α := α), IH (α := α) (n - 1) P)
  (P : HypPack (α := α)) (v : α) :
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0
:= by
  classical
  -- Choose a representable con-pack `Pc`.
  set Pc : HypPack (α := α) :=
    Classical.choose (exists_con_pack (α := α) (P := P) (v := v)) with hPc
  -- Extract the family equality from the chosen witness.
  have hPcC : Pc.C = con (α := α) v P.C := by
    have hspec := Classical.choose_spec (exists_con_pack (α := α) (P := P) (v := v))
    -- `hspec` may contain additional bookkeeping (e.g. universe compatibility) as the first component;
    -- we only rely on the family equality component.
    -- The `set`-binder `hPc` lets us rewrite the `choose`d witness into `Pc`.
    simpa [hPc] using hspec.2
  exact
    con_bound_of_IH_all_pack (α := α)
      (n := n) (ihAll := ihAll) (P := P) (v := v) (Pc := Pc) hPcC

/-- Preferred con-branch bound once IH is available as `∀ P, IH (n-1) P`. -/
theorem con_bound_of_IH_all
  (n : Nat)
  (ihAll : ∀ P : HypPack (α := α), IH (α := α) (n - 1) P)
  (P : HypPack (α := α)) (v : α) :
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0
:= by
  exact con_bound_of_IH_all_via_choose (α := α) (n := n) (ihAll := ihAll) (P := P) (v := v)

/-- Convenience: extract the `Q` part from a ∀P-style IH. -/
theorem Q_of_IH_all
  (n : Nat)
  (ihAll : ∀ P : HypPack (α := α), IH (α := α) (n - 1) P)
  (P : HypPack (α := α)) :
  Q (α := α) (n - 1) P :=
by
  simpa using (ihAll P).1

end Dr1nds
