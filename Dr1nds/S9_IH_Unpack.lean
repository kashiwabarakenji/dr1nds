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
axiom Q_con
  (n : Nat) (P : HypPack (α := α)) (v : α) :
  Q (α := α) (n - 1) P →
  NDS (α := α) (n - 1) (con (α := α) v P.C) ≤ 0

/-- Compatibility name used by older skeletons (e.g. S11). -/
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
  rcases hOK with ⟨hAU, hAcard⟩
  -- ForbidOK は `2 ≤ A.card` を仮定しているので、`v ∈ A` から `A.erase v` は非空。
  have hlt : 1 < A.card := lt_of_lt_of_le (by decide : 1 < 2) hAcard
  have hpos : 0 < A.card - 1 := Nat.sub_pos_of_lt hlt
  have hpos' : 0 < (A.erase v).card := by
    simpa [Finset.card_erase_of_mem hv] using hpos
  exact Finset.card_pos.1 hpos'

end Dr1nds
