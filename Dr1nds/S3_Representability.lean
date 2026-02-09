-- Dr1nds/S3_Representability.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

import Dr1nds.S2_Horn
import Dr1nds.S1_Families
import Dr1nds.Core   -- HornNF / IsClosed / FixFamily を使うなら

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-!
S3_Representability.lean

目的（いまの段階での“最小の凍結”）：
1) Horn(rules : Finset (Finset α × α)) から
   「head ごとの premise 集合」 premSet : α → Finset (Finset α)
   を取り出すユーティリティを確定する。
2) DR1 の下で premise を Option で取り出す premOpt を用意する
   （あなたが以前遭遇した `Decidable (HasHead ...)` 問題をここで解消）。
3) （任意）Horn(NF) → HornNF への変換の骨格を置く。
   ※ Fix / representability そのものは S9 側で詰めればよいので、
      ここでは「道具立て（premSet/premOpt/基本補題）」を固める。
-/

namespace Horn

/- 「head=h の規則が存在する」 -/
--def HasHead (H : Horn α) (h : α) : Prop :=
--  ∃ P : Finset α, (P, h) ∈ H.rules

/--
`HasHead` は Finset 上の存在なので決定可能。
（これで `if hh : HasHead H h then ...` が通る）
-/
noncomputable instance (H : Horn α) (h : α) : Decidable (HasHead (α := α) H h) := by
  classical
  -- `∃ P, (P,h) ∈ H.rules` は Finset に対する decidable exists に落とせる
  -- （`simp` が最短）
  unfold HasHead
  infer_instance

/--
head=h の premise 全体を「Finset として」取り出す。
`premSet H h = { P | (P,h)∈rules }`
-/
def premSet (H : Horn α) (h : α) : Finset (Finset α) :=
  (H.rules.filter (fun r => r.2 = h)).image Prod.fst

@[simp] lemma mem_premSet_iff (H : Horn α) (h : α) (P : Finset α) :
    P ∈ premSet (α := α) H h ↔ (P, h) ∈ H.rules := by
  classical
  -- `image` のメンバシップを分解
  constructor
  · intro hP
    rcases Finset.mem_image.1 hP with ⟨r, hr, rfl⟩
    rcases Finset.mem_filter.1 hr with ⟨hrules, rh⟩
    -- r = (P,h) という形を取り出す
    -- r.2 = h なので (Prod.fst r, h) = r
    cases r with
    | mk P' h' =>
      -- ここで rh : h' = h
      simp at rh
      subst rh
      simpa using hrules
  · intro hPH
    -- (P,h) ∈ rules なら、filter に入り、その fst が image に入る
    have : (P, h) ∈ H.rules.filter (fun r => r.2 = h) := by
      exact Finset.mem_filter.2 ⟨hPH, by simp⟩
    exact Finset.mem_image.2 ⟨(P, h), this, rfl⟩

/-- `HasHead` と `premSet` の対応。 -/
lemma hasHead_iff_nonempty_premSet (H : Horn α) (h : α) :
    HasHead (α := α) H h ↔ (premSet (α := α) H h).Nonempty := by
  classical
  constructor
  · intro hh
    rcases hh with ⟨P, hPH⟩
    refine ⟨P, ?_⟩
    exact (mem_premSet_iff (α := α) H h P).2 hPH
  · intro hn
    rcases hn with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    exact (mem_premSet_iff (α := α) H h P).1 hP

/--
DR1 のとき premSet は高々 1 要素。
（S9 で `premOpt` を作るときに便利）
-/
lemma card_premSet_le_one_of_DR1 (H : Horn α) (h : α) (hDR1 : DR1 (α := α) H) :
    (premSet (α := α) H h).card ≤ 1 := by
  classical
  -- 2つ入ったら DR1 で一致するので、card ≤ 1
  -- `Finset.card_le_one` を使うのが定番
  refine Finset.card_le_one.2 ?_
  intro P1 hP1 P2 hP2
  have h1 : (P1, h) ∈ H.rules := (mem_premSet_iff (α := α) H h P1).1 hP1
  have h2 : (P2, h) ∈ H.rules := (mem_premSet_iff (α := α) H h P2).1 hP2
  exact hDR1 h1 h2

/-
head=h の premise を（DR1 の下で）Optionで取り出す。
存在すれば `some P`、存在しなければ `none`。

※以前のエラー
  `failed to synthesize Decidable (H.HasHead h)`
は、上の `instance Decidable (HasHead H h)` で解消。
-/
/-
noncomputable def premOpt (H : Horn α) (h : α) : Option (Finset α) :=
  if hh : HasHead (α := α) H h then
    some (Classical.choose hh)
  else
    none
-/

/-- `premOpt = some P` なら (P,h) が rules にある。 -/
lemma premOpt_spec_some (H : Horn α) (h : α) (P : Finset α)
    (hSome : premOpt (α := α) H h = some P) :
    (P, h) ∈ H.rules := by
  classical
  unfold premOpt at hSome
  split_ifs at hSome with hh
  · -- some (choose hh) = some P
    have : Classical.choose hh = P := by
      simp_all only [Option.some.injEq]
    subst this
    exact Classical.choose_spec hh

/-- (P,h) が rules にあり DR1 なら premOpt = some P。 -/
lemma premOpt_eq_some_of_mem_of_DR1
    (H : Horn α) (h : α) (P : Finset α)
    (hPH : (P, h) ∈ H.rules) (hDR1 : DR1 (α := α) H) :
    premOpt (α := α) H h = some P := by
  classical
  unfold premOpt
  have hh : HasHead (α := α) H h := ⟨P, hPH⟩
  -- if-branch に入る
  simp [hh]
  -- choose hh と P が一致することを DR1 で示す
  have hchoose : Classical.choose hh = P := by
    -- choose hh は何らかの P0 で (P0,h)∈rules を満たす
    have h0 : (Classical.choose hh, h) ∈ H.rules := Classical.choose_spec hh
    exact hDR1 h0 hPH
  simp [hchoose]

/- ============================================================
  （任意）Horn → HornNF への変換の骨格
============================================================ -/

/--
Horn の rules から HornNF（head↦premise集合）を作る。
NF は Horn.NF を仮定して移す。
-/
noncomputable def toHornNF (H : Horn α) (hNF : NF (α := α) H) : HornNF α := by
  classical
  refine
    { prem := fun h => premSet (α := α) H h
      nf := ?_ }
  intro h P hPmem
  -- P ∈ premSet H h → (P,h)∈rules → NFより h∉P
  have hPH : (P, h) ∈ H.rules := (mem_premSet_iff (α := α) H h P).1 hPmem
  exact hNF hPH

/--
DR1 が HornNF.IsDR1（prem h の card ≤ 1）に落ちる、という形の補題。
（Core 側 prem: α → Finset(Finset α) を使う場合の橋）
-/
lemma toHornNF_isDR1_of_DR1 (H : Horn α) (hNF : NF (α := α) H) (hDR1 : DR1 (α := α) H) :
    (toHornNF (α := α) H hNF).IsDR1 := by
  classical
  intro h
  -- prem = premSet
  change (premSet (α := α) H h).card ≤ 1
  exact card_premSet_le_one_of_DR1 (α := α) H h hDR1

/--
NEP が HornNF.IsNEP（∅ ∉ prem h）に落ちる補題の骨格。
（必要になったら詰める）
-/
lemma toHornNF_isNEP_of_NEP (H : Horn α) (hNF : NF (α := α) H) (hNEP : NEP (α := α) H) :
    (toHornNF (α := α) H hNF).IsNEP := by
  classical
  intro h hEmpty
  -- ∅ ∈ premSet H h → ((∅,h)∈rules) → NEP に矛盾
  have : ((∅ : Finset α), h) ∈ H.rules :=
    (mem_premSet_iff (α := α) H h (∅ : Finset α)).1 hEmpty
  have hNon : (∅ : Finset α).Nonempty := hNEP this
  simp_all only [Finset.not_nonempty_empty]

end Horn

end Dr1nds
