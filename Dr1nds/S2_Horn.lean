import Mathlib.Data.Finset.Basic

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/--
General Horn rule system over α.
A rule is (premise P, head h).
We keep everything finitary via Finset.
-/
abbrev Rule (α : Type) := (Finset α) × α

structure Horn (α : Type) [DecidableEq α] where
  rules : Finset (Rule α)

namespace Horn

/-- DR1: each head appears in at most one rule. -/
def DR1 (H : Horn α) : Prop :=
  ∀ {P₁ P₂ : Finset α} {h : α},
    (P₁, h) ∈ H.rules → (P₂, h) ∈ H.rules → P₁ = P₂

/-- NEP: no empty premise rules. -/
def NEP (H : Horn α) : Prop :=
  ∀ {P : Finset α} {h : α}, (P, h) ∈ H.rules → P.Nonempty

/-- NF: no self-premise (head ∉ premise). -/
def NF (H : Horn α) : Prop :=
  ∀ {P : Finset α} {h : α}, (P, h) ∈ H.rules → h ∉ P

/--
Closedness of a set X w.r.t. Horn rules:
for every rule P → h, if P ⊆ X then h ∈ X.
This is the "rule satisfaction" definition (no closure operator needed).
-/
def IsClosed (H : Horn α) (X : Finset α) : Prop :=
  ∀ {P : Finset α} {h : α}, (P, h) ∈ H.rules → P ⊆ X → h ∈ X

/-- rules に head=h の規則が存在すること -/
def HasHead (H : Horn α) (h : α) : Prop :=
  ∃ P : Finset α, (P, h) ∈ H.rules

/-- head=h の premise を（DR1 の下で）Optionで取り出す -/
noncomputable def premOpt (H : Horn α) (h : α) : Option (Finset α) := by
  classical
  by_cases hh : HasHead (α := α) H h
  · exact some (Classical.choose hh)
  · exact none

lemma premOpt_eq_some_iff
  (H : Horn α) (h : α) :
  H.premOpt h = some P ↔ (P, h) ∈ H.rules := by
  classical
  -- スケルトン：DR1 を仮定しないと「↔」は無理。まずは「→」方向だけ等で作るのが安全。
  sorry

/-- DR1 なら premOpt は well-defined（同じ head の premise が一意）-/
lemma premOpt_wellDefined
  (H : Horn α) (hDR1 : Horn.DR1 (α := α) H)
  {P₁ P₂ : Finset α} {h : α}
  (h1 : (P₁, h) ∈ H.rules) (h2 : (P₂, h) ∈ H.rules) :
  P₁ = P₂ := by
  exact hDR1 h1 h2

/-- HasHead なら premOpt は some になる -/
lemma premOpt_eq_some_of_hasHead (H : Horn α) (h : α)
  (hh : HasHead (α := α) H h) :
  ∃ P : Finset α, H.premOpt (α := α) h = some P := by
  classical
  -- premOpt は by_cases で hh 側に入る
  -- choose hh を P とすればよい
  refine ⟨Classical.choose hh, ?_⟩
  -- unfold premOpt して simp したいが、by_cases で書いているので simp で割れるように
  -- ここは実装次第で `simp [Horn.premOpt, hh]` が通るように書き換えるのがベスト
  -- 現状の `premOpt := by classical; by_cases ...` でも `simp` は通しにくいので
  -- 「premOpt を if で書く」か「premOpt の定義を lemma に引き出す」などが必要になることがある
  admit

/-- premOpt = some P なら HasHead -/
lemma hasHead_of_premOpt_eq_some (H : Horn α) (h : α) (P : Finset α)
  (hP : H.premOpt (α := α) h = some P) :
  HasHead (α := α) H h := by
  classical
  -- by_cases の none 側では some にならない、を使う
  -- 定義展開して矛盾
  admit

/-- DR1 の下で：規則 (P,h) があるなら premOpt h = some P -/
lemma premOpt_eq_some_of_mem_rules_of_DR1
  (H : Horn α) (h : α) (P : Finset α)
  (hDR1 : Horn.DR1 (α := α) H)
  (hmem : (P, h) ∈ H.rules) :
  H.premOpt (α := α) h = some P := by
  classical
  -- hh : HasHead H h は ⟨P, hmem⟩
  have hh : HasHead (α := α) H h := ⟨P, hmem⟩
  -- premOpt が選んだ premise を P0 とし、DR1 で P0 = P を示す
  -- その後 some の一致
  admit

/-- premOpt が some P を返したら、その規則は rules にある（少なくとも存在する） -/
lemma mem_rules_of_premOpt_eq_some
  (H : Horn α) (h : α) (P : Finset α)
  (hP : H.premOpt (α := α) h = some P) :
  (P, h) ∈ H.rules := by
  classical
  -- premOpt の choose が実際に rules に入っていることを戻す
  -- これも定義形によっては少し工夫が要る
  admit

end Horn

end Dr1nds
