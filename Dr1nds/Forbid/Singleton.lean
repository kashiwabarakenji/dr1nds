-- Dr1nds/Forbid/Singleton.lean
import Mathlib.Tactic

import Dr1nds.SetFamily.CoreDefs      -- Up, Hole, NDS, NDS_corr
import Dr1nds.Forbid.Basic     -- singleton lemmas for Up/Hole

namespace Dr1nds

variable {α : Type} [DecidableEq α]

/-!
# Forbid singleton (A = {a})

このファイルは Horn を使わず、`Up`/`Hole`/`NDS_corr` の **singleton 展開**だけを theorem として固定する。

## Scope

このファイルは **family-level** の等式変形（`Up`/`Hole`/`NDS_corr` の singleton 展開）だけを扱う。

Horn ルールの「正規化」（例：`a` を前提に含む規則の削除が `Hole/Up` に与える影響）に関する主張は、
family 単体では仮定を正しく書けないため、このファイルには置かない。
それらは `Forbid/HornBridge.lean`（Horn 側のデータと一緒に）で lemma として扱う。
-/


/-- `NDS_corr n C {a}` の definitional 展開（Up/Hole をそのまま残す版）。 -/
lemma NDS_corr_singleton_unfold
  (n : Nat) (C : Finset (Finset α)) (a : α) :
  NDS_corr (α := α) n C ({a} : Finset α)
    = NDS (α := α) n (Hole (α := α) C ({a} : Finset α))
      + (Up (α := α) C ({a} : Finset α)).card := by
  simp [NDS_corr]

/-- `NDS_corr n C {a}` を filter だけで書き直す（完全に機械的）。 -/
lemma NDS_corr_singleton_rewrite
  (n : Nat) (C : Finset (Finset α)) (a : α) :
  NDS_corr (α := α) n C ({a} : Finset α)
    =
    NDS (α := α) n (C.filter (fun X => a ∉ X))
      + (C.filter (fun X => a ∈ X)).card := by
  classical
  -- unfold + rewrite Up/Hole using `Forbid/Basic.lean`
  simp [NDS_corr,
    Dr1nds.Hole_singleton_eq_filter_notmem (α := α),
    Dr1nds.Up_singleton_eq_filter_mem (α := α)]

omit [DecidableEq α] in
/-- `NDS` changes by exactly `|C|` when the ambient size increases by 1.

This is the basic accounting identity used when shifting between `n` and `n-1`.
-/
lemma NDS_succ_eq_sub_card
  (n : Nat) (C : Finset (Finset α)) :
  NDS (α := α) (n + 1) C = NDS (α := α) n C - (C.card : Int) := by
  classical
  -- After unfolding `NDS`, this is just the distributivity
  --   -( |C| * (n+1) ) = -( |C| * n ) - |C|.
  -- We let `simp` put both sides into the same normal form and finish by `ring`.
  simp [Dr1nds.NDS, w]
  ring


omit [DecidableEq α] in
/-- A convenient wrapper of Mathlib's `Finset.card_filter_add_card_filter_not`.

We keep this in the `Dr1nds` namespace because we use it repeatedly when rewriting
`Up/Hole` for singleton forbids.
-/
lemma card_filter_add_card_filter_not
  (s : Finset α) (p : α → Prop) [DecidablePred p] :
  (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  classical
  simpa using (Finset.filter_card_add_filter_neg_card_eq_card (s := s) (p := p))


/-- For singleton forbids, `Up` and `Hole` partition the family. -/
lemma card_up_add_card_hole_singleton
  (C : Finset (Finset α)) (a : α) :
  (Up (α := α) C ({a} : Finset α)).card
    + (Hole (α := α) C ({a} : Finset α)).card
    = C.card := by
  classical
  -- rewrite `Up/Hole` as filters and use the generic filter-card partition
  simpa [
    Dr1nds.Up_singleton_eq_filter_mem (α := α),
    Dr1nds.Hole_singleton_eq_filter_notmem (α := α)
  ] using (card_filter_add_card_filter_not (α := Finset α)
        (s := C) (p := fun X : Finset α => a ∈ X))

/-- A rearranged form of `card_up_add_card_hole_singleton`. -/
lemma card_up_singleton_eq
  (C : Finset (Finset α)) (a : α) :
  (Up (α := α) C ({a} : Finset α)).card
    = C.card - (Hole (α := α) C ({a} : Finset α)).card := by
  classical
  -- `u + h = c`  ⇒  `u = c - h`
  have hpart :
      (Up (α := α) C ({a} : Finset α)).card
        + (Hole (α := α) C ({a} : Finset α)).card
        = C.card :=
    card_up_add_card_hole_singleton (α := α) (C := C) (a := a)
  exact Nat.eq_sub_of_add_eq hpart

/-- Same as `card_up_singleton_eq`, but coerced to `Int`.

This is convenient when the surrounding goal lives in `Int` (e.g. inside `NDS`).
-/
lemma int_card_up_singleton_eq
  (C : Finset (Finset α)) (a : α) :
  (↑(Up (α := α) C ({a} : Finset α)).card : Int)
    = (↑C.card : Int) - (↑(Hole (α := α) C ({a} : Finset α)).card : Int) := by
  classical
  have hNat := card_up_singleton_eq (α := α) (C := C) (a := a)
  -- Coerce the Nat equality into Int.
  -- We also rewrite the RHS using `int_ofNat_sub_of_le`.
  have hle : (Hole (α := α) C ({a} : Finset α)).card ≤ C.card := by
    -- from the partition lemma: `u + h = c`
    have hpart := card_up_add_card_hole_singleton (α := α) (C := C) (a := a)
    apply Nat.le_of_add_le_add_left
    simp_all only [Up_singleton_eq_filter_mem, Hole_singleton_eq_filter_notmem, add_le_add_iff_left]
    linarith
    simp_all only [Up_singleton_eq_filter_mem, Hole_singleton_eq_filter_notmem]
    constructor
  -- now rewrite
  simp
  simp_all only [Up_singleton_eq_filter_mem, Hole_singleton_eq_filter_notmem, Nat.cast_sub]

/--- `Int.ofNat` compatibility for subtraction when the RHS is known to be ≤ LHS.

This lemma is often what remains after rewriting cardinalities and switching between
`Nat` and `Int` in NDS/NDSCorr calculations.
-/

lemma int_ofNat_sub_of_le (a b : Nat) (h : b ≤ a) :
  (↑a : Int) - (↑b : Int) = (↑(a - b) : Int) := by
  -- `Int.ofNat_sub` expects the `≤` proof.
  simp [Int.ofNat_sub h]

omit [DecidableEq α] in
/-- `card_filter_add_card_filter_not` coerced to `Int`.

This is useful when the surrounding goal is an `Int` identity (e.g. inside NDS/NDS_corr).
-/
lemma int_card_filter_add_card_filter_not
  (s : Finset α) (p : α → Prop) [DecidablePred p] :
  (↑(s.filter p).card : Int) + (↑(s.filter (fun x => ¬ p x)).card : Int) = (↑s.card : Int) := by
  classical
  -- cast the Nat partition identity and simplify
  have hNat : (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card :=
    card_filter_add_card_filter_not (s := s) (p := p)
  -- `simp` rewrites `↑(a+b)` into `↑a + ↑b`
  simpa [Int.natCast_add] using congrArg (fun z : Nat => (z : Int)) hNat


omit [DecidableEq α] in
/-- Rearranged form of `NDS_succ_eq_sub_card`.

Often you want to *add back* `|C|` rather than subtract it.
-/
lemma NDS_succ_add_card
  (n : Nat) (C : Finset (Finset α)) :
  NDS (α := α) (n + 1) C + (C.card : Int) = NDS (α := α) n C := by
  classical
  -- start from the existing identity and rearrange
  have h := NDS_succ_eq_sub_card (α := α) (n := n) (C := C)
  -- `h : NDS (n+1) C = NDS n C - |C|`
  -- move `|C|` to the left
  linarith

end Dr1nds
