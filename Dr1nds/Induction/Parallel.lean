import Dr1nds.SetFamily.CoreDefs
import Dr1nds.Horn.Horn
import Dr1nds.Horn.HornClosure
import Dr1nds.Horn.Parallel
import Dr1nds.Forbid.HornWithForbid
import Dr1nds.Induction.Statements
import Mathlib.Tactic

namespace Dr1nds

variable {α : Type} [DecidableEq α]

-- =====================================
-- (0) parallel / no-parallel 分岐（独立核）
-- =====================================

/- Parallel / NoParallel for forbid-free packs. -/
abbrev Parallel0 (P : Pack0 α) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ P.H.closure {v} ∧ v ∈ P.H.closure {u}
abbrev NoParallel0 (P : Pack0 α) : Prop := ¬ Parallel0 P

/-- Parallel / NoParallel for forbid packs. 禁止集合の中にパラレルがあるかどうか。-/
abbrev Parallel1 (F: HornWithForbid α) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ F.F ∧ v ∈ F.F ∧ u ∈ F.H.closure {v} ∧ v ∈ F.H.closure {u}
abbrev NoParallel1  (F: HornWithForbid α): Prop := ¬ Parallel1 F

--使わないかも。
def HasParallel0 (P : Pack0 α) (v:α) :=
  ∃ u, u ≠ v ∧ u ∈ P.H.closure {v} ∧ v ∈ P.H.closure {u}

def HasParallel1 (F : HornWithForbid α) (v:α) :=
  ∃ u, u ≠ v ∧ u ∈ F.H.closure {v} ∧ v ∈ F.H.closure {u}

---ほかの言明に合わせて2段階にする。getのほうは、頂点をtraceしたものがNDSが大きくなくて、Packの条件を満たすというもの。頂点を引数に入れる。
---上のほうの言明は、帰納法の仮定を仮定すると、Q n が成り立つというもの。
/-- Wiring helper: advance one step under the parallel-branch (forbid-free). -/
axiom Q_of_parallel_get
  (n : Nat) (P : Pack0 α) (hn : P.H.U.card = n):
  Parallel0 P → ∃ P':Pack0 α , (P'.H.U.card = n - 1 ∧ NDS n (P.H.FixSet) ≤ NDS (n-1) (P'.H.FixSet))

/-- Parallel-branch (forbid-free): if `Parallel0 P` holds, we can close `Q n P` by the trace reduction core. -/
theorem Q_of_parallel
  (n : Nat) (P : Pack0 α) : (∀ P':Pack0 α, P'.H.U.card = n → Q n P') →
  P.H.U.card = n + 1 →
  Parallel0 P → Q (n+1) P := by
  intro hQ hn hPar
  obtain ⟨P',hP'⟩ := Q_of_parallel_get (α := α) (n+1) P hn hPar
  simp at hP'
  dsimp [Q]
  intro hn'
  specialize hQ P'
  have :P'.H.U.card = n := by simp_all
  specialize hQ this
  dsimp [Q] at hQ
  specialize hQ this
  rw [←this] at hQ
  rw [←hn']
  rcases hP' with ⟨h1,h2⟩
  rw [←hn] at h2
  rw [←h1] at h2
  exact Int.le_trans h2 hQ

/-- Wiring helper: advance one step under the parallel-branch (with forbid). -/
axiom Qcorr_of_parallel_get
  (n : Nat) (F : HornWithForbid α)  (hn : F.H.U.card = n):
  Parallel1 F → ∃ F':HornWithForbid α , F'.H.U.card = n - 1 ∧ (F.NDS_corr n) ≤ (F'.NDS_corr (n - 1))

theorem Qcorr_ge_hasParallel
  (n : Nat) (F : HornWithForbid α) :
  (∀ F':HornWithForbid α, F'.H.U.card = n → Qcorr n F') → F.H.U.card = n + 1 → Parallel1 F →
  Qcorr (n+1) F := by
  intro hQcorr hn hPar
  obtain ⟨F',hF'⟩ := Qcorr_of_parallel_get (α := α) (n+1) F hn hPar
  dsimp [Qcorr]
  intro hn'
  specialize hQcorr F'
  have :F'.H.U.card = n := by simp_all
  specialize hQcorr this
  dsimp [Qcorr] at hQcorr
  specialize hQcorr this
  --rw [←this] at hQcorr
  rw [←hn']
  rcases hF' with ⟨h1,h2⟩
  rw [←hn] at h2
  simp at h1
  rw [←this] at hn'
  have : n = F.H.U.card -1:= by
    subst this
    simp_all only [add_tsub_cancel_right]
  rw [this] at hQcorr
  exact Int.le_trans h2 hQcorr

end Dr1nds
