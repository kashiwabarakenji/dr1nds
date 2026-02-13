/-
このファイルは、主に「出口（main wrapper）」としての役割を果たしており、
命題 Q n P を不等式 NDS n P.C ≤ 0 に変換するための薄いラッパーです。

実際の証明作業（配線や局所カーネルの構築）は S10_Steps.lean と S11_LocalKernels.lean にあり、
仕様・公理は S8_Statements.lean にまとめられています。

このファイルは、公理が入れ替わっても安定しており、新たな公理を導入しないことを意図しています。
-/
-- Dr1nds/S9_Main.lean
import Dr1nds.S8_Statements

namespace Dr1nds
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

/-
Q は定義上 NDS n P.C ≤ 0 と同値（またはそれを含意）なので、
この定理は本質的に `by simpa [Q]` で閉じます。

S10 が接続されると、意図する流れは
  IH(n,P) -> Q(n,P)
となり、
main_from_Q で最終的な不等式を得る形になります。
-/
theorem main_from_Q
  (n : Nat) (P : HypPack α) :
  Q (α := α) n P → NDS (α := α) n P.C ≤ 0 := by
  intro hQ
  simpa [Q] using hQ

-- 今後のスケルトン案
-- theorem main_from_IH (n : Nat) (P : HypPack α) : IH (α:=α) n P → NDS (α:=α) n P.C ≤ 0
--   -- S10_Steps が完成したら `IH -> Q` を経由して閉じる予定
-- theorem main (n : Nat) (P : HypPack α) : (Dr1NEP ... ) -> NDS ... ≤ 0
--   -- 最終的には Horn/HornNF 側の仮定から HypPack を生成して IH を起動する
--
-- 現在プロジェクトで使われている公理は主に S11_LocalKernels に閉じており、
-- （おそらくいくつかの representability 補題も）
-- 後で適切に解消される見込みです。

end Dr1nds
