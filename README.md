# dr1nds

Formalization project in Lean 4 for Horn-style closure systems, forbidden-set variants, and induction-based counting inequalities (`Q` / `Qcorr`).

## Requirements

- [elan](https://github.com/leanprover/elan)
- Lean toolchain: `leanprover/lean4:v4.26.0` (pinned in `lean-toolchain`)

## Build

This repository is configured so that `lake build` compiles:

- the full library target `Dr1nds`
- the executable target `dr1nds`

```bash
lake build
```

You can also build only the library:

```bash
lake build Dr1nds
```

## Project Layout

- `Dr1nds/SetFamily/`: finite family operations and accounting identities (e.g. `Con`, `Del`, `Tr`, `PairTr`, `NDS`-related lemmas)
- `Dr1nds/Horn/`: Horn normal form structures, closure/trace/contraction, and parallel-related lemmas
- `Dr1nds/Forbid/`: Horn systems with forbidden sets and bridge lemmas
- `Dr1nds/Induction/`: induction framework and main proof flow
  - `Dr1nds/Induction/Main.lean` is the induction entry module
- `Dr1nds/ClosureSystem/`: general closure-system utilities
- `Dr1nds.lean`: top-level library import aggregator

## Notes

- The executable (`Main.lean`) currently imports `Dr1nds` and prints a placeholder message.
- The codebase is under active development; theorem/lemma APIs may evolve.

## Main Theorems (Current Entry Points)

From `Dr1nds/Induction/Main.lean`:

- `Q_step0`: one induction step for forbid-free packs
- `Qcorr_step1`: one induction step for packs with forbid sets
- `Q_Qcorr_main`: mutual induction theorem combining `Q` and `Qcorr`
- `Q_main`: convenience corollary for the forbid-free branch
- `Qcorr_main`: convenience corollary for the forbid branch
