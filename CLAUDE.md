# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build & test

This is a Lean 4 project pinned to `leanprover/lean4:v4.30.0-rc1` with mathlib `v4.30.0-rc1`.

- `lake build` — build all targets (default targets are `Journal` lib and `journal` exe).
- `lake build Journal.Notes.DiscreteMeasure.Binomial` — build a single module (CI is the only test harness; module success = "passing").
- `lake exe journal` — run `Main.lean`, which uses VersoManual to emit the project's HTML manual from the `Journal` namespace into `_out/`.
- CI is `.github/workflows/lean.yml`, which just runs `leanprover/lean-action@v1` on push/PR.

For the slide deck under `Talks/`:
- `cd Talks/20260512Frankfurt && lualatex --shell-escape Pfaffelhuber.tex` — must be `lualatex` (not pdflatex) and `--shell-escape` is required for the `minted` package.

## Architecture

The mathematical content lives under `Journal/Notes/`. Two layers coexist:

1. **`Journal/Notes/DiscreteMeasure/` is the polished/active core.** It develops a custom `DiscreteMeasure α` type (a structure wrapping `weight : α → ℝ≥0∞`) as an alternative to mathlib's `PMF`. The design rationale (in `Basic.lean`'s module-doc): it coerces to a `Measure α` (via `toMeasure`, a sum of weighted Diracs) so the whole `Measure`-library is available from the start, *and* it is a `LawfulMonad`, enabling `do`-notation. A key non-obvious property proved in `Basic.lean` is that `μ.toMeasure` is additive for **arbitrary** disjoint unions, not just countable ones (`toMeasure_additive`).

   Module dependency order inside `DiscreteMeasure/`:
   ```
   Basic → Monad → Sequence → Bernoulli → Binomial / Multinomial / Hypergeometric / Uniform
   ```
   `Monad.lean` defines `map`, `pure`, `bind`, `join`, `seq` and gives the `LawfulMonad` and `ULiftable` instances. `Sequence.lean` builds `iidSequence` on top. The distribution files (`Bernoulli`, `Binomial`, `Multinomial`, …) are then constructed monadically and proved equivalent to closed-form descriptions (e.g. `binom_formula`).

2. **`Journal/Notes/*.lean` (top-level) is exploratory / older work.** Files like `cylinders.lean`, `compactSystem.lean`, `ionescu.lean`, `stochasticProcess.lean`, `Tightness.lean`, `MF.lean`, `PMF.lean`, `DiscreteMeasure.lean`, `DiscreteMeasure2.lean` are scratch material for projective/Kolmogorov-extension–style results and earlier iterations of the discrete-measure idea. `Main.lean` only imports `Journal.Notes.MF`, so these are kept building but are not the main artefact.

`Journal/Blog/` holds `.md` notes (not part of the Lean build).

## Project-specific conventions

- **Mathlib PR markers.** Lemmas tagged with comments like `-- #34138`, `-- #34239`, `-- #34702`, `-- #37060` are queued for upstream mathlib PRs (the number is the issue/PR id). When editing or moving such a lemma, preserve the marker — it tracks where the lemma is supposed to land.
- **Module headers** follow mathlib style: Apache-2.0 copyright block, then a `/-!`-doc comment summarising the file. New files in `DiscreteMeasure/` should match.
- **`MeasurableSpace ⊤` is implicit.** Many lemmas about `DiscreteMeasure` introduce `letI : MeasurableSpace α := ⊤` locally rather than requiring instances at the call site — discrete measures don't need a real σ-algebra.
- **Talk-vs-code naming gap.** The Beamer slides under `Talks/` deliberately rename `pure` to `dirac` for didactic purposes; the actual Lean code still uses `pure` (the `Monad`-typeclass field). Do not mass-rename the codebase to match the slides without an explicit ask.
