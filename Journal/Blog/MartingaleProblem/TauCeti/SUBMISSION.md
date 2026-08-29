# Submitting these roadmaps to Tau Ceti

Not part of the roadmaps. Tau Ceti requires roadmap READMEs to be timeless and
free of process; everything about *how to submit* lives here instead.

## What is here

Four roadmap directories, each in the layout `TauCetiRoadmap` expects
(`README.md` is the definitive specification, `Suggested.lean` is a
non-binding prototype):

| Directory | Depends on | Content |
|---|---|---|
| `WeakConvergence` | Mathlib | separating and convergence determining classes; continuous mapping theorem for almost everywhere continuous maps; Skorokhod representation; Vitali |
| `KolmogorovExtension` | Mathlib | compact systems, inner regular contents, the projective limit for an arbitrary index |
| `SkorokhodSpace` | Mathlib, `WeakConvergence` | càdlàg functions; the `J₁` metric; Polish; Borel equals cylinder; the modulus and compactness; tightness |
| `MartingaleProblems` | Mathlib, all three above | the manuscript: clock, abstract martingale problem, jump processes, restart and uniqueness, duality, càdlàg modification, abstract convergence, existence from a dual |

The dependency graph is a chain with one fork; `WeakConvergence` and
`KolmogorovExtension` are independent of each other and can be claimed in
parallel.

## Prior art that the licence now permits reusing

Two Apache-2.0 repositories are cited inside the roadmaps as code to take over
rather than rewrite. Tau Ceti is itself Apache-2.0, so the licences are
compatible; the obligation is to keep the copyright headers and the author
attribution.

* `RemyDegenne/brownian-motion` — `BrownianMotion/StochasticIntegral/Cadlag.lean`
  for Milestone 2 of `SkorokhodSpace`, and the quasimartingale càdlàg
  modification for Milestone 9 of `MartingaleProblems`. Note that the `paper`
  branch carries only a 32 line stub of `Cadlag.lean` and no
  `Quasimartingale/` at all; the material — `Cadlag.lean` at 236 lines and
  `Quasimartingale/CadlagModification.lean` at 1162 lines with four `sorry`s —
  is on `upstream/master`, not on the fork's `origin/master`.
  The repository is pinned to `leanprover/lean4:v4.25.0`, so taking the code
  over means porting it, not depending on it — which is what Tau Ceti wants
  anyway, since it depends on Mathlib `master` and nothing else.
* `RemyDegenne/kolmogorov_extension4` — Milestone 3 of `KolmogorovExtension`.
  Pinned to `v4.18.0-rc1`, and much of its scaffolding has since landed in
  Mathlib (`MeasureTheory.IsProjectiveMeasureFamily`,
  `MeasureTheory.measurableCylinders`, `MeasureTheory.AddContent`), so what is
  taken over should first be reduced to what Mathlib does not already provide.

One repository is cited in the manuscript but **not** here, and deliberately:
the `D([0,1], ℝ)` development accompanying the Kuan reference. Two repositories
accompany that paper and they are licensed differently.

* `Jeffrey-Kuan/type-D-asymptotics` — Apache-2.0, `LICENSE` at the root. Holds
  the paper sources and eight Lean files (`TypeDDecoupling.lean`,
  `TypeDDecouplingDuality.lean`, `…LCLT.lean`, `…EW.lean`, `…Crossover.lean`,
  `…DualPairWitness.lean`, `…Tiers34.lean`, `…TracyWidom.lean`). None of them
  contains the Skorokhod development: no `IsCadlag`, no `cadlagModulus`.
* `Jeffrey-Kuan/type-D-asymptotics-lean` — **no licence**. Single branch `main`,
  no `LICENSE` file, no per-file copyright headers, README silent. This is where
  `TypeDDecouplingSkorokhodBasic/Compact/Complete/Tight/Measurable/Aldous.lean`
  live, and they are the only files of interest to `SkorokhodSpace`.

So the Apache grant on the first repository does not reach the material worth
reusing, and no roadmap may point an implementer at it. Extending the same
`LICENSE` to the second repository is a one file change and is the request to
make to the author.

## Steps

1. Copy the four directories into a fork of `TauCetiProject/TauCetiRoadmap`.
2. For each, open an issue with the `[Intention]` template, titled
   `[Intention]: <specific targets>`, and comment `claim` to register it in the
   shared `leanprover-community/project-intentions` registry.
3. Open one pull request per roadmap. Merging needs approval from
   `@TauCetiProject/roadmap-reviewers` and a passing `build` check; the first
   merged PR earns triage rights, two earn reviewer status.
4. `Suggested.lean` files must build against Mathlib `master`. The ones here are
   prototypes written against the roadmap and have not been compiled; each needs
   a pass under `lake build` before the PR, with `sorry` kept only where the
   statement is the work.

## What is deliberately absent from the roadmaps

The manuscript's own commentary — the bundle tables `(T0)`–`(T4)` and
`(E0)`–`(E3)`, the discussion of which generalization costs what, the record of
which source states what, and the four remarks weighing weak-strong convergence
against augmentation. Roadmaps state targets. The mathematics behind each
milestone stays in `MartingaleProblem.tex`, which is the place to look when an
implementer asks why a hypothesis is there.
