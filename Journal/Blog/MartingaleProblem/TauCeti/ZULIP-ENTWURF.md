**Topic:** `#Tau Ceti > Getting started: roadmaps`
**Status:** Entwurf, nicht gepostet. Zahlen nachgemessen am 2026-09-22.

---

Hi all — I would like to announce a set of four roadmaps before opening a PR, and to
ask two coordination questions that the README's "Coordinate first" item tells me to
ask here rather than to assume.

**What they are.** Weak convergence of measures, the Kolmogorov extension theorem,
Skorokhod space `D(ι, E)`, and abstract martingale problems. They form a chain with
one fork: `WeakConvergence` and `KolmogorovExtension` sit on Mathlib alone and are
independent of each other; `SkorokhodSpace` sits on `WeakConvergence`; and
`MartingaleProblems` sits on all three. 33 milestones in total (6 / 3 / 10 / 14).

The subject is the one Ethier–Kurtz treat: càdlàg paths, tightness and weak
convergence on `D`, the martingale problem as the primitive notion, restart and
uniqueness, duality, and convergence of processes. The design choices that are
genuinely mathematical are written into the roadmaps rather than left to the
implementer — the operator as a *relation* rather than a function, solutions with
respect to an arbitrary filtration as the primitive, a time index that is an
arbitrary preorder with a measure on it (so that discrete and continuous time are one
theory), and `RCLike` test functions.

**Grounding.** Three of the four carry a `Suggested.lean`; together they are 2,927
declarations in about 82,000 lines, and they type check in dependency order against
Mathlib `master` (`94ef6b89544`, Lean `v4.35.0-rc2`) with `autoImplicit` and
`relaxedAutoImplicit` off: 0 errors, 0 `sorry`, 0 deprecated names, and every
declaration reduces to `propext`, `Classical.choice`, `Quot.sound`. Every Mathlib name
cited in the READMEs is checked against the source with its file and line, and the
"Mathlib does not have this" claims are re-checked mechanically on every revision —
that check has caught four false negatives of mine so far, all of them names generated
by `@[to_additive]` and therefore absent from every `theorem` line.

**First question — coordination.** Two of Rémy Degenne's repositories are cited as
material to *take over* rather than rewrite: `brownian-motion` (the càdlàg basics, and
the quasimartingale càdlàg modification) and `kolmogorov_extension4`. Both are
Apache-2.0, so the licence is not the issue; agreement is. @**Rémy Degenne** — would
you be happy for these roadmaps to direct an implementer at that code, with your
copyright headers and attribution kept? I would rather ask than infer it from the
licence.

I should also flag prior art I am *not* drawing on: Scott Armstrong's `MarkovProcess`
builds continuous-path Markov processes from a transition semigroup, with the Dynkin
martingale and a Trotter–Kato route to weak convergence. It touches no càdlàg path and
contains no martingale problem, so there is no collision with these roadmaps, but the
overlap in subject is close enough that it should be named rather than discovered.
(There is one further repository with the Skorokhod material I would have liked to
reuse, but it carries no licence at all, so no roadmap points at it.)

**Second question — one PR or four.** The roadmaps build on each other, and reviewing
`MartingaleProblems` without `SkorokhodSpace` in front of it seems unkind. My plan is a
single PR, with the description saying which milestone rests on which so that a
reviewer can stop at any level. But the review load is the scarce thing here, so if
four separate PRs — or the two independent ones first — would be easier on the
reviewers, I will happily split it.

The branch is here if anyone wants to look before there is a PR:
https://github.com/pfaffelh/TauCetiRoadmap/tree/martingale-problems

Thanks — and happy to answer anything.
