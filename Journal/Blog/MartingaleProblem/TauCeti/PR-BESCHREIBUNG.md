# Entwürfe der PR-Beschreibungen

Vier PRs, einer je Roadmap, in dieser Reihenfolge: `WeakConvergence`,
`KolmogorovExtension`, `SkorokhodSpace`, `MartingaleProblems`. Der erste hängt
nur an Mathlib und trägt die meisten bewiesenen Deklarationen; er ist der
geeignete Anfang, weil er den Maßstab zeigt, an dem die drei anderen gelesen
werden wollen.

**Vor dem Öffnen:** Label `awaiting-review` setzen. `[Intention]`-Issue mit
`claim` anlegen. Und den Abschnitt zur KI-Beteiligung nicht kürzen — er ist
bei uns kein Nebensatz.

---

## Gemeinsamer Block: KI-Beteiligung

*(wörtlich in jede der vier Beschreibungen, `CONTRIBUTING.md` verlangt Modelle
zu nennen)*

> **AI attribution.** These roadmaps were written by Claude Opus 5 running
> autonomously on a six- then three-hourly schedule between 2026-08-29 and
> 2026-09-07, about fifty runs, with a short interlude on Fable 5 that was
> abandoned for cost. Every run left a dated report; the whole trail is in
> `Facts/INVENTAR.md` of the source repository, including the runs that
> corrected earlier ones. The mathematical source is a manuscript of mine,
> and the direction, the priorities and every merge were mine. I have read
> what is submitted here.
>
> The process found and corrected several errors of my own, which is the
> reason I trust it enough to submit: among them a Mathlib citation list that
> claimed optional stopping, Doob and the upcrossing theory as available when
> all three are stated over `Filtration ℕ`; a statement of `Set.Ico`
> additivity that is false on a poset; seven theorems whose statement was
> `True` and therefore compiled while proving nothing; and a subadditivity
> claim for a windowed time-change norm that is refutable.

---

## PR 1 — `WeakConvergence`

**Titel:** `feat: roadmap for separating classes, the continuous mapping theorem, and Skorokhod representation`

> Weak convergence of measures is well developed in Mathlib — portmanteau, the
> Lévy–Prokhorov metric, tightness, Prokhorov — and this roadmap says so first,
> in a `What Mathlib already has` section, before asking for anything. Four
> things are wanted beyond it: the two classes of functions that determine a
> measure or its convergence, as predicates with the instances Mathlib does not
> prove; the continuous mapping theorem for maps continuous only almost
> everywhere; the Skorokhod representation theorem, which `docs/1000.yaml`
> lists as unformalized; and the link between uniform integrability and
> convergence in distribution, Mathlib's theory being about a single measure.
>
> `Suggested.lean` is not a sketch: it typechecks against Mathlib v4.33.1, with
> 48 declarations of which 27 carry proofs and no `sorry` stands in a
> *statement*. Compiling found two things that reading did not — a missing
> `[OpensMeasurableSpace E]` without which every integral in the main theorem
> is zero and the statement silently trivial, and a false implication from
> convergence determining to separating that holds only once both notions
> quantify over the same class of measures.

---

## PR 2 — `KolmogorovExtension`

**Titel:** `feat: roadmap for the Kolmogorov extension theorem`

> Mathlib has nearly all the scaffolding — `IsProjectiveMeasureFamily`,
> `IsProjectiveLimit`, the cylinder sets, `projectiveFamilyContent` with its
> whole API, `AddContent.measure`, `IsCompactSystem`, and inner regularity for
> finite measures on a completely metrizable space — and the two special cases,
> Ionescu–Tulcea and the product measure. Absent is the bridge from the compact
> system to σ-subadditivity, and the theorem itself. Two milestones, and the
> first is where the compactness actually enters.

---

## PR 3 — `SkorokhodSpace`

**Titel:** `feat: roadmap for the Skorokhod space`

> The string `cadlag` does not occur in Mathlib and neither does the space.
> This roadmap builds it, and states the index hypothesis as a typeclass rather
> than fixing `[0,1]` or `[0,∞)`: a linear order with a metric inducing the
> order topology, additive along the order, with compact closed balls. That is
> equivalent to being a closed subset of `ℝ` — classically, the order agreeing
> with Menger betweenness — and stating it as a class makes `ℝ`, `[0,∞)`,
> `[0,T]` and `h • ℤ` instances of one development rather than four.
>
> `Suggested.lean` typechecks: 92 declarations, 79 of them proved. Writing them
> refuted a construction of my own, the subadditivity of a *windowed*
> time-change norm; Billingsley measures the time change globally and localizes
> only the paths, and the witness against the windowed version is compiled in
> the file.

---

## PR 4 — `MartingaleProblems`

**Titel:** `feat: roadmap for abstract martingale problems`

> A martingale problem specifies a process by requiring a family of functionals
> of it to be martingales. Uniqueness, the Markov property, path regularity and
> convergence do not use the operator and do not use the state space; this
> roadmap develops the abstract form first and obtains the classical statements
> as instances. It depends on the three roadmaps above.
>
> Two milestones are labelled **roadmap-for-a-roadmap** and are marked in the
> text as not to be attempted: the existence route through a dual process,
> which needs the Kolmogorov extension theorem, and the full generator, whose
> theory belongs to the existing `OneParameterSemigroups` roadmap. The boundary
> to that roadmap is drawn explicitly — its semigroups are strongly continuous
> with a densely defined `LinearPMap` generator, while a Markov transition
> semigroup on the bounded measurable functions is neither strongly continuous
> nor single valued.
>
> `Suggested.lean` typechecks: 34 declarations, 23 proved.
