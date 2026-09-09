# Submitting these roadmaps to Tau Ceti

Not part of the roadmaps. Tau Ceti requires roadmap READMEs to be timeless and
free of process; everything about *how to submit* lives here instead.

## What is here

Four roadmap directories, each in the layout `TauCetiRoadmap` expects
(`README.md` is the definitive specification, `Suggested.lean` is a
non-binding prototype):

| Directory | Depends on | Content |
|---|---|---|
| `WeakConvergence` | Mathlib | separating and convergence determining classes; continuous mapping theorem for almost everywhere continuous maps; Skorokhod representation; Vitali; the functional monotone class theorem |
| `KolmogorovExtension` | Mathlib | compact systems, inner regular contents, the projective limit for an arbitrary index |
| `SkorokhodSpace` | Mathlib, `WeakConvergence` | càdlàg functions; the `J₁` metric; Polish; Borel equals cylinder; the modulus and compactness; tightness |
| `MartingaleProblems` | Mathlib, all three above | the manuscript: clock, abstract martingale problem, jump processes, restart and uniqueness, duality, continuous time martingales and the càdlàg modification, abstract convergence, existence from a dual |

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

## Was die Projektdokumente verlangen

Aus `TauCetiRoadmap/CONTRIBUTING.md`, am 2026-09-07 gelesen. **Eine Größengrenze
für PRs gibt es nicht** — weder eine Zeilen- noch eine Meilensteinzahl. Gesteuert
wird über Labels (`awaiting-review` / `awaiting-author`), und der PR merged
automatisch, sobald ein Mitglied von `@TauCetiProject/roadmap-reviewers`
zustimmt. Die eigentliche Grenze ist die Reviewlast: substantielles Review,
besonders von Fachleuten, nennt das Dokument das Knappste im Projekt.

Vier Regeln betreffen uns unmittelbar:

* **Bodenhaftung.** „A roadmap must make contact with material that already
  exists in Mathlib or Tau Ceti"; eine Roadmap, deren unterste Sprosse weit über
  dem Formalisierten liegt, lasse Agenten „thrash and produce bad code". Das ist
  unser stärkster Punkt — die Meilensteine ruhen auf zeilengenau geprüften
  Mathlib-Deklarationen, und die Prüfung ist viermal wiederholt worden.
* **Bereits Formalisiertes ist willkommen**, aber das eigene Repository ist als
  *zitierte Quelle* zu behandeln, nicht als Spezifikation. Die bewiesenen
  Deklarationen in `*/Suggested.lean` sind also Beleg, nicht Vorlage — so sind
  sie ohnehin gemeint.
* **Nicht ins Unbestimmte auslaufen.** Läuft eine Roadmap am Ende in etwas viel
  Größeres, ist das ausdrücklich als *roadmap-for-a-roadmap* zu kennzeichnen,
  mit dem Hinweis, dem nicht zu folgen. Bei uns betrifft das mindestens
  `MartingaleProblems` Meilenstein 12 (Existenz aus einem Dualen, hängt an
  `KolmogorovExtension`) und Meilenstein 13 (Halbgruppen und voller Erzeuger,
  wo Mathlib nichts hat). **Vor der Einreichung zu kennzeichnen.**
* **KI-Beteiligung nennen**, in der PR-Beschreibung, mit den benutzten Modellen.
  Bei uns ist das kein Nebensatz: die Roadmaps sind über zwei Wochen von rund
  fünfzig autonomen Läufen geschrieben, Opus 5 und zeitweise Fable 5, und jeder
  Lauf ist in `Facts/INVENTAR.md` protokolliert. Review-Kommentare mit
  KI-Hilfe tragen konventionell ein `:robot:`-Präfix.

Empfehlung daraus: **vier getrennte PRs**, einer je Roadmap. Die Dokumente
verlangen es nicht, aber die Abhängigkeitskette
(`WeakConvergence` → `SkorokhodSpace` → `MartingaleProblems`, dazu
`KolmogorovExtension`) macht sie einzeln prüfbar, und bei knappen Reviewern ist
das die Höflichkeit, die zählt. `WeakConvergence` zuerst, weil es nur an Mathlib
hängt und die meisten bewiesenen Deklarationen trägt.

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

## Was das Zielprojekt inzwischen selbst hat (nachgesehen am 2026-09-09)

Beide Repositorien geholt und gelesen: `TauCetiProject/TauCetiRoadmap` und die
Bibliothek `TauCetiProject/TauCeti` darunter.

**Die Halbgruppen sind dort weiter, als unser Punkt 2 im `TODO.md` annimmt.**
`TauCetiRoadmap/OneParameterSemigroups/Suggested.lean` ist mit 141 Zeilen und
fünf Sätzen schmal, weil sie **nachträglich** geschrieben wurde: Hille--Yosida
(`hilleYosida_generation`) und Bernstein sind **bewiesen** und werden aus der
Bibliothek zitiert; offen ist im Wesentlichen Lumer--Phillips in der
Erzeugungsrichtung. Der zentrale Begriff ist

```lean
structure StronglyContinuousSemigroup (X) [Banach] where
  toFun : ℝ≥0 → X →L[ℝ] X
  map_zero' : toFun 0 = ContinuousLinearMap.id ℝ X
  map_add'  : ∀ s t, toFun (s + t) = (toFun s).comp (toFun t)
  continuousAt_zero' : ∀ x, ContinuousAt (fun t => toFun t x) 0
```

mit `LinearPMap` für den Erzeuger, Resolvente, Wachstumsschranke und
Dissipativität daneben.

*Für das Zulip-Anliegen heißt das:* EK Theorem 4.4.1 sitzt direkt auf
Hille--Yosida, und Hille--Yosida ist dort nicht offen, sondern fertig. Wer den
Satz aufnimmt, muß die Halbgruppentheorie nicht erst bauen — das Angebot ist
konkreter als in `TODO.md` Punkt 2 beschrieben.

*Für unsere eigenen Dateien heißt es nichts.* Unser `jumpSemigroup` ist
`P_t h z = 𝔼_z[h (X t)]` auf den beschränkten meßbaren Funktionen; das ist zwar
ein Banachraum, aber für beschränkte Raten ist die Halbgruppe nach unserer
Lipschitzschranke `‖P_t h − h‖ ≤ 2 L t ‖h‖` sogar **gleichmäßig** stetig, also
der triviale Fall mit beschränktem Erzeuger, für den die Picard-Iteration
genügt. Der unbeschränkte Fall, für den ihr Apparat gebaut ist, ist durch
`rem:noch1` bewußt ausgeschlossen. Eine Verzahnung bei den Sprungprozessen
brächte also nichts.

**Ein Unterschied in der Bauweise, der die Einreichung betrifft.** Ihre
`lakefile.toml` sagt: *„Roadmap target signatures should consume existing Tau
Ceti declarations directly rather than restating a Mathlib-only approximation of
the implementation boundary."* Entsprechend importiert ihre `Suggested.lean`
`TauCeti.Analysis.*` und nicht nur Mathlib. Unsere vier Dateien sind reine
Mathlib-Dateien — für ein Gebiet, in dem dort noch nichts steht, ist das
richtig und unvermeidlich, aber es ist eine Abweichung von der Hausregel und
sollte in der PR-Beschreibung genannt werden, statt daß ein Reviewer sie
bemerkt. Sobald etwas von uns dort liegt, gilt die Regel auch für uns.
