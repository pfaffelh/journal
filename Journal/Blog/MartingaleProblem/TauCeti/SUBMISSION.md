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

* `scottnarmstrong/MarkovProcess` — Apache-2.0, `LICENSE` at the root, per-file
  copyright headers (Copyright 2026 Scott Armstrong). Read on 2026-09-22 at
  commit of 2026-09-13. 258 Lean files and about 45,700 lines, **no `sorry`**
  and **no custom `axiom`**, warning-free under the core linters, pinned to
  Lean and Mathlib `v4.33.0` — the same pin this journal carries, and two
  releases behind the `master` these roadmaps target (`v4.35.0-rc2` on
  2026-09-22).

  It constructs, from a transition-kernel semigroup on a locally compact Polish
  state space, the **continuous-path** Markov process with those transition
  probabilities, unique and strong Markov, for every starting point and with no
  exceptional set; on it the killed process, the gluing of local resolvents, the
  one-point compactification, exit times, Dynkin's formula, optional stopping,
  and Feynman–Kac.

  **It does not touch the càdlàg world.** Grepped on 2026-09-22: no `cadlag`,
  no `Skorokhod`, no `MartingaleProblem` anywhere in the 258 files. Path
  continuity comes from an *intrinsic Kolmogorov moment criterion* on the
  semigroup (Kolmogorov–Chentsov), not from a modification of a càdlàg process.
  `SkorokhodSpace` and the abstract martingale problem of `MartingaleProblems`
  therefore do not collide with it at all.

  Four places where it does touch these roadmaps, so that a reviewer's question
  about overlap has an answer already written:

  * `Audit/BrownianMotion/` states, and the library proves, that the centred
    canonical process is `IsBrownianReal` under every starting point, together
    with `t⁻¹ (P_t f − f) → ½ f''` uniformly. That is the **target** of the
    bridge in Milestone 11 of `MartingaleProblems`, reached from the other
    side: from the heat semigroup rather than as the limit of rescaled walks.
    The step "finite-dimensional distributions are the heat kernels ⟹
    `IsBrownianReal`" is the reusable part.
  * `Trajectory/DynkinMartingale.lean` proves that
    `f (ω t) − ∫₀ᵗ (L f) (ω s) ds` is a martingale for a Feller semigroup — the
    *solution* direction of the martingale problem in the special case, on
    continuous-path space.
  * `Trajectory/WeakConvergence.lean` is the structural counterpart of
    Milestone 11: Trotter–Kato gives finite-dimensional convergence, one
    **common** Kolmogorov moment bound gives tightness, and Stone–Weierstrass
    on a single compact set of paths finishes it — its module doc says "three
    epsilons finish the argument; no compactness theorem for measures is used".
    That is deliberately not the route taken here, and the difference is worth
    naming rather than hiding.
  * `Kernel/WeakConvergence.lean` (vague convergence to a probability measure is
    weak convergence, on a locally compact Polish space) and its use of
    Mathlib's Ionescu–Tulcea with its own projective-family reindexing touch the
    edges of `WeakConvergence` and `KolmogorovExtension`.

  The licence permits reuse with attribution, and the same caution applies as to
  `brownian-motion`: nothing is to be accepted merely because it matches that
  file. The version gap is real — taking anything over means porting from
  `v4.33.0` to `master`.

  **One device from that repository is worth copying, and it is process rather
  than mathematics, which is why it is recorded here and in no roadmap.** Its
  `Audit/` holds, for each main theorem, a `Challenge.lean` that imports *only*
  Mathlib, rebuilds from scratch every definition needed to read the theorem,
  states it, and ends with a single `sorry` — checked with
  `leanprover/comparator` — beside a `Solution.lean` proving the byte-identical
  statement through private bridges to the library. It answers, in a form a
  reviewer can check mechanically, the question these roadmaps will be asked
  with their 2,927 declarations: whether the main theorem is the one a reader
  means, or only the one the library's own definitions make it.

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

**ENTSCHEIDUNG DES NUTZERS, 2026-09-17: eine einzige Einreichung.** Die vier
Roadmaps gehen als *ein* PR, und ihre `Suggested.lean` **dürfen aufeinander
aufbauen** — in der Kette `WeakConvergence` → `SkorokhodSpace` →
`MartingaleProblems`, mit `KolmogorovExtension` unabhängig.

Die frühere Empfehlung dieses Dokuments waren vier getrennte PRs. Sie ist
hiermit überholt. Der Grund, der für sie sprach, bleibt bestehen und ist
festzuhalten, damit er in der PR-Beschreibung angesprochen wird: `CONTRIBUTING.md`
nennt substantielles Review das Knappste im Projekt, und ein PR über vier
Roadmaps ist schwerer zu prüfen als vier einzelne. Dem ist in der Beschreibung
entgegenzukommen — die Abhängigkeitskette nennen, den empfohlenen Leseweg
angeben (`WeakConvergence` zuerst, es hängt nur an Mathlib), und die
Meilensteine benennen, die als *roadmap-for-a-roadmap* gekennzeichnet sind.

Was die Entscheidung unmittelbar einlöst: zwei Aussagen, deren `sorry` **keine
offene Mathematik war, sondern eine Dateigrenze**, sind damit beweisbar. Die
erste, `isMPSolution_iff_forall_fdd_continuous`, ist seit dem 2026-09-17
bewiesen.

### Wie die Kette hier gebaut wird

**Seit dem 2026-09-18, dreizehntem Lauf, ist die zweite Kante der Kette
ebenfalls benutzt:** `SkorokhodSpace/Suggested.lean` beginnt mit
`import TauCetiRoadmap.WeakConvergence.Suggested` und nimmt daraus die
f.ü.-stetige Fassung des Abbildungssatzes für Meilenstein 8. Gemessen hat der
Import dort **null Fehler** und keine Anpassung im Bestand gekostet; alles vor
Meilenstein 8 ruht weiterhin allein auf Mathlib. `MartingaleProblems` importiert
beide Dateien wie bisher.

Die Importzeile lautet `import TauCetiRoadmap.WeakConvergence.Suggested` — mit
dem Präfix, unter dem das Zielrepositorium baut (`lakefile.toml` dort:
`lean_lib TauCetiRoadmap` mit `globs = ["TauCetiRoadmap.*"]` über dem
Verzeichnis `TauCetiRoadmap/`). Hier löst sie sich auf, ohne daß unser
Quellverzeichnis so heißen müßte, denn **der Modulname kommt aus der Lage der
`.olean` in `LEAN_PATH` und nicht aus der Lage des Quelltextes**;
`scripts/check_suggested.py` baut die Dateien in Abhängigkeitsordnung und legt
jede `.olean` unter `scratch/_lean/TauCetiRoadmap/<Roadmap>/` ab.

Ein `lean_lib`-Target in `lakefile.lean` gibt es dafür **nicht**, und das ist
Absicht: `lake` bildet Modulnamen auf Quellpfade ab und kennt keine Umlenkung,
also verlangte ein Target ein Verzeichnis `TauCetiRoadmap/` über den vier
Roadmaps — entweder als Symlink auf `TauCeti/` oder durch Umbenennung, die 826
Verweise im Repositorium berührt. Das ist zu entscheiden, ehe es geschrieben
wird. Für die Einreichung selbst ist es gegenstandslos: dort liegen die
Verzeichnisse ohnehin unter `TauCetiRoadmap/`.

**Eine Aufräumarbeit, die der Import nach sich zog, und sie ist erledigt.**
`MartingaleProblems` bildete mehrere Begriffe der beiden Roadmaps unter ihm nach,
mit dem Doc-Satz „restated so that this file stands against Mathlib alone" —
`IsSeparating` und `IsCadlagPath`. Dieser Grund ist mit dem Import entfallen, und
am 2026-09-17, zweiundzwanzigster Lauf, sind beide Nachbildungen gestrichen:

* `IsSeparating` steht nur noch in `WeakConvergence`, dort über einem
  `RCLike`-Skalarkörper statt über `ℝ`. Das ist die Auflösung, die keine Aussage
  doppelt stehen läßt: die reelle Fassung ist die Instanz `𝕂 = ℝ`. Kein Satz von
  Meilenstein 1 mußte dafür angefaßt werden.
* `IsCadlagPath` ist ersetzt durch `IsCadlag` aus `SkorokhodSpace`, mit dem es
  Feld für Feld übereinstimmt; die Namen der Sätze darum sind mitgezogen
  (`isCadlag_jumpProcess`, `IsCadlag.comp_coe_nnreal` und die übrigen).

Damit hält jede Roadmap ihre Begriffe selbst und keine zweite bildet sie nach.

**Und am 2026-09-18, vierundzwanzigster Lauf, ist der angekündigte zweite Schritt
vollzogen:** mit der Umstellung auf `master` tragen `IsCadlag` und
`IsRightContinuous` von `SkorokhodSpace` keinen Grund mehr und sind gestrichen;
die Datei importiert jetzt `Mathlib.Topology.Order.Cadlag` (`#43352`). Mit ihnen
fielen **drei Sätze**, die unter anderem Namen dieselbe Aussage machten wie die
Bibliothek: `isCadlag_const` ist `IsCadlag.const`, `IsCadlag.tendsto_leftLim` ist
`IsCadlag.tendsto_nhdsLT_leftLim`, und `IsCadlag.isBounded_image_of_isCompact`
ist `isBounded_image_of_isCadlag_of_isCompact`. Fünf Deklarationen weniger, und
die Kette baut unverändert mit 0 Fehlern.

**Und das ist der Befund, den die Umstellung eingebracht hat:** solange die Kette
gegen v4.33.1 gebaut wurde, war nicht zu sehen, daß fünf unserer Deklarationen
gegen den Stand, auf den Tau Ceti aufsetzt, Doppelungen der Bibliothek sind. Die
Prüfung gegen `master` ist also nicht bloß eine Formalie des `build`-Checks — sie
ist die einzige, die die Bodenhaftungsregel oben wirklich mißt. Zu erwarten ist,
daß weitere solche Doppelungen entstehen, wann immer Mathlib etwas übernimmt, was
wir hier führen; `#43352` ist die erste.

## Steps

1. Copy the four directories into a fork of `TauCetiProject/TauCetiRoadmap`.
2. For each, open an issue with the `[Intention]` template, titled
   `[Intention]: <specific targets>`, and comment `claim` to register it in the
   shared `leanprover-community/project-intentions` registry.
3. Open **one** pull request for all four roadmaps (the author's decision of
   2026-09-17; see the recommendation above for what to put in the description
   to ease the review load). Merging needs approval from
   `@TauCetiProject/roadmap-reviewers` and a passing `build` check; the first
   merged PR earns triage rights, two earn reviewer status.
4. ~~**`Suggested.lean` must build against Mathlib `master` — and that has never
   been tested.**~~ **Done on 2026-09-18**, in the twenty second, twenty third and
   twenty fourth runs of that day. `scripts/check_master.py` builds the three
   files in dependency order against a worktree on `upstream/master`
   `94ef6b89544e58e90f119da869f3fb48d1da0f4c` (Lean `4.35.0-rc2`), with
   `autoImplicit=false` and `relaxedAutoImplicit=false` as Mathlib does:

   | file | errors | `sorry` | warnings | deprecated |
   | --- | ---: | ---: | ---: | ---: |
   | `WeakConvergence` | 0 | 0 | 18 | 0 |
   | `SkorokhodSpace` | 0 | 0 | 36 | 0 |
   | `MartingaleProblems` | 0 | 0 | 106 | 0 |

   The 160 remaining warnings are style, not deprecation: 58
   `unusedSectionVars`, 50 "Try this", 24 unused `simp` arguments, 22 unused
   binder hints, six singletons. Following `unusedSectionVars` would mean
   changing signatures.

   **`master` is now the reference, and `v4.33.1` is not.** There is no spelling
   that works on both, and four families witness it: `ProbabilityMeasure.map`
   (no measurability argument on master), `measurable_pi_lambda`/`Measurable.of_eval`,
   `Filter.eventuallyEq_set`/`Filter.eventuallyEqSet_iff`, and — with 274 call
   sites, the largest — `if_pos`/`if_neg`/`dif_pos`/`dif_neg`, whose replacements
   `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right` exist on v4.33.1
   neither in the Lean core nor in Mathlib. `scripts/check_suggested.py` still
   runs against v4.33.1, but its errors are to be **reported**, not fixed.

   **What is not done, and is the one thing a reviewer will see:** the cited
   Mathlib line numbers throughout the roadmaps are still those of v4.33.1.
   `scripts/check_cited_names.py` checks that a cited *name* exists, not that it
   sits on the cited line, and the two do drift — `Set.mem_setOf_eq` stood at
   `Data/Set/Operations.lean:82` on v4.33.1 and at `:81` on master, which is the
   benign case.

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
