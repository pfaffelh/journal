# Inventar der `Fact`-Aussagen

Die 29 mit `\begin{fact}` ausgezeichneten Aussagen des Manuskripts sind seine
**Voraussetzungsfläche**: alles, was zitiert und nicht bewiesen wird. Eine
Formalisierung ist genau dann vollständig geplant, wenn zu jeder dieser Aussagen
feststeht, ob sie in Mathlib liegt, von einer der vier Roadmaps abgedeckt wird,
oder eine Lücke ist. Dieses Inventar hält das fest, eine Zeile je Fact.

Bis heute war diese Abdeckung von Hand zusammengetragen und **nachweislich
lückenhaft**: der Durchgang am 2026-08-29 fand in den Roadmaps drei falsche oder
veraltete Mathlib-Zitate und mehrere Punkte, die längst oben liegen. Das
Inventar ersetzt das Gedächtnis durch eine Liste.

## Spalten

* **tragend** — Zahl der Abschnitte, in denen der Fact außerhalb der
  Buchhaltungsabschnitte (§2.x „Where the prerequisites are used", §8, §9,
  Notation, Bündeltabelle) benutzt wird. Das ist die Prioritätsordnung: was
  nirgends tragend vorkommt, ist entweder implizit benutzt oder überflüssig, und
  beides will geklärt sein.
* **Status** — `Mathlib` (mit Deklaration), `Roadmap` (mit Meilenstein),
  `Lücke`, `bewusst` (zitiert, absichtlich nicht formalisiert), `entbehrlich`
  (im Manuskript zitiert, von keinem Beweis getragen, in keiner Roadmap mehr —
  mit Begründung und Datum), `?` (unbestimmt).
* **Beleg** — die Deklaration oder der Meilenstein. Ein Status ohne Beleg zählt
  als `?`.

## Regel

Ein Status wird nur eingetragen, wenn er **am Quelltext geprüft** wurde: die
Mathlib-Deklaration existiert unter diesem Namen und ist nicht `deprecated`, oder
der Meilenstein nennt die Aussage. Nicht aus dem Gedächtnis. Wer einen Status
setzt, nennt den Beleg.

## Regel für den Negativbefund

Vier Fehler dieses Inventars — `Locally` statt „local martingale",
`IsStronglyProgressive` statt `ProgMeasurable`, `upcrossingsBefore` statt
`upcrossing`, und am 2026-09-05 `SeparatesPoints`+`IsTightMeasureSet` statt
„konvergenzbestimmend" — hatten dieselbe Ursache: gesucht wurde nach dem
**Begriff**, den das Manuskript benutzt, statt nach der **Aussage**. Mathlib hat
kein Prädikat „konvergenzbestimmend", also schien der Satz zu fehlen; er stand
die ganze Zeit da, unter seinem mathematischen Namen.

Daher: wer „Mathlib hat das nicht" schreiben will, formuliert die Aussage
vorher **ohne unsere Vokabeln**, in Mathlibs eigenen Begriffen, und sucht
danach. Und wer sie dann noch immer nicht findet, nennt im Bericht die
Formulierungen, mit denen er gesucht hat. Ein Negativbefund ohne diese Liste
ist kein Befund, sondern ein `?`.

## Tabelle

| Fact | tragend | Aussage | Status | Beleg |
|---|---|---|---|---|
| `fact:Dcountable` | 4 | EK, Lemma 3.7.7 | Roadmap | SkorokhodSpace M8, `SkorokhodSpace.exists_countable_dense_continuity`; Mathlib hat weder `cadlag` noch den Raum. Der Unterbau ist seit dem 2026-09-07, fünftem Lauf, bewiesen und geht durch `lake env lean`: `countable_leftJumpSet` — die Sprungmenge **einer** càdlàg-Abbildung ist abzählbar — samt `IsCadlag.continuousAt_iff_notMem_leftJumpSet`, die „Stetigkeitsstelle" und „nicht in `leftJumpSet`" identifiziert (Meilenstein 2). Was M8 darüber hinaus verlangt, ist die Fassung für **ein Maß** statt für einen Pfad — daß `{t | μ {f | f⁻ t = f t} = 1}` abzählbares Komplement hat —, und die folgt nicht punktweise aus der Pfadaussage, sondern braucht ein Fubini-Argument über die Sprunghöhen; das steht weiter aus |
| `fact:monotoneclass` | 4 | Monotone class theorem; EK, Appendix 4 | Roadmap | WeakConvergence M5, `induction_on_mulSystem` — dort neu angelegt; Mathlib hat nur die Mengenfassung, und sie heißt `MeasurableSpace.induction_on_inter` (`MeasureTheory/PiSystem.lean:713`, nicht `MeasureTheory.`). Am 2026-09-06, zweiter Lauf, negativ belegt an `upstream/master` `810b3888` mit den Suchen `monotone class`, `MulSystem`, `generateFromFuns`, `multiplicative system`, `monotone limits`, `bounded monotone convergence`, `functional monotone`, `multiplicative family of functions` — kein einziger Treffer in `Mathlib/`. Der Unterbau ist seither übersetzt: `IsMulSystem`, `indicatorFuns`, `generateFromFuns`, die Brücke `generateFromFuns_indicatorFuns`, das π-System `ioiCells` samt `generateFromFuns_eq_generateFrom_ioiCells` und der erste Beweisschritt `of_tendstoUniformly_of_mono_lim` gehen durch `lake env lean`; seit dem 2026-09-06, dritter Lauf, dazu die algebraische Hälfte des zweiten Schritts — `mul_mem_span_insert_one_of_isMulSystem`, `of_mem_span_insert_one`, `exists_bound_of_mem_span_insert_one` — und die Aussage des Schritts selbst, `of_continuous_comp_of_isMulSystem` |
| `fact:cmt` | 3 | Continuous mapping theorem; EK, Corollary 3.1.9 and Co | Roadmap | WeakConvergence M2 — der stetige Fall ist Mathlib in **beiden** Fassungen, für Maße als `FiniteMeasure.tendsto_map_of_tendsto_of_continuous` und für Zufallsvariablen als `MeasureTheory.TendstoInDistribution.continuous_comp` (`MeasureTheory/Function/ConvergenceInDistribution.lean:136`, am 2026-09-01, fünfter Lauf, gefunden); die f.ü.-stetige Fassung fehlt in beiden. M2 steht auf „separabel metrisch", und das ist richtig: EK Cor. 3.1.9 verlangt nicht mehr (am Scan geprüft, 2026-08-31) |
| `fact:kolmogorov` | 3 | Kolmogorov extension; EK, Theorem 4.1.1; eqref{T0} + e | Roadmap | KolmogorovExtension M2 — Gerüst weitgehend in Mathlib, es fehlen σ-Subadditivität und `projectiveLimit` |
| `fact:stoneweierstrass` | 3 | Stone--Weierstrass for separating classes; EK, Theorem | Roadmap | WeakConvergence M1 — die separierende Hälfte ist Mathlib (`ext_of_forall_mem_subalgebra_integral_eq_of_polish`); die konvergenzbestimmende ist es **auch**, unter Straffheit und bloßer Punktetrennung: `MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`, `MeasureTheory/Measure/LevyConvergence.lean:154`, am 2026-09-05 an `upstream/master` geprüft, nicht `deprecated`. Es fehlt allein der Schritt von **starker** Trennung zu Straffheit, in M1 als `isTightMeasureSet_of_stronglySeparatesPoints` angelegt (2026-09-05). Die separierende Hälfte ist seit dem 2026-09-06, drittem Lauf, auch auf unserer Seite bewiesen: `IsSeparating.of_subalgebra`, die Anbindung unseres Prädikats an `ext_of_forall_mem_subalgebra_integral_eq_of_polish`, geht durch `lake env lean`. ~~die konvergenzbestimmende fehlt~~ — dieser Befund stand vom 2026-08-29 bis zum 2026-09-05 und war falsch: gesucht worden war nach unserer Vokabel „konvergenzbestimmend" statt nach der Aussage, die in Mathlib unter `SeparatesPoints` und `IsTightMeasureSet` steht. **Am 2026-09-06, dritter Lauf, belegt, daß dieser Weg in Mathlib nicht bloß vorhanden, sondern tragend ist:** `Measure.ext_of_charFun` (`Measure/CharacteristicFunction/Basic.lean:257` auf `upstream/master` `810b3888`, `:248` in v4.33.1) und `Measure.ext_of_charFunDual` (`:462` bzw. `:453`) — „charakteristische Funktionen trennen endliche Maße" — ruhen über `ext_of_integral_char_eq` (`:103` bzw. `:101`) Zeile für Zeile auf `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable` (`Measure/FiniteMeasureExt.lean:36`), angewandt auf `separatesPoints_charPoly` (`Analysis/Fourier/BoundedContinuousFunctionChar.lean:155`). Charakteristische Funktionen sind dort **kein eigenes Fundament**, sondern eine Anwendung der punktetrennenden Unteralgebra `charPoly` (`ibid.:141`), und diese ist eine `StarSubalgebra ℂ (V →ᵇ ℂ)` — also genau die Konjugationsabgeschlossenheit, die der Fact für $\K=\C$ verlangt. Keine der vier Deklarationen ist `deprecated` |
| `fact:bp` | 2 | EK, Lemma 3.4.1, Proposition 3.4.2, and Appendix 3, Pr | entbehrlich (2026-08-30) | Kein Beweis des Manuskripts benutzt `cor:bpclosure`, und EK 4.3.1 trägt dort nichts; der bp-Abschluss ist am 2026-08-30 aus MartingaleProblems M2 gestrichen und durch `insert_of_tendsto_of_forall_norm_le` und `submartingale_mpProcess_of_tendsto` ersetzt, M9 trägt die Anwendung (EK 4.3.9/4.3.10) |
| `fact:cadlagext` | 2 | Regularization along a dense set; EK, Lemma 2.2.8; eqr | Roadmap | MartingaleProblems M9; Vorarbeit in `brownian-motion` (Apache-2.0) |
| `fact:optsampl` | 2 | Optional sampling; EK, Theorem 2.2.13, Remark 2.2.14,  | Roadmap | MartingaleProblems M9, `Submartingale.stoppedValue_min_le_condExp` — dort neu angelegt; Mathlibs `Martingale.stoppedValue_min_ae_eq_condExp` ist der diskrete Fall und nur für Martingale |
| `fact:prohorov` | 2 | Prohorov; EK, Lemma 3.2.1 and Theorem 3.2.2 | Mathlib | `MeasureTheory/Measure/Prokhorov.lean`, `isCompact_closure_of_isTightMeasureSet` und Umkehrung |
| `fact:relcompact2` | 2 | Relative compactness, II; EK, Theorem 3.9.4 | Roadmap | MartingaleProblems M11, `isTight_map_postcomp_of_exists_martingale` — dort neu angelegt; `isRelativelyCompact_of_approx` nannte nur die Folgerung, nicht das Kriterium |
| `fact:sepcond` | 2 | Conditional determination by separating sets; EK, Chap | Roadmap | WeakConvergence M1, `IsSeparating.ae_eq_of_forall_condExp_eq` — seit dem 2026-09-06, erster Lauf, mit Beweis und durch `lake env lean`; Mathlib liefert `Filter.EventuallyEq.of_forall_separating_preimage` als Schlussschritt. Die trennende Klasse `M`, die der Fact **konsumiert**, ist in Mathlib mit `charPoly` und `Measure.ext_of_charFun` fertig instanziiert (siehe `fact:stoneweierstrass`) — aber nur über einem vollständigen zweitabzählbaren Innenprodukt- bzw. Banachraum. Am 2026-09-06, dritter Lauf, wurde jede Fundstelle des Manuskripts durchgesehen, an der eine trennende Klasse konkret instanziiert wird; an **keiner** liegt diese lineare Struktur vor, siehe den Laufbericht |
| `fact:submgreg` | 2 | Submartingale regularization; EK, Proposition 2.2.9; e | Roadmap | MartingaleProblems M9; Vorarbeit in `brownian-motion` (Apache-2.0) |
| `fact:ui` | 2 | Uniform integrability; EK, Appendix 2 | Mathlib+ | `MeasureTheory.UniformIntegrable`, `uniformIntegrable_iff`; die Kopplung an Verteilungskonvergenz fehlt → WeakConvergence M4 |
| `fact:MZtight` | 1 | Tightness; MZ, Theorem~4, and Ku | Roadmap | MartingaleProblems M11 |
| `fact:PSpolish` | 1 | EK, Theorems 3.1.7 and 3.1.8 | Roadmap | WeakConvergence M3 — Skorokhod-Darstellung fehlt in Mathlib (dort nur `docs/1000.yaml`); dass 𝒫(S) separabel bzw. polnisch ist, fehlt seit dem 2026-08-31 belegt ebenfalls (Mathlib hat nur `instMetrizableSpaceProbabilityMeasure`), und steht jetzt als eigener Block in M3; der Block ist am 2026-08-31, dritter Lauf, auf typrichtige Aussagen gebracht — `CompleteSpace` gehört auf `LevyProkhorov (ProbabilityMeasure S)`, auf `ProbabilityMeasure S` gibt es keine Uniformität |
| `fact:convdet` | 1 | EK, Proposition 3.4.4 | Roadmap | WeakConvergence M1, `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support` (separabel metrisch) und `isConvergenceDetermining_setOf_hasCompactSupport` (zusätzlich lokalkompakt) — am 2026-09-05 dort neu angelegt. ~~M1~~ nannte die Aussage bis dahin **nicht**: das Zitat war seit dem 2026-08-29 leer, kein Punkt von M1 spricht von gleichmäßig stetigen Funktionen mit beschränktem Träger oder von $C_c$. Mathlib hat sie nicht — in `MeasureTheory/Measure/` kommt `UniformContinuous` überhaupt nicht vor und `HasCompactSupport` in keiner Konvergenzaussage (`upstream/master`, 2026-09-05) |
| `fact:fddconv` | 1 | EK, Theorem 3.7.8 | Roadmap | SkorokhodSpace M8, `tendsto_finiteDimensional_of_tendsto` (a) und `tendsto_of_isCompact_closure_of_tendsto_finiteDimensional` (b); beide stehen seit dem 2026-08-31 unter Stufe (A) „separabel metrisch", wie der Fact, und (b) unter Relativkompaktheit statt Straffheit, wie EK |
| `fact:fullgenerator` | 1 | EK, Proposition 1.5.1 | Roadmap | MartingaleProblems M13 — dort neu angelegt; Mathlib hat keine Operatorhalbgruppen, `dissipative` kommt nicht vor, Hille--Yosida steht als `Q974405` ohne `decl` in `docs/1000.yaml` |
| `fact:jacodmemin` | 1 | Continuous mapping, Jacod--M'emin; CPS, Theorem 2.9 | bewusst | nicht formalisiert; `rem:augvsws` begründet, warum Augmentierung genügt |
| `fact:picard` | 1 | Picard--Lindel"of for SDEs | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:pseudopath` | 1 | Pseudo-paths; MZ, Section~1 and Lemma~1 | Roadmap | MartingaleProblems M11 |
| `fact:relcompact` | 1 | Relative compactness, I; EK, Theorem 3.9.1 | Roadmap | SkorokhodSpace M8, `isTightMeasureSet_iff_forall_postcomp` mit `continuous_postcomp` — dort neu angelegt |
| `fact:stoppingtimes` | 1 | EK, Propositions 2.1.2 and 2.1.4; eqref{T2b} | Mathlib | `MeasureTheory.IsStoppingTime` in `Probability/Process/Stopping.lean` |
| `fact:strookvaradhan` | 1 | Stroock--Varadhan; KA, Theorem 32.7 | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:yamadawatanabe` | 1 | Yamada--Watanabe | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:doob` | 0 | Doob's inequalities; EK, Corollary 2.2.17; eqref{T2b} | Roadmap | MartingaleProblems M9, `maximal_ineq_of_rightContinuous` und `Submartingale.eLpNorm_iSup_le` — dort neu angelegt; Mathlibs `MeasureTheory.maximal_ineq` ist `Filtration ℕ`, die `Lᵖ`-Ungleichung fehlt ganz |
| `fact:fdd` | 0 | EK, Proposition 3.4.6 and Proposition 3.7.1 | Roadmap | WeakConvergence M1 (Produktpunkt, am 2026-08-29 von endlichem auf beliebigen Index gebracht) und SkorokhodSpace M6, `borel_eq_iSup_comap_eval`; die Produkthälfte trägt kein Beweis, §9 verlangt sie — Auffälligkeit vom 2026-08-31. Die Zuschreibung des Facts stimmt und teilt sich sauber: EK Prop. 3.4.6 ist die Produkthälfte, EK Prop. 3.7.1 die Pfadraumhälfte (am Scan geprüft, 2026-08-31, zweiter Lauf) |
| `fact:portmanteau` | 0 | Portmanteau; EK, Theorem 3.3.1 | Mathlib | `MeasureTheory/Measure/Portmanteau.lean`; (a)⟺(b) ist `MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph` (`Measure/LevyProkhorovMetric.lean:676`). Kein Beweis benutzt (c)–(f) — Auffälligkeit vom 2026-08-31 |
| `fact:stoppedlocalmg` | 0 | EK, Proposition 2.3.1 | Roadmap | MartingaleProblems M9, `isStable_martingale_rightContinuous` — dort neu angelegt; `ProbabilityTheory.Locally`, `IsStable` und `IsStable.locally` sind Mathlib (`Probability/Process/LocalProperty.lean:93,142,153`, Namensraum am 2026-09-01 berichtigt), der Martingalfall ist es nicht |

## Offene Auffälligkeiten

* **`thm:fdd` braucht, daß ein größtes Element in $D$ liegt; gefunden am
  2026-09-06, fünfter Lauf, beim Beweisen von `IsCadlag.eq_of_eqOn_dense`.**
  Der Satz („Borel equals cylinder", §3.3) verlangt von $D\subset\T$ nur
  „countable and dense" und behauptet, $\pi_D:\DT\to E^D$ sei eine meßbare
  Einbettung. Unter \eqref{T3p} ist er so falsch, und zwar aus zwei Gründen,
  beide an einem Punkt, an dem es keinen Rechtslimes gibt.
  * Ein **größtes** Element muß in $D$ liegen. Auf $\T=[0,1]$ mit
    $D=[0,1)\cap\Q$ sind $f\equiv0$ und $g=\mathbb 1_{\{1\}}$ beide càdlàg —
    die Rechtsstetigkeit in $1$ ist leer, weil $\mathcal N_{>1}=\bot$ ist —,
    stimmen auf $D$ überein und sind verschieden; $\pi_D$ ist also nicht
    injektiv. \eqref{T2b} sieht das ausdrücklich vor („a maximal element is
    allowed … and is the one point at which a right limit is not available"),
    zieht daraus aber nicht die Folgerung für $D$. Billingsley verlangt an
    dieser Stelle für $D([0,1])$, daß die dichte Menge die $1$ enthält.
  * \eqref{T3p} verlangt \eqref{T2b} **nicht**, und ohne dessen Klausel
    scheitert es schon an nicht maximalen Punkten: $\T=[0,1]\cup\{2\}$ ist ein
    abgeschlossenes $\R$-Teilstück und erfüllt \eqref{T3p}, aber $1$ ist
    rechtsisoliert, ohne isoliert zu sein; mit $D=([0,1)\cap\Q)\cup\{2\}$
    trennen dieselben zwei Funktionen. Für $\T=[0,\infty)$ und $\T=[0,T]$ —
    \eqref{T3} — tritt nur der erste Fall auf.

  **Das Manuskript kennt die Klausel und schreibt sie an einer anderen Stelle
  auch hin:** `thm:absconv` verlangt für den Fall $D\subsetneq\T$ ausdrücklich,
  „$D$ contains the greatest element of $\T$ if there is one" (Zeile 8401). Es
  ist also keine Lücke der Theorie, sondern eine Hypothese, die in `thm:fdd`
  fehlt. Das Manuskript wird von diesen Läufen nicht geändert; die Roadmap
  **SkorokhodSpace** trägt die Bedingung seit heute in Meilenstein 2, als
  Disjunktion „$t\in D$ oder $t$ ist Häufungspunkt von $D$ von rechts", und
  `IsCadlag.eq_of_eqOn_dense` ist unter ihr bewiesen.

* **„\eqref{T3p} implies \eqref{T2b}" stimmt wörtlich nicht; gefunden am
  2026-09-06, fünfter Lauf, neben der vorigen Auffälligkeit.** Der Absatz nach
  `thm:DEpolish` (Zeile 2092) nennt die abzählbare dichte Teilmenge „available by
  \eqref{T2b}, which \eqref{T3p} implies". \eqref{T2b} verlangt aber
  $D\cap(t,u)\neq\emptyset$ für **alle** $t<u$ mit $t$ nicht maximal, und in
  einer diskreten Ordnung ist $(t,u)$ leer: $\Z$ erfüllt \eqref{T3p} — die
  Metrik ist additiv, induziert die (diskrete) Ordnungstopologie, und
  abgeschlossene Kugeln sind endlich —, verletzt \eqref{T2b} aber an jedem
  Punkt. Die Roadmap **SkorokhodSpace** führt `AddSubgroup.zmultiples h` in
  Meilenstein 1 genau als Instanz dieses Bündels. Folgenlos ist es an der
  zitierten Stelle, weil dort nur die Separabilität gebraucht wird und die aus
  \eqref{T3p} direkt folgt (abgeschlossene Teilmenge von $\R$); zu prüfen wäre
  jede andere Stelle, die \eqref{T2b} aus \eqref{T3p} zieht.

* **`IsConvergenceDetermining.isSeparating` ist falsch; am 2026-09-05, dritter
  Lauf, berichtigt.** `WeakConvergence` Meilenstein 1 führte den Punkt seit
  Anbeginn, und `Suggested.lean` hatte ihn als Satz. Er gilt nicht: `IsSeparating`
  ist über **endliche** Maße erklärt, konvergenzbestimmend ist über
  Wahrscheinlichkeitsmaße erklärt, und eine konvergenzbestimmende Klasse muß die
  Gesamtmasse nie sehen. Gegenbeispiel in einer Zeile: auf dem einpunktigen Raum
  ist `ProbabilityMeasure E` ein Punkt, also ist **jede** Menge von Funktionen
  konvergenzbestimmend, auch `∅`; und `∅` trennt das Diracmaß nicht von seinem
  Doppelten. An die Stelle tritt `IsConvergenceDetermining.eq_of_forall_integral_eq`
  — eine konvergenzbestimmende Klasse trennt Wahrscheinlichkeitsmaße —, bewiesen
  über die konstante Folge und `MeasureTheory.ProbabilityMeasure.t2Space`
  (`Measure/ProbabilityMeasure.lean:440`, dort kommt `HasOuterApproxClosed`
  herein). Berichtigt sind die Roadmap und `Suggested.lean`.

* **Der Lokalisierungsapparat steht in `ProbabilityTheory`, nicht in
  `MeasureTheory`; am 2026-09-01, zweiter Lauf, berichtigt.** `MartingaleProblems`
  führte `MeasureTheory.IsPreLocalizingSequence`,
  `MeasureTheory.IsLocalizingSequence`, `MeasureTheory.Locally` und
  `MeasureTheory.IsStable`, und dieses Inventar schrieb es nach. Falsch, und
  zwar in v4.33.1 **wie** auf master: `Mathlib/Probability/Process/LocalProperty.lean`
  eröffnet in Zeile 50 `namespace ProbabilityTheory` und schließt in Zeile 345,
  während der Rest von `Mathlib/Probability/Process/` — `Stopping.lean`,
  `Adapted.lean`, `Filtration.lean` — in `MeasureTheory` liegt. Die Datei ist
  also die Ausnahme, und genau deshalb hat es sich gehalten. Mitgefunden: die
  Namen `locally_and_iff` und `locally_locally_iff` sind `IsStable.`-Namen, nicht
  freie (`:161`, `:306`), und das zweite verlangt `[IsRightContinuous 𝓕]`.
  `Locally.of_prop`, `Locally.mono`, `Locally.localSeq` und
  `Locally.stoppedProcess_localSeq` stimmen. Berichtigt sind die Roadmap an drei
  Stellen, `Suggested.lean` und die Tabellenzeile zu `fact:stoppedlocalmg`.
  `FiniteDimensionalLaws.lean` und `Kolmogorov.lean` liegen ebenfalls in
  `ProbabilityTheory`; dort stand kein falscher Namensraum, nur gar keiner, und
  die Roadmap nennt ihn jetzt.
* **Derselbe Namensraumfehler noch zweimal, in `KolmogorovExtension`; am
  2026-09-01, vierter Lauf, berichtigt.** Der Befund vom zweiten Lauf des Tages
  war nicht auf `MartingaleProblems` beschränkt. `KolmogorovExtension` führte
  `MeasureTheory.isProjectiveLimit_infinitePi` — die Deklaration steht in
  `Mathlib/Probability/ProductMeasure.lean:363` innerhalb von `namespace Measure`
  (Zeile 346) innerhalb von `namespace MeasureTheory` (Zeile 56), heißt also
  `MeasureTheory.Measure.isProjectiveLimit_infinitePi` — und
  `MeasureTheory.isProjectiveLimit_map`, das in Wahrheit
  `ProbabilityTheory.isProjectiveLimit_map` heißt
  (`Probability/Process/FiniteDimensionalLaws.lean:53`, `namespace
  ProbabilityTheory` ab Zeile 38). Der zweite ist wörtlich derselbe Fall wie am
  zweiten Lauf: `Mathlib/Probability/Process/` liegt in `MeasureTheory`, und
  `FiniteDimensionalLaws.lean` ist neben `LocalProperty.lean` die zweite
  Ausnahme. Beide Zitate sind berichtigt.
* **`KolmogorovExtension` Meilenstein 2 verlangte einen Satz, den Mathlib
  hat; am 2026-09-01, vierter Lauf, gestrichen.** Der letzte Punkt lautete
  „`MeasureTheory.IsProjectiveLimit.unique`: zwei projektive Limiten derselben
  Familie stimmen überein, aus `generateFrom_measurableCylinders` und
  `MeasureTheory.ext_of_generate_finite`". Das ist nicht zu bauen: die
  Deklaration steht unter genau diesem Namen in
  `Mathlib/MeasureTheory/Constructions/Projective.lean:150`, und ihr Beweis ist
  Zeile für Zeile der angegebene Weg. Mitgefunden und ebenfalls schon da:
  `IsProjectiveLimit.isFiniteMeasure` (`:133`),
  `IsProjectiveLimit.isProbabilityMeasure` (`:139`),
  `measure_cylinder` (`:123`), `measure_univ_eq` (`:129`) und
  `measure_univ_unique` (`:145`) — womit auch der vorletzte Punkt von
  Meilenstein 2 auf eine Zeile schrumpft. Die Kopfliste nennt die
  Uniquenessschicht jetzt, der Meilenstein verlangt sie nicht mehr.
* **`WeakConvergence` verlangte vier Punkte, die Mathlib seit v4.33.1 hat, und
  kannte die Datei nicht, die sie enthält; am 2026-09-01, fünfter Lauf,
  berichtigt.** `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`
  (Rémy Degenne) führt `MeasureTheory.TendstoInDistribution` als **Struktur**
  mit den Feldern `forall_aemeasurable`, `aemeasurable_limit` und `tendsto`, und
  ihre Zufallsvariablen `X i : Ω i → E` leben auf einer **Familie** von
  Wahrscheinlichkeitsräumen, eine je Index. Genau das hatte Meilenstein 4 als
  fehlend geführt („where the random variables live on different spaces and only
  their laws are comparable"). Vier Punkte fallen damit weg oder ändern ihre
  Gestalt: der Satz von der stetigen Abbildung in Zufallsvariablenform ist
  `TendstoInDistribution.continuous_comp` (`:136`), die Slutsky-Fassung
  „`X n → Z` in Verteilung und `dist (X n) (Y n) → 0` nach Maß" ist
  `tendstoInDistribution_of_tendstoInMeasure_sub` (`:192`), die eigentlichen
  Slutsky-Sätze sind `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`
  (`:313`), `…continuous_comp_prodMk_of_tendstoInMeasure_const` (`:333`) und
  `…add_of_tendstoInMeasure_const` (`:345`), und die Rückrichtung der
  Skorokhod-Darstellung ist `tendstoInDistribution_of_ae_tendsto` (`:152`) —
  bereits für einen Filter mit `[l.IsCountablyGenerated]`, nicht nur für `ℕ`.
  Der Name, den Meilenstein 3 dafür nannte, `MeasureTheory.tendsto_of_ae_tendsto`,
  **existiert nicht**. Die Datei steht in v4.33.1 genauso da wie auf master; das
  ist kein Nachziehen hinter master, sondern eine nie gestellte Suche. Was von
  Meilenstein 2 bleibt, ist der eine Schritt von `Continuous h` zur Stetigkeit
  außerhalb einer Nullmenge, und Meilenstein 4 nimmt `TendstoInDistribution`
  jetzt als Hypothese, statt die verschiedenen Räume selbst zu erfinden.
* **Und ein fünfter Punkt derselben Art:** Meilenstein 2 verlangte
  `measurableSet_setOf_continuousAt` „if Mathlib does not already have" es. Es
  hat es: `measurableSet_of_continuousAt`, **Wurzelnamensraum**,
  `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:252`, unter
  `[OpensMeasurableSpace α]` und `[PseudoEMetricSpace β]`, bewiesen aus
  `IsGδ.setOfPred_continuousAt` (`Topology/GDelta/MetrizableSpace.lean:51`) und
  `IsGδ.measurableSet` (`BorelSpace/Basic.lean:248`). Der konditionale Nebensatz
  war zugleich ein Formverstoß gegen die Regeln von Tau Ceti; er ist weg.
* **Der Namensraumfehler von `FiniteDimensionalLaws.lean` ein drittes Mal, in
  `MartingaleProblems`; am 2026-09-01, fünfter Lauf, berichtigt.** Meilenstein 2
  nannte für `IsMPSolutionFor.map` den Namen
  `MeasureTheory.map_eq_of_forall_ae_eq`. Die Deklaration steht in
  `Mathlib/Probability/Process/FiniteDimensionalLaws.lean:99`, und diese Datei
  eröffnet in Zeile 38 `namespace ProbabilityTheory` und schließt ihn in Zeile
  106; sie heißt also `ProbabilityTheory.map_eq_of_forall_ae_eq`. Dieselbe Datei
  und derselbe Fehler wie bei `ProbabilityTheory.isProjectiveLimit_map` im
  vierten Lauf und wie bei `Locally` im zweiten. Mitgeprüft und richtig:
  `identDistrib_iff_forall_finset_identDistrib` (`:77`), jetzt ebenfalls mit
  Namensraum genannt.
* **`MartingaleProblems` Meilenstein 2 verlangte weniger, als Mathlibs
  `Locally` braucht; am 2026-09-01, sechster Lauf, berichtigt.** Der Meilenstein
  eröffnete mit „Fix `[Preorder ι]`" und definierte darunter
  `IsLocalMPSolution` als `∀ Y ∈ 𝓧, Locally (fun Z ↦ Martingale Z 𝓕 P) 𝓕 Y P`.
  Das ist unter `[Preorder ι]` nicht hinschreibbar.
  `ProbabilityTheory.Locally` steht in
  `Mathlib/Probability/Process/LocalProperty.lean` **innerhalb** von
  `section LinearOrder`, unter `variable [LinearOrder ι]` (`:77`) und
  `variable [OrderBot ι]` (`:88`), und führt eigene Binder
  `[TopologicalSpace ι] [OrderTopology ι] [Zero E]` (`:93`). Das Bodenelement
  ist keine Zierde: die Definition stoppt den Prozess durch
  `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)`, nennt also `⊥`, und `[Zero E]` ist,
  was dieser Indikator verlangt. Dasselbe gilt für `ProbabilityTheory.IsStable`
  (`:142`, gleicher Variablenblock). Der Meilenstein führt jetzt zwei benannte
  Stufen, **(A)** `[Preorder ι]` für das globale Problem und **(L)** zusätzlich
  `[LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]` für das
  lokale, nach dem Muster von `SkorokhodSpace` Meilenstein 2. Meilenstein 7, der
  ausschließlich über `Locally` spricht, stand mit demselben zu schwachen
  `[Preorder ι]` da und erbt die Stufe (L) jetzt ausdrücklich. Mitgeprüft und
  richtig: die Argumentreihenfolgen `Locally p 𝓕 X P` (`:93`) und
  `IsStable 𝓕 p` (`:142`), die die Roadmap an beiden Stellen so schreibt.
  `Suggested.lean` hatte denselben Fehler und hatte ihn halb gesehen — es setzte
  `[TopologicalSpace ι] [OrderTopology ι]` und ließ Linearität und Boden aus;
  dort ist `ι` jetzt in einem eigenen `section Local` neu gebunden, statt einen
  weiteren Instanzbinder neben das dateiweite `[Preorder ι]` zu stellen.
  **Übersetzt ist nichts** — der Worktree hat kein `.lake`.
* **Milestone 9 nannte `⊥` ohne `[OrderBot ι]`, und `IsQuasiLeftContinuous` war
  ein Typfehler; am 2026-09-01, sechster Lauf, berichtigt.** Zweierlei, beides
  aus derselben Wurzel — Mathlibs Stoppzeiten sind `WithTop ι`-wertig.
  Erstens schrieb das Stabilitätsstück
  `stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (Y t)) τ` unter einer
  Präambel, die nur `[LinearOrder ι]`, Ordnungstopologie und ein abzählbar
  dichtes `D` festlegt; `[OrderBot ι]` kam erst dreißig Zeilen später für den
  Block über offene Teilmengen. Die Formel ist wörtlich die von Mathlibs
  `IsStable` (`LocalProperty.lean:142`), und Mathlib führt sie unter
  `variable [OrderBot ι]` (`:88`) — die Hypothese steht jetzt an der Präambel und
  am Punkt. Zweitens definierte der letzte Block
  `IsQuasiLeftContinuous` „für jedes `τ : ℕ → Ω → ι`, mit jedem `τ n` eine
  Stoppzeit für `𝓕`". Das geht nicht:
  `IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω → WithTop ι)`
  (`Probability/Process/Stopping.lean:76` auf master, `:75` in v4.33.1 — **keine
  Versionsdrift**, der Typ steht in beiden so da). Der Punkt widersprach
  überdies seiner eigenen Begründung, die vom Ereignis `{τ < ∞}` spricht und
  damit voraussetzt, was der Typ verbietet. Berichtigt auf
  `τ : ℕ → Ω → WithTop ι` mit `MeasureTheory.stoppedValue` (`:797`,
  `fun ω ↦ u (τ ω).untopA ω`) für das Ablesen; `WithTop.untopA` ist das
  Ordnungsduale von `WithBot.unbotA` (`Order/WithBot.lean:270`,
  `noncomputable abbrev` unter `[Nonempty α]`), und `[OrderBot ι]` liefert dieses
  `Nonempty` bereits, so dass keine Hypothese hinzukommt. Das Supremum lebt in
  `WithTop ι` über die Instanz `SupSet (WithTop α)` für `[SupSet α]`
  (`Order/ConditionallyCompleteLattice/Basic.lean:52`) — die vom Block ohnehin
  geforderte bedingt vollständige Verbandsstruktur genügt. Die späteren Punkte
  desselben Blocks kürzen `stoppedValue X (fun ω ↦ min (τ n ω) t) ω` zu
  `X (min (τ n ω) t) ω`; die Blockpräambel sagt das jetzt einmal, statt jede
  Formel umzuschreiben.
* **Vier Facts ohne tragende Fundstelle** — `fact:doob`, `fact:fdd`,
  `fact:portmanteau`, `fact:stoppedlocalmg` werden nur in den
  Buchhaltungsabschnitten zitiert. Zu klären: implizit benutzt (dann die Stelle
  benennen) oder entbehrlich (dann aus §2 streichen). Für `fact:doob` ist die
  Antwort schon da: die Tabelle in §2 nennt selbst
  „Remark~`rem:EKrelcompact` (via Fact~`relcompact2`)", der Fact wird also
  mittelbar getragen und ist nicht entbehrlich. Die Spalte **tragend** zählt nur
  direkte `\ref`s und unterschätzt ihn deshalb; dasselbe ist für die anderen
  drei zu prüfen. Für `fact:stoppedlocalmg` am 2026-08-30 geprüft: die
  Lokalisierung setzt in `def:localizing`\ref{it:L1} die Martingaleigenschaft
  der gestoppten Prozesse voraus, statt sie herzuleiten; getragen wird der Fact
  erst bei der Verifikation eines konkreten lokalisierenden Systems.
  **Am 2026-08-31 sind auch die letzten beiden geklärt**, und beide Antworten
  sind zweigeteilt; die Einzelheiten stehen im Laufbericht.
  `fact:fdd` zerfällt in die Produkthälfte \eqref{eq:prodsep} (EK 3.4.6/3.7.1)
  und den Satz „die endlich-dimensionalen Verteilungen bestimmen das Gesetz".
  Die zweite Hälfte ist mittelbar getragen, an den drei Stellen, die die
  Tabelle in §2 unter `thm:fdd` führt (`thm:absuniq`, `cor:DEuniqueness`,
  `ex:determining`); die erste trägt **kein** Beweis des Manuskripts, und
  entbehrlich ist sie trotzdem nicht, weil §9 (Stelle 9048) sie ausdrücklich
  verlangt („the separating half of `fact:fdd` only"). `fact:portmanteau` wird
  von keinem Beweis benutzt; die einzige Stelle, an der es überhaupt arbeiten
  kann, ist die Implikation (a)⇒(b) und nur, wenn man den Weg über die
  Prohorov-Metrik nimmt.
* **Die Kopfliste von `SkorokhodSpace` nannte als „die ganze
  Einseitiglimes-API" sechs Sätze über monotone Funktionen; am 2026-09-01,
  vierter Lauf, berichtigt.** `tendsto_leftLim`, `tendsto_rightLim`,
  `tendsto_leftLim_within`, `continuousWithinAt_Iio_iff_leftLim_eq`,
  `continuousWithinAt_Ioi_iff_rightLim_eq` und
  `continuousAt_iff_leftLim_eq_rightLim` stehen sämtlich in `namespace Monotone`
  von `Mathlib/Topology/Order/LeftRightLim.lean` (Zeilen 268--386, mit
  `include hf` für `hf : Monotone f`) und noch einmal in `namespace Antitone`
  (388--451). Sie verlangen außerdem `[ConditionallyCompleteLinearOrder β]
  [OrderTopology β]` vom **Zielraum**. Ein càdlàg-Pfad in einen metrischen Raum
  erfüllt nichts davon; kein einziger der sechs Namen ist für diese Roadmap
  benutzbar. Was im Wurzelnamensraum steht und für beliebiges `f` gilt, ist
  `tendsto_leftLim_of_tendsto`/`tendsto_rightLim_of_tendsto` (`:121`,`:130`),
  `ContinuousWithinAt.leftLim_eq`/`.rightLim_eq` (`:110`,`:117`),
  `leftLim_eq_of_tendsto`/`rightLim_eq_of_tendsto` (`:65`,`:73`),
  `leftLim_eq_of_eq_bot`, `leftLim_eq_of_not_tendsto`, `leftLim_eq_of_isBot`,
  `rightLim_eq_of_isTop` und `mapClusterPt_leftLim`/`_rightLim`. Der Glücksfall:
  die Hypothese von `tendsto_leftLim_of_tendsto` ist wörtlich
  `∃ y, Tendsto f (𝓝[<] a) (𝓝 y)`, also genau das Feld `left_limit` von
  `IsCadlag`. Die Kopfliste sagt das jetzt und nennt beide Hälften getrennt.

  **Daran hängt eine Hypothesenkorrektur.** `Function.leftLim` ist nur für
  `[LinearOrder α]` definiert (Variablenblock `:44`, Definition `:50`). Die zwei
  Punkte von Meilenstein 2, die die Struktur an `Function.leftLim` anschließen,
  standen unter Stufe **(A)** `[Preorder ι]` und sind dort nicht formulierbar.
  Der Meilenstein führt jetzt eine dritte benannte Stufe **(A′)**
  `[LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]` — das schwächste
  Bündel, unter dem `Function.leftLim` existiert, und echt schwächer als (B),
  weil es keine dichte Teilmenge verlangt. Das ist keine Verschärfung, sondern
  die Korrektur einer zu schwachen Angabe.
* **Zwei kleinere Fehler derselben Kopfliste, am 2026-09-01 berichtigt.** Sie
  schrieb `Monotone.countable_not_continuousAt` der Datei `LeftRightLim.lean` zu;
  dort steht der Name nur im Modulkommentar (`:25`), die Deklaration liegt in
  `Mathlib/Topology/Order/Monotone.lean:166`. Meilenstein 2 sagte es schon
  richtig — die Roadmap widersprach sich selbst. Und `StieltjesFunction`, das die
  Kopfliste als Vorbild für `IsCadlag` nennt, formuliert Rechtsstetigkeit als
  `ContinuousWithinAt f (Ici x) x` (`Measure/Stieltjes.lean:118,140`), während
  `Function.RightContinuous` der Roadmap `Ioi` nimmt; die Brücke ist
  `continuousWithinAt_Ioi_iff_Ici`, dieselbe, die `StieltjesFunction.rightLim_eq`
  (`:143`) selbst geht. Beides steht jetzt da.
* **Die zentrale Definition von `SkorokhodSpace` Meilenstein 3 war ein
  Typfehler; am 2026-09-01 berichtigt.** Dort stand
  `TimeChange.norm λ = log (max (LipschitzWith.const λ) (LipschitzWith.const λ⁻¹))`.
  `LipschitzWith.const` ist der Satz „eine konstante Abbildung ist
  `0`-lipschitz" (`Topology/EMetricSpace/Lipschitz.lean:194`,
  `protected theorem const (b : β) : LipschitzWith 0 fun _ : α => b`), also ein
  Beweis und keine Zahl. Mathlib kennt **keine kleinste Lipschitzkonstante**:
  `LipschitzWith (K : ℝ≥0) (f : α → β)` ist eine Prop (`:60`), ebenso
  `LipschitzOnWith` (`:64`), und ein gebündeltes Optimum gibt es nirgends. Damit
  war die Metrik des Skorokhod-Raums — Meilensteine 3 bis 5 hängen an ihr — nicht
  aufschreibbar. Der Meilenstein führt jetzt `TimeChange.lipConst` als eigenen
  Punkt, samt Erreichtheit des Infimums und Submultiplikativität über
  `LipschitzWith.comp` (`:225`), und `norm` ist darauf gebaut.
* **`fact:fullgenerator`** trägt §8 als „nur für optionalen Kontext". Am
  2026-08-30 entschieden: solange `rem:fullgenerator` im Manuskript steht,
  gehört er in die Roadmap, und er steht jetzt dort ohne das Wort „optional"
  (MartingaleProblems M13). Für **`fact:bp`** stand dasselbe, und es ist am
  2026-08-30, zweiter Teil des Tages, zurückgenommen: der bp-Abschluss ist aus
  MartingaleProblems M2 gestrichen. Die Begründung steht im Laufbericht
  „Aufgabe 1"; kurz: kein Beweis des Manuskripts benutzt `cor:bpclosure`, und
  die einzige Stelle bei \EK{}, an der der Abschluss arbeitet (Thm. 4.3.8),
  kommt nach Prop. 4.3.9 mit einer einzelnen Folge und Fatou aus. Was das
  Manuskript ohnehin festhält, bleibt richtig: `lem:closure` ist dominierte
  Konvergenz und gilt für unbeschränkte `f, g`, der bp-Abschluss verengt auf
  `Bdd(E) × Bdd(E)`.
* **`fact:sepcond`** wird im Manuskript selbst bewiesen (`rem:sepcondproof`,
  EK Kap. 3 Aufgabe 7); zitiert wird nichts. Es ist damit kein Fact im Sinne
  der Voraussetzungsfläche, wohl aber eine zu formalisierende Aussage, und
  steht seit dem 2026-08-30 als Punkt in `WeakConvergence` Meilenstein 1. Ob
  die `fact`-Umgebung im Manuskript die richtige ist, bleibt eine Frage an das
  Manuskript.
* **Der Beweis von `rem:sepcondproof` ist länger als nötig.** Schritt 2 und 3
  konstruieren eine reguläre bedingte Verteilung und zeigen die Messbarkeit der
  Diagonale. Beides entfällt: aus Schritt 1 folgt mit `G = {V ∈ B}` und dessen
  Komplement unmittelbar `P(U ∈ B, V ∉ B) = P(U ∉ B, V ∈ B) = 0` für jedes
  messbare `B`, und eine abzählbare trennende Familie schließt daraus
  `P{U = V} = 1`. Das ist genau
  `Filter.EventuallyEq.of_forall_separating_preimage`. Gebraucht wird davon nur
  \eqref{E1} in Gestalt von `CountablySeparated`; eine reguläre bedingte
  Verteilung kommt nicht vor. Fürs Manuskript wäre das eine Kürzung, nicht eine
  Korrektur.
* **Die Roadmap `MartingaleProblems` hat den Mathlib-Bestand an Martingaltheorie
  überschätzt** — sie führte „optional stopping, Doob's inequalities" unter dem,
  was nicht neu zu bauen ist. Alle diese Sätze sind in Mathlib auf `Filtration ℕ`
  (bzw. auf einen zu einer Teilmenge von `ℕ` ordnungsisomorphen Index)
  festgelegt, und Doobs `Lᵖ`-Ungleichung fehlt für jeden Index. Am 2026-08-29
  richtiggestellt und als Meilenstein 9 nachgetragen.
* **Eine falsche Begründung in `rem:atomicdual`, am 2026-08-30 korrigiert.** Zum
  kleinsten Index mit unvergleichbaren Atomen, `T = {0,a,b,t*}`, stand dort, die
  drei Relationen längs `[0,t*)`, `[a,t*)` und `[b,t*)` erzwängen
  `m_a γ(a,t) = m_b γ(b,t) = 0`. Sie erzwingen es nicht: alle drei Intervalle
  sind `{a,b}`, die drei Relationen sagen dasselbe. Das Argument benutzte
  nirgends die Positivität der Massen und hätte deshalb auch ein Gegenbeispiel
  mit `m_a + m_b = 0` decken müssen, das es gibt (`Task23/diamond.py`). Die
  Aussage selbst bleibt richtig; die Begründung ist im Manuskript ersetzt. Das
  ist die einzige Änderung dieses Laufs am Manuskript, und sie folgt der Regel
  von Task 23: erst wenn etwas vollständig und verifiziert ist.
* **Ein falsches Mathlib-Zitat in `MartingaleProblems`, am 2026-08-30
  korrigiert.** Die Liste „Mathlib supplies" führte
  `Mathlib/Probability/Process/Kolmogorov.lean` als „the Kolmogorov–Chentsov
  continuous modification". Die Datei enthält nur die **Bedingung**
  `IsKolmogorovProcess`/`IsAEKolmogorovProcess` samt API; der Satz steht nicht
  in Mathlib, weder in v4.33.1 noch auf master — `gh api search/code` für
  „Chentsov" findet genau zwei Dateien, diese hier (nur im Modulkommentar) und
  `Topology/EMetricSpace/PairReduction.lean`. Der Beweis liegt in
  `RemyDegenne/brownian-motion`, `BrownianMotion/Continuity/`, unter einer
  Schranke an die Überdeckungszahlen. Die Roadmapzeile sagt das jetzt.
* **`rem:skorokhodform` nennt `[Preorder ι] [TopologicalSpace ι]` „\eqref{T2b}"
  (Stelle 2238).** Das ist es nicht: \eqref{T2b} verlangt lineare Ordnung,
  Ordnungstopologie, abzählbare dichte Teilmenge und Rechtsapproximierbarkeit.
  Die Hypothesen, unter denen `RemyDegenne/brownian-motion` `IsCadlag`
  deklariert, sind echt schwächer — am Quelltext geprüft, siehe
  `Facts/PRAEORDNUNG.md`, Teil 2. Das ist eine Frage an das Manuskript; die
  Aussage selbst ist davon nicht betroffen.
* **`SkorokhodSpace` Meilenstein 2 sagte weniger, als vier seiner Punkte
  brauchen; am 2026-08-30, fünfter Lauf, korrigiert.** Der Kopf setzte
  `[Preorder ι] [TopologicalSpace ι]` — richtig für das Prädikat —, aber der
  Schlusssatz von Meilenstein 1 („Throughout the rest of this roadmap") lud
  zugleich das volle \eqref{T3p} auf, und die Abzählbarkeit von `leftJumpSet`,
  die Diskretheit von `largeLeftJumpSet`, `IsCadlag.measurable` und die
  Bestimmtheit durch eine dichte Menge sagten ihre eigene Hypothese nur
  indirekt („by the exhaustion"). Der Meilenstein führt jetzt zwei benannte
  Stufen, **(A)** `[Preorder ι] [TopologicalSpace ι]` für das Prädikat und
  **(B)** \eqref{T2b} für die Sprungtheorie, und jeder Punkt steht unter einer
  von beiden; zwei Punkte nennen zusätzlich die σ-Kompaktheit, die sie wirklich
  brauchen. Der Schlusssatz von Meilenstein 1 gilt jetzt erst ab Meilenstein 3.
  Die Aufschlüsselung, aus der das stammt, steht in `Facts/PRAEORDNUNG.md`,
  Teil 2. Was nicht geschehen ist und dem Nutzer gehört: den Meilenstein in
  **zwei** Meilensteine zu zerlegen. Die Hypothesen sind jetzt richtig; die
  Gliederung ist unverändert.
* **Die Roadmaps kennen `E` nur polnisch — am 2026-08-31 für die drei genannten
  Facts geklärt und belegt.** `SkorokhodSpace` fixierte in Meilenstein 1 „`E` a
  Polish space", während `fact:fddconv`, `fact:cmt` und `fact:PSpolish` im
  Manuskript für separable metrische `E` gelten und `rem:MZcost` ausdrücklich
  festhält, dass der Pfadraum der Konvergenz nach Maß nicht polnisch ist. Der
  Beleg, den die stehende Regel verlangt — die Stelle nennen, an der die
  Vollständigkeit im Beweis nicht mehr vorkommt —, liegt seit dem 2026-08-31
  am Scan vor: \EK{} Thm. 3.1.8 (Skorokhod-Darstellung) beginnt mit „Let
  $(S,d)$ be **separable**", Cor. 3.1.9 (stetige Abbildung) mit „Let $(S,d)$
  and $(S',d')$ be **separable** metric spaces", und Thm. 3.7.8 mit „Let $E$ be
  **separable**"; die Vollständigkeit steht erst bei Lemma 3.2.1 und Thm. 3.2.2,
  also bei Prohorov, und dort in der Rückrichtung. Mathlib sagt dasselbe:
  `isCompact_closure_of_isTightMeasureSet` führt `[T2Space E] [BorelSpace E]`,
  `MeasureTheory.isTightMeasureSet_of_isCompact_closure` führt
  `[CompleteSpace 𝓧] [SecondCountableTopology 𝓧]` (`Measure/Prokhorov.lean:65`
  bzw. `:570,630`, am Quelltext geprüft). `WeakConvergence` M2 und M3 standen
  ohnehin schon auf „separabel metrisch"; `SkorokhodSpace` Meilenstein 8 führt
  seit dem 2026-08-31 zwei Stufen (A) separabel metrisch und (B) polnisch, nach
  dem Muster von Meilenstein 2, und nur die zwei Punkte, die Prohorov rückwärts
  laufen lassen, stehen unter (B). Offen bleibt allein die **Gliederungsfrage**,
  ob Meilenstein 1 von `SkorokhodSpace` seine globale Festlegung auf polnisch
  aufgibt; sie gehört dem Nutzer, wie die Zerlegung von Meilenstein 2.

* **§4.3 von \EK{} ist ausgewertet, seit dem 2026-08-30, fünfter Lauf.** Zitiert
  werden 4.3.1, 4.3.5 und 4.3.6. Thm. 4.3.8, Prop. 4.3.9 und Prop. 4.3.10 stehen
  seit dem vierten Lauf in `MartingaleProblems` M9; Thm. 4.3.12 steht seit dem
  fünften dort, abstrakt und mit einer Hypothese mehr (siehe unten);
  Cor. 4.3.13 trägt nichts und steht in keiner Roadmap. Was daran offen ist, ist
  keine Suchaufgabe mehr, sondern die Frage ans Manuskript, ob es Thm. 4.3.12
  hinter `thm:cadlag` aufnehmen will. Für den Gegenstand selbst gilt weiterhin:
  quasi-linksstetig heißt keine Sprünge zu vorhersehbaren Zeiten, der
  Poissonprozess erfüllt es; echte Stetigkeit verlangt eine Bedingung an $A$
  (kein Sprunganteil, für $\R^d$ die Lokalität nach Courrège) und steht bei
  \EK{} nicht in §4.3.
* **`rem:absreggain`(ii) „Atome sind harmlos" ist richtig und endet genau an der
  Quasi-Linksstetigkeit.** Der fünfte Lauf des 2026-08-30 hat
  belegt, dass \EK{} Thm. 4.3.12 in der Allgemeinheit des Manuskripts — Uhr ein
  beliebiges lokal endliches Maß — **falsch** ist: ein Atom der Uhr bei $u$ ist
  ein fester Unstetigkeitszeitpunkt, und schon auf $E=\{0,1\}$ mit
  $q=\delta_u$ löst ein Prozess, der bei $u$ eine faire Münze wirft, ein
  Martingalproblem und ist nicht quasi-linksstetig. Die Existenz einer
  c\`adl\`ag-Modifikation und die Quasi-Linksstetigkeit trennen sich also genau
  an den Atomen. Das ist kein Fehler des Manuskripts — `rem:absreggain`(ii)
  spricht nur über `thm:absreg` —, aber es ist der schärfste Satz, den man über
  die Reichweite der Atomtoleranz sagen kann, und er stünde gut dort.
* **`rem:ccverify` bleibt bei $D_{E^\Delta}$ stehen.** Die Bemerkung schließt
  mit „the modification has paths in $D_{E^\Delta}[0,\infty)$"; das ist genau,
  was \EK{} Cor. 4.3.7 hergibt (Buchseite 179, am Scan geprüft). Der Schritt
  zurück nach $D_E$ ist \EK{} Thm. 4.3.8 mit Prop. 4.3.9/4.3.10, und der steht
  seit dem 2026-08-30 in `MartingaleProblems` M9. Ob `rem:ccverify` ihn nennen
  soll, gehört dem Nutzer; das Inventar hält nur fest, dass die Bemerkung heute
  weniger schließt, als der Leser erwartet.
* **Zwei Fehler in der Tabelle „Where the prerequisites are used" (§2, Stelle
  1639ff), am 2026-08-31 gefunden.** Erstens führt Stelle 1661
  „Fact `portmanteau`, `cmt` → Lemma `EKconv`, Theorem `CPSconv`". Für `cmt`
  stimmt das, für `portmanteau` nicht: beide Beweise verifizieren die
  Bedingungen \ref{it:C1}--\ref{it:C3} von `thm:absconv`, und dessen Beweis
  benutzt in allen vier Schritten nur `fact:cmt`, `fact:ui` und (in `EKconv`
  und `CPSconv`) `fact:Dcountable`. Weder die Prohorov-Metrik noch abgeschlossene
  oder offene Mengen noch Stetigkeitsmengen kommen irgendwo vor. Die Zeile
  sollte nur `fact:cmt` nennen. Zweitens fehlt `fact:fdd` in der Tabelle ganz —
  aufgeführt ist `thm:fdd`, der Satz des Manuskripts, nicht der Fact. Beides
  sind Fragen ans Manuskript; das Inventar ändert es nicht.
* **`fact:portmanteau` arbeitet höchstens durch (a)⇒(b), und ob überhaupt,
  hängt an einem undefinierten Wort.** „Relativ kompakt" kommt in
  `fact:fddconv`(b), `fact:relcompact`, `fact:relcompact2` und
  `rem:EKrelcompact` vor und wird im Manuskript **nirgends definiert**. Liest
  man es als Relativkompaktheit in der Topologie der schwachen Konvergenz, so
  wird `fact:portmanteau` an keiner Stelle des Manuskripts gebraucht; liest man
  es metrisch — `fact:PSpolish` versieht $\Prob(S)$ mit der Prohorov-Metrik —,
  so braucht der Schritt von der Relativkompaktheit zu einer schwach
  konvergenten Teilfolge in `rem:EKrelcompact` genau (a)⇒(b). Die Hälften
  (c)--(f) trägt in keiner der beiden Lesarten irgendetwas. Für die
  Formalisierung ist die Frage ohne Kosten: Mathlibs Prokhorov
  (`isCompact_closure_of_isTightMeasureSet`, `Measure/Prokhorov.lean:530`,
  nicht `deprecated`, und **im Wurzelnamensraum** — nur die Rückrichtung
  `MeasureTheory.isTightMeasureSet_of_isCompact_closure` bei `:634` steht in
  `MeasureTheory`) steht in `ProbabilityMeasure E` mit der Topologie der
  Verteilungskonvergenz, also in der ersten Lesart, und die zweite ist mit
  `MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph`
  (`Measure/LevyProkhorovMetric.lean:676`) ebenfalls da. Eine Definition von
  „relativ kompakt" im Manuskript wäre trotzdem eine Verbesserung.
* **Der Produktpunkt von `WeakConvergence` Meilenstein 1 hatte eine falsche
  Begründung, am 2026-08-31 korrigiert.** Er schloss mit „every determining set
  in **MartingaleProblems** is built from it". Das ist nicht so:
  `isDetermining_products` in `MartingaleProblems` Meilenstein 3 nennt als
  Beweisweg „`induction_on_mulSystem` der Roadmap **WeakConvergence**,
  Meilenstein 5, angewandt auf das multiplikative System jener Produkte", und
  das Manuskript macht es genauso — `ex:determining` sagt „this uses
  $\Bor(F) = \sigma(X_t)$ (`thm:fdd`) and the monotone class theorem",
  `thm:uniqueness` Schritt 2 und `prop:uniqfromprop` führen das Dynkin-Argument
  auf dem Pfadraum aus. Der Produktpunkt wird damit heute von **keinem** Punkt
  einer der vier Roadmaps und von keinem Beweis des Manuskripts benutzt. Er
  bleibt stehen, weil §9 ihn verlangt; die Begründung sagt jetzt, was geprüft
  ist: die Determining-Sets sind sein Spezialfall `Γ i` alle beschränkt
  messbar, in dem die Separiertheit leer ist, und der Zusatz ist, dass ein
  separierendes `Γ i` je Faktor genügt.
* **Der Konvergenzteil rechnet nirgends still auf Atomlosigkeit; am 2026-08-31
  durchgegangen.** Jede Aussage von §7 ist entweder uhrenfrei oder ausdrücklich
  Lebesgue, und die eine Stelle, an der ein Atom beißt, hat einen eigenen
  Abschnitt. Uhrenfrei sind `thm:absconv` (die Uhr kommt nur über das abstrakte
  $\XX$ herein), `lem:contuse`, `thm:absconvaug` und `thm:absconvws`; die
  Bündeltabelle trägt für die ersten drei „---" ein. Lebesgue sind
  `lem:EKconv`, `thm:CPSconv` (Tabelle: „Lebesgue") und `thm:MZconv`, dessen
  Beweis $\lambda$ in jedem Schritt benutzt. `thm:clockchange` verlangt
  \ref{it:C3a} als Hypothese und schiebt die Uhr in \ref{it:K3}/\ref{it:K4} —
  also genau dorthin, wo ein Atom sichtbar ist, statt es zu verstecken.
  `rem:EKrelcompact` ruht auf `fact:relcompact`, `relcompact2`, `fddconv` und
  `prohorov`, die sämtlich über $D_E[0,\infty)$ mit dem Lebesgue-Kompensator
  formuliert sind (`fact:relcompact2` schreibt $Y(t) - \int_0^t Z(s)\dif s$
  hin), und es speist `lem:EKconv`. Ein Atom stört an keiner dieser Stellen,
  weil keine von ihnen für eine allgemeine Uhr behauptet wird. Wo es stört, ist
  \ref{it:C3a}, und das sagt `ex:atomicdiscontinuity` mit Gegenbeispiel,
  `thm:absconvaug`/`prop:atomaug` reparieren es („any, atoms allowed"), und
  `rem:MZcost` nennt die Grenze der Reparatur.
* **Die o-Konvention auf einer Halbordnung ist nicht offen, sondern falsch; am
  2026-08-31, achtem Lauf, belegt und im Manuskript berichtigt.** Sieben Läufe
  hielten sie für richtig und unbewiesen; die Statuszeile von
  `rem:atomsnotchange` sagte „verified exhaustively up to five points; not
  proved". Beides trifft nicht zu. Der kleinste Zeuge steht auf **vier** Punkten:
  der Diamant $0\prec a,b\prec c$ mit $m_a=1$, $m_b=4$, $m_c=2$, alle Massen
  nichtnegativ. Er ist ausgeschrieben, nicht nur als Rangvergleich festgestellt,
  und die Zeile lautet jetzt „*false*; counterexample in `rem:atomicposet`". Die
  Bedingung ist scharf und heißt $m_c^2=m_am_b$ — die Masse der Spitze ist das
  geometrische Mittel der beiden unvergleichbaren Massen —, also eine
  abgeschlossene algebraische und, auf allem Geprüften, echte Bedingung: die
  o-Aussage gilt außerhalb einer Nullmenge und fällt auf ihr. Warum es sieben
  Läufe überlebt hat, ist der eigentliche Befund: der erschöpfende Sweep lief auf
  fünf Punkten über Massen aus $\{0,1\}$ und auf vier über $\{0,1,2\}$, und
  keines der beiden Gitter kann $m_c^2=m_am_b$ mit $m_a\ne m_b$ treffen. Ein
  Gitter, das eine algebraische Ausnahmebedingung nicht enthalten kann, ist keine
  Evidenz gegen sie. Die Einzelheiten stehen im `Task23/PROTOKOLL.md`, Abschnitt
  „Die o-Konvention, 2026-08-31 (achter Lauf)".
* **Die Statuszeile „purely atomic, atoms incomparable" war falsch; am
  2026-08-31, siebtem Lauf, im Manuskript berichtigt.** Bewiesen ist seit dem
  sechsten Lauf der **ganze** Fall: auf jeder endlichen Halbordnung mit
  nichtnegativen Massen — und die Massen einer Uhr sind nichtnegativ —
  verschwindet der Dualitätsdefekt, ohne Bedingung an die Lage der Atome
  zueinander, ohne kleinstes oder größtes Element und ohne Antikettenhypothese.
  Der Satz steht jetzt als `lem:selfadjoint` und `prop:atomicposet` im
  Manuskript, die Statuszeile lautet `proved`, und `check.py` meldet `clean`.
  Er enthält den Satz des fünften Laufs (flache Spitze) für Uhren; jener bleibt
  daneben richtig, weil er Massen beider Vorzeichen erlaubt, und
  `prop:atomicdual` bleibt deshalb stehen.
* **Beim Eintragen ist eine neue Lücke aufgefallen: die Konvention
  $\iota=\mathrm o$ auf einer Halbordnung.** Sechs Läufe lang galt „die
  o-Konvention ist die p-Konvention für die umgekehrte Ordnung"; das stimmt auf
  einer **Kette**, weil eine endliche Kette ein größtes Element hat, an dem die
  Spiegelung aufhängt, und auf einer Halbordnung nicht. Sichtbar wird es an der
  Matrix: unter $\iota=\mathrm o$ ist $(0,s]=\T_{\le s}\setminus\T_{\le0}$, also
  $V_{s,s}=m_s\ne0$, und $V$ ist **nicht nilpotent**. `prop:atomicposet` ist
  deshalb für $\iota=\mathrm p$ formuliert; die o-Fassung galt einen Lauf lang
  als „verified, not proved" und ist seit dem achten Lauf **widerlegt** — siehe
  den ersten Punkt dieser Liste. Der Fehler stand auch in `MartingaleProblems`
  bei
  `duality_of_atomic` („in both conventions … the hypotheses are unchanged") und
  ist dort korrigiert.
* **Drei Aussagen von §7 fehlen in der Bündeltabelle.** `thm:absconvws`,
  `thm:MZconv` und `rem:EKrelcompact` haben dort keine Zeile, während
  `thm:absconv`, `thm:absconvaug`, `prop:atomaug`, `thm:clockchange`,
  `lem:EKconv` und `thm:CPSconv` eine haben. Bei `thm:MZconv` ist das mehr als
  Buchhaltung: `rem:MZcost` hält fest, dass der Pfadraum dort separabel
  metrisch und **nicht** polnisch ist, also gerade eine Abweichung von
  \eqref{E3}, und Abweichungen von der schwächsten Spalte zu markieren ist der
  erklärte Zweck der Tabelle. `rem:EKrelcompact` ist die Stelle, an der sieben
  Facts zusammenlaufen, und die Tabelle in §2.x nennt es viermal als Abnehmer.
  Frage ans Manuskript.
* **`cor:atomless` schließt schwächer, als sein Beweis hergibt; am 2026-09-01
  gefunden.** Die Konklusion lautet „$\Phi(t,0)=\Phi(0,t)$ für $Q$-fast jedes
  $t$", und das ist ein Artefakt des Umwegs über `lem:calculus` (\EK{} 4.4.10),
  dessen Schluss selbst ein Fast-überall ist. Das seit heute im Manuskript
  stehende `lem:rectangle` gibt auf demselben transportierten Paar
  $\Psi=f(x+y)$ **überall**, also die Identität an jedem $t$; es ruht auf nichts
  als `lem:calculus` und der Stetigkeit von
  $r\mapsto\Psi(x+r,y')-\Psi(x,y'+r)$. Die Verschärfung kostet einen Satz im
  Beweis von `cor:atomless` und ist nicht vorgenommen worden, weil dieser Lauf
  sie nicht gebraucht hat: `prop:mixeddual` benutzt `lem:rectangle` direkt.
  Die zweite Bemerkung in `rem:atomsnotchange` — „die Konklusion ist genuin
  $Q$-fast jedes $t$" — wäre dann ebenfalls zu prüfen. Frage ans Manuskript.

* **Die Endlichkeit in `prop:atomicposet` ist unentbehrlich, und der
  Schlußsatz der Proposition sagt es nicht; am 2026-09-04, zweiter Lauf,
  belegt.** Die Proposition schließt mit „No hypothesis is made on the mutual
  position of the atoms, and none beyond the existence of the integrals in
  \eqref{eq:incrementrep} and the non-negativity of $q$." Das ist richtig, legt
  aber nahe, die Hypothese „die Atome in $\T_{<t^*}$ sind endlich viele" sei
  eine Bequemlichkeit des Matrizenbeweises. Sie ist es nicht: auf einer
  abzählbaren **Antikette** mit positiven summierbaren Massen gibt es
  $\Phi,\gamma$, die \eqref{eq:incrementrep} an jedem vergleichbaren Paar
  erfüllen und $\Phi(t^*,0)\neq\Phi(0,t^*)$ haben (Theorem 19,
  `Task23/PROTOKOLL.md`, dreiundzwanzigster Lauf; exakt nachgerechnet in
  `Task23/poset_infinite.py`). Das Manuskript ist davon **nicht** betroffen —
  die Hypothese steht da —, aber eine Bemerkung wäre die schärfste Aussage, die
  sich über die Reichweite von `prop:atomicposet` machen läßt, und sie stünde
  neben `rem:atomicposet`. Vorschlag, zur Entscheidung des Nutzers:

  > *Remark (the finiteness is sharp).* For infinitely many atoms the
  > conclusion of `prop:atomicposet` fails. Let $\T=\{0\}\cup A\cup\{t^*\}$
  > with $A=\{a_1,a_2,\dots\}$ pairwise incomparable and $0<a_i<t^*$, let
  > $q(\{0\})=0$ and $m_i=q(\{a_i\})>0$ with $M=\sum_im_i<\infty$ and tails
  > $\sigma_i=\sum_{j\ge i}m_j$, and put
  > $\gamma(a_i,a_j)=\tfrac12\operatorname{sgn}(i-j)
  > (\sigma_n\sigma_{n+1})^{-1}$ with $n=\min(i,j)$ and
  > $\gamma(a_j,0)=\gamma(a_j,t^*)=\tfrac12M^{-2}$, extended antisymmetrically.
  > Every integral in \eqref{eq:incrementrep} exists, both representations hold
  > at every comparable pair, and $\Phi(t^*,0)-\Phi(0,t^*)=1/M$. What fails is
  > the integrability of $\gamma$ for $q\otimes q$ on $A\times A$; under that
  > hypothesis the conclusion holds on any antichain, by Fubini and the
  > antisymmetry of $\kappa$.

  Zweierlei ist daran auch für die Roadmaps von Belang, und beides steht seit
  diesem Lauf in `MartingaleProblems` Meilenstein 8: das Gegenbeispiel hat
  **beschränktes $\Phi$**, die Hypothesengestalt von
  `duality_of_atomic_twoChains_of_bounded` ist außerhalb von Ketten also
  wertlos; und es braucht $q(\{0\})=0$, also genau die Bedingung „es gibt ein
  $s$ mit $\T_{<s}\neq\emptyset$ und $q(\T_{<s})=0$", die `sharp.py` im
  endlichen Fall als notwendig gefunden hatte.

## Läufe

### 2026-08-29 — `fact:Dcountable`, `fact:monotoneclass`, `fact:optsampl`, `fact:doob`, `fact:fddconv`, `fact:relcompact`, `fact:relcompact2`, `fact:fdd`

Acht Zeilen von `?` auf `Roadmap` gebracht, jede am Quelltext belegt. Geprüft
wurde gegen `~/Code/lean/journal/.lake/packages/mathlib` (v4.33.1) und, wo es auf
**master** ankam, gegen `gh api`/`gh search code`; die Verzeichnisse
`Mathlib/Probability/Martingale/` und `Mathlib/Probability/Process/` sind auf
master identisch mit v4.33.1, die v4.33.1-Quelle ist für diesen Lauf also ein
tragfähiger Stellvertreter.

* **`fact:Dcountable`** (tragend 4). Mathlib hat den Skorokhod-Raum nicht:
  `gh search code` findet `cadlag` nirgends und `Skorokhod` nur in
  `docs/1000.yaml`. Die Aussage steht wörtlich in `SkorokhodSpace` Meilenstein 8
  als `SkorokhodSpace.exists_countable_dense_continuity`. Die Stellen 8471, 8474
  und 8511 des Manuskripts benutzen den Fact nur vergleichend (Pseudopfade,
  S-Topologie) und verlangen nichts über die Aussage hinaus.
* **`fact:monotoneclass`** (tragend 4). Lücke. Der Begriff „monotone class"
  kommt in Mathlib weder in v4.33.1 noch auf master vor; `docs/1000.yaml` führt
  den Satz als `Q242045` **ohne** `decl`. Vorhanden ist nur die Mengenfassung,
  Dynkins π–λ-Satz als `induction_on_inter` in
  `Mathlib/MeasureTheory/PiSystem.lean:692`. Die vier tragenden Stellen (2376,
  2630, 5468, 8862) brauchen sämtlich die **funktionale** Fassung. Neu angelegt
  als `WeakConvergence` Meilenstein 5 mit `IsMulSystem`, `generateFromFuns`,
  `induction_on_mulSystem` und den zwei benutzten Korollaren; die Produktaussage
  in Meilenstein 1 und `isDetermining_products` in `MartingaleProblems`
  Meilenstein 3 verweisen jetzt darauf statt auf „ein Monotone-Klassen-Argument".
* **`fact:optsampl`** (tragend 2). Lücke, und zugleich ein falsches Zitat in der
  Roadmap. Mathlibs Optional-Sampling-Satz ist
  `MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp`
  (`Probability/Martingale/OptionalSampling.lean:195`) und steht in der Sektion
  `SubsetOfNat` unter `[LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]` —
  ein zu einer Teilmenge von `ℕ` ordnungsisomorpher Index — und nur für
  `Martingale`. Die Submartingal-Fassung `Submartingale.expected_stoppedValue_mono`
  (`OptionalStopping.lean:44`) liegt auf `{𝒢 : Filtration ℕ m0}` und vergleicht
  nur Erwartungswerte, nicht bedingte. Das Manuskript braucht rechtsstetige
  Submartingale in stetiger Zeit mit `≥` unter `Filt_{τ₁}`. Nachgetragen als
  erste zwei Punkte von `MartingaleProblems` Meilenstein 9.
* **`fact:doob`** (tragend 0, aber über `fact:relcompact2` mittelbar getragen).
  Lücke. `MeasureTheory.maximal_ineq` (`OptionalStopping.lean:155`) ist Doobs
  Maximalungleichung für nichtnegative Submartingale über `Filtration ℕ`; der
  Modulkommentar `OptionalStopping.lean:153` sagt selbst, dass die
  `Lᵖ`-Ungleichung „will be proved in an upcoming PR" — auf master steht dieser
  Satz unverändert, die Ungleichung fehlt also weiterhin. Nachgetragen als
  dritter Punkt von `MartingaleProblems` Meilenstein 9
  (`maximal_ineq_of_rightContinuous`, `Submartingale.eLpNorm_iSup_le` und die
  Martingal-Korollare), zusammen mit der Messbarkeit des Supremums über einen
  überabzählbaren Index.
* **`fact:fddconv`** (tragend 1). Beide Hälften stehen in `SkorokhodSpace`
  Meilenstein 8: (a) `tendsto_finiteDimensional_of_tendsto`, (b)
  `tendsto_of_isTight_of_tendsto_finiteDimensional`. „Relativ kompakt" gegen
  „straff" ist über Prohorov dasselbe, aber nur auf polnischem `E`; der Fact
  verlangt nur separabel. Als Auffälligkeit notiert, nicht stillschweigend
  gleichgesetzt.
* **`fact:relcompact`** (tragend 1) und **`fact:relcompact2`** (tragend 2).
  Beides Lücken; Mathlib scheidet mit dem Skorokhod-Raum aus. `rem:EKrelcompact`
  des Manuskripts sagt selbst, woraus es besteht: „Facts `relcompact`,
  `relcompact2`, `fddconv` und `prohorov`". Die Roadmaps hatten davon nur die
  **Folgerung**: `MartingaleProblems` Meilenstein 11 nannte
  `isRelativelyCompact_of_approx` und als Beweisweg „Stone–Weierstrass plus das
  Straffheitskriterium von `SkorokhodSpace`" — aber das Kriterium von EK 3.9.1
  (Rückführung auf `D_ℝ` entlang einer kompakt-gleichmäßig dichten Teilmenge von
  `Cb(E)`) stand in `SkorokhodSpace` Meilenstein 7/8 nirgends, und das
  Martingalkriterium von EK 3.9.4 (der Banachraum `𝓛 n`, die Paare `𝓐 n`, die
  `Lᵖ`-Schranke an `Z n`) in Meilenstein 11 auch nicht. Beide sind jetzt als
  eigene Punkte benannt: `SkorokhodSpace.continuous_postcomp` und
  `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` in Meilenstein 8,
  `isTight_map_postcomp_of_exists_martingale` in Meilenstein 11, und
  `isRelativelyCompact_of_approx` verweist jetzt auf beide statt auf eine
  Beweisskizze. EK 3.9.4 ist über `ℝ` formuliert; das Manuskript hält bei 2387
  fest, dass das nur an EK liegt, und die Roadmap notiert die `𝕂`-Fassung.
* **`fact:fdd`** (tragend 0). Die zweite Hälfte, `Bor(D_E) = σ(π_t)`, ist
  `SkorokhodSpace.borel_eq_iSup_comap_eval` in Meilenstein 6 und war schon da.
  Die erste war es nur halb: der Produktpunkt von `WeakConvergence`
  Meilenstein 1 stand für einen **endlichen** Index `S 1, …, S k`, der Fact
  verlangt `S = ∏_{k ≥ 1} S_k`. Für endlich-dimensionale Verteilungen eines
  Prozesses ist der Index die Zeitmenge, der endliche Fall genügt also nicht.
  Der Punkt ist auf einen beliebigen Index umgestellt, mit Produkten über
  `J : Finset ι` und Abzählbarkeit von `ι` nur für die konvergenzbestimmende
  Hälfte.

Nebenbefund, in die Roadmap eingetragen: die Liste „Mathlib supplies" von
`MartingaleProblems` nannte optional stopping, Doobs Ungleichungen, die
Upcrossing-Theorie und die Konvergenzsätze pauschal als vorhanden. Alle vier
sind auf `Filtration ℕ` festgelegt (`Convergence.lean:55`, `Upcrossing.lean:315`,
`OptionalStopping.lean:37`); nur die **Definitionen** `Martingale`,
`Supermartingale`, `Submartingale` (`Basic.lean:48,53,59,65`) gelten für
`[Preorder ι]`. Die Liste sagt das jetzt.

**Offen geblieben.** Nichts an diesen acht Zeilen; nicht angefasst wurden
`fact:bp`, `fact:sepcond`, `fact:fullgenerator` und `fact:stoppedlocalmg`.
Damit stehen noch vier `?` in der Tabelle, gegenüber zwölf zu Beginn des Laufs.
`fact:stoppedlocalmg` ist der nächste: die Notiz in der Tabelle vermutet
`MeasureTheory.Locally` und `stoppedProcess_localSeq` aus
`Probability/Process/LocalProperty.lean`, und diese Datei existiert auf master
wie in v4.33.1, aber ob sie EK Proposition 2.3.1 wirklich hergibt, ist
ungeprüft. `fact:bp` und `fact:fullgenerator` sind keine Suchaufgabe, sondern
die offene Entscheidung aus der Liste oben: „nur für optionalen Kontext" ist
kein Roadmap-Status.

**Als Nächstes zu formalisieren: `MeasureTheory.induction_on_mulSystem`**
(`WeakConvergence` Meilenstein 5). Es ruht auf nichts als
`MeasurableSpace.comap` (`MeasureTheory/MeasurableSpace/Basic.lean:82`), dem
Satz von der monotonen Konvergenz und `induction_on_inter`
(`MeasureTheory/PiSystem.lean:692`), das zugleich die Vorlage für Gestalt,
`@[elab_as_elim]`-Attribut und Beweisführung ist. Es ist jetzt dran, weil es die
einzige der acht heute geschlossenen Lücken ist, die von keiner anderen Roadmap
abhängt — `WeakConvergence` hängt nur an Mathlib —, und weil drei Punkte, die
schon in den Roadmaps stehen, unmittelbar darauf warten: die Produktaussage in
`WeakConvergence` Meilenstein 1, `isDetermining_products` in
`MartingaleProblems` Meilenstein 3 und `isMPSolutionFor_iff_forall_fdd`
ebenda. Ein Satz ohne Vorbedingungen, an dem drei wartende Punkte hängen, ist
der richtige erste.

### 2026-08-30 — `fact:bp`, `fact:sepcond`, `fact:fullgenerator`, `fact:stoppedlocalmg`

Die letzten vier `?` der Tabelle. Alle vier sind Lücken, alle vier stehen jetzt
als benannte Punkte in einer Roadmap. Damit ist **jede der 29 Zeilen belegt**.
Geprüft wurde gegen `~/Code/lean/journal/.lake/packages/mathlib` (v4.33.1) und
gegen master über `gh api`/`gh search code`.

* **`fact:sepcond`** (tragend 2). Kein zitierter Fact: das Manuskript beweist
  ihn in `rem:sepcondproof` selbst. Zu formalisieren ist er trotzdem, denn
  `thm:absreg` schließt mit ihm (Stelle 3167). Nachgetragen als letzter Punkt
  von `WeakConvergence` Meilenstein 1, wo `IsSeparating` definiert wird:
  `IsSeparating.ae_eq_of_forall_condExp_eq`. Der Beweis wird dabei kürzer als
  im Manuskript. Schritt 1 bleibt, braucht aber keine Normierung, weil
  `IsSeparating` für endliche Maße formuliert ist; Schritt 2 und 3 entfallen
  ganz. Mit `G = {V ∈ B} ∈ 𝒢` und dessen Komplement gibt Schritt 1 direkt
  `P(U ∈ B, V ∉ B) = P(U ∉ B, V ∈ B) = 0`, und
  `Filter.EventuallyEq.of_forall_separating_preimage`
  (`Mathlib/Order/Filter/CountableSeparatingOn.lean:257`) macht daraus
  `U =ᵐ V`. Dessen Instanzhypothese `HasCountableSeparatingOn E MeasurableSet
  univ` ist `MeasurableSpace.CountablySeparated`, geliefert von
  `CountablyGenerated` und `SeparatesPoints`
  (`MeasurableSpace/CountablyGenerated.lean:381`), und `CountablyGenerated`
  wiederum von `BorelSpace` mit `SecondCountableTopology`
  (`Constructions/BorelSpace/Basic.lean:210`). Reguläre bedingte Verteilungen
  werden nicht gebraucht, und das ist ein Glück: Mathlibs `condDistrib`
  (`Probability/Kernel/CondDistrib.lean:64`) bedingt auf eine **Abbildung**,
  nicht auf eine Teil-σ-Algebra, und `condExpKernel`
  (`Probability/Kernel/Condexp.lean:70`) verlangt `Ω` selbst standard-borelsch.
  Beides trifft hier nicht zu.
* **`fact:bp`** (tragend 2). Lücke. Mathlib kennt bp-Konvergenz nicht:
  `gh search code` findet weder „boundedly pointwise" noch „bp-closure", und
  `seqClosure`/`IsSeqClosed` (`Topology/Defs/Sequences.lean:55,61`) schließen
  unter den Limiten einer Topologie ab, was bp-Limiten nicht sind. Die
  Roadmaps hatten weder den bp-Abschluss noch `lem:closure`, die vom Manuskript
  als die eigentlich benutzte Fassung bezeichnete Aussage. Beides ist jetzt in
  `MartingaleProblems` Meilenstein 2: `mpProcess`, `MPSolutions.span`,
  `IsMPSolutionFor.insert_of_tendsto` (`lem:closure`, mit
  `MeasureTheory.eLpNorm_condExp_le_eLpNorm`,
  `ConditionalExpectation/Real.lean:288`, als einzigem analytischen Werkzeug)
  und darauf der bp-Block `BpTendsto`, `bpClosure`, `Submodule.bpClosure`,
  `isMPSolutionFor_bpClosure`. Der Befund, der die Größe der Lücke bestimmt:
  EKs transfinite Rekursion über die abzählbaren Ordinalzahlen wird in Lean
  durch eine **induktive Definition** von `bpClosure` ersetzt, und EK Appendix 3
  Proposition 3.1 ist dann eine doppelte Induktion über deren
  Induktionsprinzip, nach dem Muster von `induction_on_inter`. Der Fact ist
  damit kein schwerer Punkt mehr, sondern ein mittlerer.
* **`fact:fullgenerator`** (tragend 1). Die größte der vier Lücken, und die
  einzige, die außerhalb der Wahrscheinlichkeitstheorie liegt: Mathlib hat
  **keine Operatorhalbgruppen**. `dissipative` kommt in master nirgends vor
  (`gh search code`, null Treffer), eine stark stetige oder messbare
  Halbgruppe gibt es nicht, und Hille--Yosida steht in `docs/1000.yaml` als
  `Q974405` ohne `decl`. Vorhanden ist nur die Resolvente beschränkter
  Elemente einer Banachalgebra (`Analysis/Normed/Algebra/Spectrum.lean:285ff`),
  die hier nichts hilft. Da kein Meilenstein den Gegenstand hatte, ist
  `MartingaleProblems` Meilenstein 13 neu angelegt: `IsDissipative`,
  `MeasurableContractionSemigroup`, `fullGenerator`,
  `fullGenerator_isDissipative` mit der Resolventenformel (EK 1.5.1), die
  Darstellung `mpSolution_resolvent_repr` als eigener Punkt, und die beiden
  Richtungen `isDissipative_of_forall_exists_mpSolution` (EK 4.3.5) und
  `isMPSolutionFor_fullGenerator` (EK 4.1.7). Messbarkeit, nicht starke
  Stetigkeit: die Übergangshalbgruppe eines Markovprozesses auf `Bdd(E)` ist
  nicht stark stetig, und nichts im Meilenstein braucht es. Hille--Yosida,
  Cores und die Exponentialformel bleiben draußen, wie `rem:noch1` es sagt.
* **`fact:stoppedlocalmg`** (tragend 0). Lücke, aber die kleinste. Die Notiz
  des letzten Laufs war halb richtig: `MeasureTheory.Locally`, `IsStable` und
  `IsStable.locally` existieren (`Probability/Process/LocalProperty.lean:93,142,153`,
  auf master wie in v4.33.1), aber sie sind **abstrakt** — die Datei nennt
  Martingale nur im Modulkommentar, und `Locally` wird nirgends an einem
  Martingal instanziiert. Was fehlt, ist genau die Stabilität der
  Martingaleigenschaft unter Stoppen in stetiger Zeit;
  `Submartingale.stoppedProcess` (`OptionalStopping.lean:104`) ist auf
  `Filtration ℕ` und reellwertige Prozesse festgelegt. Nachgetragen als Punkt
  von `MartingaleProblems` Meilenstein 9, wo das dafür nötige Optional Sampling
  in stetiger Zeit schon steht: `isStable_martingale_rightContinuous`, als
  Eigenschaft die **Konjunktion** aus Martingal und Rechtsstetigkeit, denn nur
  sie ist stabil. `IsStable.locally` liefert dann EK 2.3.1 ohne weiteren
  Beweis. Der Fact ruht also auf `fact:optsampl`, und beide liegen jetzt im
  selben Meilenstein.

**Zur offenen Frage der vier Facts ohne tragende Fundstelle.** Für
`fact:stoppedlocalmg` nachgesehen und nichts gefunden: die Lokalisierung des
Manuskripts (`def:localizing`, Stelle 4385) setzt in \ref{it:L1} die
Martingaleigenschaft der gestoppten Prozesse **voraus** und leitet sie nicht
her. Mittelbar getragen wird der Fact damit erst dort, wo ein konkretes
lokalisierendes System verifiziert wird — in der Roadmap
`localizingSystem_of_boundedJumps`. Das ist eine schwächere Trägerschaft als
die von `fact:doob`, aber keine Entbehrlichkeit.

**Offen geblieben.** Nichts an diesen vier Zeilen. Das Inventar ist damit
vollständig: 29 Zeilen, kein `?`. Ungeprüft bleibt weiterhin die in den
Auffälligkeiten notierte Frage, ob die Roadmaps von polnischem auf
separabel-metrisches `E` umgestellt werden; sie betrifft `fact:fddconv`,
`fact:cmt` und `fact:PSpolish` und ist keine Suchaufgabe, sondern eine
Entscheidung.

**Als Nächstes zu formalisieren: `MeasureTheory.IsSeparating` samt
`IsSeparating.ae_eq_of_forall_condExp_eq`** (`WeakConvergence` Meilenstein 1).
Das Prädikat ruht auf `ext_of_forall_integral_eq_of_IsFiniteMeasure`
(`MeasureTheory/Measure/HasOuterApproxClosed.lean`), die bedingte Fassung
zusätzlich auf `Filter.EventuallyEq.of_forall_separating_preimage`
(`Order/Filter/CountableSeparatingOn.lean:257`) und der bestimmenden
Eigenschaft von `condExp`. Beides ist heute am Quelltext geprüft, beides liegt
in Mathlib fertig vor, und der Beweis ist der oben skizzierte Zweischritt --
also kein neuer Begriff außer dem Prädikat selbst. Es ist jetzt dran, weil
`IsSeparating` das einzige Prädikat ist, das **zwei** Roadmaps als Hypothese
führen: der Satz über die càdlàg-Modifikation in `MartingaleProblems`
Meilenstein 9 verlangt „`Φ` ist separierend", und `isDetermining_products` in
Meilenstein 3 baut darauf. Solange das Prädikat nicht existiert, greift jeder
dieser Punkte an den `ext_of_…`-Sätzen vorbei — und die bedingte Fassung
kostet, einmal das Prädikat da ist, zwanzig Zeilen. Sie schließt zugleich die
einzige Stelle des Manuskripts, an der eine trennende Klasse gegen eine
σ-Algebra statt gegen ein zweites Maß gespielt wird.

Damit sind es zwei benannte Ziele, die nebeneinander stehen dürfen, weil beide
nur an Mathlib hängen: `induction_on_mulSystem` (Meilenstein 5, vom
2026-08-29) und `IsSeparating` (Meilenstein 1). Reihenfolge: `IsSeparating`
zuerst, denn `isDetermining_products` braucht beide, und dieses ist das
kleinere.

### 2026-08-30, zweiter Lauf — Inventar vollständig, also Task 23

Die Tabelle hat kein `?` mehr; nach der stehenden Regel wechselt der Lauf zu
**Task 23**, dem Beweis der Dualitätsidentität für eine rein atomare Uhr. Am
Inventar wurde nichts geändert, an den Roadmaps eine Ergänzung, am Manuskript
der Eintrag, den Task 23 vorsieht. Der ausführliche Bericht steht in
`Task23/PROTOKOLL.md`; hier das Wesentliche.

**Stufe 1 und Stufe 2 sind bewiesen.** `rem:atomicdual` ist jetzt
`prop:atomicdual` mit Beweis, gestützt auf ein neues `lem:atomgrid`. Der Kern:
eliminiere `γ` durch Kreuzmultiplikation der beiden Zuwachsdarstellungen an
derselben Stelle, was
`m_j(Φ(i+1,j)-Φ(i,j)) = m_i(Φ(i,j+1)-Φ(i,j))` liefert; diese Relation ist linear
in `Φ` und invariant unter Transposition, also erfüllt der antisymmetrische
Anteil `w = Φ - Φᵀ` sie ebenfalls, und eine Induktion über den **Abstand zur
Diagonale**, die die Stufen `d` und `d-1` zugleich mitführt, gibt `w ≡ 0`.
Gebraucht wird nur `m_i ≠ 0`: keine Positivität, keine Integrabilität, keine
Regularität von `γ`. Die zweite Konvention `ι = o` ist nicht ein zweiter Beweis,
sondern dieselbe Aussage nach Spiegelung des Gitters und Umkehrung der
Massenliste.

Stufe 2 kostet danach nichts: sind die Atome unter `t` endlich viele und
paarweise vergleichbar, so ist die Kette `0, a₁, …, a_N, t` ein Gitter, und
abzählbar viele Atome insgesamt sind kein Hindernis. Genau das ist die stehende
Hypothese von `rem:atomicdual`.

**Verifiziert, nicht nur geglaubt.** `Task23/verify.py` (neu) baut das volle
homogene System, das \eqref{eq:incrementrep} den Unbekannten `Φ, γ` auferlegt,
nimmt dessen Kern und prüft an einer Kernbasis die Dualitätsidentität, die
Symmetrie von `Φ` auf dem ganzen Quadrat und die Symmetrie von `γ` im Inneren.
Exakte rationale Arithmetik, `N = 2..8`, drei Massenvektoren, beide
Konventionen: 42 Konfigurationen, alle drei Aussagen überall erfüllt. Das ist
stärker als `oracle.py`, das die Reduktion auf eine freie Zeile schon
voraussetzte. Danach meldet `python3 check.py` `clean` (123 Seiten, keine
undefinierten Referenzen).

**Ein Befund am Manuskript, und er ist eingetragen.** `rem:atomicdual` behauptete
bisher, das Argument brauche „no order structure beyond a preorder". Bewiesen
ist weniger: die Atome unter `t` müssen eine **Kette** bilden — unter
\eqref{T2a} automatisch, unter \eqref{T0} nicht. Die Statustabelle von
`rem:atomsnotchange` trennt jetzt beide Zeilen: „purely atomic, atoms a chain"
ist `proved`, „purely atomic, atoms incomparable" bleibt „verified symbolically;
not proved", und ordnungsdichte Atome stehen bei „open" statt stillschweigend
unter der bewiesenen Zeile. Ordnungsdichte Atommengen sind nämlich gar nicht
Stufe 2: sie verletzen die Hypothese „endlich viele Atome unter jedem `t`", und
der Grund ist scharf — liegen die Atome dicht, trägt kein Intervall `[s,s')`
genau ein Atom, die Gitterrelation hat kein Gegenstück, und es gibt kein Gitter,
an dem entlang induziert werden könnte.

**In die Roadmap eingetragen.** `MartingaleProblems` Meilenstein 8 hatte zur
atomaren Uhr keinen Punkt — er nannte `duality_of_atomless` und
`duality_discrete` und ließ dazwischen eine Lücke. Jetzt stehen dort
`atomGrid_symm`, `Clock.atomChain` und `duality_of_atomic`, und
`duality_discrete` ist als der Fall `m ≡ 1` von `duality_of_atomic` kenntlich.

**Ein zweiter Befund, der den nächsten Lauf spart.** `Task23/poset.py` (neu)
prüft den Fall unvergleichbarer Atome an `T = {0,1,2}²` mit der Produktordnung
nach, und zwar mit *allen* Relationen aus \eqref{eq:incrementrep} — für jedes
vergleichbare Paar, nicht nur für Einschrittintervalle. Zweierlei kommt heraus:
die Notiz des Manuskripts stimmt, `Φ(t,0) = Φ(0,t)` gilt dort für jedes `t`;
aber die **Symmetrie** `Φ(s,t) = Φ(t,s)` gilt nicht, sie fällt an den maximalen
und unvergleichbaren Punkten aus, etwa bei `((1,2),(2,1))`. Die Symmetrie ist
ein Phänomen der Kette, nicht der atomaren Uhr. Ein Beweis für den allgemeinen
Präordnungsfall kann also nicht über sie laufen — was die naheliegendste
Verallgemeinerung von `lem:atomgrid` ausschließt, bevor jemand sie versucht.
Auch das steht jetzt im Manuskript.

**Offen geblieben.** Der Fall unvergleichbarer Atome (der kleinste Fall geht von
Hand und steht im Protokoll; ein allgemeines Argument fehlt, und der Weg über
die Symmetrie ist nach dem eben Gesagten versperrt), ordnungsdichte Atommengen,
und Stufe 3, die gemischte Uhr. Ebenso unberührt die ältere Frage aus den
Auffälligkeiten, ob die Roadmaps von polnischem auf separabel-metrisches `E`
umgestellt werden.

**Als Nächstes zu formalisieren: `atomGrid_symm`** (`MartingaleProblems`
Meilenstein 8). Es ruht auf nichts — Körperarithmetik über `ℝ`, `ℕ` als einziger
Index, und eine Induktion, die zwei Stufen zugleich mitführt, also
`Nat.le_induction` auf der starken Form der Aussage. Kein Maß, keine Uhr, keine
Topologie, kein Import außer `Mathlib/Algebra/Order/`. Es ist jetzt dran, weil es
das kleinste vollständig bewiesene Objekt des ganzen Manuskripts ist, weil sein
Beweis seit heute Zeile für Zeile im Manuskript steht und symbolisch gegengeprüft
ist, und weil `duality_of_atomic` unmittelbar darauf wartet, ohne dass eine der
vier Roadmaps sonst etwas beisteuern müsste. Ein Satz ohne Vorbedingungen, dessen
Beweis schon geschrieben ist, ist der billigste erste Schritt, den dieses Projekt
gerade hat — und der einzige, bei dem die Formalisierung den Papierbeweis
tatsächlich prüfen kann, statt ihn nur nachzuzeichnen.

### 2026-08-30, dritter Lauf — Task 23, der Halbordnungsfall

Die Tabelle hat weiterhin kein `?`; der Lauf ging nach der stehenden Regel an
Task 23, und zwar an dessen ersten offenen Punkt, die **unvergleichbaren
Atome**. Ein Beweis kam nicht heraus. Zwei Dinge kamen heraus, die es wert sind,
und das Ausführliche steht in `Task23/PROTOKOLL.md`.

**Eine Reduktion, die `Φ` eliminiert.** Weil `T` ein kleinstes Element hat, ist
`T_{<0}` leer, und \eqref{eq:incrementrep} an `s = 0` bzw. `t = 0` löst `Φ` auf:
`Φ(s,t) = Φ(0,t) + Σ_{a<s} m_a γ(a,t)` und ebenso in der zweiten Variablen.
Beides zusammen ist mit \eqref{eq:incrementrep} gleichwertig, und übrig bleibt
eine Bedingung an `γ` allein. Diese zerfällt entlang `γ = (λ+κ)/2` in eine
Bedingung an den symmetrischen und eine an den antisymmetrischen Anteil, und der
Dualitätsdefekt `Φ(t,0) − Φ(0,t) = Σ_{a<t} m_a (γ(a,0) − γ(0,a))` hängt **nur an
`κ`**. Der symmetrische Anteil von `γ` kommt in der Dualität nicht vor. Auf einer
Kette erzwingt die `κ`-Bedingung sofort `κ ≡ 0` — das ist `lem:atomgrid` ohne
`Φ`. Als `duality_defect_eq_integral` in `MartingaleProblems` Meilenstein 8
eingetragen, vor `atomGrid_symm`, weil es unbedingt gilt und `duality_of_atomic`
kürzer macht.

**Ein Gegenbeispiel, das eine Begründung des Manuskripts widerlegt.** Auf dem
Diamanten `T = {0,a,b,t*}` mit `m_a = 1`, `m_b = −1` erfüllen
`γ(a,·) ≡ 1`, `γ` sonst `0`, und `Φ(t*,·) ≡ 0`, `Φ` sonst `≡ −1` beide
Darstellungen aus \eqref{eq:incrementrep} und haben `Φ(t*,0) − Φ(0,t*) = 1`.
Exakt gerechnet und die Relationen unabhängig nachgeprüft (`Task23/diamond.py`).
Damit steht fest: **`lem:atomgrid` kommt mit `m_i ≠ 0` aus, der Halbordnungsfall
nicht.** Die Positivität der Massen — also dass `q` ein Maß ist — ist dort
tragend. Siehe die Auffälligkeit oben.

**Und die Hypothese, die es stattdessen braucht, belegt statt geraten.** Über
alle Halbordnungen mit kleinstem Element auf vier und fünf Punkten und alle
Massenvektoren eines kleinen Gitters mit beiden Vorzeichen (18955
Konfigurationen, 624 Ausfälle) gilt ausnahmslos: fällt die Dualität, so gibt es
ein `s` mit `q(T_{<s}) = 0` bei nichtleerem `T_{<s}`. Für eine echte Uhr ist das
automatisch, und über dieselben Halbordnungen mit nichtnegativen Massen (58081
Konfigurationen) gab es keinen einzigen Ausfall. Die Vermutung lautet damit: für
jede Uhr auf einer Halbordnung mit kleinstem Element und endlich vielen Atomen
unter `t*` gilt `Φ(t*,0) = Φ(0,t*)`, ohne Vergleichbarkeit.

`python3 Journal/Blog/MartingaleProblem/check.py` meldet `clean` (123 Seiten).

**Offen geblieben.** Der Beweis des Halbordnungsfalls. Das Protokoll hält fest,
wo er hakt: unter der `κ`-Bedingung allein ist der Defekt durch *gewichtete*
Summen der Gleichungen unterhalb `t` nicht bestimmt — jede solche Kombination
wird zur Identität —, der Gehalt sitzt in den einzelnen Gleichungen an den
maximalen Elementen von `T_{<t}`. Unberührt: ordnungsdichte Atommengen, Stufe 3,
und die ältere Entscheidung, ob die Roadmaps von polnischem auf
separabel-metrisches `E` umgestellt werden.

**Als Nächstes zu formalisieren: `duality_defect_eq_integral`**
(`MartingaleProblems` Meilenstein 8). Es ruht auf nichts als
`MeasureTheory.setIntegral` über `Set.Iio` und der Beobachtung `Iio 0 = ∅` für
ein kleinstes Element — kein Gitter, keine Atome, keine Kette, keine
Vergleichbarkeit, und es gilt für jede Uhr, atomar oder nicht. Es ist jetzt dran,
weil es die einzige Aussage dieses Meilensteins ist, die *vor* der Fallunterteilung
in atomlos und atomar steht und beide Zweige trägt: `duality_of_atomless` und
`duality_of_atomic` beginnen beide damit, `Φ` aus `γ` aufzulösen, und beide
Beweise werden dadurch kürzer statt nur anders. Es ist zugleich die Aussage, die
den Beweisstand am schärfsten wiedergibt — sie sagt, dass Dualität eine Aussage
über den antisymmetrischen Anteil von `γ` ist und über sonst nichts —, und sie
ist noch kleiner als `atomGrid_symm`, das der Lauf vom 2026-08-30 vorgeschlagen
hat. Reihenfolge also: `duality_defect_eq_integral`, dann `atomGrid_symm`, dann
`duality_of_atomic`.

### 2026-08-30, vierter Lauf — Aufgabe 1: der bp-Abschluss ist gestrichen

Die Tabelle hatte kein `?`; der Lauf hat die vorrangige Aufgabe 1 ausgeführt.
Ergebnis: **\EK{} Proposition 4.3.1 trägt im Manuskript nichts**, und der
bp-Abschluss ist aus der Roadmap verschwunden.

**Der Befund am Manuskript, vollständig.** `\ref{cor:bpclosure}` kommt an fünf
Stellen vor — 1402 (`rem:bpunused`), 1666 (Bündeltabelle §2), 2755, 2761 und
2775 (`rem:bpscope`), 9053 (§8) — und `\ref{fact:bp}` an vier, alle in
denselben Abschnitten. Kein Beweis benutzt eines von beiden. `lem:closure`
dagegen wird in `rem:fddconsequences`(b) (2662) benutzt und ist die tragende
Aussage, wie das Manuskript selbst sagt.

**Der Befund an \EK{}, am Scan geprüft** (`references/EthierKurtz1986.pdf`,
Buchseiten 174 und 178–182). Proposition 4.3.1 steht auf Buchseite 174 und hat
den Beweis „This is immediate from the discussion above"; die Diskussion ist die
Bemerkung, dass die Menge der Paare `(f,g)`, für die (3.1) ein Martingal ist,
bp-abgeschlossen ist. Gebraucht wird das in §4.3 an genau einer Stelle: im
Beweis von Theorem 4.3.8 (Buchseite 180) hält (3.32) zunächst nur für
`A ∩ (C̄(Ê) × B(Ê))` und wird auf den bp-Abschluss ausgedehnt, um `(χ_E, 0)`
einsetzen zu können. Proposition 4.3.9 unmittelbar darunter ersetzt das durch
eine Folge `(f_n,g_n) ⊂ A` mit `bp-lim f_n = χ_E`, `inf_n inf_x g_n > -∞` und
`g_n → 0` punktweise; ihr Beweis ist eine Zeile: einsetzen in (3.32), `n → ∞`,
Fatou. Proposition 4.3.10 (Buchseiten 180/181) erledigt `E = ⋂_k E_k`, indem sie
das Argument für jedes `E_k` einzeln führt — „the analogue of (3.32)" — und
danach die abzählbar vielen fast sicheren Ereignisse schneidet.

**Was in der Roadmap jetzt steht.** `MartingaleProblems` Meilenstein 2 hat
`BpTendsto`, `IsBpClosed`, `bpClosure`, `Submodule.bpClosure` und
`isMPSolutionFor_bpClosure` nicht mehr. An ihrer Stelle stehen drei Punkte:

* `IsMPSolutionFor.insert_of_tendsto_of_forall_norm_le` — die gleichmäßig
  beschränkte punktweise Folge liefert die beiden `L¹`-Limiten von
  `insert_of_tendsto` durch dominierte Konvergenz. Das ist die erste Hälfte von
  `cor:bpclosure`, also die, die das Manuskript in `rem:bpscope` „die stärkste
  von `X` unabhängige Hypothese" nennt. Die Schranke steht als Hypothese der
  Aussage; ein eigenes Prädikat lohnt bei einer einzigen Verwendung nicht.
* Ein Punkt, der festhält, dass kein Abschlussoperator gebaut wird, und warum.
* `IsMPSolutionFor.submartingale_mpProcess_of_tendsto` — der einseitige
  Begleiter, reellwertig: ist `g_n` nur nach unten gleichmäßig beschränkt, so
  ist `mpProcess q c X f g` ein **Submartingal** statt eines Martingals. Der
  Beweis ist dieselbe Rechnung mit Fatou statt dominierter Konvergenz auf der
  `g`-Seite, und `MeasureTheory.submartingale_of_setIntegral_le`
  (`Mathlib/Probability/Martingale/Basic.lean:281`) schließt ab — am Quelltext
  geprüft, unter `[Preorder ι]` formuliert, also ohne Zusatzhypothese an den
  Index benutzbar. Das ist die abstrakte Fassung des Fatou-Schritts von
  Prop. 4.3.9 und der ganze Inhalt, den der bp-Abschluss dort hatte.

Meilenstein 9 trägt die Anwendung, hinter der càdlàg-Modifikation, wo sie
hingehört, weil sie Optional Sampling, càdlàg-Pfade und eine Metrik auf `E`
braucht, die Meilenstein 2 alle nicht hat:
`IsMPSolutionFor.integral_comp_stoppedLim_eq` (die Identität (3.32) von
Thm. 4.3.8, ohne Abschluss), `IsMPSolutionFor.ae_forall_mem_of_tendsto`
(Prop. 4.3.9) und `IsMPSolutionFor.ae_forall_mem_iInter_of_tendsto`
(Prop. 4.3.10). **Das weicht von der Aufgabenstellung ab**, die alle drei an die
Stelle des bp-Blocks in Meilenstein 2 setzen wollte; Meilenstein 2 fixiert nur
`[Preorder ι]` und einen messbaren Zustandsraum, und die stehende Regel der
minimalen Voraussetzungen verbietet, ihm dafür eine Metrik und eine Topologie
auf dem Index aufzuladen. Der abstrakte Kern — der Fatou-Schritt — steht dort,
wo er verlangt war.

**Ein Nebenbefund, der eine Roadmap-Zeile wert war.** Mathlib hat Fatou nur für
`ℝ≥0∞`: `MeasureTheory.lintegral_liminf_le` und `lintegral_liminf_le'`
(`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231,213`). Eine
Bochner-Fassung für nach unten beschränkte reelle Funktionen gibt es nicht — die
Suche nach „Fatou" über ganz Mathlib findet außerhalb dieser Datei nur einen
Modulkommentar in `Probability/Martingale/Convergence.lean:77`. Der Meilenstein
nennt sie deshalb als eigene, an Mathlib gerichtete Aussage.

**Das Manuskript ist unverändert.** `cor:bpclosure` und `fact:bp` bleiben
stehen; `fact:bp` steht im Inventar jetzt auf `entbehrlich (2026-08-30)`, nicht
gelöscht. Was zu erwägen bleibt und dem Nutzer gehört: `rem:bpscope` sagt schon
„even that is optional" — nach diesem Lauf ist es nicht mehr optional, sondern
unbenutzt, und §8 könnte das sagen.

Damit ist auch die Auffälligkeit „§4.3 von \EK{} ist nur zu einem Drittel
ausgeschöpft" zur Hälfte erledigt: 4.3.8, 4.3.9 und 4.3.10 stehen jetzt in
`MartingaleProblems` Meilenstein 9. Offen aus dieser Sektion bleiben Thm. 4.3.12
(Quasi-Linksstetigkeit) und Cor. 4.3.13.

#### Aufgabe 2: die Präordnung, \eqref{T3p}, `AdditiveDist`

Ergebnis ist `Facts/PRAEORDNUNG.md`, neu angelegt, mit der verlangten Tabelle
und drei Empfehlungen. Hier nur, was das Inventar angeht.

**Die Ausgangsliste war zu groß, und zwar aus zwei prüfbaren Gründen.**
\eqref{T2b} enthält \eqref{T2a} (`def:bundles`, Zeile 634), also hat jede mit
\eqref{T2b} annotierte Aussage eine lineare Ordnung und dort ist
`Set.Iio t \ Set.Iio s = Set.Ico s t`; und keine Aussage des Manuskripts ist mit
\eqref{T1} annotiert — §2 sagt bei 1856 selbst, \eqref{T1p} komme „not at all"
vor. Übrig bleiben die \eqref{T0}-Aussagen.

**Und sie war zugleich zu klein.** Bei $s = 0$ fallen die Differenzform und
Mathlibs `Set.Ico`/`Set.Ioc` auch auf einer Präordnung zusammen, weil
`Set.Iio 0 = ∅` für ein kleinstes Element. Der Kompensator selbst ist deshalb
von der Wahl unabhängig; die Frage entscheidet sich allein an den zehn Stellen
mit $s \neq 0$, die in `PRAEORDNUNG.md` einzeln aufgeführt sind.

**Die Antwort ist: sie trägt, an vier Stellen, und weit außerhalb von §6.**
`prop:fddchar` (§4, mit `lem:closure` und `cor:bpclosure`), `ex:shiftXA` (§6),
`lem:dualsemigroup` und `prop:dualCK` (§8) benutzen `eq:clockadd` bei
allgemeinem $s$, und die Additivität ist unter `Set.Ico` auf $\Rp^2$ falsch —
$[0,2)^2 \neq [0,1)^2 \cup [1,2)^2$. Der nicht lineare Index ist instanziiert
und nicht bloß zugelassen: `ex:clocks`(iv) nennt ihn, `rem:fddnochain` rechnet
auf $\Rp^2$, und 749 begründet mit ihm, warum die Uhr ein Maß sein muss.
`lem:chain` und `prop:atomicdual` brechen im Beweis *nicht*, aber ihre Hypothese
`eq:incrementrep` wird vom Kompensator geliefert und hängt damit doch daran.
Empfehlung: die Differenzform behalten.

**Zwei Befunde nebenbei, beide oben unter Auffälligkeiten eingetragen**: das
falsche Kolmogorov--Chentsov-Zitat in `MartingaleProblems` (korrigiert) und die
zu schwach angegebenen Hypothesen von `SkorokhodSpace` Meilenstein 2 (nicht
geändert, weil die Entscheidung dem Nutzer gehört). Dazu die Stelle 2238 des
Manuskripts, die `[Preorder ι] [TopologicalSpace ι]` mit \eqref{T2b}
gleichsetzt.

**Zu \eqref{T3p}.** Prädikat: `[Preorder ι] [TopologicalSpace ι]`, am Quelltext
von `RemyDegenne/brownian-motion` belegt. Sprungtheorie: \eqref{T2b} genügt ihr
ganz — gebraucht werden Linearität (für die monotone Folge im Beweis der lokalen
Endlichkeit), eine abzählbare dichte Teilmenge (für die Treppenapproximation in
`IsCadlag.measurable` und für die Bestimmtheit) und σ-Kompaktheit für die
Abzählbarkeit; die Metrik auf dem **Index** kommt nirgends vor, `dist` steht in
`largeLeftJumpSet` auf `E`. Raum mit $J_1$: \eqref{T3p}, und `thm:T3sharp`(b)
zeigt, dass es nicht weniger geht.

**Zur Gegenprobe.** Ein Stetigkeitssatz bräuchte keinerlei Ordnung auf dem
Index — `IsKolmogorovProcess` steht unter `[PseudoEMetricSpace T]` — und ist ein
Momentenkriterium, keine Martingalaussage; deshalb verträgt er allgemeinere
Indexräume als die càdlàg-Modifikation, die über Doobs Upcrossing-Ungleichung
und damit über Filtration und Ordnung läuft. Er gehört weder in
`MartingaleProblems` (das `[Preorder ι]` und eine `Filtration` als Hypothesen
führt, die im Beweis nicht vorkommen) noch in `SkorokhodSpace` (dessen
Meilenstein 1 den Index auf \eqref{T3p} festlegt), sondern neben
`Probability/Process/Kolmogorov.lean` in Mathlib.

**Eine Korrektur an der Aufgabenstellung.** `\CE` kommt zehnmal vor, aber
**nicht** in §3 (Skorokhod): die Stellen sind 50 und 518 (Notation), 2342
(`def:canonical`), 2784–2786 (`def:wellposed`) und 5264–5274 (`thm:uniqueness`
und ihre lokale Fassung), also §4 und §6. Der Punkt der Aufgabe bleibt richtig:
einen Stetigkeitssatz analog zu `thm:absreg` gibt es nicht.

**Offen geblieben.** Alle drei Entscheidungen — Differenzform, Zerlegung von
`SkorokhodSpace` Meilenstein 2, `AdditiveDist` als Klasse — gehören dem Nutzer
und sind in `PRAEORDNUNG.md` mit Kosten und Ersparnis gegeneinander gestellt,
nicht getroffen. Nicht nachgeschlagen wurde, ob die Teilraumtopologie einer
abgeschlossenen Teilmenge von $\R$ stets deren Ordnungstopologie ist; das ist
die unbezifferte Position des Wegs „Teilmenge statt Typklasse".

**Als Nächstes zu formalisieren: `Clock.interval_union`**
(`MartingaleProblems` Meilenstein 1). Es ruht auf nichts als
`Set.Iio_subset_Iio` und `Set.Iic_subset_Iic` (`Mathlib/Order/Interval/Set/`,
beide für `[Preorder α]`) und der Disjunktheit zweier Differenzen derselben
aufsteigenden Kette von Mengen — kein Maß, kein Zustandsraum, keine Topologie,
kein Prozess. Es ist jetzt dran, weil dieser Lauf gezeigt hat, dass es **die**
tragende Eigenschaft der Uhr ist: vier Aussagen des Manuskripts in drei
verschiedenen Abschnitten ziehen `eq:clockadd` beim Namen heran, und alle vier
brächen, wenn das Intervall `Set.Ico` wäre. Zugleich ist es die Aussage, an der
die offene Entscheidung von `PRAEORDNUNG.md` hängt: wer die Differenzform durch
`Set.Ico` ersetzen will, muss zuerst dieses Lemma verlieren, und ein
formalisiertes `Clock.interval_union` samt den beiden `@[simp]`-Brücken
`Clock.Ico_eq_setIco` und `Clock.Ioc_eq_setIoc` macht die Kosten beider Wege
sichtbar, statt sie zu schätzen. Es ist außerdem kleiner als
`duality_defect_eq_integral`, das der dritte Lauf vom 2026-08-30 vorgeschlagen
hat, und dieses baut darauf: die Auflösung von `Φ` aus `γ` beginnt mit der
Additivität. Reihenfolge damit: `Clock.interval_union`, dann
`duality_defect_eq_integral`, dann `atomGrid_symm`.

### 2026-08-30, fünfter Lauf — Rückstau 1, 2 und 3

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da; der Lauf ging
nach der stehenden Regel in den Rückstau, von oben. Punkt 1 (Thm. 4.3.12
abstrakt), Punkt 2 (\EK{} §4.3 zu Ende auswerten) und Punkt 3
(`SkorokhodSpace` Meilenstein 2) sind erledigt und in `BACKLOG.md` gestrichen.
Geprüft wurde am Scan
(`references/EthierKurtz1986.pdf`, Buchseiten 179–182, PDF-Seiten 189–192),
gegen `~/Code/lean/journal/.lake/packages/mathlib` (v4.33.1) und gegen master
über `gh api`/`gh search code`.

**Ja, es geht ohne Operator — und es kostet eine Hypothese mehr, als der
Rückstau vermutet hat.** \EK{} Thm. 4.3.12 ruht auf vier Schritten, und keiner
nennt $A$: optional sampling für $Y^f$ an den beschränkten Stoppzeiten
$\tau_n \wedge t \leq \tau \wedge t$; das Verschwinden von
$E[C^f(\tau\wedge t) - C^f(\tau_n\wedge t) \mid \Filt_{\tau_n}]$; Lévys
Aufwärtssatz an der Filtration $\Filt_{\tau_n} \uparrow \bigvee_n
\Filt_{\tau_n}$; und `fact:sepcond` als Schluss. Das ist derselbe Schluss wie in
Schritt 4 von `thm:absreg`, und die Separiertheit von $\Phi$ ist die **einzige**
Hypothese, die beide Sätze teilen: eine abzählbare punktetrennende Teilmenge
kommt hier nicht vor, `eq:cc` auch nicht. In der Sprache von `def:regclass`
heißt der zweite Schritt: $C^f$ ist **in $L^1$ linksstetig entlang Stoppzeiten**.
Das ist nicht \ref{it:R3} — \ref{it:R3} nähert von rechts und an
deterministischen Zeiten — und es folgt auch nicht aus \ref{it:R2}.

**Und die neue Hypothese ist nicht technisch, sie ist die Atomlosigkeit.** Für
den Kompensator $C^f(t) = \int_{(0,t]} g(X(s))\,q(\dif s)$ mit beschränktem $g$
ist $|C^f(\tau\wedge t) - C^f(\tau_n\wedge t)| \leq \lVert g\rVert\,
q((\tau_n\wedge t, \tau\wedge t])$, und $\bigcap_n (\tau_n, \tau] = \{\tau\}$ bei
$\tau_n \uparrow \tau$; die Schranke geht also gegen $\lVert g\rVert\,
q(\{\tau\})$ und nicht gegen null, sobald die Uhr bei $\tau$ ein Atom hat. Das
ist scharf: auf $E=\{0,1\}$ mit $q=\delta_u$ wirft ein Prozess bei $u$ eine faire
Münze, löst ein Martingalproblem und hat $X(u-) \neq X(u)$ mit
Wahrscheinlichkeit $1/2$. \EK{} bemerken das nicht, weil bei ihnen
$q=$ Lebesgue ist. Damit steht fest, wo `rem:absreggain`(ii) endet, und das ist
oben als Auffälligkeit eingetragen.

**Was in der Roadmap jetzt steht.** `MartingaleProblems` Meilenstein 9 hat einen
weiteren Block, hinter dem Teilraumblock: `IsQuasiLeftContinuous` als Prädikat
(pro $t$ formuliert, weil genau das die Stoppzeiten beschränkt hält),
`IsQuasiLeftContinuous.ae_eq_leftLim` als die Verschärfung von \EK{} Lemma 3.7.7
— dort abzählbares Komplement, hier keines —,
`isQuasiLeftContinuous_of_isRegularizingClass` als die abstrakte Fassung mit dem
oben genannten Beweisweg, `isQuasiLeftContinuous_of_isMPSolutionFor` als die
klassische Instanz unter `∀ u, q {u} = 0`, und
`not_isQuasiLeftContinuous_of_atom` als benanntes Gegenbeispiel statt als
Bemerkung. `Suggested.lean` hat die passenden Stümpfe.

**Am Quelltext belegt, was der Beweis aus Mathlib zieht.** Lévys Aufwärtssatz ist
`MeasureTheory.tendsto_ae_condExp` und `MeasureTheory.tendsto_eLpNorm_condExp`
(`Mathlib/Probability/Martingale/Convergence.lean:426,439` in v4.33.1; auf
master dieselben Zeilen, kein `deprecated`), formuliert für
`ℱ : Filtration ℕ m0`, `[IsFiniteMeasure μ]` und reellwertiges `g` — der
`𝕂`-Fall sind also die zwei Komponenten. Dass $n \mapsto \Filt_{\tau_n}$ eine
`Filtration ℕ` ist, liefern
`MeasureTheory.IsStoppingTime.measurableSpace_mono` und
`MeasureTheory.IsStoppingTime.measurableSpace_le`
(`Mathlib/Probability/Process/Stopping.lean:468,481`).
Quasi-Linksstetigkeit selbst gibt es in Mathlib nicht: `gh search code` findet
für `quasi-left` und für `QuasiLeftContinuous` je null Treffer.

**Cor. 4.3.13 trägt nichts, und das ist geprüft, nicht vermutet.** Der Satz sagt
für abgeschlossenes $F$, dass $\inf\{t : X(t)\in F \text{ oder } X(t-)\in F\}$
fast sicher gleich $\inf\{t : X(t)\in F\}$ ist. Das Manuskript hat die
Konstruktion mit „oder $X(t-)$" genau einmal, in `rem:uniquelocal` bei 5282, und
dort ist die Menge $E\setminus K_m$ **offen**, nicht abgeschlossen; Cor. 4.3.13
greift also nicht. Die Débutfrage, die das Manuskript wirklich hat, ist eine
andere und schon beantwortet: `rem:strictdebut` bei 4578 trennt strikte von
rechtsstetigen Débuts, und `lem:L1auto` löst sie über das laufende Supremum.
Cor. 4.3.13 steht deshalb in keiner Roadmap.

**Und was Thm. 4.3.8–4.3.10 für das Manuskript tragen, ist jetzt benannt.**
`rem:ccverify` schließt mit Pfaden in $D_{E^\Delta}$ — genau die Aussage von
\EK{} Cor. 4.3.7, am Scan geprüft (Buchseite 179). Der Schritt zurück nach $D_E$
ist Thm. 4.3.8 mit Prop. 4.3.9/4.3.10, seit dem vierten Lauf in M9. Damit ist
die zweite Rückstaufrage beantwortet: die drei Sätze tragen den Schritt, den
`rem:ccverify` nicht tut. Auch das steht oben als Auffälligkeit.

**Rückstau 3: die Hypothesen von `SkorokhodSpace` Meilenstein 2 stehen jetzt je
Punkt da.** Der Rückstau verlangte einen Vorschlag; die stehende Regel der
minimalen Voraussetzungen verlangt mehr, nämlich die Korrektur, denn der
Meilenstein verlangte über den Schlusssatz von Meilenstein 1 das volle
\eqref{T3p} für Aussagen, denen \eqref{T2b} genügt. Beides ist getan und
getrennt gehalten: der Meilenstein führt jetzt zwei benannte Stufen (A) und (B),
jeder Punkt steht unter einer von beiden, die zwei Punkte mit σ-Kompaktheit
nennen sie, und der Schlusssatz von Meilenstein 1 gilt jetzt erst ab
Meilenstein 3. Die **Gliederung** — ob daraus zwei Meilensteine werden — ist
nicht angetastet; das ist die Entscheidung, die der Lauf vom 2026-08-30 dem
Nutzer zugeschrieben hat, und sie bleibt dort. Nebenbei fällt damit auch
Meilenstein 2 aus der Auffälligkeit „Die Roadmaps kennen `E` nur polnisch"
heraus: polnisch braucht dort allein `IsCadlag.measurable`, alles andere kommt
mit einem topologischen oder pseudometrischen `E` aus, und das steht jetzt da.
Die Auffälligkeit selbst bleibt, denn sie betrifft Meilenstein 1 von
`SkorokhodSpace` und `fact:fddconv`, `fact:cmt`, `fact:PSpolish`.

**Dabei ein Befund, den `PRAEORDNUNG.md` Teil 2 noch nicht hatte:
\eqref{T2b} und \eqref{T3p} sind unvergleichbar.** $h\Z$ trägt jede Instanz von
`SkorokhodSpace` Meilenstein 1 und verletzt die Rechtsapproximierbarkeit von
\eqref{T2b}, denn $(t,t+h)=\emptyset$. Die Sprungtheorie leidet nicht darunter,
aber nur aus einem Grund, der benannt gehört: auf einem diskreten linearen Index
sind `𝓝[<] x` und `𝓝[>] x` beide `⊥`, also ist jede Funktion càdlàg, und
`Function.leftLim f x = f x` — die Definition in
`Mathlib/Topology/Order/LeftRightLim.lean` setzt genau das, wenn `𝓝[<] a = ⊥`
ist, am Quelltext geprüft. Damit ist `leftJumpSet f = ∅` und alle vier Aussagen
sind trivial. Der Meilenstein sagt das jetzt, statt den diskreten Fall
stillschweigend unter (B) zu subsumieren, wo er nicht liegt. In
`PRAEORDNUNG.md` steht es als Nachtrag zu Teil 2.

**Und ein falsches Dateizitat, nebenbei gefunden und korrigiert.**
`PRAEORDNUNG.md` gab `Monotone.countable_not_continuousAt` als in
`Mathlib/Topology/Order/LeftRightLim.lean` liegend an. Dort steht der Name nur
im Modulkommentar; die Deklaration ist
`Mathlib/Topology/Order/Monotone.lean:164` in v4.33.1 und `:166` auf master, in
beiden Fällen ohne `deprecated`, und auf master findet `gh search code` den
Namen in acht Dateien, von denen `LeftRightLim.lean` die einzige ohne
Deklaration ist. Das ist genau der Fehlertyp, den Rückstaupunkt 4 turnusmäßig
sucht; `PRAEORDNUNG.md` und der Meilenstein sagen es jetzt richtig.

**Offen geblieben.** Nichts an diesen drei Rückstaupunkten. Nicht getan wurde,
was der Rückstau ausdrücklich dem Manuskript zuschlägt: ob Thm. 4.3.12 hinter
`thm:cadlag` aufgenommen wird und ob `rem:absreggain`(ii) die Grenze der
Atomtoleranz nennt, entscheidet der Nutzer; ebenso, ob `SkorokhodSpace`
Meilenstein 2 in zwei Meilensteine zerfällt. Neu im Rückstau steht als Punkt 5
die Frage, welche weiteren Aussagen des Manuskripts still auf Atomlosigkeit
rechnen.

**Als Nächstes zu formalisieren: `IsQuasiLeftContinuous` samt
`IsQuasiLeftContinuous.ae_eq_leftLim`** (`MartingaleProblems` Meilenstein 9).
Nur das Prädikat und die deterministische Lesart, nicht der Satz. Es ruht auf
`MeasureTheory.IsStoppingTime` (`Probability/Process/Stopping.lean`),
`Function.leftLim` und der Ordnungstopologie — kein Maßwechsel, keine bedingte
Erwartung, kein Martingal. Es ist jetzt dran, weil es die einzige Aussage dieses
Laufs ist, die von der schweren Vorarbeit des Meilensteins **nicht** abhängt:
`isQuasiLeftContinuous_of_isRegularizingClass` braucht optional sampling in
stetiger Zeit und `IsSeparating.ae_eq_of_forall_condExp_eq`, also zwei Punkte,
die selbst noch nicht existieren, während das Prädikat und `ae_eq_leftLim` reine
Ordnungs- und Grenzwertarbeit sind. Zugleich ist es die Stelle, an der sich
entscheidet, ob die Formulierung „pro `t`, unter `⨆ n, τ n ω ≤ t`" trägt oder ob
sie durch `WithTop ι` ersetzt werden muss, wie es
`MeasureTheory.IsLocalizingSequence` tut — und diese Frage ist billiger am
Prädikat zu klären als am Satz. Gegenüber den älteren Vorschlägen bleibt
`Clock.interval_union` der erste; `IsQuasiLeftContinuous` ist der erste Punkt
aus Meilenstein 9, der ohne den Rest von Meilenstein 9 auskommt.

### 2026-08-31 — Rückstau: `fact:fdd`, `fact:portmanteau`, und die Uhr in §7

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da; der Lauf ging
nach der stehenden Regel in den Rückstau, von oben. Der damalige Punkt 1 ist
eine **Manuskript**\-änderung und damit von der nicht verhandelbaren Regel 2
dieses Auftrags ausgeschlossen — er bleibt stehen, jetzt mit einem
Zwischenstand, der das sagt, und gehört dem Nutzer. Erledigt und in
`BACKLOG.md` gestrichen sind die damaligen Punkte 2 (die beiden letzten Facts
ohne tragende Fundstelle) und 5 (die Uhr im Konvergenzteil, auf Atome hin); die
Nummerierung ist danach neu vergeben, und ein neuer Punkt steht als 4 dort.

#### Rückstau 2: `fact:fdd` und `fact:portmanteau`

Beide Antworten sind zweigeteilt, und beide sind zugleich ein Befund an der
Tabelle „Where the prerequisites are used" in §2.

**`fact:portmanteau`: kein Beweis, eine Implikation, und ein undefiniertes
Wort.** Die §2-Tabelle schreibt bei 1661 „Fact `portmanteau`, `cmt` → Lemma
`EKconv`, Theorem `CPSconv`". Beide Beweise sind nachgelesen. Sie tun dasselbe:
sie verifizieren \ref{it:C1}--\ref{it:C3} von `thm:absconv` und überlassen
diesem alles Weitere. `lem:EKconv` benutzt `fact:Dcountable` (für $D$),
`ex:determining` (für \ref{it:C2}), die $J_1$-Stetigkeit der Auswertung an
Stetigkeitsstellen (für \ref{it:C3a}), Beschränktheit (\ref{it:C3b}) und
`prop:fddchar` mit der gleichmäßigen Schranke aus \eqref{eq:approxA}
(\ref{it:C3c}). `thm:CPSconv` ersetzt nur die letzten beiden Zutaten durch
\eqref{eq:cps1}--\eqref{eq:cps3}. Und `thm:absconv` selbst benutzt in Schritt 0,
1, 2 und 3 ausschließlich `fact:cmt` und `fact:ui`; `rem:absconvtopfree` sagt
das sogar selbst — „the proof invoked \ref{it:C1} and \ref{it:C3a} only through
Fact `cmt`". Portmanteau kommt nicht vor, in keinem der drei Beweise. Die
Tabellenzeile ist falsch und sollte nur `fact:cmt` nennen.

Damit bleibt die Frage, ob der Fact irgendwo mittelbar trägt, und sie hängt an
einem Wort, das das Manuskript nicht definiert. „Relativ kompakt" steht in
`fact:fddconv`(b), `fact:relcompact`, `fact:relcompact2` und
`rem:EKrelcompact`, und eine Definition gibt es nicht. In der Lesart „relativ
kompakt in der Topologie der schwachen Konvergenz" wird `fact:portmanteau`
nirgends gebraucht. In der metrischen Lesart — `fact:PSpolish` versieht
$\Prob(S)$ mit der Prohorov-Metrik, `fact:prohorov` sagt „straff genau dann,
wenn relativ kompakt" — braucht `rem:EKrelcompact` beim Übergang von der
Relativkompaktheit zu einer schwach konvergenten Teilfolge die Implikation
(a)⇒(b), und nur diese. Die Hälften (c), (d), (e) und (f) trägt in beiden
Lesarten nichts. Für die Formalisierung ist die Entscheidung kostenlos, und
das ist am Quelltext geprüft: `isCompact_closure_of_isTightMeasureSet`
(`Mathlib/MeasureTheory/Measure/Prokhorov.lean:530`, nicht `deprecated`; das
`@[deprecated]` bei 524 gehört zu einem Alias darüber, und der Name steht im
**Wurzelnamensraum** — die Sektion `Forward` der Datei öffnet `MeasureTheory`
nur, während die Sektion `Backward` ab 568 wirklich darin liegt, so dass die
Umkehrung `MeasureTheory.isTightMeasureSet_of_isCompact_closure` heißt und die
Hinrichtung nicht) ist über
`ProbabilityMeasure E` mit der Topologie der Verteilungskonvergenz formuliert,
also in der ersten Lesart, und die zweite steht als
`MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph`
(`Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean:676`) daneben. Der
Status `Mathlib` bleibt also; was sich ändert, ist die Kenntnis darüber, wieviel
davon gebraucht wird — nämlich fast nichts.

**`fact:fdd`: die zweite Hälfte trägt, die erste nicht.** Der Fact besteht aus
\eqref{eq:prodsep} (EK 3.4.6 und 3.7.1: Produkte separierender bzw.
konvergenzbestimmender Klassen sind es wieder) und dem Satz „in particular the
finite-dimensional distributions of a process determine its law". Die zweite
Hälfte ist mittelbar getragen, an genau den drei Stellen, die die §2-Tabelle
unter `thm:fdd` führt: `thm:absuniq`, `cor:DEuniqueness` und `ex:determining`.
Die erste Hälfte ist an keiner Stelle des Manuskripts benutzt, und das ist
nachgesehen, nicht vermutet:

* `prop:fddchar` beweist die Suffizienz mit einem funktionalen
  Monotone-Klassen-Argument (`fact:monotoneclass`) über der multiplikativen
  Klasse \eqref{eq:multclass} und benutzt Fubini als einzigen inhaltlichen
  Schritt; von separierenden Klassen ist keine Rede.
* `thm:uniqueness` Schritt 2 und `prop:uniqfromprop` schließen von den
  endlich-dimensionalen Verteilungen auf das Gesetz mit **Dynkin**, angewandt
  auf $\mathcal{K} = \{\prod_k f_k(\pi_{t_k}) : f_k \in \Bdd(E)\}$ und
  \eqref{eq:pathsigma}. Mit $\Bdd(E)$ ist die Separiertheit leer.
* `ex:determining` sagt es selbst: „this uses $\Bor(F) = \sigma(X_t)$
  (Theorem `thm:fdd`) and the monotone class theorem".
* `cor:DEuniqueness` beruft sich auf `thm:fdd`, nicht auf `fact:fdd`.
* Die separierenden Klassen der Dualitätsabschnitte
  (`lem:histrestart`\ref{it:hist_sep}, `prop:hawkesDcheck`\ref{it:hd_sep},
  `prop:rieszmarkov`) leben auf $\Prob(\hat E_r)$ bzw. $C(E_1)$ und sind keine
  Produkte.

Und dass die §2-Tabelle `fact:fdd` **überhaupt nicht** führt, ist das
Gegenstück dazu: die Buchhaltung hat den Fact nicht bloß unterschätzt, sondern
ausgelassen. Entbehrlich ist er trotzdem nicht — §9 verlangt bei 9048
ausdrücklich „the separating half of `fact:fdd` only, its path space half being
Theorem `thm:fdd`", und bei 9239 steht, er solle unabhängig von
Martingalproblemen entwickelt werden. Das ist dieselbe Lage wie bei
`fact:fullgenerator` und die entgegengesetzte zu `fact:bp`: dort war der Fact
im Manuskript zitiert *und* in §8 als optional bezeichnet, hier verlangt §9 ihn
ohne Einschränkung.

**Ein Roadmap-Fehler, der daran hing, und er ist korrigiert.** Der Produktpunkt
von `WeakConvergence` Meilenstein 1 begründete sich mit „every determining set
in **MartingaleProblems** is built from it". Das stimmt nicht:
`isDetermining_products` in `MartingaleProblems` Meilenstein 3 nennt selbst
`induction_on_mulSystem` (Meilenstein 5) als Beweisweg, und das Manuskript
macht es an allen vier oben aufgezählten Stellen ebenso. Der Produktpunkt hat
damit heute **keinen Abnehmer**, weder in einer der vier Roadmaps noch im
Manuskript. Gestrichen wird er nicht — §9 verlangt ihn —, aber seine
Begründung sagt jetzt, was geprüft ist: die Determining-Sets sind sein
Spezialfall `Γ i` alle beschränkt messbar, und der Zusatz besteht darin, dass
ein *separierendes* `Γ i` je Faktor genügt. Die Hypothesen des Punktes bleiben
unangetastet; sie sind schwächer als die des Manuskripts (beliebiger Index und
messbare Faktoren statt abzählbarem Index und separablen metrischen Faktoren)
und das ist nach der stehenden Regel richtig so.

#### Rückstau 5: die Uhr im Konvergenzteil, auf Atome hin

Ebenfalls erledigt und in `BACKLOG.md` gestrichen; die Antwort ist ein
Negativbefund, und er ist der bessere von beiden möglichen. **Keine Aussage von
§7 rechnet still auf Atomlosigkeit.** Der Rückstau nannte zwei Kandidaten und
beide halten stand. `rem:EKrelcompact` ruht auf `fact:relcompact`,
`fact:relcompact2`, `fact:fddconv` und `fact:prohorov`; alle vier sind über
$D_E[0,\infty)$ mit dem Lebesgue-Kompensator formuliert — `fact:relcompact2`
schreibt $Y(t) - \int_0^t Z(s)\dif s$ ausdrücklich hin —, und die Bemerkung
speist `lem:EKconv`, das die Bündeltabelle mit „Lebesgue" führt. Eine allgemeine
Uhr wird dort nirgends behauptet, also kann ein Atom auch nichts verderben.
Dasselbe für die übrigen Sätze des Abschnitts, einzeln nachgesehen:
`thm:absconv`, `lem:contuse`, `thm:absconvaug` und `thm:absconvws` sind
uhrenfrei (die Uhr kommt nur über das abstrakte $\XX$ herein und die
Bündeltabelle trägt „---" ein); `thm:MZconv` rechnet in jedem Schritt mit
$\lambda$; `thm:clockchange` setzt \ref{it:C3a} als Hypothese und trägt die Uhr
in \ref{it:K3} und \ref{it:K4}, also genau dort, wo ein Atom sichtbar wird.

Der Grund für den Negativbefund ist, dass das Manuskript die Frage schon gestellt
und beantwortet hat, an der einzigen Stelle, an der ein Atom wirklich beißt:
\ref{it:C3a}. `ex:atomicdiscontinuity` führt das Gegenbeispiel $q = \delta_1$ vor
und zeigt, dass die schlechten Zeiten dort eine **Halbgerade** bilden und nicht
eine abzählbare Menge, also kein $\Gamma$ hilft; `lem:contuse` sperrt ein, wo die
Stetigkeit überhaupt gebraucht wird; `thm:absconvaug` und `prop:atomaug`
reparieren es durch Vergrößerung des Pfadraums um die Werte an den Atomen
(Bündeltabelle: „any, atoms allowed"); und `rem:MZcost` nennt die Grenze der
Reparatur — die Konvergenz nach Maß sieht die Auswertung am Atom nicht, und
keine Augmentierung ändert das. Der Punkt aus dem Rückstau, der die Analogie zur
Quasi-Linksstetigkeit vermutete, trifft hier also nicht: dort war die
Atomtoleranz eine unbemerkte Grenze, hier ist sie ein eigener Abschnitt.

Ein Nebenbefund, der dabei anfiel und oben unter den Auffälligkeiten steht:
`thm:absconvws`, `thm:MZconv` und `rem:EKrelcompact` haben keine Zeile in der
Bündeltabelle, obwohl die übrigen sechs Aussagen des Abschnitts eine haben und
`thm:MZconv` mit dem separabel-metrischen, nicht polnischen Pfadraum gerade eine
Abweichung von \eqref{E3} trägt.

**Offen geblieben.** Rückstaupunkt 1, aus dem oben genannten Grund: er ändert
das Manuskript. Nicht angefasst wurde Task 23 (unvergleichbare Atome, jetzt
Rückstau 2): drei Läufe haben es versucht, `Task23/PROTOKOLL.md` hält fest, wo
es hakt, und ein vierter Anlauf in der Restzeit dieses Laufs hätte dieselbe Wand
ohne neuen Hebel getroffen — der Lauf hat stattdessen zwei Punkte abgearbeitet,
die eine Antwort haben. Ebenfalls nicht angefasst: die turnusmäßige Prüfung der
Roadmapzitate gegen master, die am 2026-08-29 lief und nach der dortigen Regel
(alle zwei Wochen) nicht fällig ist. Neu unter den Auffälligkeiten steht, dass
„relativ kompakt" im Manuskript undefiniert bleibt.

**Als Nächstes zu formalisieren: `MeasureTheory.induction_on_mulSystem`**
(`WeakConvergence` Meilenstein 5). Der Vorschlag ist nicht neu — der Lauf vom
2026-08-29 hat ihn schon gemacht —, aber dieser Lauf hat ihm das Argument
gegeben, das ihm fehlte, und rückt ihn dabei vor den Produktpunkt derselben
Roadmap. Es ruht auf `MeasurableSpace.comap`, dem Satz von der monotonen
Konvergenz und `induction_on_inter` (`Mathlib/MeasureTheory/PiSystem.lean:692`),
das zugleich die Vorlage für Gestalt, `@[elab_as_elim]` und Beweisführung ist —
also auf nichts außer Mathlib. Es ist jetzt dran, weil heute gezeigt ist, dass
es der Knoten ist, unter dem **alle** Wege des Manuskripts von den
endlich-dimensionalen Verteilungen zum Gesetz zusammenlaufen. Vier Stellen
führen dasselbe multiplikativ-erzeugende Argument aus: `prop:fddchar` und
`ex:determining` in der funktionalen Gestalt, die `induction_on_mulSystem`
wörtlich ist, `thm:uniqueness` Schritt 2 und `prop:uniqfromprop` in Dynkins
Maßgestalt, die daraus in einer Zeile folgt. Und zwei Roadmap-Punkte nennen es
ausdrücklich als ihren Beweisweg, `isDetermining_products`
(`MartingaleProblems` M3) und der Produktpunkt (`WeakConvergence` M1). Der
Produktpunkt, den dieselbe Roadmap bisher als das Fundament ausgab, hat
dagegen keinen Abnehmer. Ein Satz ohne Vorbedingungen, an dem sechs Stellen
hängen, geht dem voran, an dem keine hängt. Gegenüber den älteren Vorschlägen bleibt
`Clock.interval_union` der erste der Task-23-Linie; `induction_on_mulSystem`
ist der erste der Konvergenzlinie, vor `IsSeparating` und vor dem Produktpunkt.

### 2026-08-31, zweiter Lauf — Rückstau 4, und die Vollständigkeit von `E`

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da; der Lauf ging
nach der stehenden Regel in den Rückstau. Punkt 1 bleibt stehen (Manuskript,
Regel 2), Punkt 2 ist Task 23 und ohne neuen Hebel, Punkt 3 ist nach seiner
eigenen Regel — alle zwei Wochen, zuletzt 2026-08-29 — nicht fällig. Erledigt
und gestrichen ist **Punkt 4**, und zwar weil seine Blockade keine war.

**Der \EK{}-Scan ist erreichbar.** Der Punkt schloss mit der Warnung,
`references/EthierKurtz1986.pdf` sei aus diesem Worktree nicht zu lesen. Das
stimmt für den Worktree, nicht für den Pfad: die Datei liegt im Hauptcheckout,
unter `/home/pfaffelh/Code/lean/journal/references/`, und `Read` liest sie mit
`pages`. Der Seitenversatz ist +10. Das steht jetzt im Kopf von `BACKLOG.md`,
damit es kein Lauf mehr zweimal herausfinden muss.

#### Rückstau 4: der Abnehmer ist ausgeschlossen, und zwar zweifach

**Erstens am Wortlaut von \EK{} Prop. 3.7.1** (Buchseite 127, am Scan gelesen).
Sie lautet: `π_t(x) = x(t)`, und
`𝒮_E ⊇ 𝒮'_E ≡ σ(π_t : 0 ≤ t < ∞) = σ(π_t : t ∈ D)` für **jede** dichte
Teilmenge `D ⊆ [0,∞)`, mit Gleichheit für separables `E`. Das ist die
Pfadraumhälfte — `SkorokhodSpace.borel_eq_iSup_comap_eval`, Meilenstein 6 —
und **nicht** die Produkthälfte. Die Produkthälfte ist allein Prop. 3.4.6
(Buchseite 115): `M_k` separierend ⟹ `M` separierend; `(S_k,d_k)` vollständig
separabel und `M_k` konvergenzbestimmend ⟹ `M` konvergenzbestimmend. Die
Zuschreibung von `fact:fdd` an „3.4.6 und 3.7.1" verteilt sich also sauber auf
die zwei Hälften des Facts, und die Vermutung des Rückstaus, 3.7.1 sei die
konvergenzbestimmende Produkthälfte, trifft nicht zu.

**Zweitens am Beweis von \EK{} Thm. 3.7.8(b)** (Buchseite 132). Er benutzt sie
nicht. Der Gang ist: Teilfolge aus der Relativkompaktheit; Zeiten aus `D` an die
Stetigkeitspunkte des Limes schieben, mit Rechtsstetigkeit; Lemma 3.7.7, damit
diese dicht liegen; und dann wörtlich „By Proposition 7.1 and the Dynkin class
theorem (Appendix 4)". Gemeint ist dort der **funktionale** Dynkin-Satz: die
Eingabe des Schrittes ist (7.27), also die Gleichheit der Integrale von
Produkten `∏ f_i(X(t_i))` mit `f_i ∈ C̄(E)`, und die Mengenfassung greift auf
stetige Funktionen nicht. Appendix 4 führt ihn, \EK{} zitieren ihn auf
Buchseite 111 im Beweis von Prop. 3.4.2 unter diesem Namen — „the Dynkin class
theorem for functions (Theorem 4.3 of the Appendixes)". Damit ist der
Schlussschritt von 3.7.8(b) genau `induction_on_mulSystem`
(`WeakConvergence` M5), nicht die Produkthälfte.

Es gibt eine Stelle bei \EK{}, an der die konvergenzbestimmende Produkthälfte
wirklich arbeitet, und sie ist gefunden: der Schlusssatz von **Cor. 3.9.2**
(Buchseite 144), „This, together with the fact that `H` is dense in `C̄(E)` …,
allows one to conclude that the finite-dimensional distributions converge. The
details are left to the reader." Das Manuskript zitiert Cor. 3.9.2 nicht — es
zitiert aus §3.9 nur Thm. 3.9.1 (`fact:relcompact`) und Thm. 3.9.4
(`fact:relcompact2`), und `rem:EKrelcompact` ist \EK{} Rem. 4.5.2 und geht über
Relativkompaktheit plus Eindeutigkeit des Häufungspunkts, nicht über 3.9.2.
Der Befund des Laufs vom 2026-08-31 steht damit: **der Produktpunkt von
`WeakConvergence` Meilenstein 1 hat keinen Abnehmer, und sein einziger Grund
ist §9 des Manuskripts.** Der Punkt sagt das jetzt und nennt Cor. 3.9.2 als den
Weg, den das Manuskript gerade nicht geht.

#### Die Vollständigkeit von `E`: die älteste offene Auffälligkeit, belegt

Sie steht seit dem 2026-08-29 da und war nie eine Suchaufgabe ohne Werkzeug,
sondern eine ohne Scan. Mit dem Scan ist sie eine Zeile:

* \EK{} Thm. 3.1.8, Skorokhod-Darstellung (Buchseite 102): „Let $(S,d)$ be
  **separable**." Der Beweis benutzt Lemma 1.3, disjunkte Borelmengen kleinen
  Durchmessers und die Prohorov-Metrik; Vollständigkeit kommt nicht vor.
* \EK{} Cor. 3.1.9, stetige Abbildung (Buchseite 103): „Let $(S,d)$ and
  $(S',d')$ be **separable** metric spaces." Der Beweis ist Thm. 1.8 plus
  Cor. 1.6.
* \EK{} Thm. 3.7.8 (Buchseite 131): „Let $E$ be **separable**."
* Die Vollständigkeit beginnt eine Seite später, bei Lemma 3.2.1 („If $(S,d)$
  is complete and separable, then each $P$ is tight") und Thm. 3.2.2, also bei
  Prohorov — genau dort, wo die stehende Regel dieses Auftrags sie vermutet
  hatte, und in der Rückrichtung.

Mathlib bestätigt die Trennung an derselben Naht, am Quelltext geprüft:
`isCompact_closure_of_isTightMeasureSet` steht in der Sektion `Forward` unter
`[MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]`
(`Measure/Prokhorov.lean:65`) und sagt es im Docstring selbst („We only require
the space to be T2"), während `MeasureTheory.isTightMeasureSet_of_isCompact_closure`
in der Sektion `Backward` unter `[PseudoMetricSpace 𝓧] [OpensMeasurableSpace 𝓧]
[SecondCountableTopology 𝓧]` (`:570`) **und** `[CompleteSpace 𝓧]` (`:630`)
steht.

**Was daraufhin korrigiert ist.** `SkorokhodSpace` Meilenstein 8 fixierte „`E`
Polish" für alle sieben Punkte. Er führt jetzt, nach dem Muster von
Meilenstein 2, zwei benannte Stufen: **(A)** `E` separabel metrisch für die
ganze Theorie der endlich-dimensionalen Verteilungen und für Prohorov in
Richtung Straffheit ⟹ Relativkompaktheit, **(B)** `E` polnisch für die zwei
Punkte, die Prohorov rückwärts laufen lassen, `isTightMeasureSet_iff` und
`isTightMeasureSet_iff_forall_postcomp` (\EK{} Thm. 3.9.1 sagt „complete and
separable" selbst). Der Schlusssatz von Meilenstein 1 nennt Meilenstein 8 jetzt
als zweite Ausnahme neben Meilenstein 2.

**Und eine zweite Korrektur, die aus demselben Wortlaut fällt.**
`tendsto_of_isTight_of_tendsto_finiteDimensional` verlangte **Straffheit**;
\EK{} Thm. 3.7.8(b) und `fact:fddconv`(b) verlangen **Relativkompaktheit**, und
das ist unter der Hinrichtung von Prohorov die schwächere Hypothese. Nach der
stehenden Regel ist das ein Befund, und er ist ausgeführt: der Punkt heißt jetzt
`SkorokhodSpace.tendsto_of_isCompact_closure_of_tendsto_finiteDimensional`, sagt
seine vier Zutaten einzeln (Rechtsstetigkeit, `exists_countable_dense_continuity`,
`borel_eq_iSup_comap_eval` in der Fassung längs einer dichten Menge,
`induction_on_mulSystem`) und hält fest, dass die Produkthälfte nicht darunter
ist und warum: identifiziert wird ein Gesetz auf `D ι E` und nicht auf einem
Produktraum, und `eval t` ist dort messbar und nicht stetig — was der Beweis von
Prop. 3.7.1 zeigt, indem er `f ∘ π_t` nur als punktweisen Limes stetiger
Mittelungen bekommt. Die Straffheitsfassung steht als Korollar daneben, über
`isCompact_closure_of_isTightMeasureSet`, und bleibt damit in Stufe (A).

#### Ein Nebenbefund, der zu einer belegten Lücke wurde

Die Zeile `fact:PSpolish` trug seit dem 2026-08-29 die Notiz „dass 𝒫(S) polnisch
ist, ungeprüft". Geprüft, und es ist eine Lücke: Mathlib hat von
`ProbabilityMeasure E` als metrischem Raum nur die **Metrisierbarkeit**
(`MeasureTheory.instMetrizableSpaceProbabilityMeasure`,
`Measure/LevyProkhorovMetric.lean:695`, unter `[PseudoMetrizableSpace X]
[SeparableSpace X] [BorelSpace X]`). `SeparableSpace (ProbabilityMeasure`,
`CompleteSpace (ProbabilityMeasure` und `PolishSpace (ProbabilityMeasure` haben
in v4.33.1, im Arbeitsbranch des Nutzers und auf master (`gh search code`, nach
einer Gegenprobe an `instMetrizableSpaceProbabilityMeasure` als Beleg, dass die
Suche greift) **null** Treffer. Das ist die erste Hälfte von `fact:PSpolish`,
und sie stand in keiner Roadmap. Sie steht jetzt als eigener Block am Kopf von
`WeakConvergence` Meilenstein 3 — `separableSpace`, `completeSpace`,
`polishSpace` —, weil sie der Untergrund der Skorokhod-Darstellung und jedes
Teilfolgenarguments des Konvergenzteils ist, und weil sie nach der Regel der
vollständigen Grundtheorie je Objekt ohnehin dorthin gehört. Der Meilenstein
heißt jetzt „the space of laws, and the Skorokhod representation theorem", und
der Kopf der Roadmap zählt fünf statt vier fehlende Dinge.

**Offen geblieben.** Rückstau 1 (Manuskript, Regel 2) und Rückstau 2 (Task 23,
unvergleichbare Atome) sind unberührt; für Task 23 gilt weiter, was der letzte
Lauf sagte — die Wand steht im Protokoll, ein Hebel fehlt. Nicht getroffen ist
die **Gliederungsfrage**, ob `SkorokhodSpace` Meilenstein 1 seine globale
Festlegung „`E` a Polish space" aufgibt, nachdem jetzt zwei von acht
Meilensteinen ihre Hypothesen selbst führen; das ist dieselbe Art Entscheidung
wie die Zerlegung von Meilenstein 2 und gehört dem Nutzer. Ebenfalls nicht
angefasst: die turnusmäßige Prüfung der Roadmapzitate gegen master, nach ihrer
eigenen Regel nicht fällig.

**Als Nächstes zu formalisieren:
`MeasureTheory.ProbabilityMeasure.separableSpace`** (`WeakConvergence`
Meilenstein 3, erster Punkt des neuen Blocks). Es ruht auf nichts als
`TopologicalSpace.exists_dense_seq` für `E`, der endlichen Konvexkombination von
Diracmaßen und der Metrisierbarkeit, die Mathlib in
`instMetrizableSpaceProbabilityMeasure` schon liefert — kein Prozess, keine
Filtration, keine Uhr, kein Pfadraum, und aus der ganzen Roadmap keine
Vorbedingung. Es ist jetzt dran, weil es die einzige heute gefundene Lücke ist,
die **unterhalb** aller bisherigen Vorschläge liegt: `induction_on_mulSystem`,
`IsSeparating` und der Produktpunkt reden über Funktionenklassen auf `E`,
dieser Punkt über den Raum, in dem alle drei ihre Aussagen später machen. Und
er ist die Vorbedingung, die der Konvergenzteil am dichtesten braucht — jedes
Teilfolgenargument von `rem:EKrelcompact` und jedes „relativ kompakt" der vier
Facts `fddconv`, `relcompact`, `relcompact2`, `prohorov` lebt in
`ProbabilityMeasure`, und ohne Separabilität ist dort nicht einmal gesichert,
dass Kompaktheit Folgenkompaktheit ist. Gegenüber den älteren Vorschlägen
bleibt `Clock.interval_union` der erste der Task-23-Linie;
`ProbabilityMeasure.separableSpace` tritt in der Konvergenzlinie **vor**
`induction_on_mulSystem`, weil dieses über `ProbabilityMeasure` quantifiziert
und jenes es konstruiert.

### 2026-08-31, dritter Lauf — Rückstau 4: `ProbabilityMeasure E` als metrischer Raum

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da. Rückstaupunkt 1
bleibt stehen (Manuskript, Regel 2), Punkt 2 ist Task 23 und ohne neuen Hebel,
Punkt 3 ist nach seiner eigenen Regel — alle zwei Wochen, zuletzt 2026-08-29 —
nicht fällig. Der Lauf ging an **Punkt 4**. Er ist nicht gestrichen, sondern hat
einen Zwischenstand: der Block, den der zweite Lauf des Tages an den Kopf von
`WeakConvergence` Meilenstein 3 gesetzt hat, war **nicht formalisierbar, wie er
dastand**, aus zwei Gründen, und beide sind jetzt behoben. Geprüft wurde an
`~/Code/lean/journal/.lake/packages/mathlib` (v4.33.1), am Arbeitsbranch des
Nutzers (`091609e560a`) und gegen master über `gh api search/code`.

**Erstens: eine der drei Aussagen war nicht typrichtig.** Der Block verlangte
`MeasureTheory.ProbabilityMeasure.completeSpace`, „die Lévy--Prokhorov-Metrik auf
`ProbabilityMeasure E` ist vollständig". Das lässt sich so nicht hinschreiben.
`LevyProkhorov` ist eine einfeldrige **Struktur** über der Maßklasse
(`Measure/LevyProkhorovMetric.lean:259`), und die Abstandsinstanzen sitzen auf
ihr: `LevyProkhorov.instPseudoMetricSpaceProbabilityMeasure` (`:311`) und, unter
`[BorelSpace E]`, `LevyProkhorov.levyProkhorovDist_metricSpace_probabilityMeasure`
(`:336`). `ProbabilityMeasure E` selbst trägt die Topologie der
Verteilungskonvergenz und **keine Uniformität**, also ist
`CompleteSpace (ProbabilityMeasure E)` keine Aussage, sondern ein Typfehler. Der
Meilenstein führt jetzt vier Punkte statt drei:
`ProbabilityMeasure.separableSpace`, `ProbabilityMeasure.secondCountableTopology`,
`LevyProkhorov.completeSpace_probabilityMeasure` — auf dem Synonym — und
`ProbabilityMeasure.isCompletelyMetrizableSpace`, das über
`LevyProkhorov.probabilityMeasureHomeomorph` (`:676`),
`Homeomorph.isClosedEmbedding` (`Topology/Homeomorph/Defs.lean:297`) und
`Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`
(`Topology/Metrizable/CompletelyMetrizable.lean:249`) zurückwandert. Dass
`polishSpace` danach nichts mehr kostet, ist ebenfalls am Quelltext belegt:
`PolishSpace` ist definiert als `SecondCountableTopology` zusammen mit
`IsCompletelyMetrizableSpace` (`Topology/MetricSpace/Polish.lean:62`), und die
Instanz bei `:65` baut es aus Separabilität und vollständiger Metrisierbarkeit.
Dieselbe Naht trifft die Zweitabzählbarkeit:
`UniformSpace.secondCountable_of_separable`
(`Topology/UniformSpace/Cauchy.lean:932`) verlangt einen uniformen Raum mit
abzählbar erzeugter Uniformität und greift auf `ProbabilityMeasure E` nicht; der
Schluss läuft über das Synonym und `Homeomorph.secondCountableTopology`
(`Topology/Homeomorph/Lemmas.lean:37`) zurück. Die Regel, die dabei herauskommt
und im Meilenstein jetzt vorneweg steht: jede **uniforme** Aussage über den Raum
der Gesetze wird auf `LevyProkhorov (ProbabilityMeasure E)` formuliert, jede
**topologische** auf `ProbabilityMeasure E`.

**Zweitens: der angegebene Beweisweg der Vollständigkeit war zirkulär.** Er
lautete, eine Cauchyfolge sei straff „durch das Überdeckungsargument, das
`MeasureTheory.isTightMeasureSet_of_isCompact_closure` für eine Menge mit
kompaktem Abschluss führt". Dieser Satz ist die **Umkehrung**: er setzt den
kompakten Abschluss voraus, den der nächste Schritt erst herstellen soll. Was
der Schritt wirklich braucht, ist Ulams Satz, und den hat Mathlib:
`MeasureTheory.isTightMeasureSet_singleton` (`Measure/Tight.lean:99`, unter
`[IsCompletelyPseudoMetrizableSpace] [SecondCountableTopology] [BorelSpace]`, auf
master zeichengleich und nicht `deprecated`), dazu
`MeasureTheory.IsTightMeasureSet.union` (`Tight.lean:119`) für den endlichen
Kopf. Der Meilenstein sagt jetzt den vollständigen Weg: `N` aus der
Cauchybedingung, Ulam plus `union` für `μ 0, …, μ N`, deren Kompaktum durch
endlich viele `r/2`-Bälle überdecken, und für `n > N` liefert die
Lévy--Prokhorov-Ungleichung dieselbe Schranke, weil die `r/2`-Verdickung von
`⋃ x ∈ F, ball x (r/2)` in `⋃ x ∈ F, ball x r` liegt.

**Und daraus fällt eine eigene, an Mathlib gerichtete Aussage.** Der Beweis von
`isTightMeasureSet_of_isCompact_closure` zerfällt sauber in zwei Teile, und
Mathlib hat den einen nur inline. Die Zeilen 640--704 von
`Measure/Prokhorov.lean` bauen das Kompaktum
`⋂ m, ⋃ i ≤ k m, closure (ball (D i) (u m))`, summieren die Fehler über `m` und
schließen mit `TotallyBounded.isCompact_of_isClosed`; die Kompaktheitshypothese
geht dort **an genau einer Stelle** ein, nämlich im Schritt `byclaim`, der
`exists_measure_iUnion_gt_of_isCompact_closure` (`:573`) aufruft. Herausgezogen
ist das Übrige die Aussage: auf einem vollständigen, zweitabzählbaren
metrischen Raum ist eine Menge von Wahrscheinlichkeitsmaßen straff, sobald sie
**gleichmäßig totalbeschränkt im Maß** ist — zu jedem `ε > 0` und `r > 0` ein
endliches `F` mit `μ (⋃ x ∈ F, ball x r)ᶜ ≤ ε` für alle `μ`. Sie steht jetzt als
`MeasureTheory.isTightMeasureSet_of_forall_exists_finite_iUnion_ball` im
Meilenstein, der Mathlib-Satz wird ihr Korollar, und die Vollständigkeit oben
ist die zweite Anwendung.

**Ein dritter Punkt, der beim Nachlesen der Skorokhod-Darstellung anfiel.** Der
Meilenstein sagte, die Konstruktion benutze „eine abzählbare Partition von `E`
in Mengen kleinen Durchmessers, deren Ränder `μ`-null sind", ohne ein Werkzeug zu
nennen. Mathlibs Partition
`MeasureTheory.SeparableSpace.exists_measurable_partition_diam_le`
(`LevyProkhorovMetric.lean:540`) ist aus Bällen **eines festen Radius** gebaut
und sagt über Ränder nichts; die Nullränder sind der eigentliche Inhalt des
Schritts. Sie stehen jetzt als eigener Punkt
`exists_measurable_partition_diam_le_null_frontier`, mit den drei Werkzeugen, die
Mathlib dafür hat: `MeasureTheory.exists_null_frontier_thickening`
(`Measure/Portmanteau.lean:401`, das über
`MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion`,
`Measure/Typeclasses/SFinite.lean:305`, läuft) für die Radienwahl,
`Metric.thickening_singleton` (`Topology/MetricSpace/Thickening.lean:157`), um
eine Punktverdickung als Ball zu lesen, und `frontier_inter_subset`,
`frontier_union_subset`, `frontier_compl` (`Topology/Closure.lean:537,544,528`),
damit `disjointed` die Nullränder nicht zerstört.

**Nichts davon steht auf master.** `SeparableSpace (ProbabilityMeasure`,
`CompleteSpace (LevyProkhorov`, `IsCompletelyMetrizableSpace (ProbabilityMeasure`
und `PolishSpace (ProbabilityMeasure` haben je null Treffer
(`gh api search/code`, mit `instMetrizableSpaceProbabilityMeasure`,
`isTightMeasureSet_singleton` und
`exists_measure_iUnion_gt_of_isCompact_closure` als Gegenprobe, dass die Suche
greift: 1, 2 und 1 Treffer). Ebenso null im Arbeitsbranch des Nutzers und in
v4.33.1.

**Ein Nebenbefund in `SkorokhodSpace` Meilenstein 8, eingetragen.** Der Punkt
`tendsto_of_isCompact_closure_of_tendsto_finiteDimensional` sagte, der Beweis
benutze „eine konvergente Teilfolge und sonst nichts". Das stimmt, verschweigt
aber, woher die Teilfolge kommt: aus einem kompakten Abschluss folgt
Folgenkompaktheit erst über die Metrisierbarkeit von
`ProbabilityMeasure (D ι E)`, also über `instMetrizableSpaceProbabilityMeasure`
angewandt auf `SeparableSpace (D ι E)` aus Meilenstein 5. Der Punkt nennt das
jetzt. Für Stufe (A) ist es unschädlich — `SeparableSpace (D ι E)` verlangt nach
Meilenstein 5 nur eine abzählbare dichte Teilmenge von `E` —, aber es ist die
zweite Stelle desselben Punktes, an der die Separabilität arbeitet, und sie war
ungenannt.

**Bei der Gelegenheit die Liste „What Mathlib already has" derselben Roadmap
nachgeprüft**, weil der Lauf ohnehin in der Datei war. Alle elf genannten
Deklarationen existieren in v4.33.1 unter dem angegebenen Namen und in der
angegebenen Datei, keine ist `deprecated`:
`ext_of_forall_integral_eq_of_IsFiniteMeasure` und
`ext_of_forall_lintegral_eq_of_IsFiniteMeasure`
(`Measure/HasOuterApproxClosed.lean:269,256`),
`ext_of_forall_mem_subalgebra_integral_eq_of_polish` und
`…_of_pseudoEMetric_complete_countable` (`Measure/FiniteMeasureExt.lean:72,36`),
`FiniteMeasure.tendsto_iff_forall_integral_tendsto`,
`tendsto_of_forall_integral_tendsto`, `tendsto_iff_forall_integral_rclike_tendsto`,
`tendsto_map_of_tendsto_of_continuous`, `continuous_map`
(`Measure/FiniteMeasure.lean:726,701,748,957,972`, die
`ProbabilityMeasure`-Fassungen bei `Measure/ProbabilityMeasure.lean:346,354,639,654`),
`ProbabilityMeasure.tendsto_iff_tendsto_charFun`
(`Measure/LevyConvergence.lean:215`, auf master drei Treffer, davon einer in
`docs/1000.yaml`) und `uniformIntegrable_iff`
(`Function/UniformIntegrable.lean:878`). Das ist keine Erledigung von
Rückstaupunkt 3 — der verlangt alle vier Roadmaps gegen master — aber es nimmt
ihm eine Roadmap ab.

**Was nicht geschehen ist.** Kein Lean wurde übersetzt: der Worktree hat kein
`.lake`, und Regel 3 verbietet den Wechsel in den Hauptcheckout. Die fünf neuen
Stümpfe in `WeakConvergence/Suggested.lean` sind Prototypen wie die übrigen und
tragen `sorry`. Rückstaupunkt 4 bleibt deshalb offen; was dieser Lauf ihm
genommen hat, ist der Grund, aus dem er in seiner alten Fassung nicht
ausführbar war.

**Als Nächstes zu formalisieren:
`MeasureTheory.isTightMeasureSet_of_forall_exists_finite_iUnion_ball`**
(`WeakConvergence` Meilenstein 3). Es ruht auf nichts als
`TopologicalSpace.exists_dense_seq`, `measure_iUnion_le` und
`TotallyBounded.isCompact_of_isClosed` — kein Prozess, kein Pfadraum, keine Uhr,
und aus der ganzen Roadmap keine Vorbedingung. Es ist jetzt dran, weil es der
einzige Punkt dieses Projekts ist, dessen **Beweis in Mathlib schon steht**: die
Zeilen 640--704 von `Measure/Prokhorov.lean` sind er, wörtlich, und die Arbeit
besteht darin, den einen Aufruf von
`exists_measure_iUnion_gt_of_isCompact_closure` durch die Hypothese zu ersetzen.
Das ist zugleich ein Mathlib-PR, der für sich steht — der vorhandene Satz
`isTightMeasureSet_of_isCompact_closure` wird sein Korollar, ohne dass eine Zeile
seines Beweises verlorengeht —, und die Vorbedingung von
`LevyProkhorov.completeSpace_probabilityMeasure`, also der Aussage, ohne die
keines der Teilfolgenargumente des Konvergenzteils steht. Gegenüber den älteren
Vorschlägen: `Clock.interval_union` bleibt der erste der Task-23-Linie; in der
Konvergenzlinie tritt dieses vor `ProbabilityMeasure.separableSpace`, das der
zweite Lauf des 2026-08-31 vorgeschlagen hat, denn jenes verlangt eine
Konstruktion und dieses nur eine Umstellung.

### 2026-08-31, vierter Lauf — Rückstau 2: die Idealreduktion des Halbordnungsfalls

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da. Rückstaupunkt 1
bleibt stehen (Manuskript, Regel 2). Der Lauf ging an **Punkt 2**, den offenen
Fall unvergleichbarer Atome aus Task 23, den der dritte Lauf des Tages mit „ohne
neuen Hebel" übergangen hatte. Ein Hebel hat sich gefunden; der Beweis ist
damit nicht fertig, aber der Fall ist auf **eine einzige Aussage** eingeschränkt,
und der Massenbereich, in dem sie zu zeigen ist, ist vermessen. Am Manuskript
wurde nichts geändert, an den Roadmaps nichts; geändert sind
`Task23/PROTOKOLL.md`, `Facts/BACKLOG.md` und dieses Inventar, neu sind
`Task23/antisym.py` und `Task23/reduction.py`. Der ausführliche Bericht steht im
PROTOKOLL, Abschnitt „Der Halbordnungsfall, 2026-08-31 (vierter Lauf)"; hier das
Wesentliche.

**Die Rechnung läuft in der `κ`-Gestalt.** Der dritte Lauf des 2026-08-30 hatte
`Φ` eliminiert und `(**)` in einen symmetrischen und einen antisymmetrischen
Teil zerlegt, von denen nur der zweite den Defekt trägt. `antisym.py` (neu)
stellt das System allein in `κ` auf — `n(n-1)/2` Unbekannte statt `n²` — und ist
gegen `posetsearch.py` geeicht: Ketten fallen nie, der Diamant mit
`m_a = 1, m_b = -1` fällt, nichtnegative Massen fallen nie (4864 + 53217 Fälle,
exakte Bruchrechnung).

**Die Idealreduktion, bewiesen.** Enthält eine Teilmenge `I ⊆ 𝕋` das kleinste
Element und ist sie abwärtsabgeschlossen, so ist `𝕋_{<s} ⊆ I` für `s ∈ I`, also
stimmen `Ψ` und `δ` auf `I` mit denen auf `𝕋` überein, und die Relationen an
Paaren aus `I` sind eine Teilmenge derer auf `𝕋`. Eine Lösung auf `𝕋`
schränkt sich also ein. Folglich: **`δ(t) = 0` ist auf `𝕋` erzwungen, sobald es
auf `𝕋_{≤t}` erzwungen ist**, und `𝕋_{≤t}` hat kleinstes *und* größtes Element.
Die Induktion über `|𝕋|` liefert damit `δ(s) = 0` für jedes `s`, dessen
Hauptideal echt kleiner ist als `𝕋` — also für alles außer einem größten
Element. Hat `𝕋` zwei maximale Elemente, ist gar nichts mehr zu zeigen.
`reduction.py` (neu) prüft die behauptete Richtung an 3513 Paaren `(𝕋,t)` mit
Massen beider Vorzeichen nach: null Abweichungen. Verlustfrei ist die Reduktion
nicht — in vier dieser Fälle ist `δ(t)` auf `𝕋_{≤t}` frei und auf `𝕋` erzwungen;
für nichtnegative Massen kostet das nichts.

**Und Nullmassen fallen weg.** Ist `m_c = 0` für ein `c ≠ 0`, so ändert das
Streichen von `c` kein `Ψ(s,t)`, lässt `0` kleinstes Element und nimmt dem
System nur Relationen. Alle Massen außer `m_0` dürfen also als strikt positiv
angenommen werden.

**Der Restdefekt hat eine scharfe Gestalt.** Auf einer Halbordnung mit
kleinstem Element `0` und größtem `z` ist nach dem Obigen `δ` auf
`W = 𝕋 ∖ {z}` null, und die Relationen an `(0,a)` und `(0,z)` geben
`Ψ(a,0) = 0` für `a ∈ W` und `Ψ(z,0) = δ(z)`. Mit `g(c) := m_c κ(c,0)` heißt
das: `g` summiert sich über **jedes** Hauptideal `𝕋_{<a}`, `a ∈ W`, zu null, und
`δ(z)` ist die Summe über das eine verbleibende Ideal `W`. Da die Vereinigung
der `𝕋_{<a}` gerade `W` ohne die maximalen Elemente von `W` ist, sitzt der
Defekt genau auf der Antikette der maximalen Elemente von `𝕋_{<z}` — dieselbe
Stelle wie beim dritten Lauf, jetzt aber ohne `Φ`, ohne `γ` und ohne das obere
Ende. Auch das ist nachgerechnet (243 + 608 beschränkte Halbordnungen, keine
Abweichung).

**Was den Rest schließt, und wo es gilt.** Aus `Ψ(a,z) = 0` für alle `a < z`
folgt (R) in vier Zeilen: die mit `m_a` gewichtete Summe der Relationen an
`(a,z)` lässt `∑ m_a Ψ(z,a) = ∑_{a,b<z} m_a m_b κ(b,a) = 0` verschwinden und
gibt `q(𝕋_{<z}) δ(z) = 0`; bei `q(𝕋_{<z}) = 0` sind unter `m ≥ 0` alle Massen
unter `z` null und `Ψ(z,·)` verschwindet ohnehin. Das ist genau das
`q(𝕋_{<s})` des Suchbefunds von `sharp.py` vom 2026-08-30. Die zugehörige
Vermutung ist **(C4)** „`Ψ(a,x) = 0`, sobald `a < x`", und ihre Reichweite ist
jetzt vermessen: bei nichtnegativen Massen ist sie **falsch** (864 Ausfälle auf
fünf Punkten, kleinster Zeuge `𝕋_{<1} = {0,2,3,4}` mit `m = (0,0,1,0,1)`, wo
`Ψ(3,1)` frei bleibt), bei strikt positiven Massen und ebenso bei `m_0 = 0` und
sonst positiven Massen **ohne einen einzigen Ausfall** (je 1539 + 7008 Fälle).
Sie hält also genau in dem Bereich, den die Streichung der Nullmassen
übriglässt. Als Sackgasse mit festgehalten: die stärkere Vermutung `Ψ ≡ 0` ist
schon bei positiven Massen falsch, mit einem Gegenbeispiel von Hand auf fünf
Punkten — `Ψ` lebt auf den unvergleichbaren Paaren, und (C4) ist die richtige
Abschwächung.

**Was nicht geschehen ist.** Kein Lean übersetzt (der Worktree hat kein
`.lake`), keine Roadmap geändert, `check.py` nicht gelaufen, weil das Manuskript
nicht angefasst wurde. Die Idealreduktion ist bewusst **nicht** in
`MartingaleProblems` Meilenstein 8 eingetragen: sie ist ein Hilfssatz zu einer
Aussage, die noch nicht bewiesen ist, und ein Meilenstein trägt keine
Gerüste für Ungewisses. Sie steht im PROTOKOLL, bis (R) bewiesen ist.

**Als Nächstes zu formalisieren: `atomGrid_symm`** (`MartingaleProblems`
Meilenstein 8). `M : ℕ`, Massen `m i ≠ 0` für `1 ≤ i ≤ M-1`, und ein
`Φ : ℕ → ℕ → ℝ` mit `m j * (Φ (i+1) j - Φ i j) = m i * (Φ i (j+1) - Φ i j)`;
Konklusion `Φ i j = Φ j i`. Es ruht auf nichts als der Linearität der Relation,
ihrer Invarianz unter Transposition und einer Induktion über den Abstand zur
Diagonale — kein Maß, keine Uhr, `ℕ` als einziger Index, und deshalb nach
`Mathlib/Algebra/Order/` und nicht in den Wahrscheinlichkeitsbaum. Es ist
**jetzt** dran, und der Grund kommt aus diesem Lauf: `duality_of_atomic` besteht
aus dem Kettenfall und dem Halbordnungsfall, der Kettenfall ist seit dem
2026-08-30 vollständig bewiesen und `atomGrid_symm` ist sein ganzer Inhalt,
während der Halbordnungsfall nach dem heutigen Stand auf einer Vermutung sitzt,
die noch keinen Beweis hat. Auf die Halbordnung zu warten hieße, den fertigen
Teil liegen zu lassen; und `atomGrid_symm` ist von ihr nicht berührt, weil die
Idealreduktion oben das obere Ende und nicht das Gitter betrifft. Gegenüber den
älteren Vorschlägen: `isTightMeasureSet_of_forall_exists_finite_iUnion_ball`
(dritter Lauf) bleibt der erste der Konvergenzlinie; in der Task-23-Linie tritt
`atomGrid_symm` **vor** `Clock.interval_union`, denn jenes verlangt die
Uhrendefinition samt Maßtheorie und dieses nur Arithmetik auf `ℕ`.

### 2026-08-31, fünfter Lauf — Rückstau 2: die flache Spitze ist bewiesen

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da, Rückstaupunkt 1
bleibt beim Nutzer (Manuskript, Regel 2). Der Lauf ging wieder an **Punkt 2**,
den Fall unvergleichbarer Atome, und zwar an den Auftrag, den der vierte Lauf
hinterlassen hatte: „(C4$^+$) beweisen oder widerlegen". Herausgekommen ist
beides und keines von beidem — der **Hebel** ist widerlegt, ein **Stück des
Falles** ist bewiesen. Am Manuskript wurde nichts geändert, an den Roadmaps
nichts; geändert sind `Task23/PROTOKOLL.md`, `Facts/BACKLOG.md` und dieses
Inventar, neu sind `Task23/c5.py`, `Task23/flat.py` und
`Task23/certificate.py`. Der ausführliche Bericht steht im PROTOKOLL,
Abschnitt „Der Halbordnungsfall, 2026-08-31 (fünfter Lauf)"; hier das
Wesentliche.

**(C5) ist falsch.** Der vierte Lauf hatte (C4$^+$) — „$\Psi(a,x)=0$, sobald
$a<x$" — als das benannt, was den Halbordnungsfall schließt. Der
naheliegende Weg dorthin ist die termweise Fassung: in
$\Psi(a,x)=\sum_{c<a}m_c\kappa(c,x)$ hat jeder Summand ein $c$ mit $c<a<x$,
also genügte „$m_c\kappa(c,x)=0$, sobald es ein $b$ mit $c<b<x$ gibt" (C5).
Diese Aussage ist **falsch**, und zwar schon bei lauter Massen $1$: auf
$\T=\{0,3,4,2,1\}$ mit $0<3,4<2<1$ bleibt $\kappa(3,1)$ frei, obwohl
$3<2<1$; erzwungen ist allein die Kombination
$m_3\kappa(3,1)+m_4\kappa(4,1)$, die in $\Psi(2,1)$ steht. (C4$^+$) selbst hält
dort und überall: $0$ Ausfälle unter $2052+10512$ Konfigurationen mit strikt
positiven Massen und $m_0$ auch $0$ (`c5.py`, exakte Bruchrechnung). Das ist
kein Nebenbefund, sondern eine Weichenstellung: der Beweis muss über $\Psi$
laufen, nicht über die einzelnen $\kappa$.

**Bewiesen: die flache Spitze, und schärfer als erwartet.** Liegt unter $t$ nur
eine Antikette von Atomen — $\T_{<c}=\{0\}$ für jedes $c$ mit $0<c<t$ —, so ist
$\delta(t)=0$ und $\Psi(a,t)=0$ für jedes $a<t$. Gebraucht wird davon **nicht**
die Positivität der Massen, sondern allein $q(M)\neq0$ für
$M=\T_{<t}\setminus\{0\}$: die Relationen an $(c,t)$, mit $m_c$ gewichtet und
über $c\in M$ summiert, geben durch Antisymmetrie $q(M)R=0$ für
$R=\sum_{c\in M}m_c\kappa(c,t)$, und die Relationen an $(0,c)$ und $(0,t)$
erledigen den $m_0$-Anteil. Vier Schritte, kein Grenzübergang, keine Vermutung.
Der Satz enthält den **Diamanten** als den Fall $|M|=2$ — den kleinsten Fall
also, dessen Begründung im Manuskript der dritte Lauf des 2026-08-30 als falsch
nachgewiesen hat und der seither ohne Beweis dasteht —, und er erklärt zugleich
das dortige Gegenbeispiel: $m_a=1$, $m_b=-1$ ist genau $q(M)=0$. Weglassen
lässt sich die Hypothese nicht: bei $q(M)=0$ fällt die Dualität an $60$ von
$2625$ geprüften Stellen. Für eine echte Uhr ist sie automatisch, denn $q$ ist
ein Maß. Nachgerechnet mit `flat.py` über alle Halbordnungen der Höhe $\le2$ auf
bis zu **sechs** Punkten ($1053+21141+80736$ Konfigurationen) und in der
scharfen Fassung mit Massen beider Vorzeichen ($10500+5071$ Stellen): kein
Ausfall.

**Ein Werkzeug, das der nächste Lauf erbt.** `certificate.py` rechnet mit
symbolischen Massen die Linearkombination der Relationen aus, die ein
verschwindendes Funktional *ist* — nicht nur, dass es verschwindet. Am
Diamanten steht dort der Faktor $1/(m_1+m_2)$, an dem die Positivität sichtbar
wird; bei „drei Atomen unter der Spitze" kommt genau der Beweis oben heraus.
Aus einem gerechneten Fall ein Argument abzulesen, ist damit keine Ratearbeit
mehr.

**Offen geblieben.** (R) für ein $t$, unter dem eine Kette $0<a<b<t$ liegt.
Warum der Beweis dort anders aussehen muss, ist jetzt benannt: Schritt 2 der
flachen Rechnung benutzt, dass $\Psi(c,t)$ für **alle** $c\in M$ dieselbe Größe
$m_0\kappa(0,t)$ ist; bei zwei Stockwerken ist das nicht mehr so. Nicht
geschehen ist zweierlei, und beides mit Absicht. Kein Lean übersetzt — der
Worktree hat kein `.lake`. Und nichts in eine Roadmap eingetragen: die flache
Spitze ist ein Spezialfall von `duality_of_atomic`, und sobald der
Halbordnungsfall ganz steht, wäre der Punkt Gerüst. Was dem **Nutzer** gehört,
ist die Frage ans Manuskript: `rem:atomsnotchange` führt die Zeile „purely
atomic, atoms incomparable" als „verified exhaustively up to five points; not
proved", und das stimmt seit heute nicht mehr für die flache Spitze samt
Diamant. Eine Proposition dafür ist im PROTOKOLL fertig formuliert und
bewiesen; sie ins Manuskript zu setzen, ist ein eigener Lauf wert, weil danach
`check.py` laufen muss.

**Als Nächstes zu formalisieren: weiterhin `atomGrid_symm`**
(`MartingaleProblems` Meilenstein 8), aus den Gründen des vierten Laufs — der
Kettenfall ist vollständig bewiesen, `atomGrid_symm` ist sein ganzer Inhalt, und
es ruht auf nichts als Arithmetik auf `ℕ`. Der heutige Satz ändert daran
nichts, sondern bestätigt die Reihenfolge: er ist ein zweiter, unabhängiger
Baustein desselben Meilensteins (`duality_of_atomic`), aber er ruht auf der
Idealreduktion, die ihrerseits die Uhrendefinition und `Clock.interval_union`
verlangt, und ist damit der spätere von beiden. Wer ihn dennoch zuerst will,
formalisiere ihn in der reinen Gestalt, in der er hier bewiesen ist —
`Finset`-Halbordnung, Massen in `ℝ`, `κ` antisymmetrisch, keine Maßtheorie —,
denn in dieser Gestalt ruht er auf ebensowenig wie `atomGrid_symm`.

### 2026-08-31, sechster Lauf — Rückstau 1: der Halbordnungsfall ist bewiesen

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da. Der Lauf ging an
den ersten Punkt des Rückstaus, den Fall unvergleichbarer Atome aus Task 23, an
dem die Läufe vier und fünf gearbeitet hatten. Er ist **bewiesen**, und zwar
nicht in dem Zuschnitt, in dem er offen stand, sondern ganz: beliebige endliche
Halbordnung, nichtnegative Massen, keine weitere Bedingung. Geändert sind
`Task23/PROTOKOLL.md`, `TauCeti/MartingaleProblems/README.md`,
`Facts/BACKLOG.md` und dieses Inventar; neu sind `Task23/selfadjoint.py` und
`Task23/stress.py`. Am
Manuskript wurde nichts geändert — die Eintragung gehört an den Anfang eines
Laufs, weil danach `check.py` laufen muss, und steht deshalb als Rückstaupunkt 1.

**Der Satz.** Ist $\T$ eine endliche Halbordnung, $m:\T\to[0,\infty)$ und
$\kappa$ antisymmetrisch mit $(\diamondsuit)$, so ist $\delta\equiv0$. Für eine
Uhr ist $m\ge0$ automatisch, denn $q$ ist ein Maß; der Fall ist damit
abgeschlossen. Ein kleinstes Element wird nicht gebraucht, ein größtes nicht,
eine Kette nicht, eine Antikette nicht, die Idealreduktion nicht.

**Der Beweis wechselt die Sprache.** Fünf Läufe haben nach einer Induktion über
die Halbordnung gesucht — von unten, von oben, über Ideale, über die Antikette
der maximalen Elemente. Der Beweis, der trägt, induziert über gar nichts. Mit
$V_{s,a}=[a<s]m_a$ und $K=(\kappa(a,b))$ ist $\Psi=VK$, und $(\diamondsuit)$
heißt $VK+(VK)^{\mathsf T}=\delta\mathbb 1^{\mathsf T}+\mathbb 1\delta^{\mathsf T}$.
Daraus zwei Zeilen: für jedes symmetrische $T$ ist
$\operatorname{tr}(TVK)=\langle\delta,T\mathbb 1\rangle$, und ist überdies $TV$
symmetrisch, so ist die Spur null, weil $K$ antisymmetrisch ist. Alles hängt
also daran, ob $e_t$ im Bild
$\mathcal L=\{T\mathbb 1: T=T^{\mathsf T},\,TV=V^{\mathsf T}T\}$ liegt — und
$\mathcal L$ ist ganz $\R^\T$, sobald $\mathbb 1$ im $\R[x]$-Modul $(\R^\T,V)$
maximale Ordnung hat. Genau das leistet die Nichtnegativität, in einer Zeile:
$V$ hat nichtnegative Einträge, $V^k\mathbb 1$ ist der Zeilensummenvektor von
$V^k$, und eine nichtnegative Matrix mit lauter Zeilensummen null ist null; also
ist $V^k\mathbb 1=0$ genau dann, wenn $V^k=0$. Das ist die **einzige** Stelle,
an der $m\ge0$ vorkommt, und der Diamant mit $m_a=1$, $m_b=-1$ zeigt, dass sie
nicht wegfällt.

**Verifiziert, nicht nur geglaubt.** `selfadjoint.py` (neu) prüft in exakter
Bruchrechnung über **alle** Halbordnungen — auch ohne kleinstes Element — auf
bis zu fünf Punkten vier Dinge: das Kriterium als **Äquivalenz** („$\delta(t)$
erzwungen" gegen „$e_t\in\mathcal L$", auch bei gemischten Vorzeichen, wo beide
Seiten fallen dürfen; $228\,000$ Stellen), das Lemma über die Zeilensummen
($6\,259\,626$ Potenzen), die explizite Konstruktion von $T$ ($265\,128$
Konstruktionen) und den Satz selbst ($89\,440$ Fälle) — kein Ausfall und keine
Abweichung. Ende zu Ende, also im vollen System in $(\Phi,\gamma)$ statt in der
$\kappa$-Gestalt, mit `posetsearch.clock_sweep` gegengeprüft ($1539+7008$ Fälle,
kein Ausfall), und jenseits der Aufzählung mit `stress.py` (neu) an $120$
zufälligen Halbordnungen auf sechs bis acht Punkten. Dass der erste Punkt eine
Äquivalenz prüft und nicht nur die
Hinrichtung, ist der schärfste Teil: er bestätigt, dass $\mathcal L$ die Lage
vollständig beschreibt, und erklärt damit auch die bekannten Gegenbeispiele.

**In die Roadmap eingetragen, und warum jetzt.** Der fünfte Lauf hatte bewusst
nichts eingetragen, weil ein Meilenstein kein Gerüst für Ungewisses trägt. Jetzt
ist es gewiss, und `MartingaleProblems` Meilenstein 8 führt fünf neue Punkte:
die vier Matrixaussagen
`Matrix.trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`,
`Matrix.trace_mul_eq_dotProduct_diag_of_isSymm`,
`Matrix.mulVec_one_eq_zero_iff_of_nonneg` und
`Matrix.exists_isSymm_mulVec_one_eq_single`, sowie
`dualityDefect_eq_zero_of_nonneg` als deren Zusammenfassung auf einer endlichen
Halbordnung. `Clock.atomChain` bekommt in `Clock.atomPoset` ein Gegenstück ohne
Vergleichbarkeitshypothese, und `duality_of_atomic` **verliert seine
Vergleichbarkeitshypothese** — das ist nach der stehenden Regel eine Korrektur,
nicht eine Erweiterung: die Roadmap verlangte mehr, als der Satz braucht.
`atomGrid_symm` bleibt stehen und behält seinen Rang, denn auf der Kette gilt
die stärkere Konklusion $\Phi(s,t)=\Phi(t,s)$ und sie gilt für Massen beider
Vorzeichen, wo `dualityDefect_eq_zero_of_nonneg` $m\ge0$ verlangt. Dass die
starke Symmetrie ein Kettenphänomen ist und an unvergleichbaren Paaren ausfällt,
steht jetzt ausdrücklich dort; es war seit `poset.py` (2026-08-30) bekannt, aber
nicht in der Roadmap vermerkt.

**Offen geblieben.** Von Task 23 zwei Punkte, beide unberührt: ordnungsdichte
Atommengen und Stufe 3, die gemischte Uhr. Beide stehen jetzt als Rückstaupunkt
2. Nicht geschehen und mit Absicht: kein Lean übersetzt (der Worktree hat kein
`.lake`), das Manuskript nicht angefasst, `check.py` deshalb nicht gelaufen.

**Als Nächstes zu formalisieren:
`Matrix.trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`** — für `A.IsSymm` und
`Bᵀ = -B` ist `(A * B).trace = 0`. Es ruht auf `Matrix.IsSymm`
(`LinearAlgebra/Matrix/Symmetric.lean:35`), `Matrix.trace_transpose`
(`Trace.lean:73`) und `Matrix.trace_mul_comm` (`Trace.lean:158`), alle drei
heute am Quelltext von v4.33.1 geprüft und nicht `deprecated`; ein Prädikat für
`Bᵀ = -B` allein hat Mathlib nicht, `Matrix.IsSkewAdjoint`
(`SesquilinearForm.lean:562`) ist relativ zu einer Form `J`. Es ist jetzt dran,
weil es das kleinste Stück des heutigen Beweises ist, weil es der einzige der
fünf neuen Punkte ist, der auf **nichts** aus diesem Projekt ruht, und weil es
allein in Mathlib gehört: eine Aussage über Spuren, drei Zeilen lang, ohne Uhr,
ohne Maß und ohne Halbordnung. Gegenüber den älteren Vorschlägen: `atomGrid_symm`
bleibt der kleinste Einstieg der **Kettenlinie** und
`isTightMeasureSet_of_forall_exists_finite_iUnion_ball` der erste der
Konvergenzlinie; in der Task-23-Linie tritt die Spuraussage vor beide, denn sie
hat keine Vorbedingung überhaupt.

### 2026-08-31, siebter Lauf — Rückstau 1: der Halbordnungssatz steht im Manuskript

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da. Der Lauf ging an
den ersten Punkt des Rückstaus, der ausdrücklich eine Aufgabe für den **Anfang**
eines Laufs war, weil danach `check.py` laufen muss. Er ist erledigt, und bei
der Gelegenheit ist eine Lücke aufgefallen, die sechs Läufe übersehen hatten.
Geändert sind `MartingaleProblem.tex`, `TauCeti/MartingaleProblems/README.md`,
`Task23/PROTOKOLL.md`, `Facts/BACKLOG.md` und dieses Inventar; neu ist
`Task23/oconvention.py`.

**Was ins Manuskript kam.** Vier Stücke, hinter `rem:atomicdual`:
`lem:selfadjoint` (ist $V$ nichtnegativ und nilpotent, so gibt es zu jedem $t$
ein symmetrisches $T$ mit $TV=V^{\mathsf T}T$ und $T\mathbb 1=e_t$, mit dem
Dreischritt Zeilensummen / duale Kette / explizite Formel), `prop:atomicposet`
(rein atomare Uhr, endlich viele Atome unter $t^*$, **keine** Bedingung an ihre
Lage zueinander, $\Phi(t^*,0)=\Phi(0,t^*)$), `rem:atomicposet` (was die beiden
atomaren Sätze je geben, und warum der Diamant mit $m_a=1$, $m_b=-1$ zeigt, dass
$m\ge0$ nicht wegfällt), sowie die Statuszeile, die Bündeltabelle und fünf
Zitate der Kettenhypothese. Die beiden Propositionen sind **nicht** geschachtelt
und stehen deshalb nebeneinander: die Kette erlaubt Massen beider Vorzeichen und
gibt die stärkere Symmetrie $\Phi(s,t)=\Phi(t,s)$, die Halbordnung verlangt
$m\ge0$ und gibt nur den Defekt. Für eine Uhr enthält die zweite die erste.
Der Beweis von `prop:atomicposet` führt die Reduktion aus, die im PROTOKOLL nur
behauptet war, einschließlich der Nachrechnung, dass $a\in\T_{<s}$ auf einer
**Präordnung** transitiv und irreflexiv ist — darauf ruht die Nilpotenz.
`selfadjoint.py` ist vor dem Eintrag noch einmal gelaufen (alle vier Punkte,
kein Ausfall), danach meldet `python3 check.py` `clean`: 126 Seiten, keine
undefinierten Referenzen, größte Überlänge 7.7pt wie im Ausgangszustand.

**Der Befund: $\iota=\mathrm o$ ist nicht mitbewiesen.** Die Konvention geht an
genau einer Stelle ein, aber an der tragenden. Unter $\iota=\mathrm p$ ist
$[0,s)=\T_{<s}$ und $V_{s,a}=[a\prec s]m_a$ strikt dreieckig; unter
$\iota=\mathrm o$ ist $(0,s]=\T_{\le s}\setminus\T_{\le0}$, also $V_{s,s}=m_s$,
und $V$ ist nicht nilpotent — `lem:selfadjoint` greift nicht. Auf einer Kette
repariert `prop:atomicdual` das durch Spiegelung des Gitters; eine Halbordnung
hat kein größtes Element und bietet keine Spiegelung. Der Satz „die o-Konvention
ist die p-Konvention für die umgekehrte Ordnung" ist damit für eine Halbordnung
**falsch**. Er stand so in `MartingaleProblems` bei `duality_of_atomic` („in
both conventions … the hypotheses are unchanged"); die Roadmapzeile sagt jetzt,
was gilt, und nennt die Matrix, an der es scheitert. Das ist nach der stehenden
Regel eine Korrektur: die Roadmap behauptete mehr, als bewiesen ist.

**Nachgerechnet, nicht behauptet.** `oconvention.py` (neu) baut dasselbe volle
System in $(\Phi,\gamma)$ wie `posetsearch`, nur mit $(0,s]$ statt $[0,s)$:
alle Halbordnungen mit kleinstem Element auf bis zu fünf Punkten,
nichtnegative Massen, $81+1539+7008$ Fälle, **kein Ausfall**. Die o-Fassung ist
also vermutlich richtig; es fehlt der Beweis, nicht die Evidenz, und sie steht
als einzige „verified, not proved"-Zeile der Statustabelle. Der erste Anlauf des
Skripts hatte einen Fehler — es ließ $0$ im Intervall $(0,s]$ stehen —; die
Zahlen oben stammen aus dem berichtigten Lauf.

**Offen geblieben.** Von Task 23 dieselben zwei Punkte wie zuvor,
ordnungsdichte Atommengen und die gemischte Uhr, plus der neue: die
o-Konvention. Nicht geschehen und mit Absicht: kein Lean übersetzt (der Worktree
hat kein `.lake`).

**Als Nächstes zu formalisieren:
`Matrix.trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`** — für `A.IsSymm` und
`Bᵀ = -B` ist `(A * B).trace = 0`. Der Vorschlag des sechsten Laufs bleibt
stehen und wird durch diesen Lauf **bestätigt und wichtiger**, nicht ersetzt:
`oconvention.criterion_o` hat gezeigt, dass
$\mathcal L=\{T\mathbb 1: T=T^{\mathsf T},\,TV=V^{\mathsf T}T\}$ die erzwungenen
Stellen auch unter $\iota=\mathrm o$ **vollständig** beschreibt — beide
Abweichungsrichtungen null, über alle Halbordnungen auf drei und vier Punkten
mit Massen aus $\{0,1,2\}$, $243+6156$ Stellen. Der Spurteil des Beweises ist
damit konventionsfrei belegt, und diese drei Zeilen Spuralgebra tragen künftig
**beide** Konventionen statt nur einer. Sie ruhen auf `Matrix.IsSymm`
(`LinearAlgebra/Matrix/Symmetric.lean:35`), `Matrix.trace_transpose`
(`Trace.lean:73`) und `Matrix.trace_mul_comm` (`Trace.lean:158`), am Quelltext
von v4.33.1 geprüft und nicht `deprecated`; ein Prädikat für `Bᵀ = -B` allein
hat Mathlib nicht (`Matrix.IsSkewAdjoint`, `SesquilinearForm.lean:562`, ist
relativ zu einer Form `J`), die Bedingung wird also ausgeschrieben.

Und der mathematische Vorschlag daneben, für den Rückstau: **die offene Frage
ist keine über Uhren mehr, sondern eine über Matrizen.** Sei $\prec$ eine
strikte Halbordnung auf endlichem $F$ mit kleinstem Element $0$, sei
$m:F\to[0,\infty)$ mit $m_0=0$ und
$V_{s,a}=[a\prec s\text{ oder }a=s\ne0]\,m_a$. Ist $\mathcal L=\R^F$? Für
nilpotentes $V$ ist die Antwort der Satz des sechsten Laufs (maximale Ordnung
von $\mathbb 1$); hier ist $V=N+D$ mit $N$ nilpotent und
$D=\operatorname{diag}(m)$, die nicht kommutieren, und Zeile wie Spalte $0$
verschwinden. Das ist jetzt dran, weil es die letzte „verified, not proved"-Zeile
des Manuskripts schließt und weil es dieselbe Spuralgebra wiederverwendet.

### 2026-08-31, achter Lauf — Rückstau 1: die o-Konvention ist widerlegt

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da. Der Lauf ging an
den ersten Punkt des Rückstaus, die o-Konvention auf einer Halbordnung, die der
siebte Lauf als „verified, not proved" hinterlassen hatte. Sie ist erledigt, und
zwar in der Richtung, die sieben Läufe für ausgeschlossen hielten: **die Aussage
ist falsch.** Geändert sind `MartingaleProblem.tex`,
`TauCeti/MartingaleProblems/README.md`, `Task23/PROTOKOLL.md`,
`Facts/BACKLOG.md` und dieses Inventar; neu sind `Task23/omaxorder.py`,
`Task23/ocounter.py`, `Task23/odiamond.py`, `Task23/certificate_o.py` und
`Task23/oshape.py`.

**Der Zeuge, auf vier Punkten.** Der Diamant $\T=\{0,a,b,c\}$ mit
$0\prec a\prec c$, $0\prec b\prec c$, $a$ und $b$ unvergleichbar, und den
nichtnegativen Massen $m_a=1$, $m_b=4$, $m_c=2$. Setzt man $\gamma(0,c)=-1$,
$\gamma(a,c)=-2$, $\gamma(b,c)=1$ und $\Phi(0,c)=-2$, $\Phi(a,c)=-4$,
$\Phi(b,c)=2$ und alles Übrige null, so gelten **beide** Zuwachsdarstellungen an
jedem vergleichbaren Paar in der Lesart $\iota=\mathrm o$, und
$\Phi(c,0)-\Phi(0,c)=2$. Dieselbe Uhr trägt unter $\iota=\mathrm p$. Die beiden
Konventionen unterscheiden sich also nicht darin, was man beweisen kann, sondern
darin, was gilt.

**Die Bedingung ist scharf.** Auf den drei Atomen ist $V$ die Dreiecksmatrix mit
den Eigenwerten $m_a,m_b,m_c$; der Linkseigenvektor zu $m_c$ ist
$(m_a/(m_c-m_a),\ m_b/(m_c-m_b),\ 1)$, und er steht senkrecht auf $\mathbb 1$
genau dann, wenn $m_c^2=m_am_b$ — die Masse der Spitze ist das geometrische
Mittel der beiden unvergleichbaren Massen. `odiamond.py` prüft die Vorhersage
gegen zwölf Massenvektoren, in beiden Systemen und beiden Konventionen: sie
trifft genau. Damit ist der Ausfall eine abgeschlossene algebraische Bedingung
und, auf allem Geprüften, eine echte: über alle Halbordnungen mit kleinstem
Element auf vier und fünf Punkten mit zufälligen paarweise verschiedenen Massen
(114+657 Fälle) fällt keine. Die o-Aussage gilt außerhalb einer Nullmenge und
fällt auf ihr.

**Was daran der eigentliche Befund ist.** Nicht der Zeuge, sondern warum ihn
sieben Läufe nicht gesehen haben. `oconvention.sweep_o` lief **erschöpfend** —
über alle Halbordnungen mit kleinstem Element auf bis zu fünf Punkten —, aber
auf fünf Punkten nur über Massen aus $\{0,1\}$ und auf vier über $\{0,1,2\}$, und
keines dieser Gitter kann $m_c^2=m_am_b$ mit $m_a\ne m_b$ treffen: der kleinste
Fall braucht die 4. Ein Gitter, das eine algebraische Ausnahmebedingung gar nicht
enthalten kann, ist keine Evidenz gegen sie, und „erschöpfend geprüft" heißt
nichts, solange nicht dasteht, worüber. Umgekehrt hätte ein Zufallsvektor hier
ebenfalls nichts gefunden, weil die Ausnahme eine Nullmenge ist. Gebraucht wurde
beides.

**Was stehen bleibt und geprüft ist.** Zwei Aussagen tragen weiter, und beide
sind heute erst richtig belegt. Erstens das Kriterium in seiner allgemeinen
Gestalt: $\mathcal L=\{T\mathbb 1: T=T^{\mathsf T},\ TV=V^{\mathsf T}T\}$ ist
ganz $\R^F$ genau dann, wenn $\mathbb 1$ **maximale Ordnung** hat, also
$\mu_{\mathbb 1}=\mu_V$ — das Minimalpolynom des Vektors ist das der Matrix. Für
nilpotentes $V$ ist das $V^{r-1}\mathbb 1\ne0$ und damit `lem:selfadjoint`; das
Kriterium ist also nicht durch die Nilpotenz bedingt, sondern nur unter
$\iota=\mathrm p$ geschenkt. Nachgerechnet über alle Halbordnungen auf bis zu
fünf Punkten mit Massen aus $\{0,1,2\}$, in beiden Richtungen, 81+1539+53217
Fälle, keine Abweichung. Dazu kommt, dass $\mathcal L$ die erzwungenen Stellen
**genau** beschreibt — auch das jetzt auf fünf Punkten geprüft, 266085 Stellen,
beide Abweichungsrichtungen null, wo der siebte Lauf nur drei und vier hatte und
dort $\mathcal L$ ohnehin alles ist. Der Ausfall ist damit nicht nur belegt,
sondern erklärt: wo $\mathbb 1$ die maximale Ordnung verliert, bleibt der Defekt
frei. Zweitens die Reduktion auf den Teil positiver Massen:
mit $Z=\{m=0\}$, das $0$ enthält, hat $\mathbb 1$ maximale Ordnung für $V$ genau
dann, wenn $\mathbb 1_{F'}$ sie für den invertierbaren Block $B=P'D'$ auf
$F'=\{m>0\}$ hat. Diese Richtung ist nicht nur geprüft (1539+53217 Fälle),
sondern bewiesen; der Beweis steht im PROTOKOLL und benutzt allein, dass kein
Punkt von $F'$ unter $0$ liegt.

**Ins Manuskript eingetragen.** Die Statuszeile „the same for
$\iota=\mathrm o$" lautet jetzt „*false*; counterexample in `rem:atomicposet`",
und der letzte Absatz von `rem:atomicposet`, der bisher schloss „It is the one
row of the table that is verified rather than proved", trägt jetzt den Zeugen,
die Bedingung $m_c^2=m_am_b$ und den Satz, dass $\iota=\mathrm p$ in
`prop:atomicposet` eine Eigenschaft der Aussage ist und nicht eine des
Arguments. `check.py` meldet danach `clean`: 126 Seiten, keine undefinierten
Referenzen, größte Überlänge 7.7pt wie im Ausgangszustand. In
`MartingaleProblems` sagt die Zeile zu `duality_of_atomic` jetzt dasselbe und
nennt den Diamanten; sie sagte bisher nur, das Werkzeug greife nicht.

**Offen geblieben.** Von Task 23 dieselben zwei Punkte wie zuvor, ordnungsdichte
Atommengen und die gemischte Uhr; sie sind jetzt Rückstaupunkt 1. Nicht
geschehen und mit Absicht: kein Lean übersetzt (der Worktree hat kein `.lake`).
Nicht angefasst: die Frage, ob man die richtige o-Aussage — der Defekt
verschwindet, sobald $\mathbb 1$ maximale Ordnung hat — ins Manuskript aufnehmen
will. Sie ist wahr und geprüft, aber ihre Hypothese ist keine Uhrenhypothese,
sondern eine Bedingung an die Massen, der man nicht ansieht, welche Uhren sie
trifft; das gehört dem Nutzer.

**Als Nächstes zu formalisieren:
`Matrix.trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`** — für `A.IsSymm` und
`Bᵀ = -B` ist `(A * B).trace = 0`. Der Vorschlag steht seit dem sechsten Lauf und
wird durch diesen **zum zweiten Mal bestätigt, jetzt aus der anderen Richtung**:
der Zeuge trifft nicht den Spurteil, sondern allein die Konstruktion von `T`. Was
unter $\iota=\mathrm o$ ausfällt, ist die Hypothese von
`Matrix.exists_isSymm_mulVec_one_eq_single`; die drei Zeilen Spuralgebra gelten
in beiden Konventionen und sind heute mit einem Gegenbeispiel gegen den anderen
Teil noch schärfer abgegrenzt als vorher mit einem Rangvergleich für ihn. Sie
ruhen auf `Matrix.IsSymm` (`LinearAlgebra/Matrix/Symmetric.lean:35`),
`Matrix.trace_transpose` (`Trace.lean:73`) und `Matrix.trace_mul_comm`
(`Trace.lean:158`); ein Prädikat für `Bᵀ = -B` allein hat Mathlib nicht
(`Matrix.IsSkewAdjoint`, `SesquilinearForm.lean:562`, ist relativ zu einer
Form `J`), die Bedingung wird also ausgeschrieben.

Neue Roadmap-Punkte trägt dieser Lauf **keine** ein, und das ist die richtige
Folge eines negativen Ergebnisses: eine Roadmap führt zu beweisende Aussagen,
und die o-Fassung ist keine mehr. Was sie stattdessen bekommen hat, ist die
Korrektur einer Zeile, die mehr behauptete, als gilt.

### 2026-09-01 — Rückstau 1: die gemischte Uhr ist bewiesen

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da; der Lauf ging an
den ersten Punkt des Rückstaus, und dort an die Hälfte, die seit dem 2026-08-29
unberührt lag: **Stufe 3, die gemischte Uhr.** Sie ist erledigt, unter einer
genannten Hypothese. Geändert sind `MartingaleProblem.tex`,
`TauCeti/MartingaleProblems/README.md`, `Task23/PROTOKOLL.md`,
`Facts/BACKLOG.md` und dieses Inventar; neu ist `Task23/mixed.py`.

**Der Satz.** Für $q=\mu+\sum_{i=1}^N m_i\delta_{a_i}$ mit $\mu$ atomlos und
endlich vielen Atomen gilt $\Phi(s,t)=\Phi(t,s)$ auf dem ganzen Quadrat,
insbesondere $\Phi(t^*,0)=\Phi(0,t^*)$ bei **jedem** $t^*$, sobald zwischen je
zwei aufeinanderfolgenden Atomen — und vor dem ersten — stetige Masse liegt.
Die Masse nach dem letzten Atom darf null sein. Im Manuskript ist das
`prop:mixeddual`, gestützt auf ein neues `lem:rectangle`; die Statuszeile
„order-dense atoms, or mixed & open" ist in zwei Zeilen zerlegt, deren erste
`proved` lautet.

**Der Mechanismus, in einem Satz.** In Uhrzeit zerfällt der Definitionsbereich
in Strecken $S_0,\dots,S_N$ mit Lücken dazwischen, eine je Atom; auf
$S_i\times S_j$ ist $\Psi(x,y)=f_{ij}(x+y)$, und das Überqueren einer Lücke der
Masse $m$ ist der Operator $g\mapsto g+mg'$, der **nur an der Masse hängt** und
nicht daran, welche Koordinate überquert — das ist $\gamma_1=\gamma_2$ in
Operatorform. Eine Induktion über den Abstand $d=i-j$ macht
$w_{ij}=f_{ij}-f_{ji}$ zu null: auf dem unteren Stück des gemeinsamen
Definitionsbereichs durch die Kreuzungsrelation, auf dem oberen, weil dort
$w+m w'=0$ mit Anfangswert null am Nahtpunkt gilt. Der Kern von $1+m\dif/\dif u$
ist $e^{-u/m}$, eindimensional; die stetige Masse liefert genau die Stelle, an
der er weggeschnitten wird. Mehr tut sie nicht, und deshalb ist die Hypothese so
schwach.

**Was der Beweis nicht braucht.** Die Eckrelationen an zwei Atomen — wörtlich
`lem:atomgrid` — kommen nicht vor. Der rein atomare und der getrennt gemischte
Fall sind also nicht Spezialfälle voneinander, sondern zwei Enden: dort trägt
allein die Kreuzmultiplikation, hier allein die Kreuzungsrelation.

**Nachgerechnet.** `Task23/mixed.py` stellt den vollen Lösungsraum als lineares
System auf: die $f_{ij}$ stückweise auf den Einheitsintervallen, in lokaler
Koordinate mit der Basis $1,\tau,\tau^2,\tau^3,e^{-\tau/m}$ — die
Exponentialfunktionen mit Absicht, denn der Kern des Kreuzungsoperators ist die
einzige Richtung, in der ein Gegenbeispiel Platz hätte; über die Stücke hinweg
nur Stetigkeit, denn mehr als absolute Stetigkeit ist von $f_{ij}$ nicht
bekannt. Neun Konfigurationen, $N=1,2,3$, ungleiche Strecken und Massen: Defekt
und Symmetriedefekt null ($\max<10^{-13}$). Dasselbe **ohne** die
Eckrelationen — die Probe auf den Beweis. Zwei Kontrollen, und beide sind der
Grund, dem Ergebnis zu trauen: ohne die $y$-Kreuzungen bleibt der Defekt stehen
(der Test ist nicht leer), und bei $c\equiv0$ reproduziert das Modell
`prop:atomicdual` (das Modell ist nicht falsch aufgestellt). Die zweite
Kontrolle hat nebenbei gezeigt, dass die symmetrische Konfiguration $c=[1,1]$
auch ohne die $y$-Kreuzungen defektfrei ist — wer nur sie prüft, prüft nichts.

**Ein Befund über die eigene Hypothese.** Läßt man einzelne $c_j$ verschwinden
— zwei benachbarte Atome ohne stetige Masse dazwischen —, so verschwindet der
Defekt im Modell weiterhin (sechs Konfigurationen). $c_j>0$ ist damit, soweit
geprüft, eine Hypothese des Beweises und nicht der Aussage. Das ist im
Manuskript so gesagt (`rem:mixeddual`, letzter Absatz) und nicht verschwiegen.

**Am Beweis hat sich unterwegs etwas verbessert.** `lem:rectangle` stand
zunächst mit einem distributionellen Beweis da: $(\partial_x-\partial_y)\Psi=0$,
also Funktion von $x+y$. Das Manuskript trägt jetzt den kürzeren: `lem:calculus`
auf ein Quadrat angewandt hat rechts null, gibt $\Psi(x+r,y')=\Psi(x,y'+r)$ für
fast alle $r$, und beide Seiten sind in $r$ stetig, also für alle. Für die
Formalisierung ist das der Unterschied zwischen „Mathlib braucht Distributionen
auf $\R^2$" und einer Zeile Stetigkeit.

**In die Roadmap eingetragen** (`MartingaleProblems` Meilenstein 8, drei neue
Punkte und zwei Korrekturen): `eq_comp_add_of_chain_identity` (das
Rechteck-Lemma, zurückgeführt auf `chain_identity_of_absolutelyContinuous`),
`Clock.stretches` (die Strecken-und-Lücken-Zerlegung in Uhrzeit) und
`duality_of_mixed` mit dem Beweisweg in drei Schritten. Korrigiert:
`duality_of_atomless` sagte „für $q$-fast jedes $t$" und sagt jetzt „für jedes
$t$" mit dem Grund, und der Schlusssatz von `duality_of_atomic` zählt die
abgedeckten Uhren jetzt vollständig auf.

**`check.py` meldet `clean`**: 129 Seiten (vorher 126), 12 Überlängen, größte
7.7pt — Zahl und Maximum wie im Ausgangszustand des Laufs.

**Offen geblieben.** Von Task 23 zwei Reste, beide im Rückstau vermerkt:
ordnungsdichte Atommengen (unverändert offen, und aus demselben scharfen Grund —
es gibt keine Aufzählung $a_1<a_2<\dots$, entlang der induziert werden könnte)
und zwei benachbarte Atome ohne stetige Masse. Der zweite ist der nähere: dort
greift statt der Kreuzungsrelation die Eckrelation, beide Mechanismen sind
einzeln bewiesen, und zu tun ist, sie in einer Induktion zu verschränken. Nicht
geschehen und mit Absicht: kein Lean übersetzt (der Worktree hat kein `.lake`),
und `cor:atomless` ist nicht verschärft worden — die Beobachtung steht als
Auffälligkeit oben und gehört dem Nutzer.

**Als Nächstes zu formalisieren:
`chain_identity_of_absolutelyContinuous`** (`MartingaleProblems`
Meilenstein 8) — für $\T=[0,\infty)$, Lebesgue-Uhr und $\Phi$ in jeder Variablen
absolut stetig mit $\nabla\Phi=(\gamma_1,\gamma_2)$ und $\iint|\gamma_i|<\infty$
auf Quadraten:
$\Phi(t,0)-\Phi(0,t)=\int_0^t(\gamma_1(s,t-s)-\gamma_2(s,t-s))\dif s$ für fast
jedes $t$. Es ruht auf nichts als Mathlib: `MeasureTheory.integral_integral_swap`
(`MeasureTheory/Integral/Prod.lean:482`) für den Fubini-Schritt, und für den
Schluss „aus $\int_0^T A=\int_0^T B$ für alle $T$ folgt $A=B$ fast überall"
entweder `MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq`
(`MeasureTheory/Function/AEEqOfIntegral.lean:364`) oder die
Lebesgue-Differentiation, `VitaliFamily.ae_tendsto_average`
(`MeasureTheory/Covering/Differentiation.lean:885`, im Namensraum
`VitaliFamily`, Zeilen 87--902; `VitaliFamily` selbst steht im Wurzelnamensraum,
`Covering/VitaliFamily.lean:68`) mit
`Real.tendsto_Icc_vitaliFamily_right` (`MeasureTheory/Covering/OneDim.lean:34`)
— alle vier heute am Quelltext geprüft, Namensräume nachgesehen, keine
`deprecated`.

Es ist **jetzt** dran, weil es heute vom Träger eines Punktes zum Träger von
vieren geworden ist. Bis gestern hing an ihm allein `duality_of_atomless`; seit
heute hängen daran zusätzlich `eq_comp_add_of_chain_identity`, über dieses
`duality_of_mixed`, und über die Verschärfung von „fast jedes $t$" auf „jedes
$t$" auch die Konklusion von `duality_of_atomless` selbst. Es ist zugleich der
einzige analytische Satz des ganzen Dualitätsmeilensteins — alles andere dort
ist Teleskopieren, lineare Algebra oder die eine Zeile Gronwall. Wer ihn hat,
hat den Meilenstein bis auf Kombinatorik.

### 2026-09-01, zweiter Lauf — Rückstau 1: die Hypothese der gemischten Uhr fällt; dann Rückstau 2

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da; der Lauf ging an
den ersten Punkt des Rückstaus, und dort an den Rest, den der Lauf davor
ausdrücklich stehen gelassen hatte: **zwei benachbarte Atome ohne stetige Masse
dazwischen.** Er ist erledigt, und nicht durch eine Zusatzbedingung, sondern
durch Streichen der Hypothese. Danach blieb Zeit für ein Stück von Rückstau 2,
und dort fiel ein systematischer Namensfehler auf. Geändert sind
`MartingaleProblem.tex`, `TauCeti/MartingaleProblems/README.md`,
`TauCeti/MartingaleProblems/Suggested.lean`, `Task23/mixed.py`,
`Task23/PROTOKOLL.md`, `Facts/BACKLOG.md` und dieses Inventar.

**Der Satz.** `prop:mixeddual` gilt jetzt für **jede** Uhr
$q=\mu+\sum_{i=1}^N m_i\delta_{a_i}$ mit $\mu$ atomlos und endlich vielen Atomen
unterhalb $t^*$ — ohne jede Bedingung an die stetige Masse zwischen ihnen. Die
Bedingung \eqref{eq:separated} ist aus dem Manuskript verschwunden, und mit ihr
die Ausnahme für ein Atom bei $0$, die sie nebenbei erzwungen hatte. Offen
bleibt von Task 23 allein die ordnungsdichte Atommenge.

**Der Angelpunkt, in einem Satz.** Der Lauf davor las $c_j>0$ als die Bedingung,
unter der die Zeile $\gamma(a_i,\cdot)$ auf der Strecke $S_j$ eine *Dichte* ist —
richtig, aber es übersieht, was an ihre Stelle tritt. Ist $c_j=0$, so ist
$S_j$ ein Punkt, alle Zeiten mit diesem $Q$-Wert liefern dasselbe
$\Phi(\cdot,s)$, also ist $\gamma(a_i,\cdot)$ auf ihnen konstant, und $a_{j+1}$
ist eine von ihnen. Der Sprung über eine entartete Spalte ist damit
$m_i\gamma(a_i,a_{j+1})$, ein **Eckwert**, und den erreicht die andere
Koordinate auch. Die Elimination dazwischen ist wörtlich die
Kreuzmultiplikation des rein atomaren Falls. Der Beweis behält seine Induktion
über $d=i-j$ und bekommt auf dem unteren Stück eine Fallunterscheidung: Strecke
oder Nachbarschaft, Kreuzungsrelation oder Eckrelation, und beide übergeben
demselben Gronwall-Schritt denselben Anfangswert.

**Eine Aussage des letzten Laufs ist zurückgenommen.** `rem:mixeddual` sagte, der
rein atomare und der gemischte Fall seien „nicht Spezialfälle voneinander,
sondern zwei Enden". Sie sind die zwei Fälle **einer** Induktion. Die Probe:
setzt man alle Strecken auf null, so bleibt nur der zweite Fall, und die
Induktion ist Zeile für Zeile der Beweis von `lem:atomgrid`. Was die Induktion
sich dafür leistet, leistet sich `lem:atomgrid` auch — sie benutzt ihre
Hypothese auf zwei Stufen zugleich, $d-1$ und $d-2$, und der Eckdefekt sitzt auf
$d-2$. Damit ist auch die Rolle der stetigen Masse genauer benannt: sie ist
nicht nötig, sie ist bequem. Nötig ist ein Punkt, an dem der eindimensionale
Kern $e^{-u/m}$ festgenagelt wird, und den hat jede Uhr — als Strecke oder als
Nachbarschaft.

**Nachgerechnet, und dabei ein Mangel des Orakels behoben.** `mixed.py` fehlte
die Relation über eine entartete Spalte ganz. Das entwertet seine früheren
Befunde nicht — eine fehlende wahre Relation *vergrößert* den Lösungsraum, ein
verschwindender Defekt darauf ist die stärkere Aussage —, aber es machte den
neuen Beweis nicht nachprüfbar. Sie steht jetzt als eigene Familie im Skript,
mit Schalter, dazu vier neue entartete Konfigurationen (Atom bei $0$ mit
mehreren Atomen, abwechselnd entartete Spalten, entartete Spalte am Ende,
$N=4$). Zehn Konfigurationen: Defekt und volle Symmetrie null, $\max<10^{-13}$.
Die drei Kontrollen sind der eigentliche Gehalt: ohne die Eckrelationen, aber
mit der neuen — null; ohne die neue, aber mit den Ecken — null; **ohne beide**
bleibt der Symmetriedefekt in allen sechs geprüften Konfigurationen stehen. Die
beiden sind also zwei Wege über dieselbe Spalte, jeder für sich genügt, und
keiner ist entbehrlich, wenn der andere fehlt. Nebenbei ist damit ein
Kanarienvogel des letzten Laufs entwertet: „ohne die Ecken bleibt der Defekt
stehen" galt nur, solange das Modell die neue Relation nicht kannte. Das steht
im PROTOKOLL, statt stillschweigend ersetzt zu werden.

**In die Roadmap eingetragen** (`MartingaleProblems` Meilenstein 8):
`duality_of_mixed` ohne die Hypothese `0 < c j`, mit den beiden entarteten
Relationen und der Fallunterscheidung ausgeschrieben; die Schlusszeile von
`duality_of_atomic`, die die abgedeckten Uhren aufzählt, nennt jetzt die
ordnungsdichte Atommenge als den einen Fall, den keiner der drei Sätze erreicht;
`atomGrid_symm` sagt, dass seine Induktionsgestalt auch die von
`duality_of_mixed` ist. Und ein Fehler nebenbei: `Clock.stretches` schrieb
`0 ≤ a 1 < ... < a N ≤ t*`, das Manuskript verlangt `a N < t*`, weil ein Atom
auf $t^*$ in keiner Menge `[s,s') ⊆ 𝕋_{<t*}` liegt. Korrigiert.

**`check.py` meldet `clean`**: 129 Seiten, 12 Überlängen, größte 7.7pt — Zahl und
Maximum wie im Ausgangszustand des Laufs.

**Danach Rückstau 2, ein Stück weit: die Liste „Mathlib supplies" von
`MartingaleProblems`.** 38 Namen aus elf Dateien, gegen **master** geprüft, die
Quellen über `gh api` geholt und im Text nachgesehen, nicht im Gedächtnis. Alle
vorhanden. Ein Fehler, und der lohnt die Übung: vier Namen — die ganze
Lokalisierungsschicht — standen in `MeasureTheory` statt in `ProbabilityTheory`.
`LocalProperty.lean` ist die einzige Datei in `Mathlib/Probability/Process/`, die
nicht in `MeasureTheory` liegt, und genau deshalb hat sich der falsche Präfix
gehalten; dieses Inventar hat ihn am 2026-08-30 mitgeschrieben. Berichtigt sind
die Roadmap an drei Stellen, `TauCeti/MartingaleProblems/Suggested.lean` und die
Tabellenzeile zu `fact:stoppedlocalmg`; die Einzelheiten stehen oben unter den
Auffälligkeiten. Drei Behauptungen der Liste sind nachgeprüft und **bleiben
richtig**: `ProgMeasurable` ist weiterhin ein `deprecated`-Alias von
`IsStronglyProgressive` (`Process/Adapted.lean:381`, seit 2026-04-24), Doobs
`Lᵖ`-Ungleichung fehlt weiterhin für jeden Index — der Modulkommentar
`OptionalStopping.lean:143` sagt selbst, sie komme „in an upcoming PR" —, und
`IsStable` ist für keine hier interessierende Eigenschaft bewiesen; die Datei
führt nur `IsStable.and`, und `gh search code` findet den Bezeichner in genau
einer Wahrscheinlichkeitsdatei, alle übrigen Treffer sind
`MorphismProperty.IsStableUnder…` aus Algebra und Kategorientheorie.

**Offen geblieben.** Von Task 23 die ordnungsdichte Atommenge, aus dem
unveränderten scharfen Grund. Von Rückstau 2 die Roadmaps `SkorokhodSpace` und
`KolmogorovExtension` und die Zitate in den Meilensteinen aller vier; geprüft ist
bisher nur, was in den Kopflisten steht. Der Rückstau nennt jetzt, wo ein Anlauf anfinge:
bei der Frage, ob eine ordnungsdichte Atommenge mit lokal endlicher Gesamtmasse
eine Ausschöpfung durch endliche Teilmengen zulässt, längs deren der Defekt
stetig ist. Nicht geschehen und mit Absicht: kein Lean übersetzt (der Worktree
hat kein `.lake`), und `cor:atomless` ist weiterhin nicht verschärft — die
Auffälligkeit vom Vormittag steht unverändert oben und gehört dem Nutzer.

**Als Nächstes zu formalisieren: `atomGrid_symm`** (`MartingaleProblems`
Meilenstein 8). Für `M : ℕ`, `m : ℕ → ℝ` mit `m i ≠ 0` und
`Φ : ℕ → ℕ → ℝ` mit `m j * (Φ (i+1) j - Φ i j) = m i * (Φ i (j+1) - Φ i j)` auf
`1 ≤ i, j ≤ M-1` folgt `Φ i j = Φ j i`. Es ruht auf **nichts** — kein Maß, keine
Uhr, keine Topologie, `ℕ` als einziger Index, Körperarithmetik als einziges
Werkzeug; die Roadmap verortet es deshalb in `Mathlib/Algebra/Order/` und nicht
im Wahrscheinlichkeitsbaum. Der Beweis ist die Induktion über `d = |i - j|` mit
zwei mitgeführten Stufen, und die einzige Lean-Frage daran ist, wie man diese
Zweistufigkeit formuliert: als starke Induktion über `d` mit der
Induktionsaussage „`w` verschwindet auf allen Abständen `< d`" — genau die
Gestalt, in der sie auch im Beweis der gemischten Uhr gebraucht wird.

Es ist **jetzt** dran, weil es heute vom Träger eines Satzes zum Träger von
zweien geworden ist. Bis gestern hing daran allein `duality_of_atomic`; seit
heute hängt daran auch der entartete Fall von `duality_of_mixed`, und zwar nicht
als Analogie, sondern als dieselbe Aussage an den Ecken des Streckengitters.
Es ist zugleich das einzige benannte Ziel der vier Roadmaps, das gar keine
Mathlib-Vorbedingung hat: `chain_identity_of_absolutelyContinuous` (der Vorschlag
vom Vormittag, unverändert gültig) braucht Fubini und die
Lebesgue-Differentiation, `IsSeparating` braucht die `ext_of_…`-Sätze,
`induction_on_mulSystem` braucht `induction_on_inter`. `atomGrid_symm` braucht
nichts. Reihenfolge, wenn beide anstehen: `atomGrid_symm` zuerst, denn es ist
das kleinere und schließt einen ganzen Zweig von Meilenstein 8 ab.

### 2026-09-01, dritter Lauf — Rückstau 1: die Ausschöpfung der ordnungsdichten Atommenge ist quantifiziert

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da; der Lauf ging an
den ersten Punkt des Rückstaus und dort an das, was von Task 23 allein übrig ist:
die **ordnungsdichte Atommenge**. Der Rückstau nannte dafür einen Anfang — ob es
eine Ausschöpfung durch endliche Teilmengen gibt, längs deren der Defekt stetig
ist. Der Lauf hat diese Frage nicht mit ja oder nein beantwortet, sondern sie
rechenbar gemacht und die Rechnung ausgeführt. Neu ist `Task23/dense.py`;
geändert sind `Task23/PROTOKOLL.md`, `Facts/BACKLOG.md` und dieses Inventar.
**Bewiesen ist nichts, und der Punkt bleibt offen.** Am Manuskript ist nichts
geändert, an den Roadmaps auch nicht — die vier Matrizenlemmata des sechsten
Laufs stehen bereits in `MartingaleProblems` M8, und die Schlusszeile von
`duality_of_atomic` nennt die ordnungsdichte Menge schon als den Fall, den keiner
der drei Sätze erreicht. Beides ist nachgesehen und bleibt richtig.

**Der Hebel: der Beweis des sechsten Laufs, störungsweise gelesen.** Er brauchte
keine neue Idee, nur eine Buchführung über den Fehler. Gilt (S) nur bis auf einen
symmetrischen Rest $E$, so bleibt die zweite Hälfte der Paarung unberührt und die
erste bekommt einen Zusatzterm:
$\langle\delta,T\mathbb 1\rangle=-\frac12\operatorname{tr}(TE)$. Das ist eine
**Identität**, keine Abschätzung, und `dense.py check` bestätigt sie an
zufälligen $K$ mit künstlich gestörtem (S) in allen Fällen exakt. Damit hängt die
ganze Ausschöpfung an einer einzigen berechenbaren Zahl,

$$C(V,t)=\|T\|_F,\qquad T=T^{\mathsf T},\ TV=V^{\mathsf T}T,\ T\mathbb 1=e_t:$$

schneidet man das volle System auf ein endliches $F$ zurück, so ist
$|\delta(t)|\le\|\kappa\|_\infty\varepsilon_F(1+2|F|C_F)$ mit
$\varepsilon_F=q(A\setminus F)$, und der Defekt verschwindet, sobald
$|F|C_F\varepsilon_F\to0$ für **irgendeine** Folge endlicher $F$ gilt. Das
Gleichungssystem für $T$ ist quadratisch, sein Kern durchweg eindimensional, die
Minimalnorm-Lösung also die richtige Messgröße.

**Gerechnet wird exakt, und das war nötig.** Die Gleitkommarechnung bricht
zusammen, sobald $C$ groß wird: für $n=8$, $\rho=4$ meldet `lstsq` Kerndimension
2 und ein *kleineres* $C$ als für $\rho=3$ — die `rcond`-Abschneidung, kein
Messwert. Alle berichteten Zahlen stammen deshalb aus `defect_bound_exact`, Gauß
über $\mathbb Q$ mit Minimierung der Frobeniusnorm über den Kern in der richtigen,
außerdiagonal doppelt zählenden Form.

**Der Befund, und er ist schärfer als erhofft.** $C$ ist skaleninvariant — mit
$V$ löst auch $cV$ die Bedingung $TV=V^{\mathsf T}T$ —, hängt also nur an der
*Gestalt* des Massenvektors, nicht an der Gesamtmasse. Und dann:

* gleiche Massen: $C=\sqrt{2n-1}$, geprüft bis $n=40$;
* geometrisch **fallende** Massen: $C\approx1.6$, gleichmäßig beschränkt in $n$
  und $\rho$;
* geometrisch **steigende** Massen: $C\sim\rho^{n^2/2}$, also überexponentiell —
  bei gleicher Länge und gleichem Massenverhältnis zehn Größenordnungen mehr als
  im fallenden Fall.

Das erklärende Gesetz: eine einzige kleine Masse $\varepsilon$ an der Stelle $k$
einer Kette aus $n$ Atomen kostet $C\sim\varepsilon^{-\max(n-2k,0)}$. Der
Exponent ist **exakt** $\max(n-2k,0)$, abgelesen über zwei Dekaden und bestätigt
für $n=4,6,8,10$ an jeder Stelle $k$ — vierzig Werte, keine Abweichung. Kleine
Massen in der oberen Hälfte der Kette sind gratis, kleine Massen in der unteren
ruinieren die Schranke. Nicht die Größe des Massenverhältnisses entscheidet,
sondern seine **Richtung**.

**Was daraus folgt.** Die Ausschöpfung scheitert, aber an einer anderen Stelle als
der Rückstau vermutete: nicht an der fehlenden Aufzählung $a_1<a_2<\dots$ und
nicht an der Endlichkeit einer Induktion, sondern an der Richtung des
Massenprofils — und quantitativ. Eine ordnungsdichte Menge erzwingt das teure
Profil, weil unter jedem Punkt unendlich viele Atome liegen. **Was der Befund
nicht sagt:** $C$ misst die beste Konstante *dieser Beweisgestalt*, nicht die
Wahrheit der Aussage. In $|\operatorname{tr}(TE)|\le\|T\|_F\|E\|_F$ steckt eine
Cauchy--Schwarz-Ungleichung, die die Struktur von $E$ als Schwanzbeitrag
wegwirft. Widerlegt ist die grobe Ausschöpfung, nicht die Dualität für
ordnungsdichte Atommengen; ein Gegenbeispiel ist nicht gesucht und nicht
gefunden. Drei Wege stehen jetzt als Sackgassen im PROTOKOLL (zehnter Nachtrag):
die exakte Einschränkung auf endliches $F$, das Zusammenfassen der Massen zu
Blöcken, und die Hoffnung auf ein Wachstum von $C$ in $|F|$ allein.

**Offen geblieben.** Die ordnungsdichte Atommenge selbst, jetzt mit einer
benannten nächsten Frage statt einer Richtung: ob die Cauchy--Schwarz-Ungleichung
durch eine Paarung ersetzt werden kann, die $E$ als Schwanzbeitrag benutzt. Von
Rückstau 2 unverändert die Roadmaps `SkorokhodSpace` und `KolmogorovExtension`
und die Zitate in den Meilensteinen aller vier; dieser Lauf hat daran nicht
gearbeitet, weil Rückstau 1 die Zeit gebraucht hat. Nicht geschehen und mit
Absicht: kein Lean übersetzt (der Worktree hat kein `.lake`), und `cor:atomless`
ist weiterhin nicht verschärft — die Auffälligkeit vom 2026-09-01 steht
unverändert oben und gehört dem Nutzer. `check.py` ist nicht gelaufen, weil am
Manuskript nichts geändert wurde.

**Als Nächstes zu formalisieren: `atomGrid_symm`** (`MartingaleProblems`
Meilenstein 8), unverändert gegenüber dem Vorschlag des letzten Laufs und aus
demselben Grund — es ruht auf nichts, `ℕ` als einziger Index, Körperarithmetik
als einziges Werkzeug, und es trägt seit dem zehnten Lauf zwei Sätze statt einem.
Dieser Lauf hat daran nichts geändert und nichts gefunden, was die Reihenfolge
umwirft.

Der heutige Befund benennt aber den **zweiten**: `Matrix.exists_isSymm_mulVec_one_eq_single`
(ebenfalls M8, dort schon eingetragen) — aus `V ^ r = 0` und
`V ^ (r-1) *ᵥ 1 ≠ 0` die explizite Konstruktion von `T` mit `T.IsSymm`,
`T * V = Vᵀ * T` und `T *ᵥ 1 = Pi.single t 1`. Es ist jetzt reif, weil es heute
vom Beweisschritt zum **Messgerät** geworden ist: $C(V,t)$ ist per definitionem
die Norm des von ihm gelieferten $T$, und jede weitere Aussage über den offenen
Fall — auch eine feinere Paarung — wird an diesem Objekt formuliert. Es ist
zugleich das einzige der vier Matrizenlemmata aus M8, das kein Zweizeiler ist;
die drei übrigen (`trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`,
`trace_mul_eq_dotProduct_diag_of_isSymm`, `mulVec_one_eq_zero_iff_of_nonneg`)
fallen danach als Beiwerk. Reihenfolge, wenn beide anstehen: `atomGrid_symm`
zuerst, denn es ist das kleinere und schließt einen Zweig ab; dann die
Konstruktion von `T`, die den Zweig für den offenen Fall öffnet.

### 2026-09-01, vierter Lauf — Rückstau 2: `KolmogorovExtension` und `SkorokhodSpace` gegen master

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da. Rückstau 1 hat der
Lauf davor bis an eine benannte Forschungsfrage geführt — ob die
Cauchy--Schwarz-Ungleichung in $|\operatorname{tr}(TE)|\le\|T\|_F\|E\|_F$ durch
eine Paarung ersetzbar ist, die $E$ als Schwanzbeitrag benutzt —, und daran hat
dieser Lauf nicht gearbeitet; der Grund steht unten. Er ging an **Rückstau 2**
und dort an dessen ausdrücklich offenen Rest: die beiden Roadmaps, die noch nie
gegen master geprüft waren. Beide sind jetzt **vollständig** durch, Kopfliste
**und** Meilensteine — bei `SkorokhodSpace` zitieren nur die Meilensteine 1, 2, 3
und 8 überhaupt Mathlib, die Meilensteine 4 bis 7 führen ausschließlich neue
Namen. Geändert sind `TauCeti/KolmogorovExtension/README.md`,
`TauCeti/SkorokhodSpace/README.md`, `Facts/BACKLOG.md` und dieses Inventar. Am
Manuskript ist nichts geändert.

Geprüft wurde gegen master vom heutigen Tag (`df0e53b7`, `gh api`), Datei für
Datei am Quelltext, mit Namensraum, Zeilennummer und Variablenblock. Das lokale
`origin/master` in `~/Code/lean/mathlib4` steht auf dem 2026-03-23 und ist als
Stellvertreter untauglich; das ist beim Nachfetchen aufgefallen und für den
nächsten Lauf notiert.

**Vier Fehler in `KolmogorovExtension`.** Zwei Namensräume — dieselbe Familie wie
am zweiten Lauf des Tages, und deshalb der eigentliche Ertrag der Übung:
`MeasureTheory.isProjectiveLimit_infinitePi` heißt
`MeasureTheory.Measure.isProjectiveLimit_infinitePi`, und
`MeasureTheory.isProjectiveLimit_map` heißt
`ProbabilityTheory.isProjectiveLimit_map`. Ein Meilensteinpunkt, den Mathlib
längst hat: `MeasureTheory.IsProjectiveLimit.unique` steht unter genau diesem
Namen in `Constructions/Projective.lean:150`, mit dem Beweis, den die Roadmap als
zu gehenden Weg beschrieb; mit ihm `isFiniteMeasure`, `isProbabilityMeasure`,
`measure_cylinder`, `measure_univ_eq` und `measure_univ_unique`, die den
vorletzten Punkt auf eine Zeile bringen. Und eine zu schwach angegebene
Hypothese: `innerRegular_isCompact_isClosed_measurableSet_of_finite`
(`RegularityCompacts.lean:203`) verlangt neben
`IsCompletelyPseudoMetrizableSpace` auch `SecondCountableTopology` und
`BorelSpace`; die Kopfliste ließ die letzten beiden weg und behauptete damit mehr
Mathlib, als es gibt. Die Einzelheiten stehen oben unter den Auffälligkeiten.

**Ein Fund in die andere Richtung, ebenfalls eingetragen.** master hat seit
kurzem `isCompactSystem_isCompact_isClosed` (`Topology/Compactness/CompactSystem.lean:163`),
„die abgeschlossenen kompakten Mengen sind ein kompaktes System", dazu
`isCompactSystem_isCompact` für `T2Space`,
`isCompactSystem_insert_univ_isCompact_isClosed`,
`IsCompactSystem.of_nonempty_iInter`, `IsCompactSystem.iff_nonempty_iInter`,
`isCompactSystem_insert_empty_iff` und `isCompactSystem_iff_of_directed`. Das ist
genau die Vorbedingung des dritten Punktes von Meilenstein 1, und der Punkt
sagt jetzt, dass ihm nur noch der Übergang zu den Zylindern darüber bleibt. Was
sonst geprüft und **richtig** ist: alle zwölf `projectiveFamilyContent_*`-Namen
(die `deprecated`-Aliase seit 2026-06-03 heißen `_diff` und `_diff_of_subset`,
die Roadmap nennt die aktuellen `_sdiff` und `_sdiff_of_subset`), die drei
`isSet*_measurableCylinders`, `AddContent.IsSigmaSubadditive` (`:149`),
`AddContent.measure` (`OfAddContent.lean:163`) und `measure_eq` (`:172`),
`generateFrom_measurableCylinders` (`Cylinders.lean:362`) — samt der Richtung:
`AddContent.measure` verlangt `hC_gen : mα ≤ generateFrom C`, und
`generateFrom_measurableCylinders.symm.le` liefert genau das, die Roadmap
typisiert also —, `ext_of_generate_finite`, `ProbabilityTheory.Kernel.traj`
(`Traj.lean:518`) und `IsProjectiveMeasureFamily`.

**Drei Fehler in `SkorokhodSpace`, und der erste ist der schwerste.** Die
Kopfliste nannte sechs Sätze als „die ganze Einseitiglimes-API"; alle sechs
stehen in `namespace Monotone` und verlangen Monotonie von `f` sowie
`[ConditionallyCompleteLinearOrder β] [OrderTopology β]` vom Zielraum. Für einen
càdlàg-Pfad ist keiner benutzbar. Das ist derselbe Fehlertyp wie `Locally` gegen
„local martingale" am 2026-08-29 — nach dem Begriff gesucht, den Namen gefunden,
den Namensraum nicht angesehen. Berichtigt, mit der Liste dessen, was im
Wurzelnamensraum wirklich steht; und dabei kam der Glücksfall heraus, dass die
Hypothese von `tendsto_leftLim_of_tendsto` wörtlich das Feld `left_limit` von
`IsCadlag` ist. Daran hängt eine Hypothesenkorrektur: `Function.leftLim` gibt es
nur für `[LinearOrder α]`, die zwei Punkte, die die Struktur daran anschließen,
standen unter `[Preorder ι]`, und Meilenstein 2 führt jetzt eine dritte Stufe
**(A′)**. Zweitens der Selbstwiderspruch um `Monotone.countable_not_continuousAt`
— Kopfliste falsch, Meilenstein 2 richtig. Drittens, und das trifft die Substanz:
`TimeChange.norm` war über `LipschitzWith.const` definiert, das der Satz „eine
Konstante ist `0`-lipschitz" ist und keine Zahl, und Mathlib kennt keine
kleinste Lipschitzkonstante. Die Metrik des Skorokhod-Raums war damit nicht
aufschreibbar; Meilenstein 3 führt jetzt `TimeChange.lipConst` als eigenen Punkt.
Alle drei stehen ausgeschrieben oben unter den Auffälligkeiten.

Zwei Gegenproben, die den ersten und den dritten Befund stützen und beide aus
`TauCeti/SkorokhodSpace/Suggested.lean` stammen — der Datei ist nichts zu
korrigieren, sie war schon richtig, wo die README falsch war. Sie führt `ι`
durchweg unter `[LinearOrder ι]` und nicht unter `[Preorder ι]` und schreibt
`leftJumpSet` mit `Function.leftLim` genau dort hin; und `TimeChange` hat die
Felder `lipschitz : ∃ C, LipschitzWith C toOrderIso` und `lipschitz_symm`, also
die Existenz einer Konstanten und nicht eine ausgezeichnete. Wer die Skizze
ansah, konnte den Fehler der README nicht machen — er stand allein in der Prosa.

**Was an `SkorokhodSpace` geprüft und richtig ist**, und zwei davon lohnen die
Erwähnung, weil sie eine offene Frage des Inventars schließen: die Zusage von
Meilenstein 8, `isCompact_closure_of_isTightMeasureSet` verlange „`[T2Space E]`
und `[BorelSpace E]` und nichts weiter", stimmt buchstäblich — der
Variablenblock `Prokhorov.lean:65` führt genau
`[MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]`, und der
Satz steht bei `:530` im Wurzelnamensraum, weil `namespace MeasureTheory` erst
bei `:568` im Abschnitt `Backward` beginnt. Und die Gegenrichtung
`MeasureTheory.isTightMeasureSet_of_isCompact_closure` (`:634`) trägt wirklich
`[CompleteSpace 𝓧]`, gesetzt durch ein eigenes `variable` bei `:630`, neben
`[PseudoMetricSpace 𝓧] [OpensMeasurableSpace 𝓧] [SecondCountableTopology 𝓧]`;
ihr Dokumentationskommentar sagt es selbst. Die Zweiteilung von Meilenstein 8 in
(A) separabel metrisch und (B) polnisch ruht damit auf Nachgesehenem und nicht
auf einer Erinnerung. Weiter richtig: `orderTopology_of_ordConnected` als
Instanz (`Topology/Order/Basic.lean:344`), `ProperSpace.of_isClosed`
(`Topology/MetricSpace/ProperSpace.lean`), `Subgroup.isClosed_of_discrete`
(`IsUniformGroup/Basic.lean:279`, mit `@[to_additive]`, die additive Form gibt es
also wie behauptet), `OrderTopology.of_discreteTopology` (`Instances/Discrete.lean:59`,
mit `PredOrder` und `SuccOrder`, wie die Roadmap sagt), `AddSubgroup.zmultiples`,
`StieltjesFunction` mit `right_continuous` (`:140`) und `rightLim_eq` (`:143`),
`MeasureTheory.instMetrizableSpaceProbabilityMeasure` (`LevyProkhorovMetric.lean:695`,
Zeile auf den Punkt) und
`ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`
(`ProbabilityMeasure.lean:639`). Ein zweiter Fund in die freundliche Richtung:
neben `OrderTopology.of_discreteTopology` steht bei `:63`
`OrderTopology.of_linearLocallyFinite` mit `[LocallyFiniteOrder α]` statt
`PredOrder`/`SuccOrder` — ein dritter und bequemerer Weg für den diskreten Index
`h • ℤ`, den Meilenstein 1 jetzt nennt.

**Offen geblieben.** Von Rückstau 2 die Zitate in den Meilensteinen von
`WeakConvergence` und `MartingaleProblems`; deren Kopflisten sind seit dem
2026-08-31 beziehungsweise heute früh geprüft, die Meilensteine nicht. Nach dem
Ertrag von heute — vier Fehler in einer Roadmap von 101 Zeilen, drei in einer von
346 — ist das der nächste Griff im Rückstau und nicht mehr Routine. Von Rückstau 1
unverändert die ordnungsdichte Atommenge; dieser Lauf hat sie nicht angefasst,
weil die Frage, an der sie steht, eine Beweisidee verlangt und nicht eine Suche,
und weil zwei Roadmaps ungeprüft dastanden, deren Prüfung erfahrungsgemäß
Fehler findet. Sie hat sieben gefunden. Nicht geschehen und mit Absicht: kein
Lean übersetzt (der Worktree hat kein `.lake`), `check.py` nicht gelaufen (am
Manuskript ist nichts geändert), und `cor:atomless` ist weiterhin nicht
verschärft — die Auffälligkeit vom 2026-09-01 steht unverändert oben und gehört
dem Nutzer.

**Als Nächstes zu formalisieren: `Function.RightContinuous` und `IsCadlag` samt
`IsCadlag.tendsto_leftLim` und `IsCadlag.rightLim_eq`** (`SkorokhodSpace`
Meilenstein 2, Stufen (A) und (A′)). Das Prädikat ist
`∀ a, ContinuousWithinAt f (Set.Ioi a) a`, die Struktur hat die zwei Felder
`right_continuous` und `left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)`, und
der Anschluss an Mathlib besteht aus genau drei Namen, die heute am Quelltext
geprüft sind: `tendsto_leftLim_of_tendsto`
(`Topology/Order/LeftRightLim.lean:121`), dessen Hypothese wörtlich das Feld
`left_limit` ist, `ContinuousWithinAt.rightLim_eq` (`:117`) und
`continuousWithinAt_Ioi_iff_Ici`, das aus `Ioi` das `Ici` macht, welches der
zweite verlangt — derselbe Schritt, den `StieltjesFunction.rightLim_eq` (`:143`)
geht. Mehr braucht es nicht: keine Metrik, kein Maß, keine Sprungtheorie, kein
dichtes `D`.

Es ist **jetzt** dran, weil heute der Grund weggefallen ist, es aufzuschieben,
und weil zugleich sichtbar geworden ist, worauf es trägt. Weggefallen ist die
Unklarheit über die Anschlussstelle: bis heute nannte die Roadmap dafür sechs
Sätze über monotone Funktionen, und wer sie aufgeschlagen hätte, wäre auf
`include hf : Monotone f` gestoßen und hätte neu suchen müssen. Getragen wird es
von der ganzen Roadmap — Meilenstein 4 definiert den Raum als die Struktur über
diesem Prädikat, und über Meilenstein 8 hängen vier Facts daran
(`fact:Dcountable`, `fact:fddconv`, `fact:relcompact`, `fact:fdd`), mehr als an
jedem anderen einzelnen Punkt der vier Roadmaps. Und es ist billig: das Prädikat
samt Abschlusseigenschaften liegt als Apache-2.0-Vorlage in
`RemyDegenne/brownian-motion`, `BrownianMotion/StochasticIntegral/Cadlag.lean`,
zu übernehmen mit Kopfzeile und Autorennennung. Reihenfolge, wenn mehrere
anstehen: `atomGrid_symm` bleibt der erste, denn es ruht auf nichts und schließt
einen Zweig von `MartingaleProblems` M8 ab; `IsCadlag` ist der erste Punkt der
Roadmap, die von allen vieren die meisten Facts trägt, und der einzige, dessen
Mathlib-Anschluss heute vollständig nachgeschlagen ist.

### 2026-09-01, fünfter Lauf — Rückstau 2: die Meilensteine von `WeakConvergence`, und ein Anfang bei `MartingaleProblems`

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine da. Rückstau 1 steht
seit dem dritten Lauf des Tages an einer Beweisidee und nicht an einer Suche —
ob die Cauchy--Schwarz-Ungleichung in
$|\operatorname{tr}(TE)|\le\|T\|_F\|E\|_F$ durch eine Paarung ersetzbar ist, die
$E$ als Schwanzbeitrag benutzt —; daran hat auch dieser Lauf nicht gearbeitet,
und der Grund ist derselbe wie beim vierten: der ausdrücklich offene Rest von
Rückstau 2 stand da, und seine Trefferquote ist hoch. Sie war es wieder.
Geändert sind `TauCeti/WeakConvergence/README.md`,
`TauCeti/MartingaleProblems/README.md`, `Facts/BACKLOG.md` und dieses Inventar.
Am Manuskript ist nichts geändert.

**Zuerst das Werkzeug, denn es hat den Lauf getragen.** Das lokale
`origin/master` in `~/Code/lean/mathlib4` zeigt auf den Fork des Nutzers und
steht auf dem 2026-03-23; der vierte Lauf hat es deshalb für untauglich erklärt
und alles über `gh api` geholt. Es gibt aber ein zweites Remote, `upstream`, das
auf `leanprover-community/mathlib4` zeigt. Ein `git -C ~/Code/lean/mathlib4
fetch --no-tags upstream master` bringt `upstream/master` auf den Tagesstand,
und danach beantwortet `git grep -n <muster> upstream/master -- Mathlib` in einem
Aufruf Fragen, für die `gh search code` ein Dutzend braucht — mit Zeilennummern,
Namensraumgrenzen und Variablenblöcken am Quelltext. Der Lauf hat so auf
`981fa8f5` (master vom heutigen 08:37 UTC) geprüft. Das ist der Weg für alle
weiteren Durchgänge dieses Rückstaupunktes.

**Der Hauptbefund, und er ist größer als ein falsches Zitat.**
`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` war
`WeakConvergence` unbekannt — die Kopfliste nannte die Datei nicht, und vier
Punkte der Meilensteine 2 und 3 verlangten, was in ihr steht. Sie führt
`MeasureTheory.TendstoInDistribution` als Struktur, deren Zufallsvariablen
`X i : Ω i → E` auf einer Familie von Räumen leben, eine je Index; Meilenstein 4
hatte genau diese Gestalt als das geführt, was fehlt. Weggefallen sind die
Slutsky-Fassung, die drei eigentlichen Slutsky-Sätze und die Rückrichtung der
Skorokhod-Darstellung; von Meilenstein 2 bleibt der eine Schritt von
`Continuous h` zur f.ü.-Stetigkeit, und der Punkt in Zufallsvariablenform steht
jetzt auf Mathlibs Struktur statt auf einer eigenen. Der Name
`MeasureTheory.tendsto_of_ae_tendsto`, den Meilenstein 3 nannte, existiert
nicht; gemeint war `tendstoInDistribution_of_ae_tendsto` (`:152`). Dazu der
fünfte Punkt: `measurableSet_setOf_continuousAt` gibt es als
`measurableSet_of_continuousAt` im Wurzelnamensraum
(`Constructions/BorelSpace/Basic.lean:252`). Beide Auffälligkeiten stehen oben
ausgeschrieben.

**Das Lehrstück daran.** Die Datei steht in v4.33.1 wortgleich da, mit denselben
dreizehn Deklarationen und nur anderen Zeilennummern (`:64`, `:121`, `:137`,
`:177`, `:301` statt `:64`, `:136`, `:152`, `:192`, `:313`). Es ist also kein
Nachziehen hinter master, sondern eine nie gestellte Suche — und zwar dieselbe
Sorte wie am 2026-08-29: nach dem Wort des Manuskripts gesucht („weak
convergence", „Skorokhod representation") statt nach dem Begriff, unter dem
Mathlib ihn führt („convergence in distribution"). Wer den Rückstaupunkt
fortsetzt, suche zu jedem Meilensteinpunkt zuerst nach dem **Verzeichnis**, in
dem er läge, und lese dessen Dateinamen, bevor er nach Deklarationen sucht.

**Was in `WeakConvergence` geprüft und richtig ist.** Alle sechs Zitate aus
`LevyProkhorovMetric.lean` stimmen auf die Zeile und den Namensraum
(`LevyProkhorov` `:259`, `LevyProkhorov.instPseudoMetricSpaceProbabilityMeasure`
`:311`, `LevyProkhorov.levyProkhorovDist_metricSpace_probabilityMeasure` `:336`,
`SeparableSpace.exists_measurable_partition_diam_le` `:540`,
`LevyProkhorov.probabilityMeasureHomeomorph` `:676`,
`instMetrizableSpaceProbabilityMeasure` `:695`, sämtlich in `namespace
MeasureTheory` ab `:41`), ebenso `isCompact_closure_of_isTightMeasureSet`
(`:530`), `exists_measure_iUnion_gt_of_isCompact_closure` (`:573`) und
`isTightMeasureSet_of_isCompact_closure` (`:634`) aus `Prokhorov.lean`,
`isTightMeasureSet_singleton` (`:99`) und `IsTightMeasureSet.union` (`:119`,
`protected lemma`) aus `Tight.lean`, `tendsto_measure_of_null_frontier` (`:243`)
und `exists_null_frontier_thickening` (`:401`) aus `Portmanteau.lean`,
`Measure.countable_meas_pos_of_disjoint_iUnion` (`SFinite.lean:305`),
`frontier_compl`/`frontier_inter_subset`/`frontier_union_subset`
(`Closure.lean:528,537,544`),
`Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`
(`CompletelyMetrizable.lean:249`, mit `_root_.`), `PolishSpace`
(`Polish.lean:62`) samt der Instanz aus Separabilität und vollständiger
Metrisierbarkeit (`:65`), `TotallyBounded.isCompact_of_isClosed`
(`Cauchy.lean:755`), `Filter.EventuallyEq.of_forall_separating_preimage`
(`CountableSeparatingOn.lean:257`), die Instanzkette
`BorelSpace.countablyGenerated` (`BorelSpace/Basic.lean:209`) →
`CountablySeparated` (`CountablyGenerated.lean:383`), `condDistrib`
(`CondDistrib.lean:64`, `namespace ProbabilityTheory`), `condExpKernel`
(`Condexp.lean:71`, und es verlangt wirklich `[StandardBorelSpace Ω]`, gesetzt
bei `:62`), `uniformIntegrable_iff` (`UniformIntegrable.lean:868`),
`induction_on_inter` (`PiSystem.lean:713`) und `MeasurableSpace.comap`
(`MeasurableSpace/Basic.lean:84`).

**Vier Zeilennummern stammten aus v4.33.1 und sind auf master nachgeführt:**
`Metric.thickening_singleton` `:157`→`:149`,
`UniformSpace.secondCountable_of_separable` `:932`→`:931`,
`Homeomorph.secondCountableTopology` `:37`→`:36`,
`Homeomorph.isClosedEmbedding` `:297`→`:296`. Der Beleg dafür, dass es sich um
v4.33.1-Zahlen handelt und nicht um Fehler: in der lokalen v4.33.1-Quelle stehen
die Deklarationen auf genau diesen vier Zeilen. Alle übrigen Zeilenangaben der
Roadmap treffen master, sie ist also im Grundsatz master-genau; diese vier sind
die Ausnahme.

**`MartingaleProblems`, angefangen.** Die Meilensteine dieser Roadmap sind mit
1038 Zeilen der größte Rest des Rückstaupunktes; dieser Lauf hat die
Fundstellen mit ausgeschriebenem Mathlib-Pfad abgearbeitet, nicht die bloßen
Namen. Ein Fehler, und wieder der Namensraum von `FiniteDimensionalLaws.lean`
(oben ausgeschrieben). Zwei Zeilennummern nachgeführt:
`Matrix.IsSkewAdjoint` (`SesquilinearForm.lean:562`→`:560`) und
`lintegral_liminf_le` (`Add.lean:231`→`:233`). Eine Hypothese ergänzt:
`MeasureTheory.submartingale_of_setIntegral_le` (`Martingale/Basic.lean:281`)
steht wie behauptet unter `[Preorder ι]` (Variablenblock `:48`), verlangt aber
außerdem `[SigmaFiniteFiltration μ ℱ]`, `StronglyAdapted ℱ f` und
Integrierbarkeit jedes `f i`, was die Roadmap verschwieg — derselbe Fehlertyp
wie `innerRegular_isCompact_isClosed_measurableSet_of_finite` im vierten Lauf.
Und ein Zitat präzisiert: `integral_rieszMeasure` von Meilenstein 12 stand nur
mit Verzeichnis da und heißt `RealRMK.integral_rieszMeasure`
(`RieszMarkovKakutani/Real.lean:345`, `namespace RealRMK` ab `:52`), mit
`NNRealRMK.integral_rieszMeasure` und `NNRealRMK.lintegral_rieszMeasure`
(`NNReal.lean:47,56`) daneben. Geprüft und **richtig**:
`Matrix.IsSymm` (`Symmetric.lean:35`), `Matrix.trace_transpose` (`Trace.lean:73`),
`Matrix.trace_mul_comm` (`Trace.lean:158`), `IsStable.locally`
(`LocalProperty.lean:153`), `IsStable.locally_and_iff` (`:161`),
`IsStable.locally_locally_iff` (`:306`, mit `[IsRightContinuous 𝓕]`),
`Submartingale.stoppedProcess` (`OptionalStopping.lean:95`), `maximal_ineq`
(`:144`), `MeasureTheory.tendsto_ae_condExp` (`Convergence.lean:426`) und
`tendsto_eLpNorm_condExp` (`:439`) samt ihren `Integrable.`-Fassungen (`:360`,
`:414`), `IsStoppingTime.measurableSpace_mono` (`Stopping.lean:464`) und
`measurableSpace_le` (`:477`), `seqClosure`/`IsSeqClosed`
(`Topology/Defs/Sequences.lean:55,61`), `Set.Ico_union_Ico_eq_Ico`
(`Order/Interval/Set/LinearOrder.lean:298`) und die Definition der Intervalle
in `namespace Set` von `Order/Interval/Set/Defs.lean` (`:31`--`:94`).

**Offen geblieben.** Von Rückstau 2 die Meilensteine von `MartingaleProblems`,
soweit sie Mathlib **ohne** Pfadangabe zitieren — das sind die meisten
Nennungen, und der heutige Ertrag sagt, dass sie es lohnen. Ganz ungeprüft sind
außerdem die Meilensteine von `WeakConvergence` auf Punkte hin, die Mathlib
inzwischen unter einem dritten Namen führt: dieser Lauf hat die Datei
`ConvergenceInDistribution.lean` gefunden, weil er einem falschen Namen
nachging, nicht weil er systematisch gesucht hätte. Von Rückstau 1 unverändert
die ordnungsdichte Atommenge. Nicht geschehen und mit Absicht: kein Lean
übersetzt (der Worktree hat kein `.lake`), `check.py` nicht gelaufen (am
Manuskript ist nichts geändert), und `cor:atomless` ist weiterhin nicht
verschärft — die Auffälligkeit vom 2026-09-01 steht unverändert oben und gehört
dem Nutzer.

**Als Nächstes zu formalisieren:
`MeasureTheory.ProbabilityMeasure.tendsto_map_of_measure_setOf_continuousAt_eq_one`**
(`WeakConvergence` Meilenstein 2, erster Punkt): für separabel metrische `E`,
`E'`, ein Borel-messbares `h : E → E'`, `μ n → μ` schwach und
`μ {x | ContinuousAt h x} = 1` gilt `(μ n).map h → μ.map h` schwach. Es ruht auf
zwei Dingen, und beide sind seit heute am Quelltext belegt: Mathlibs
Portmanteau, namentlich `MeasureTheory.tendsto_measure_of_null_frontier`
(`Measure/Portmanteau.lean:243`), und die Messbarkeit der Stetigkeitsmenge,
`measurableSet_of_continuousAt`
(`MeasureTheory/Constructions/BorelSpace/Basic.lean:252`). Der stetige Fall,
den es verallgemeinert, ist `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`
(`Measure/ProbabilityMeasure.lean:639`), und die Zufallsvariablenfassung fällt
danach als Korollar durch die drei Felder von `TendstoInDistribution`.

Es ist **jetzt** dran, weil heute alles um es herum weggefallen ist. Bis heute
führte Meilenstein 2 vier Punkte, von denen drei ungeprüft waren; nach diesem
Lauf sind zwei Mathlib, einer ist sein Korollar, und dieser eine ist der ganze
Rest. Getragen wird er von `fact:cmt` mit **tragend 3** — nach `fact:Dcountable`
und `fact:monotoneclass` der am stärksten belastete Fact der Tabelle, und der
einzige der drei, dessen Lücke heute auf eine einzige Aussage zusammengeschmolzen
ist. Reihenfolge, wenn mehrere anstehen: `atomGrid_symm` bleibt der erste, denn
es ruht auf nichts; danach dieser hier vor `IsCadlag`, weil sein
Mathlib-Anschluss aus zwei heute nachgeschlagenen Namen besteht statt aus einer
zu übernehmenden Fremddatei, und weil er `WeakConvergence` — die einzige der
vier Roadmaps ohne Abhängigkeit von den anderen dreien — um einen ganzen
Meilenstein verkürzt.

### 2026-09-01, sechster Lauf — Rückstau 2: die Meilensteine von `MartingaleProblems`

Das Inventar ist geschlossen — keine Zeile steht auf `?` —, also Rückstau. Punkt 1
ist Task 23, ordnungsdichte Atommenge; der elfte Lauf hat ihn mit einer scharfen
Diagnose liegen lassen (die grobe Ausschöpfung ist widerlegt, die Konstante
`C(V,t)` wächst wie `ε^{-(n-2k)}` bei kleinen Massen unten), und der benannte
nächste Schritt dort ist eine neue Paarung anstelle von Cauchy--Schwarz — eine
Beweisidee, kein Nachschlagen. Punkt 2 hatte dagegen eine benannte Restmenge aus
dem fünften Lauf: die Mathlib-Nennungen der Meilensteine von
`MartingaleProblems` **ohne** ausgeschriebenen Pfad. Die sind dieser Lauf.

Geprüft gegen `upstream/master`, frisch geholt: `e076e1ca8f3`, gegenüber
`981fa8f5` des fünften Laufs. Rund dreißig Nennungen aus den Meilensteinen 1, 2,
8, 9, 12 und 13. **Drei Befunde, alle in der Lokalisierungs- und
Stoppzeitschicht, und alle aus einer Wurzel** — die Roadmap las Mathlibs
Stoppzeitapparat schwächer, als er ist.

* **Meilenstein 2 stand auf `[Preorder ι]` und benutzte `Locally`.** Das ist
  nicht hinschreibbar: `ProbabilityTheory.Locally` steht in
  `LocalProperty.lean` innerhalb von `section LinearOrder`, unter
  `variable [LinearOrder ι]` (`:77`) und `variable [OrderBot ι]` (`:88`), mit
  den Bindern `[TopologicalSpace ι] [OrderTopology ι] [Zero E]` (`:93`). Der
  Meilenstein führt jetzt die Stufen (A) und (L), und Meilenstein 7, der nur
  über `Locally` spricht, erbt (L). Einzelheiten bei den Auffälligkeiten.
* **Meilenstein 9 nannte `⊥` ohne `[OrderBot ι]`.** Die Formel des
  Stabilitätspunktes ist wörtlich die von `IsStable` (`:142`), und Mathlib führt
  sie unter `[OrderBot ι]`.
* **`IsQuasiLeftContinuous` typisierte die Stoppzeiten als `Ω → ι`.** Mathlibs
  `IsStoppingTime` ist `Ω → WithTop ι` (`Stopping.lean:76`), und zwar in
  v4.33.1 (`:75`) genauso — keine Versionsdrift, sondern wieder eine nie
  gestellte Suche, diesmal nicht nach einem Namen, sondern nach einer
  **Signatur**. Der Punkt widersprach dabei seiner eigenen Begründung, die vom
  Ereignis `{τ < ∞}` spricht.

Berichtigt sind der Kopf von Meilenstein 2, der Stabilitätspunkt und die
Präambel von Meilenstein 9, die Definition von `IsQuasiLeftContinuous` samt der
Präambel ihres Blocks, und `Suggested.lean`, das denselben Fehler halb gesehen
hatte — es setzte Topologie und Ordnungstopologie und ließ Linearität und Boden
aus. Dort ist `ι` jetzt in einem eigenen `section Local` neu gebunden, damit
keine Deklaration `[Preorder ι]` und `[LinearOrder ι]` zugleich trägt.
**Übersetzt ist nichts; der Worktree hat kein `.lake`.**

**Geprüft und richtig**, damit es nicht noch einmal geprüft wird: die
Argumentreihenfolgen `Locally p 𝓕 X P` und `IsStable 𝓕 p`; `IsStable.locally`
(`:153`), `IsStable.locally_and_iff` (`:161`), `locally_locally_iff` (`:306`,
mit `[IsRightContinuous 𝓕]`); `Matrix.IsSymm` (`Symmetric.lean:35`),
`Matrix.trace_transpose` (`Trace.lean:73`), `Matrix.trace_mul_comm` (`:158`),
`Matrix.vecMulVec` (`Data/Matrix/Mul.lean:616`) und — entgegen dem ersten
Anschein einer Suche, die `protected def Matrix.IsSkewAdjoint` nicht traf —
`Matrix.IsSkewAdjoint` an genau der zitierten Stelle
(`LinearAlgebra/Matrix/SesquilinearForm.lean:560`); `submartingale_of_setIntegral_le`
(`Martingale/Basic.lean:281`), `lintegral_liminf_le` (`Lebesgue/Add.lean:233`),
`eLpNorm_condExp_le_eLpNorm` (`ConditionalExpectation/Real.lean:288`);
`seqClosure` und `IsSeqClosed` (`Topology/Defs/Sequences.lean:55,61`);
`Submartingale.expected_stoppedValue_mono` (`OptionalStopping.lean:43`),
`Submartingale.stoppedProcess` (`:95`, `Filtration ℕ` und reellwertig, wie die
Roadmap sagt), `maximal_ineq` (`:144`),
`Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`
(`Upcrossing.lean:689`), `…mul_lintegral_upcrossings_le_lintegral_pos_part`
(`:799`), `upcrossings_lt_top_iff` (`:781`);
`IsStoppingTime.measurableSpace_mono` (`Stopping.lean:464`) und
`…measurableSpace_le` (`:477`); `Function.leftLim`/`rightLim`
(`LeftRightLim.lean:50,60`); `Set.Ico_union_Ico_eq_Ico`
(`Order/Interval/Set/LinearOrder.lean:298`); `RealRMK.integral_rieszMeasure`
(`RieszMarkovKakutani/Real.lean:345`) und die beiden `NNRealRMK`-Formen
(`NNReal.lean:47,56`) — alle drei genau an den zitierten Zeilen.

Und eine Hypothesenbehauptung der Roadmap, die stimmt: Lévys Aufwärtssatz,
`tendsto_ae_condExp` (`Convergence.lean:426`) und `tendsto_eLpNorm_condExp`
(`:439`), steht in `section L1Convergence`, dessen Variablenblock (`:243`)
`[IsFiniteMeasure μ] {g : Ω → ℝ}` lautet — „stated for a real valued integrand
and a finite measure", wie Meilenstein 9 es sagt.

**Offen geblieben.** Meilenstein 9 ist der längste der Roadmap, und geprüft sind
seine Mathlib-Nennungen, nicht seine Beweiswege. Nicht angefasst sind die
Meilensteine 4, 5, 6, 7, 10 und 11, die kaum Mathlib zitieren; ihre wenigen
Nennungen (`Kernel`, `NormedSpace`, `BoundedContinuousFunction`) sind Typen und
keine Sätze. Damit ist Rückstaupunkt 2 für alle vier Roadmaps durch, und die
Rundenzählung fängt von vorn an — sinnvoll in etwa zwei Wochen.

**Was als Nächstes formalisiert werden soll: `Matrix.trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`**
(`MartingaleProblems` Meilenstein 8): für `A B : Matrix n n ℝ` mit `A.IsSymm` und
`Bᵀ = -B` ist `(A * B).trace = 0`. Es ruht auf nichts als drei Mathlib-Namen, die
dieser Lauf an ihren zitierten Zeilen belegt hat — `Matrix.IsSymm`
(`Symmetric.lean:35`), `Matrix.trace_transpose` (`Trace.lean:73`) und
`Matrix.trace_mul_comm` (`Trace.lean:158`) —, und der Beweis ist drei Zeilen:
`(A*B).trace = (A*B)ᵀ.trace = (Bᵀ*Aᵀ).trace = ((-B)*A).trace = -(A*B).trace`.
Es ist **jetzt** dran, weil es das einzige Ziel der vier Roadmaps ist, dessen
sämtliche Voraussetzungen heute am Quelltext nachgeschlagen sind und dessen
Aussage weder Maß noch Uhr noch Ordnung kennt; die Roadmap nennt es selbst „the
smallest self contained target of this roadmap". Es ist der erste der vier
Matrixpunkte, die den Halbordnungsfall von `duality_of_atomic` tragen — also
Task 23 von der formalisierten Seite her —, und es gehört nach
`Mathlib/LinearAlgebra/Matrix/`, ist damit auch der erste Punkt der ganzen
Planung, der als Mathlib-PR abgehen könnte. Gegenüber `atomGrid_symm`, dem
stehenden Vorschlag der Vorläufe, hat es den Vorzug, keine Induktion zu
brauchen.

### 2026-09-01, siebter Lauf — Task 23, die ordnungsdichte Atommenge: Reduktion, lineares Programm, Energiegesetz

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine, Rückstaupunkt 2 ist
seit dem sechsten Lauf durch und Punkt 3 wartet auf `.lake`; der Lauf ging an
Rückstaupunkt 1, den offenen Rest von Task 23. Das Ausführliche steht in
`Task23/PROTOKOLL.md`, zwölfter Lauf; hier das Gerüst.

**Die Reduktion ist zu Ende geführt.** Aufbauend auf
`duality_defect_eq_integral` (dritter Lauf) ist das volle System für den
Dualitätsdefekt äquivalent zu drei Bedingungen an
`h(a,t) = κ(a,t) − κ(a,0)`, `κ` der antisymmetrische Anteil von `γ`, und die
Behauptung des Manuskripts ist äquivalent zu `h(a,a) = 0` für jedes Atom. Die
Äquivalenz trägt in beide Richtungen: jede Lösung mit nichtverschwindender
Diagonale **ist** ein Gegenbeispiel (`Φ := w/2`, `γ := κ/2`). Damit ist die
Suche nach Beweis und Gegenbeispiel dieselbe lineare Frage.

**Die Frage des elften Laufs ist beantwortet.** Auf Level-Trunkierungen der
dyadischen Uhr ist die Frage ein lineares Programm (`Task23/lp_dense.py`;
die Kontrolle `η = 0` reproduziert den endlichen Satz exakt, auf jedem Level —
die Kodierung ist damit unabhängig gegengeprüft). Befund: die beste **lineare**
Zertifikatskonstante ist exakt `n + ½`, wächst also linear in der Atomzahl —
die vom elften Lauf gesuchte feinere lineare Paarung existiert nicht, in
keiner Norm. Zugleich fällt der maximal erreichbare Defekt für alle drei
gemessenen Massenprofile (`r = 2.5, 4, 8`) gegen null: **auf der dyadischen
Uhr gibt es kein beschränktes Gegenbeispiel**, soweit `J ≤ 7` den Trend trägt.
Beides sitzt auf einem Zwei-Regime-Gesetz
`v ≈ min(κ·η, 0.85·√(BMη))` mit Übergang exakt bei `BM/κ²`.

**Das benannte Ziel daraus:** die **Energieschranke**
`Δ(t)² ≤ C·B·M·η` (`C ≤ 1`) für endliche Kettensysteme mit Residuum `η` und
`|h| ≤ B`. Sie ist quadratisch — die Beschränktheit von `h` geht ein, das ist
der Unterschied zu allen bisherigen Paarungen —, die Numerik sitzt profil- und
levelübergreifend auf ihr, und bewiese man sie, folgte die Dualität per
Ausschöpfung für **jede** rein atomare Uhr endlicher Masse mit beschränktem
`κ`, ordnungsdichte Atommengen eingeschlossen. Der erste Paarungsschritt steht
im Protokoll. Mitgenommen: eine noch zu prüfende Skizze, dass Atommengen, in
denen jedes Atom Nachbarn hat (Typ `ω*`, `ℤ`-Ketten), schon der
Zwei-Diagonalen-Induktion von `atomGrid_symm` zugänglich sind — sie braucht
keinen Boden. Roadmaps und Manuskript sind unverändert; die Skizze und die
Vermutung wandern erst nach einer Nachprüfung dorthin.

**Offen geblieben.** Der Beweis der Energieschranke; die `B`-Hypothese
(Beschränktheit von `κ` gibt das Manuskript nirgends her); die Nachprüfung der
`ω*`-Skizze; und die Geometrieabhängigkeit der Messung (nur dyadisch,
geometrische Levelmassen, `J ≤ 7`).

**Was als Nächstes formalisiert werden soll:
`Matrix.mulVec_one_eq_zero_iff_of_nonneg`** (`MartingaleProblems`
Meilenstein 8, dritter Matrixpunkt): für `A : Matrix n n ℝ` mit `0 ≤ A i j`
ist `A *ᵥ 1 = 0 ↔ A = 0`. Es ruht auf zwei Mathlib-Namen, beide an diesem Lauf
auf master belegt: `Matrix.mulVec` (`Data/Matrix/Mul.lean:698`) und
`Finset.sum_eq_zero_iff_of_nonneg` (als `to_additive` von
`Finset.prod_eq_one_iff_of_one_le'`,
`Algebra/Order/BigOperators/Group/Finset.lean:201`). Es ist jetzt dran, weil
es neben dem Spurlemma des sechsten Laufs der zweite Punkt ist, dessen
sämtliche Voraussetzungen am Quelltext nachgeschlagen sind, weil es die
**einzige** Stelle des Halbordnungsfalls ist, an der die Nichtnegativität der
Massen arbeitet — also genau die Hypothese, deren Tragen der dritte Lauf am
Diamanten belegt hat —, und weil mit ihm und dem Spurlemma zwei der vier
Matrixpunkte stehen, die `dualityDefect_eq_zero_of_nonneg` tragen. Wie das
Spurlemma gehört es nach `Mathlib/LinearAlgebra/Matrix/` und taugt als
eigenständiger Mathlib-PR.

### 2026-09-01, achter Lauf — Task 23: die Energieschranke ist falsch, in jeder Konstante

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine, Rückstaupunkt 2 ist
durch, Punkt 3 wartet auf `.lake`; der Lauf ging an Rückstaupunkt 1, das
benannte Ziel des zwölften Task-23-Laufs: die Energieschranke
$\Delta(t)^2\le C\,B\,M\,\eta$ ($C\le1$) für endliche Kettensysteme. Das
Ausführliche steht in `Task23/PROTOKOLL.md`, dreizehnter Lauf; hier das Gerüst.

**Die Schranke ist widerlegt, nicht bewiesen.** Der zwölfte Lauf hatte als
offen markiert, dass nur dyadisch mit geometrischen Levelmassen gemessen war;
genau dort saß der Fehler. Drei Stufen, alle in exakter Bruchrechnung
verifiziert (`Task23/energy_counterexample.py`, neu; das LP mit freiem
Massenvektor in `Task23/energy_lp.py`, neu, auf den dyadischen Instanzen
bitgleich mit `lp_dense.py`):

* **$C\le1$ fällt bei $n=2$, analytisch.** Massen $(\mu,1)$, $\eta=2\mu^2/3$:
  eine explizite Belegung gibt $\Delta=\mu-\mu^2/3$ und
  $\Delta^2/(BM\eta)\to3/2$. Exakt nachgerechnet: $\mu=1/10$ gibt $841/660$.
* **Keine Konstante überlebt.** Leichtes Präfix $[\mu]^k+[1]$: Verhältnis
  $\approx1.85k$; aufsteigend geometrisch $m_k\propto2^k$: zertifizierte
  Instanzen mit Verhältnis $1513$, $4399$, $5929$, $27589$.
* **Auch masse-lokale Residuenbudgets retten nichts** (aufsteigende Ketten:
  $8273$ bei $n=8$).

Der Mechanismus verkehrt die Lesart des zwölften Laufs: die Sättigung
$|h|=B$ auf den leichten Atomen deckelt den Defekt nicht, sie **trägt** ihn —
ein leichtes Atom unter einem schweren transportiert per Bedingung 3 die
Diagonale $m_2d_2\approx\mu B$ zum Preis $\eta\sim\mu^2B$.

**Was das für Task 23 heißt.** Kein Gegenbeispiel zur Dualität (die Instanzen
haben $\eta>0$; die Rückrichtung der Reduktion gilt nur exakt), aber der
Ausschöpfungsweg über eine profilfreie Schranke ist nach Frobenius (elfter
Lauf) und linear (zwölfter) nun auch quadratisch zu, und damit im Ganzen: die
Relaxation „endliches System plus Slack" ist echt schwächer als „Trunkierung
eines exakten Systems". Festgehalten ist auch, warum die schlimmsten Muster
als Uhren nicht vorkommen: eine ordnungsdichte Uhr mit durchweg aufsteigenden
Massen hätte unendliche Masse. Und die Gegenprobe stützt das: realisierbare
steigende Profile auf der dyadischen Ordnung ($m(k/2^j)=(k/2^j)^p r^{-j}$,
echtes Trunkierungsresiduum $\eta_J=2B\varepsilon_J$) kollabieren weiterhin,
$v_J/M_J$ fällt auf $0.16$ bzw. $0.51$ bei $J=6$, und $v_J^2/(M_J\eta_J)$
bleibt dort überall unter $0.82$ (`Task23/dyadic_adversarial.py`, neu) — die
Verstärkung lebt genau in dem Slack, den keine Trunkierung erzeugt.

**Offen geblieben.** Die $\omega^*$-Skizze (unverändert); und die Frage,
welche Gestalt-Eigenschaft des Trunkierungsresiduums die Verstärkung
ausschließt — sie ist jetzt die eigentliche Frage des ordnungsdichten Falls.

**Was als Nächstes formalisiert werden soll:
`Matrix.mulVec_one_eq_zero_iff_of_nonneg`**, unverändert der Vorschlag des
siebten Laufs, und heute dringlicher: mit dem Ausschöpfungsweg ist der
**bewiesene** Halbordnungsfall (`prop:atomicposet`,
`dualityDefect_eq_zero_of_nonneg` in `MartingaleProblems` M8) der stabile
Kern von Task 23, und dieses Lemma ist sein einziger Punkt, an dem die
Nichtnegativität der Massen arbeitet. Die Voraussetzungen sind unverändert
belegt; `Matrix.IsSymm` (`LinearAlgebra/Matrix/Symmetric.lean:35`),
`Matrix.mulVec` (`Data/Matrix/Mul.lean:698`) und `Matrix.trace_mul_comm`
(`LinearAlgebra/Matrix/Trace.lean:158`) sind an diesem Lauf erneut auf
upstream/master geprüft.

### 2026-09-01, neunter Lauf — Task 23: der intervallendliche Kettenfall ist bewiesen

Die Tabelle hat kein `?`, vorrangige Aufgaben stehen keine; der Lauf ging an
Rückstaupunkt 1 und dort an den ersten der zwei Wege, die der dreizehnte
Task-23-Lauf hinterließ: **die $\omega^*$-Skizze des zwölften Laufs
nachrechnen**. Sie ist nachgerechnet und Satz; das Ausführliche steht in
`Task23/PROTOKOLL.md`, vierzehnter Lauf, hier das Gerüst.

**Bewiesen:** für jede rein atomare Uhr, deren Atome unter $t^*$ paarweise
vergleichbar und **intervallendlich** sind — je zwei Atome schließen nur
endlich viele ein —, gilt $\Phi(t^*,0)=\Phi(0,t^*)$, in beiden Konventionen,
ohne Hypothese über die Existenz der Integrale in \eqref{eq:incrementrep}
hinaus, und schärfer die volle Symmetrie von $\Phi$. Das enthält
`prop:atomicdual` und erfasst neu die Ordnungstypen $\omega$, $\omega^*$ und
$\zeta$ — Atome, die sich bei $0$, an inneren Punkten oder bei $t^*$ häufen.
Der Beweis: die Zwei-Diagonalen-Induktion von `lem:atomgrid` braucht weder
Boden noch Deckel (nur endliche Abstände aller Indexpaare — genau die
Intervallendlichkeit), und die Ränder kommen als Schwänze der absolut
konvergenten Atomsummen, die die Existenz der Integrale ohnehin ist.

**Drei Befunde neben dem Satz.** Erstens ist die wörtliche Hypothese der
Skizze — „jedes Atom hat beidseits ein Nachbaratom" — echt schwächer als das,
was ihre eigene Induktion braucht; zwei $\zeta$-Ketten übereinander trennen
beide Bedingungen, und dort endet die lokale Algebra nachweislich
(`Task23/neighbor.py`, Test X: blockintern erzwungen, Kreuzpaare frei).
Zweitens war die **$B$-Hypothese nie nötig**: der offene Punkt 2 des zwölften
Laufs (Beschränktheit von $\kappa$) fällt für den Kettenfall, weil dominierte
Konvergenz mit der vorausgesetzten Integralexistenz die Randlimiten trägt.
Drittens, mechanisch gegengeprüft: die Randfreiheit der Induktion an
endlichen Ketten ohne jede Randrelation, $M=2..7$, drei Massenvektoren, beide
Konventionen, exakt rational und symbolisch (`neighbor.py`, Test R, rc=0).

**Eingetragen:** `atomGrid_symm_int` und `duality_of_atomic_intervalFinite`
in `MartingaleProblems` Meilenstein 8, samt korrigierter Reichweitenangabe
von `duality_of_atomic`; Zwischenstand an Rückstaupunkt 1; Protokollabschnitt
mit Beweis und Sackgassennachtrag. Das Manuskript ist nicht angefasst.

**Offen geblieben.** Die diskrete, nicht intervallendliche Kette (kleinste
Instanz: zwei $\zeta$-Ketten) und die in sich dichte Atommenge; beide hängen
am Überqueren eines Häufungspunkts, und der Sackgassennachtrag sagt, wo dort
anzusetzen ist (Schwanzrelationen, nicht feinere Induktion).

**Was als Nächstes formalisiert werden soll: `prop:atomicdual` im Manuskript
auf den intervallendlichen Fall heben.** Die Aussage: Atome unter $t^*$
paarweise vergleichbar und intervallendlich, Konklusion und
Beweislosigkeit an Regularität wie bisher. Sie ruht auf `lem:atomgrid` in der
$\mathbb Z$-Fassung (`atomGrid_symm_int`, Beweis wörtlich derselbe) und zwei
Schwanzlimiten aus der Integralexistenz; Beweis vollständig und verifiziert
im PROTOKOLL, vierzehnter Lauf. Sie ist jetzt dran, weil sie die Statuszeile
„purely atomic, atoms a chain" von „lokal endlich" auf die wahre Reichweite
der Induktion bringt und den offenen Kern von Task 23 auf zwei benannte
Restfälle verengt. Der Lauf, der sie einträgt, passt auch
`rem:atomicdual` („What is not covered") und die Statustabelle von
`rem:atomsnotchange` an und lässt `check.py` laufen.

### 2026-09-02, erster Lauf — vorrangige Aufgabe: Teil (a) erledigt, Teil (b) begonnen

Der Lauf ging ganz an die am 2026-09-01 gestellte vorrangige Aufgabe
(mengen-indizierte Lévy-Literatur, Summierbarkeit); die Tabelle hat kein `?`
und blieb unberührt.

**Teil (a) ist erledigt: `Facts/SETINDEXED.md`.** Alle vier Fragen sind am
Text beantwortet — Herbin–Merzbach (SPA **123** (2013), arXiv:1108.0873) über
die ar5iv-Fassung in fünf gezielten Auszügen, Pedersen–Sato (J. Math. Soc.
Japan **56** (2004)) direkt am PDF; Bass–Pyke und Adler–Feigin nur
bibliographisch. Die Kurzfassung: (1) ihre fünf Axiome an $\mathcal A$
verteilen sich auf \eqref{T1} ($\cap$-Abschluss), \eqref{T2b}/\eqref{T1p}
(separability from above — die auffälligste Entsprechung, gemeinsamer Vorfahr
\EK{} §2.8) und drei rein topologische ohne Gegenstück; unsere
Voraussetzungsfläche ist echt kleiner, wofür wir ihre Existenz-, Markov- und
Pfadtheorie nicht bekommen. Ihre $m$-Stationarität braucht keinerlei Algebra
auf dem Index (Gleichheit von $m$-Massen statt Verschiebung) — unsere
Verschiebungsinvarianz braucht \eqref{T4}; dafür trägt unsere Uhr auch
nicht-stationäre Kompensatoren. (2) **Negativbefund, und das ist die
Hauptantwort:** Dualität, bivariate Zuwachsdarstellungen mit gemeinsamer
Dichte, Martingalprobleme, Generatoren — nichts davon kommt vor; das
nächstliegende Objekt ist das Übergangssystem $Q_{U,V}$ mit
$m$-Homogenität über $m(V\setminus U)$, ein Kern, keine Darstellung.
\eqref{eq:incrementrep} und §\ref{ssec:antidiag} haben dort kein Vorbild.
(3) Die Flow-Projektion ist der Zeitwechsel von `cor:atomless`
($\theta(t)=m[f(t)]$ ist $Q$), setzt Invertierbarkeit von $\theta$ voraus und
ihre Prozessklasse schließt Atome von $m$ über die stochastische Stetigkeit
aus (unsere Folgerung, als solche markiert) — für den ordnungsdichten Fall
von Task 23 gibt sie nichts her, was `cor:atomless` nicht ist. Der Bedarf an
*simple* statt *elementary* flows — ihr eigener Kommentar: „the embedding in
$\mathcal A(u)$ is the key point" — ist wörtlich `rem:fddnochain`. (4) Am
nächsten an einer Präordnung: Pedersen–Sato, Kegelordnung
$s\le_Kt\iff t-s\in K$ — exakt \eqref{T0}+\eqref{T4} —, mit Negativsätzen
der Sorte `rem:chainonly` (keine $S_d^+$-Brownsche Bewegung, Eindeutigkeit
fällt); daneben Rajput–Rosiński (δ-Ring, keine Ordnung) als Anschlusspunkt
für eine etwaige Existenztheorie. Der **Vorschlag für die
Manuskriptbemerkung** samt fünf Bibliographieeinträgen steht am Ende von
`SETINDEXED.md`; das Manuskript ist nicht angefasst.

**Teil (b) ist begonnen: `Task23/summable_lp.py`, Protokollabschnitt
fünfzehnter Lauf.** Die Frage der Läufe 11–13 ist neu gestellt als Frage (S)
über geschachtelten Trunkierungen einer festen summierbaren Uhr, mit dem
echten Residuum $|R_J(s,t)|\le B(\varepsilon(s)+\varepsilon(t))$ aus der
fehlenden Masse unterhalb jedes Gitterpunkts. Gemessen auf fünf Uhren,
darunter erstmals **langsame Schwänze** ($\varepsilon_J\sim1/J$ und
$\sim1/\log J$, wo die profilfreie lineare Schranke des zwölften Laufs
nutzlos ist): $v_J$ kollabiert überall, empirisch als
$v_J\approx c\sqrt{M\varepsilon_J}$ mit je Uhr stabilem $c\le1.08$ — die für
freie Systeme in jeder Konstante widerlegte Energieform kehrt auf echten
Trunkierungen als Gesetz zurück. Uniform über Uhren bleibt sie falsch
(geformter Zwei-Atom-Zeuge: $\to3$; leichtes Präfix: $\sim0.77k$), aber
jeder Zeuge ist eine einzelne Stufe, und die Massenbilanz sagt, warum
anhaltender Gewinn Summierbarkeit widerspricht (Lücke: Interferenz der
Skalen, benannt). Offen und im Protokoll präzisiert: der Interferenztest und
die Stufenpaar-Rekursion; die $B$-Hypothese für die dichte Menge bleibt
unberührt. Die Aufgabe steht mit Zwischenstand in `scripts/facts_prompt.md`.

**Was als Nächstes formalisiert werden soll: `atomGrid_symm`, in Lean.** Die
Aussage steht wörtlich in `MartingaleProblems` Meilenstein 8: endliches
Gitter, Massen $m_i\ne0$, Kreuzrelation \eqref{eq:atomgrid}, Konklusion
$\Phi(i,j)=\Phi(j,i)$. Sie ruht auf nichts als Induktion über zwei Diagonalen
(`lem:atomgrid`, Beweis vollständig im Manuskript) und ist jetzt dran, weil
seit dem vierzehnten Lauf die gesamte atomare Dualitätsschicht — 
`duality_of_atomic`, `duality_of_atomic_intervalFinite`, über
`atomGrid_symm_int` — auf ihr steht: sie ist der erste Lean-taugliche
Baustein von Task 23, hat keinerlei Maßtheorie im Beweis und macht die
$\mathbb Z$-Fassung zu einer Übertragung statt einer Neuentwicklung. Daneben
bleibt der Manuskriptvorschlag des Vortagslaufs (Hebung von
`prop:atomicdual` auf intervallendlich) stehen und wartet auf den Nutzer.

### 2026-09-02, zweiter Lauf des Tages — vorrangige Aufgabe, Teil (b): der Interferenztest, und (S) ist falsch

Kein Fact bearbeitet; der ganze Lauf gehört der vorrangigen Aufgabe
(Summierbarkeit, Teil b), wie vom Auftrag verlangt. Ergebnis in einer Zeile:
**die Frage (S) des fünfzehnten Laufs ist widerlegt, mit exaktem
Zertifikat**, und der Befund reicht tiefer, als die Frage gestellt war.

* **Der Interferenztest ist gebaut und beantwortet** (`Task23/interference.py`,
  `interference_certificate.py`, `interference_separable.py`;
  Protokollabschnitt sechzehnter Lauf). Die hierarchische Motor-Uhr — Block
  $i$ = schweres Atom $\lambda_i$ über einem Vier-Präfix der Masse
  $\lambda_i$, $\lambda_{i+1}=\lambda_i/4$, Gesamtmasse $16/15$, Typ
  $\omega^*$, intervallendlich — hält $v_J$ von $0$ weg: zertifiziert
  $v_8\ge0.144$ bei $E_8=1.6\cdot10^{-5}$ (Bruchrechnung, Nenner $10^9$).
  Die Skalen **teilen** sich die fehlende Masse; die
  Massenbilanz-Heuristik und die Kontraktions-Deutung des fünfzehnten Laufs
  sind als Sackgassen protokolliert.
* **Die Gestalt des Residuums (Punkt 3 des dreizehnten Laufs) ist erstmals
  ins LP eingebaut** — separables $\varphi(s)+\varphi(t)$, $|\varphi|\le BE$ —
  und rettet den Kollaps nicht: $v_i^{\rm sep}=\tfrac1{24}+E_i\downarrow
  \tfrac1{24}$, exakt auf den Stufen 3–10, Gewinn stabil in Block 1.
* **Die Kollision, und sie ist der eigentliche Ertrag:** die Uhr ist
  intervallendlich, die Dualität gilt auf ihr also nach dem Satz des
  vierzehnten Laufs — die LP-Relaxation ist damit als Beweisvehikel für
  aufsteigende Strukturen **bewiesen zu schwach**, ein Kollaps-Argument
  à la (S) kann für den ordnungsdichten Fall nicht der Weg sein. Zugleich
  scheint ein Kompaktheitsargument aus den Messwerten ein exaktes $h^*$ mit
  $\Delta^*=\tfrac1{24}$ zu liefern; die drei Verdächtigen (Äquivalenz des
  zwölften Laufs im Unendlichen — sie ankert am Bodenatom, das $\omega^*$
  nicht hat —, das Kompaktheitsargument selbst, der Zusammenbau des
  vierzehnten Laufs) stehen gereiht im Protokoll. Die Adjudikation ist die
  benannte Aufgabe des nächsten Laufs.
* Offen blieb: nichts von der gestellten Aufgabe; die Stufenpaar-Rekursion
  hat sich durch das Ergebnis erledigt (keine Kontraktion vorhanden).

**Was als Nächstes formalisiert werden soll: `atomGrid_symm`, in Lean —
unverändert, aber mit neuer Dringlichkeit.** Aussage wie im Bericht des
Vortagslaufs (`MartingaleProblems` Meilenstein 8: endliches Gitter,
$m_i\ne0$, Kreuzrelation, Konklusion $\Phi(i,j)=\Phi(j,i)$; ruht allein auf
der Zwei-Diagonalen-Induktion `lem:atomgrid`). Jetzt dran, weil sie mit
`atomGrid_symm_int` der mechanische Schiedsrichter für Verdächtigen 3 der
Kollision ist: eine Lean-geprüfte Fensterstarrheit samt
$\mathbb Z$-Übertragung macht den intervallendlichen Satz maschinenfest, und
dann liegt die Lücke beweisbar bei der Äquivalenz oder beim
Kompaktheitsargument.

### 2026-09-02, dritter Lauf des Tages — vorrangige Aufgabe abgeschlossen: die Adjudikation, und „(S) ist falsch" ist zurückgenommen

Kein Fact bearbeitet; der Lauf gehört der Adjudikation der Kollision, der
benannten Aufgabe des Vortagslaufs. Sie ist entschieden, durch Beweis, und
die vorrangige Aufgabe ist damit ganz erledigt (im Runner-Prompt gestrichen,
Abschluss dort eingetragen). Ergebnis in einer Zeile: **das exakte
$h$-System 1–3 ist auf jeder intervallendlichen Kette starr; der Fehler lag
im Kompaktheitsargument, in dessen extrapolierter Prämisse
$\lim v_i=\tfrac1{24}$; tatsächlich gilt $v_i\to0$, nur praeasymptotisch
unsichtbar.** Einzelheiten:

* **Der Beweis** (Protokoll, siebzehnter Lauf): $\widehat w(s,t):=
  H(s,t)+\Delta(t)-\Delta(s)$ erfüllt exakt die Kreuzrelation $(\ast)$ des
  vierzehnten Laufs — Erstschritt definitorisch, Zweitschritt aus Bedingung
  3 zweimal, Antisymmetrie von $\kappa(a,t):=h(a,t)-h(a,a)$ aus Bedingung 2.
  $h$- und $\Phi$-System sind im antisymmetrischen Sektor **isomorph**;
  Induktion und Schwanzlimiten des vierzehnten Laufs geben $\Delta\equiv0$.
  Der Bodenatom-Verdacht gegen die Äquivalenz des zwölften Laufs war
  unbegründet; ihre Rückrichtung braucht $\kappa(a,0)=-h(a,a)$ statt $0$
  (im endlichen Fall unsichtbar).
* **Die Fensterschranke** macht den Kollaps quantitativ:
  $v_i\le2B\,M_{<u_l}+(K_l+2B)E_i$ mit stufenunabhängigem $K_l$; die
  Summierbarkeit liefert $M_{<u_l}\to0$ — genau die im Aufgabenteil (b)
  vermutete Rolle der endlichen Variation. Die $K_l$ sind Produkte von
  Massenverhältnissen ($\ge10^4$ ab Stufe 9, roh $\lesssim10^{48}$); das
  erklärt das exakte Plateau $\tfrac1{24}+E_i$ vollständig.
* **Mechanisch verifiziert** (`Task23/adjudicate.py`): die Beweisalgebra am
  LP-Optimum — $(\ast)$-Defekt exakt $-m_i(\varphi(u_{j+1})-\varphi(u_j))$
  bis $10^{-10}$, erzwungene Identität $h(u_j,u_{j+1})=h(u_j,u_j)$ bis
  $10^{-8}$ —, die Sättigung der Randterme, und die Stufen 10–14 (Plateau
  hält, wie vom Beweis erlaubt). Nebenbefund: HiGHS' Presolve meldet auf der
  reformulierten Fassung fälschlich „Unknown"; `presolve=False` behebt es.
* **Zurückgenommen:** der Kernbefund des Vortagslaufs „(S) ist falsch". Die
  Motor-Uhr ist kein Gegenbeispiel — ihre endlichen Zertifikate bleiben
  richtig und sagen über den Limes nichts. Für intervallendliche Uhren mit
  stabilisierenden Fenstern ist (S) wahr; offen bleibt (S) genau für
  ordnungsdichte Atommengen, wie der ordnungsdichte Kern selbst.
* Offen blieb: nichts von der gestellten Aufgabe. Das Manuskript ist
  unverändert (der Satz betrifft nur die Task-23-interne Reduktion; der
  manuskriptseitige intervallendliche Satz steht seit dem vierzehnten Lauf).

**Was als Nächstes formalisiert werden soll: `atomGrid_symm`, in Lean —
zum dritten Mal benannt, und jetzt ohne Konkurrenz.** Aussage unverändert
(`MartingaleProblems` Meilenstein 8: endliches Gitter, $m_i\ne0$,
Kreuzrelation $(\ast)$, Konklusion $\Phi(i,j)=\Phi(j,i)$; ruht allein auf
der Zwei-Diagonalen-Induktion `lem:atomgrid`). Jetzt dran, weil der
siebzehnte Lauf gezeigt hat, dass **drei** Resultate wörtlich auf dieser
einen Induktion ruhen — der intervallendliche Satz, die Starrheit des
$h$-Systems und die Fensterschranke —, und die LP-Schiene als
Evidenzquelle ausgeschöpft ist: was Task 23 noch weiterbringt, ist
maschinengeprüfte Algebra, nicht Messung.

### 2026-09-02, vierter Lauf des Tages — Rückstau 1 / Task 23, achtzehnter Lauf: die Viertelgitterfrage der zwei $\zeta$-Ketten

Kein Fact bearbeitet: die Tabelle ist vollständig belegt, die vorrangige
Aufgabe erledigt, Rückstaupunkt 2 erst in etwa zwei Wochen wieder fällig,
Punkt 3 ohne `.lake` nicht übersetzbar — also Rückstaupunkt 1, der
ordnungsdichte Kern von Task 23, an seiner kleinsten Instanz, der
Viertelgitterfrage der zwei $\zeta$-Ketten (siebzehnter Lauf).

Zur Laufgeschichte, weil sie sonst nirgends stünde: die zwei Läufe zwischen
dem dritten Lauf des Tages und diesem (07:23 und 10:23 UTC) wurden von der
Nutzungsgrenze abgeschnitten (`STATUS.md`: „limit-teilarbeit" bzw. keine
inhaltliche Arbeit). Übrig blieb `Task23/zeta_cross.py` mit Proben (a)–(e)
und Verweisen auf nie geschriebene Sätze. Dieser Lauf hat die Beweise
selbst geführt, das Skript um Probe (f) ergänzt (läuft, alle Proben exakt)
und den Protokolleintrag „achtzehnter Lauf" geschrieben. Befunde, je mit
Beweis im Protokoll:

* **Normalform:** das Viertelgittersystem (Q) ist eine kommutierende
  Evolution $F(\cdot,j{+}1)=(I+\nu_jL)F(\cdot,j)$ mit **einem** festen
  Operator $(Lg)_i=(g_{i+1}-g_i)/\mu_i$; die Nordevolution ist die
  Operatorfassung des Geschlecht-0-Produkts
  $\Pi_j(c)=\prod_{j'\ge j}(1+c\nu_{j'})$, die Summierbarkeit die endliche
  Horizontzeit. Die Frage (V) ist damit eine Quasianalytizitätsfrage:
  Injektivität von $\Pi_j(L)$ auf westabfallenden Zeilen.
* **Bewiesen:** (Q) ⟺ $(\ast)$ + Westlimes des Flusses $=0$ + Nordabfall
  (Lemma 1, Hakenkonstanz); ohne Summierbarkeit ist (V) **falsch**
  (Proposition 2, Buckel $g(i+j)$ bei Massen $\equiv1$); jeder
  Einzelschritt $I+\nu_jL$ ist injektiv (Proposition 3); **keine endliche
  Superposition separabler Moden** löst (Q) (Theorem 4, Momentenschritt
  plus Vandermonde — der Nordabfall wird dafür nicht einmal gebraucht);
  reelle Spektralmaße haben lauter verschwindende Momente und sterben bei
  exponentiellem Abfallspielraum (Proposition 5).
* **Sackgasse mit Beleg:** die exakte Energieidentität (Probe (f)) trägt
  den indefiniten Faktor $\mu_i\nu_j(\nu_j-\mu_i)$ — denselben wie der
  Dispersionsdefekt des charakteristischen Ansatzes (Probe (e)); separable
  Gewichte reparieren das Vorzeichen nicht.
* **Offen bleibt (V) selbst**, jetzt scharf lokalisiert: für geometrische
  Massen wachsen die Modenprodukte nur wie $e^{O((\log r)^2)}$, zulässige
  Spektralmaße dürfen also quasipolynomial abfallen, und dort existieren
  Maße mit lauter Nullmomenten — ob eines die ganze
  $\{\lambda_j\}$-Familie annihiliert, ist eine Vollständigkeitsfrage, in
  die die Massen über ihre Zählfunktion eingehen. Wege (α)
  Spektraldarstellung/Carleman und (β) Gegenbeispiel bei lakunären Massen
  stehen im Protokoll.

Offen blieb sonst: nichts Neues; das Manuskript ist unverändert, die
Roadmaps auch (die Viertelgitterfrage ist Task-23-intern, bis sie
entschieden ist). Der Rückstaupunkt 1 hat einen neuen Zwischenstand.

**Was als Nächstes formalisiert werden soll: unverändert `atomGrid_symm`,
in Lean** (`MartingaleProblems` Meilenstein 8; Aussage und Begründung wie
im dritten Lauf des Tages — jetzt zum vierten Mal benannt). Dieser Lauf
verstärkt die Begründung: auch die Viertelgitteranalyse ruht mit Lemma 1
und Theorem 4 auf exakter Gitteralgebra derselben Bauart, und jede
maschinengeprüfte Fassung der Zwei-Diagonalen-Induktion ist
wiederverwendbar, sobald (V) entschieden ist.

### 2026-09-02, fünfter Lauf des Tages — Task 23, neunzehnter Lauf: Weg (β) ist zu, durch Beweis

Kein Fact bearbeitet: Tabelle vollständig belegt, keine vorrangigen
Aufgaben, Rückstaupunkt 2 erst in etwa zwei Wochen fällig, Punkt 3 ohne
`.lake` nicht übersetzbar — also Rückstaupunkt 1, die Viertelgitterfrage
(V), an den zwei Wegen des achtzehnten Laufs. (Der Lauf 16:23 UTC dazwischen
wurde von der Nutzungsgrenze abgeschnitten und hat nur `STATUS.md` berührt.)

Ergebnis in einer Zeile: **die „Vollständigkeitsfrage", die der achtzehnte
Lauf als offenen Kern von Weg (β) benannt hat, ist keine — in der
zulässigen Klasse folgt die Annihilation der ganzen Modenfamilie doch aus
den Momenten, und die Spektralschiene stellt nur die Null dar.** Der
Mechanismus ist eine Zeile: die Geschlecht-0-Produkte $\beta^c_i$,
$\lambda^c_j$ haben nichtnegative Taylorkoeffizienten, und die
Zulässigkeitsschranke $e^{\Phi_\mu+\Phi_\nu}$ von Proposition 5 ist genau
ihre Koeffizienten-Majorante — also paart die Taylorreihe jeder Mode gegen
jedes zulässige $\sigma$ absolut, und Fubini rechnet jede Paarung aus den
Momenten aus. Einzelheiten:

* **Theorem 6** (Protokoll, neunzehnter Lauf): für zulässiges reelles
  $\sigma$ — es genügt $\int e^{\Phi_\mu+\Phi_\nu}\,d|\sigma|<\infty$, die
  Polynomgewichte von Proposition 5 sind entbehrlich — sind äquivalent:
  Nullmomente ⟺ Annihilation aller $\lambda_j$ ⟺ aller $\beta_i$ ⟺ jeder
  ganzen Funktion mit zulässiger Koeffizienten-Majorante. Der Beweis ist
  der Momentenschritt des achtzehnten Laufs plus seine Rückrichtung
  (Fubini über die nichtnegativen Koeffizienten).
* **Korollar:** jeder zulässige reelle Spektralkandidat, der (Q) löst, ist
  identisch null — der Exponentialspielraum von Proposition 5.2 war für
  diese Konklusion entbehrlich. Die drei (β)-Bedingungen sind äquivalent
  zu den Nullmomenten, von jedem Stieltjes-Maß erfüllt und stellen nur
  $x\equiv0$ dar; **Weg (β) ist für jede summierbare Massenfolge leer**,
  und die Denjoy–Carleman-Spekulation des achtzehnten Laufs
  (Massenzählfunktion) ist zurückgenommen.
* **Mechanisch verifiziert:** `Task23/spectral_closed.py` (mpmath,
  50 Stellen, Gauß–Legendre je Halbperiode, rc=0). Geometrische Massen,
  Stieltjes-Maß $e^{-t^2/(2s^2)}\sin(2\pi t/s^2)\,dt$ unter $c=e^t$: alle
  Momente, alle $\lambda_j$, $\beta_i$, das $13\times13$-Gitter
  $\int\beta_i\lambda_j\,d\sigma$ und die übrigen (β)-Bedingungen
  verschwinden relativ auf $<10^{-47}$ bei $\|\sigma\|_{TV}=0.94$; die
  Kontrollfunktion $e^{-3c}$ außerhalb der Klasse paart auf
  $5\cdot10^{-13}$ — 37 Größenordnungen Trennung. Es ist die Majorante,
  die tötet, nicht die Kleinheit von $\sigma$.
* Offen blieb: (V) selbst, jetzt ohne Gegenbeispielweg in der
  Spektralklasse. Was bleibt, ist Weg (α), und der ist leichter geworden:
  es genügt, jeder westabfallenden Lösung irgendeine zulässige reelle
  Spektraldarstellung zu verschaffen (quasipolynomialer Abfall reicht),
  oder ein Carleman-Argument direkt an der Evolution. Ehrliche Grenze wie
  bei Proposition 5: bedingt konvergente Darstellungen und komplexe
  Träger bleiben außerhalb des Satzes.

Das Manuskript und die Roadmaps sind unverändert (die Viertelgitterfrage
ist Task-23-intern); Rückstaupunkt 1 hat einen neuen Zwischenstand.

**Was als Nächstes formalisiert werden soll: unverändert `atomGrid_symm`,
in Lean** (`MartingaleProblems` Meilenstein 8: endliches Gitter,
$m_i\ne0$, Kreuzrelation $(\ast)$, Konklusion $\Phi(i,j)=\Phi(j,i)$; ruht
allein auf der Zwei-Diagonalen-Induktion `lem:atomgrid` — zum fünften Mal
benannt). Dieser Lauf ändert an der Begründung nichts und verstärkt sie:
die analytische Schiene von Task 23 verengt sich Lauf um Lauf auf exakte
Gitteralgebra — Theorem 6 ist reine Reihenrechnung, und was von (V) offen
ist, hängt an derselben Kreuzrelation, deren endliche Fassung
`atomGrid_symm` ist. Maschinengeprüfte Algebra ist der nächste echte
Zugewinn, nicht weitere Messung.

### 2026-09-03 — Task 23, zwanzigster Lauf: Weg (α) trägt, (V) ist für quadrantensummierbare Lösungen bewiesen, die zwei $\zeta$-Ketten sind in der beschränkten Klasse geschlossen

Kein Fact bearbeitet: Tabelle vollständig belegt, keine vorrangigen
Aufgaben, Rückstaupunkt 2 erst in etwa zwei Wochen fällig, Punkt 3 ohne
`.lake` nicht übersetzbar — also Rückstaupunkt 1, die Viertelgitterfrage
(V), am einzig verbliebenen Weg (α).

Zur Laufgeschichte, zum dritten Mal dasselbe Muster: die zwei Läufe 02:23
und 08:23 UTC wurden von der Nutzungsgrenze abgeschnitten (rc=1); der
zweite hinterließ `Task23/quarter_transform.py`, ein Prüfskript, das auf
einen nie geschriebenen „Beweis des zwanzigsten Laufs" verweist und wegen
eines Syntaxfehlers in einer toten Platzhalterzeile nicht einmal lief.
Dieser Lauf hat den Fehler behoben, die Beweise selbständig geführt und
den Protokolleintrag geschrieben, den das Skript voraussetzt. Befunde, je
mit Beweis in `Task23/PROTOKOLL.md`, zwanzigster Lauf:

* **Theorem 9, unbedingt:** die W-Transformation
  $a\mapsto\sum_ia_iW^c_i$ mit den Geschlecht-0-Schwänzen
  $W^c_i=\prod_{i'>i}(1+c\mu_{i'})$ ist auf $\ell^1(\mathbb Z)$ injektiv
  (Fußpunktzerlegung, Phragmén–Lindelöf für Typ 0, Liouville,
  Konstantenterm-Extraktion).
* **Theorem 10:** (V) gilt unter der Quadrantensummierbarkeit (H)
  $\sum_{j\ge j_0}\nu_j\sum_i\mu_i|x_{ij}|<\infty$ — die Transformierte
  $G_j(c)=\sum_i\mu_iF(i,j)W^c_i$ ist ganz vom Typ 0, erfüllt exakt die
  Nordrekursion, ist rechts beschränkt, fällt reell, ist also identisch
  null; Theorem 9 holt $x\equiv0$ zurück. (H) steht genau am Nordlimes
  und an der Reihe der Identität I; das liegengebliebene Skript sprach
  sie nirgends aus — sie zu finden und auszusprechen war die eigentliche
  Prüfarbeit dieses Laufs.
* **Korollar 11:** jede beschränkte Lösung von (Q) verschwindet, und über
  die Reduktion des siebzehnten Laufs ist die Dualität für zwei
  gestapelte $\zeta$-Ketten in der Klasse $|h|\le B$ **geschlossen** —
  der Klasse, in der sämtliche LPs, Zertifikate und Messungen des
  zwölften bis siebzehnten Laufs liefen. Die Identität I ist das erste
  Argument von Task 23, das einen Häufungspunkt überquert.
* **Sackgasse mit Beleg:** die gespiegelte $\nu$-seitige Transformation
  braucht dieselbe gemeinsame Summe wie die $\mu$-seitige — (H) ist die
  Grenze der Methode, nicht der Seitenwahl.

`Task23/quarter_transform.py` läuft exakt (rc=0, Proben (A)–(E)); der
Docstring nennt jetzt (H) und die Satznummern. Offen bleibt (V) in der
nackten Klasse (nur zeilen-/spaltenweise absolute Konvergenz; benannte
Angriffe: Bootstrap oder eine Paarung ohne gemeinsame Summe) und der
Cantor–Bendixson-Weg jenseits der zwei Ketten. Das Manuskript ist
unverändert. Die Roadmaps auch, und das ist eine begründete Entscheidung:
ein Eintrag der (H)-Fassung neben `duality_of_atomic_intervalFinite`
stünde schief, solange die Manuskriptklasse nur absolute Konvergenz
liefert; er ist zurückgestellt, bis (V) in der nackten Klasse entschieden
ist, und der Nutzer kann das umstoßen (Protokoll, „Was offen bleibt").

**Was als Nächstes formalisiert werden soll: unverändert `atomGrid_symm`,
in Lean** (`MartingaleProblems` Meilenstein 8: endliches Gitter,
$m_i\ne0$, Kreuzrelation $(\ast)$, Konklusion $\Phi(i,j)=\Phi(j,i)$; ruht
allein auf der Zwei-Diagonalen-Induktion `lem:atomgrid` — zum sechsten
Mal benannt). Die Begründung wird wieder stärker: der erste Beweis, der
einen Häufungspunkt überquert, ruht mit den Proben (A)–(C) auf exakt der
Gitteralgebra, deren endliche Fassung `atomGrid_symm` ist, und sein
klassischer Rest (Phragmén–Lindelöf, Liouville) liegt in Mathlib bereits
vor — am Quelltext geprüft (upstream/master):
`PhragmenLindelof.horizontal_strip`
(`Mathlib/Analysis/Complex/PhragmenLindelof.lean:113`; die
Halbebenen-Fassung für Typ 0 selbst steht dort nicht, die Datei führt
Streifen und Quadranten) und `Differentiable.exists_eq_const_of_bounded`
(`Mathlib/Analysis/Complex/Liouville.lean:128`). Das ist Anschluss für
den späteren Ausbau, kein neues Nahziel.

### 2026-09-03 — Task 23, einundzwanzigster Lauf: (H) war nie die Grenze, und die Manuskriptklasse liefert die Hypothese

Das Inventar ist geschlossen (keine Zeile mit `?`), der Rückstau führt als
ersten Punkt Task 23; dieser Lauf hat dort weitergearbeitet und **nichts** am
Inventar, an den Facts oder am Manuskript geändert.

**Befund.** Der zwanzigste Lauf schloss, (H) — die
$\mu\otimes\nu$-Integrierbarkeit von $|x|$ auf dem Nordquadranten — sei „die
Grenze der Transformationsmethode". Das ist zurückgenommen. Der Beweis von
Theorem 10 benutzt (H) an genau drei Stellen und dort nur durch zwei
Folgerungen: eine in $j$ gleichmäßige summierbare Majorante für den
Nordlimes, und $\sum_{j\ge j_0}\nu_j|R_j|<\infty$ für die Beschränktheit
rechts. Abgezogen ist das die Bedingung **(U)** = *Straffheit nach Norden*
plus *Nordsummierbarkeit der Zeilensummen*, und **Theorem 12** (Protokoll,
einundzwanzigster Lauf) schließt daraus $x\equiv0$ — mit Theorem 9
unverändert, der Fortsetzung nach Süden als eigenem hypothesenfreien
Schritt, und ohne die Identität I, die ein Koeffizientenvergleich in
(B$\infty$) ersetzt.

**Warum das mehr ist als eine Umformulierung.** (U) hat zwei
unvergleichbare hinreichende Kriterien. Das eine ist (H), womit Theorem 10
Korollar wird. Das andere ist $\sup_{i,\,j\ge j_0}|F(i,j)|<\infty$, und $F$
ist der **Dualitätsdefekt** $\Phi(s,t)-\Phi(t,s)$: gefordert ist damit die
Beschränktheit des **Wertes** $\Phi$, nicht der **Dichte** $\gamma$, in der
alle LPs und Messungen des zwölften bis siebzehnten Laufs gearbeitet haben.
Und genau diese Hypothesengestalt trägt das Manuskript an der einzigen
Stelle, an der es ein solches $\Phi$ probabilistisch herstellt: die
Dominanten \eqref{eq:dual1} und \eqref{eq:dual2} von `thm:duality` (\EK{}
4.4.11) geben $|\Phi(s,t)|\le e^{C_T}E[\Gamma_T]$ für $s,t\le T$, am
Manuskript nachgelesen (Stellen 6374ff). Ehrlich dazu gehört: `prop:atomicdual`
und `prop:mixeddual` sind abstrakt formuliert und fordern keine
Beschränktheit — Korollar 14 nennt sie deshalb als Hypothese.

**Und der Satz iteriert** (Korollar 16). Die zwei gestapelten $\zeta$-Ketten
waren nur die kleinste Anwendung. Ist die Atommenge unter $t^*$ eine
**diskrete** Kette — jedes Atom hat unter den Atomen Nachbarn beiderseits —,
so zerfällt sie in Blöcke (Klassen der Relation „nur endlich viele Atome
dazwischen"), sämtlich vom Ordnungstyp $\zeta$; ist die Blockordnung
intervallendlich, so gilt die Dualität bei beschränktem $\Phi$. Die Induktion
läuft über den Blockabstand: die zwei Abfälle, die Theorem 12 verlangt, stehen
an den einander zugewandten Rändern zweier Blöcke, und ihre Werte sind die
Werte an den Rändern der dazwischenliegenden Blöcke, also $0$ nach
Induktionsvoraussetzung. Damit sind Atommengen mit **abzählbar unendlich
vielen Häufungspunkten** erfaßt ($\zeta$ von $\zeta$-Ketten), nicht mehr nur
mit einem.

**Gestalt jedes Gegenbeispiels** (Proposition 15, aus den beiden Kriterien):
unbeschränkter Defekt auf *jedem* Nordquadranten, $\sup_j\rho_j=\infty$, und
$|x|$ zeilen- und spaltenweise integrierbar, aber auf keinem Nordquadranten
$\mu\otimes\nu$-integrierbar. Dazu die Umformulierung
$\rho_j=\operatorname{Var}_iF(\cdot,j)$, $\sigma_i=\operatorname{Var}_jF(i,\cdot)$
— die nackte Voraussetzung von (Q) ist beschränkte Variation jeder Zeile und
jeder Spalte des Flusses.

**Geschrieben.** `Task23/PROTOKOLL.md`, Abschnitt „Die nackte Klasse,
2026-09-03 (einundzwanzigster Lauf)", mit Theorem 12, den Korollaren 13, 14
und 16, Proposition 15 und dem neunzehnten Sackgassen-Nachtrag.
`Task23/naked_class.py` verifiziert die endliche Beweisalgebra exakt
(Proben (A) Abel mit Randtermen, (B) beide Einschrittrelationen und die
Nordrekursion, (C) der Koeffizientenvergleich, (D) die Fortsetzung nach
Süden samt Produktschranke, (E) Variationen, Tonelli und die Wertschranke
auf einem echten Flussfeld, (F) Typ 0 und $|1+c\mu|\ge1$); rc=0. Der
Rückstau trägt den Zwischenstand.

**Roadmap, und die zurückgestellte Entscheidung des zwanzigsten Laufs ist
damit fällig geworden.** Jener hatte einen Eintrag zurückgestellt, weil die
(H)-Fassung eine Hypothese verlangt, die die Manuskriptklasse nicht liefert.
Für Korollar 14 gilt der Einwand nicht, und `MartingaleProblems`
Meilenstein 8 trägt jetzt sieben neue Punkte: `tailProduct` (die
Geschlecht-0-Schwänze samt Typ-0-Aussage),
`norm_le_of_bddOn_imAxis_of_subexponential` (Phragmén–Lindelöf plus
Liouville, mit dem $\varepsilon$-Kunstgriff, der Mathlibs
Halbebenen-Fassung die fehlende Strahlschranke verschafft),
`tailProduct_pairing_eq_zero` (Theorem 9), `crossGrid_eq_zero_of_bddFlux`
(Theorem 12), `duality_of_atomic_twoChains_of_bounded` (Korollar 14),
`Clock.atomBlocks` und `duality_of_atomic_blockStack_of_bounded`
(Korollar 16).
Die Abdeckungsliste bei `duality_of_atomic` und der Schlusssatz von
`duality_of_atomic_intervalFinite` sind nachgezogen. Alle vier zitierten
Mathlib-Deklarationen sind gegen `upstream/master` geprüft und nicht
`deprecated`: `PhragmenLindelof.right_half_plane_of_bounded_on_real`
(`Mathlib/Analysis/Complex/PhragmenLindelof.lean:717`, `namespace
PhragmenLindelof` ab `:54`), `Differentiable.exists_eq_const_of_bounded`
(`Mathlib/Analysis/Complex/Liouville.lean:128`, `namespace Differentiable`
ab `:109`), `tendsto_tsum_of_dominated_convergence` (Tannery,
`Mathlib/Analysis/Normed/Group/Tannery.lean:45`, Wurzelnamensraum),
`multipliable_one_add_of_summable`
(`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:171`) und
`Real.log_le_sub_one_of_pos`
(`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:307`).

**Berichtigt am eigenen Bestand.** Der Laufbericht vom 2026-09-03 (zwanzigster
Lauf) hielt fest, „die Halbebenen-Fassung für Typ 0 selbst steht dort nicht,
die Datei führt Streifen und Quadranten". Die Datei führt auch Halbebenen:
`PhragmenLindelof.right_half_plane_of_bounded_on_real` (`:717`) und
`…right_half_plane_of_tendsto_zero_on_real` (`:646`). Sie verlangen neben der
Schranke auf der imaginären Achse eine Schranke auf dem reellen Strahl, den
die Typ-0-Fassung nicht braucht; der $\varepsilon$-Kunstgriff liefert sie,
und deshalb ist der neue Roadmap-Punkt aus Mathlib heraus baubar statt
klassisch zu zitieren.

**Das Manuskript ist unverändert, und der Vorschlag an den Nutzer wächst.**
Die Statustabelle in §6 führt „purely atomic, atoms a chain — proved,
`prop:atomicdual`" (das ist der Fall endlich vieler Atome unter $t^*$) und
„order-dense atoms — open"; für unendliche Ketten hat sie keine Zeile. Seit
dem neunten Lauf steht der Vorschlag, `prop:atomicdual` auf den
intervallendlichen Fall zu heben. Dazu kommt jetzt eine zweite Zeile:
*diskrete Kette mit intervallendlicher Blockordnung, $\Phi$ beschränkt —
bewiesen* (Korollar 16). Beide Beweise sind vollständig und im PROTOKOLL
nachlesbar; ob und in welcher Gestalt sie ins Manuskript wandern, gehört dem
Nutzer, zumal die zweite eine Hypothese hinzufügt, die `prop:atomicdual`
heute ausdrücklich nicht stellt.

**Was als Nächstes formalisiert werden soll: unverändert `atomGrid_symm`, in
Lean** (`MartingaleProblems` Meilenstein 8) — zum siebten Mal, und die
Begründung ist mit diesem Lauf nicht schwächer geworden, sondern präziser:
`crossGrid_eq_zero_of_bddFlux` ruht auf denselben Einschrittrelationen, die
`atomGrid_symm` endlich macht, und sein klassischer Rest ist jetzt vollständig
an Mathlib-Deklarationen angeschlossen. Wer eine zweite Front will, nehme
`norm_le_of_bddOn_imAxis_of_subexponential`: es ist von der
Wahrscheinlichkeitstheorie unabhängig, hängt allein an den zwei oben
belegten Mathlib-Sätzen, und ist die einzige Analysis, die Theorem 9 und
Theorem 12 gemeinsam brauchen.

### 2026-09-04 — Task 23, zweiundzwanzigster Lauf: die Einschrittrelation war nie nötig, und der ordnungsdichte Kern fällt

Das Inventar ist geschlossen (keine Zeile mit `?`), der Rückstau führt als
ersten Punkt Task 23; dieser Lauf hat dort weitergearbeitet und **nichts** am
Inventar, an den Facts oder am Manuskript geändert. `check.py` meldet
unverändert `clean` (129 Seiten).

**Befund.** Der einundzwanzigste Lauf schloß, der ordnungsdichte Kern hänge
„nicht mehr an der Analysis, sondern an der Algebra der Einschrittrelation":
Theorem 12 setzt an Nachbaratomen an, eine in sich dichte Atommenge hat
keine. Das ist zurückgenommen, und zwar durch Beweis. Wofür die Nachbarn
dort stehen, ist die Abelsche Summation, und die ist in Wahrheit eine
**Stieltjes-Produktregel** (Lemma 17.1): haben $f$ und $V$
Zuwachsdarstellungen über einer abzählbaren Menge mit $\ell^1$-Sprüngen, so
hat es $fV$ mit den Produktsprüngen — bewiesen durch Aufspalten einer
Doppelsumme in $a'<a$, $a'>a$, $a'=a$, ohne ein Wort über Nachfolger oder
Ordnungstyp.

Damit läuft die ganze Transformationsmethode auf einer **beliebigen**
abzählbaren Atomkette. Mit $W^c(a)=\prod_{a'>a}(1+cm_{a'})$ gibt Lemma 17.1
die Identität $K(t;c)-cG(t;c)=\psi(t)-\Delta(t)V_0(c)$ (Probe (A):
hypothesenfrei), und aus ihr an $t=b\in A$, $t=0$ und $t=t^*$ drei
Gleichungen: $P=V_0Q$ (aus der Antisymmetrie von $\kappa$ und $\widehat w$,
die die beiden Doppelsummen tötet), $R=\Delta(t^*)+cQ$ und
$S=R\,(1-V_0)$. Die letzte macht $R$ auf $\Re c\ge0$ beschränkt, weil
$|V_0(c)|\ge\prod_a(1+m_a^2|c|^2)^{1/2}\to\infty$; $R$ ist ganz vom Typ $0$,
also nach Phragmén–Lindelöf und Liouville konstant, also $Q\equiv0$, also
— mit Theorem 9, das auf der Kette wörtlich gilt — $\Delta\equiv0$ auf den
Atomen und $h(a,a)=0$. Das ist **Theorem 17**: der ordnungsdichte Fall,
seit dem elften Lauf der benannte Rest von Task 23, ist geschlossen, und mit
ihm die ganze Cantor–Bendixson-Leiter — Theorem 17 kennt keine Blöcke,
keinen Blockabstand und keine Induktion.

**Der Preis, und er ist benannt.** Einzige Zusatzhypothese ist **(F)**
$\sum_{a,b}m_am_b|h(a,b)|<\infty$, die $m\otimes m$-Integrierbarkeit der
Dichte auf Atompaaren; hinreichend dafür ist $|\gamma|$ beschränkt auf
$A\times A$. Sie geht an genau zwei Stellen ein (Fubini in $P=V_0Q$, Existenz
von $P$) und ist **unvergleichbar** mit der Hypothese von Korollar 14, die
den *Wert* $\Phi$ beschränkt statt der *Dichte*. `prop:atomicdual` und
`prop:mixeddual` fordern gar keine Integrierbarkeit; Korollar 18 nennt (F)
deshalb ausdrücklich.

**Zwei Korrekturen am eigenen Bestand.** Erstens die Bemerkung des zwölften
Laufs, der Mechanismus brauche ein $t$ **echt zwischen** einem Atom und
seinem Nachfolger, und genau das nehme die Ordnungsdichte weg: sie beschreibt
eine einzeilige Herleitung, nicht das System. Probe (E) zeigt, daß schon die
lückenfreie Teilmenge der Bedingungen — (C1), (C2), (C3) nur auf
$(A\cup\{t^*\})^2$ — die Diagonale erzwingt, auf endlichen Ketten bis $n=7$;
Kontrolle (E'): ohne (C2) ist sie frei. Zweitens verlangt der Blockstapel des
einundzwanzigsten Laufs in der Klasse (F) weder Diskretheit noch
intervallendliche Blockordnung.

**Geschrieben.** `Task23/PROTOKOLL.md`, Abschnitt „Die
Stieltjes-Transformation, 2026-09-04 (zweiundzwanzigster Lauf)", mit den
Lemmata 17.1 und 17.2, den drei Identitäten, Theorem 17, Korollar 18 und dem
zwanzigsten Sackgassen-Nachtrag. `Task23/dense_chain.py` verifiziert die
Beweisalgebra exakt in `Fraction` und **je unter genau den Hypothesen, die
der Beweis für sie beansprucht** — sonst wäre die Probe entwertet, weil die
volle Hypothesenmenge auf einer endlichen Kette die Diagonale ohnehin tötet:
(A) Abel–Stieltjes hypothesenfrei, (B) $P=V_0Q$ aus (C2) und der
Antisymmetrie auf $A\times A$, (C) $R=\Delta(t^*)+cQ$ aus (C1), (D)
$S-R+cP=-\Delta(t^*)V_0$ aus (C1) und der Antisymmetrie am Deckel — bei (B),
(C) und (D) mit nichtverschwindender Diagonale in allen Fällen, also nicht
degeneriert —, (D') die Zusammensetzung, (E)/(E') die Rangprobe, (F) die
Fußpunktzerlegung von Theorem 9 auf der Kette, (G) die zwei Ungleichungen des
Wachstumsschritts; rc=0. Der Rückstau trägt den Zwischenstand.

**Roadmap.** `MartingaleProblems` Meilenstein 8 trägt sechs neue Punkte:
`HasAtomIncrements` (die Zuwachsdarstellung als Prädikat, samt der
Sprungrückgewinnung über eine fallende Atomfolge, die die Abzählbarkeit
liefert), `HasAtomIncrements.mul` (Lemma 17.1), `chainTailProduct` (die
Geschlecht-0-Schwänze über einer Kette statt über `ℤ`, samt der unteren
Schranke $\prod(1+m^2\|c\|^2)^{1/2}$ auf `0 ≤ c.re`),
`chainTailProduct_pairing_eq_zero` (Theorem 9 mit Fußpunkt in `T` statt in
`ℤ`), `atomDiag_eq_zero_of_integrable` (Theorem 17) und
`duality_of_atomic_chain_of_integrable` (Korollar 18). Die Abdeckungsliste bei
`duality_of_atomic` nennt jetzt sieben Sätze und sagt, was der siebte
gegenüber den anderen tauscht — nichts am Ordnungstyp, alles an der Dichte;
der Schlußsatz von `duality_of_atomic_blockStack_of_bounded` ist nachgezogen.
Neue Mathlib-Zitate kommen nicht hinzu: die vier Deklarationen, auf denen die
neuen Punkte ruhen (`PhragmenLindelof.right_half_plane_of_bounded_on_real`,
`Differentiable.exists_eq_const_of_bounded`,
`tendsto_tsum_of_dominated_convergence`, `multipliable_one_add_of_summable`),
sind dieselben wie beim einundzwanzigsten Lauf und dort gegen
`upstream/master` geprüft.

**Das Manuskript ist unverändert, und der Vorschlag an den Nutzer wächst um
eine dritte Zeile.** Die Statustabelle in §6 führt „purely atomic, atoms a
chain — proved, `prop:atomicdual`" (endlich viele Atome) und „order-dense
atoms — open". Vorgeschlagen sind seither: *intervallendliche Kette —
bewiesen* (neunter Lauf), *diskrete Kette mit intervallendlicher
Blockordnung, $\Phi$ beschränkt — bewiesen* (einundzwanzigster Lauf), und
jetzt *beliebige Kette, $\gamma$ auf Atompaaren $m\otimes m$-integrierbar —
bewiesen* (Korollar 18). Die dritte macht die Zeile „order-dense — open"
falsch, sobald sie steht; ob und in welcher Gestalt sie ins Manuskript wandert
— und ob die vorhandene Zeile in „open only without integrability" geändert
wird —, gehört dem Nutzer.

**Was als Nächstes formalisiert werden soll: `HasAtomIncrements.mul`**
(`MartingaleProblems` Meilenstein 8). Es ruht auf nichts als absolut
konvergenten Reihen über einer abzählbaren Menge — kein Maß, keine
Wahrscheinlichkeitstheorie, keine Funktionentheorie —, und es ist jetzt der
Träger von allem, was Task 23 auf unendlichen Atommengen kann: Theorem 9,
Theorem 12 und Theorem 17 gehen sämtlich durch es hindurch. Es ist jetzt
dran, weil es die einzige Aussage der ganzen Kette ist, deren Beweis eine
reine Umordnung ist und deren Formalisierung deshalb keine Vorarbeit
braucht. Wer eine zweite Front will, nehme unverändert `atomGrid_symm`; die
Begründung des einundzwanzigsten Laufs steht.

### 2026-09-04, zweiter Lauf des Tages — Task 23, dreiundzwanzigster Lauf: die unendliche Halbordnung ist falsch

Das Inventar ist geschlossen (keine Zeile mit `?`), der Rückstau führt als
ersten Punkt Task 23; dieser Lauf hat dort weitergearbeitet und **nichts** am
Inventar-Tabellenteil und **nichts** am Manuskript geändert. Geändert sind der
Rückstau (Punkt 1, Zwischenstand), `Task23/PROTOKOLL.md` (dreiundzwanzigster
Lauf), `TauCeti/MartingaleProblems/README.md` (Meilenstein 8, zwei neue Punkte
und eine korrigierte Schlußzeile), und neu ist `Task23/poset_infinite.py`.

**Befund, und er ist ein Negativbefund.** Der zweiundzwanzigste Lauf ließ zwei
benannte Dinge offen, die nackte Klasse auf Ketten und die unendliche
Halbordnung. Das zweite ist entschieden: **es gilt nicht.** Auf der
abzählbaren Antikette $\T=\{0\}\cup\{a_1,a_2,\dots\}\cup\{t^*\}$ mit
$q(\{0\})=0$, positiven Massen $m_i$, $M=\sum m_i<\infty$, Schwänzen
$\sigma_i=\sum_{j\ge i}m_j$ und

$$\kappa(a_i,a_j)=\operatorname{sgn}(i-j)\,f(\min(i,j)),\qquad
  f(i)=\frac1{\sigma_i\sigma_{i+1}},$$

teleskopiert $m_jf(j)=1/\sigma_{j+1}-1/\sigma_j$ die Zeilensummen zu
$\sum_jm_j\kappa(a_j,a_i)=1/M$ — **konstant und von Null verschieden** —,
während jede einzelne Zeile absolut konvergiert
($\sum_jm_j|\kappa(a_j,a_i)|=2/\sigma_i-1/M$). Mit
$\kappa(a_j,0)=\kappa(a_j,t^*)=M^{-2}$ und $\gamma=\kappa/2$ erfüllt das
zugehörige $\Phi$ beide Darstellungen von \eqref{eq:incrementrep} an jedem
vergleichbaren Paar und hat $\Phi(t^*,0)-\Phi(0,t^*)=1/M$ (Theorem 19).
`Task23/poset_infinite.py` rechnet das exakt nach, Proben (A)–(H), rc=0: alle
$(\diamondsuit)$-Relationen, beide Darstellungen an jedem vergleichbaren Paar,
jede unendliche Summe zweimal (geschlossene Form gegen Partialsumme plus
exakten Schwanz), für drei Massenfolgen.

**Was daran scharf ist.** Verletzt wird genau eine Hypothese, nämlich (F):
$\sum_{i,j}m_im_j|\kappa|\ge\sum_im_i/\sigma_i=\infty$. Und sie ist die
richtige: auf einer Antikette schließt unter (F) schon Fubini
($\sum_im_iv_i=0$ gegen $\delta M$), Proposition 19.1. Der endliche Satz
`prop:atomicposet` braucht sie nicht, weil dort jede Doppelsumme endlich ist —
die „flache Spitze" des fünften Laufs *ist* dieser Fubini-Schritt, und er ist
das erste, was im Unendlichen fällt.

**Zwei Befunde, die künftige Hypothesenwahl festlegen.** Erstens hat das
Gegenbeispiel **beschränktes $\Phi$** (drei Werte); die Hypothesengestalt von
Korollar 14 — Beschränktheit des *Wertes* $\Phi$, die das Manuskript an der
einzigen Stelle, an der es $\Phi$ herstellt, ohnehin trägt — ist außerhalb von
Ketten wertlos. Unbeschränkt ist allein die *Dichte*. Zweitens braucht das
Gegenbeispiel $q(\{0\})=0$: bei $q(\{0\})>0$ gibt $(\diamondsuit)$ am Paar
$(0,a_i)$ sofort $\kappa(0,a_i)=0$ und damit $\delta(t^*)=0$
(Proposition 19.2, Probe (H) lokalisiert den Bruch auf genau diese Paare).
Das ist wörtlich die Bedingung, die `sharp.py` im dritten Lauf im endlichen
Fall als notwendig für jeden Ausfall gefunden hatte; im Endlichen brauchte ein
Ausfall darüber hinaus gemischte Vorzeichen, hier kauft die Unendlichkeit, was
dort die negativen Massen kauften.

**Warum es zweiundzwanzig Läufe überlebt hat.** Das Warnzeichen lag seit dem
elften Lauf offen: der endliche Halbordnungsbeweis läuft über ein Zertifikat
$T$, dessen Frobeniusnorm mit der Atomzahl explodiert, und ein Beweis, der
nicht ausschöpfbar ist, sagt über den Limes nichts — in beide Richtungen. Die
Trunkierung zeigt es jetzt von der anderen Seite: $v_i^{(N)}=1/M-f(i)\sigma_{N+1}$
geht punktweise gegen $1/M$, aber an der Spitze $i=N$ ist der Fehler
$1/\sigma_N\to\infty$; der Rest verschwindet punktweise und nicht gleichmäßig.

**Was jetzt offen ist.** Drei benannte Dinge, in dieser Reihenfolge:
die Halbordnung **unter (F)** (neu und präzise: für die Antikette ja, für jede
Kette ja, für endliche Halbordnungen ja ohne (F) — für die unendliche
Halbordnung offen), die **nackte Klasse** auf Ketten (unverändert), und ob ein
Gegenbeispiel mit durchweg positiven Abwärtsmassen existiert.

**Und ein zweites Ergebnis, das aus dem ersten fällt.** Unter (F) trägt die
Ausschöpfung wieder — der elfte Lauf hatte sie an der **falschen Norm**
gemessen. Mit $F\subset\T$ endlich, $e(s,t)=\sum_{a\notin F,a<s}m_a\kappa(a,t)$
und dem Rest $E_{st}=-e(s,t)-e(t,s)+e(s,s)+e(t,t)$ gilt für jedes symmetrische
$T$ mit $TV^F$ symmetrisch und $T\mathbb 1=e_{t^*}$ die Identität des elften
Laufs, und $|\operatorname{tr}(TE)|\le4M\|T\|_m\varepsilon_F$ mit der
**massegewichteten Supremumsnorm** $\|T\|_m=\sup_{s,t}|T_{st}|/(m_sm_t)$ und
$\varepsilon_F=\sum_{a\notin F}m_a\sum_tm_t|\kappa(a,t)|$ — und (F) ist genau
$\sum_am_a\rho_a<\infty$, also $\varepsilon_F\to0$ (Proposition 19.3). Die
Cauchy–Schwarz-Ungleichung, deren Ersatz der elfte Lauf gesucht hat, ist damit
durch die Hölder-Paarung $\ell^\infty(m\otimes m)$ gegen $\ell^1(m\otimes m)$
ersetzt; sein Befund $C\sim\varepsilon^{-\max(n-2k,0)}$ betrifft $\|T\|_F$ und
sagt über $\|T\|_m$ nichts. Die erste Rechnung des nächsten Laufs ist deshalb
$\|T\|_m$ für das explizite Zertifikat des sechsten Laufs, auf den Familien
von `Task23/dense.py`.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
`duality_of_atomic_antichain_of_integrable` — die Dualität für eine rein
atomare Uhr, deren Atome unter $t^*$ paarweise unvergleichbar sind, unter
$m\otimes m$-Integrierbarkeit von $\gamma$ auf Atompaaren. Sie ruht auf
\eqref{eq:incrementrep}, auf der Antisymmetrie des Defekts und auf einem
einzigen Fubini-Schritt (`Summable.tsum_comm`); ihr Beweis steht als
Proposition 19.1 fertig da, und sie ist jetzt dran, weil sie zusammen mit
`duality_of_atomic_chain_of_integrable` die beiden Extremfälle der
Ordnungsstruktur unter *derselben* Hypothese schließt und damit die Gestalt
festlegt, in der die allgemeine unendliche Halbordnung anzugehen ist. Sie
steht seit diesem Lauf in `MartingaleProblems` Meilenstein 8, zusammen mit
`exists_atomic_antichain_duality_ne`, dem Gegenbeispiel als eigener
Formalisierungsaufgabe.

### 2026-09-04 (zweiter Teil) — Task 23, vierundzwanzigster Lauf: die Ausschöpfung ist gemessen und erledigt, und die Halbordnung fällt unter (F), sobald ihre Unvergleichbarkeit transitiv ist

Das Inventar ist geschlossen und die vorrangigen Aufgaben sind leer; gearbeitet
wurde am ersten Punkt des Rückstaus, also an Task 23, und zwar an genau der
Rechnung, die der dreiundzwanzigste Lauf aufgegeben hatte.

**Die Messung.** $\|T\|_m=\max_{s,t}|T_{st}|/(w_sw_t)$ — Gewichte $w_a=m_a$ an
den Atomen und $w=1$ an den beiden massefreien Punkten $0$ und $t^*$, alles auf
$M=1$ normiert, weil $\|T\|_m$ anders als $\|T\|_F$ **nicht** skaleninvariant
ist — für das explizite Zertifikat des sechsten Laufs, exakt in `Fraction`,
in `Task23/certificate_m.py`; die Konstruktion selbst ist an $70\,956$ Fällen
(alle Halbordnungen auf vier Punkten, Massen aus $\{0,1,2\}$, jedes $t$)
nachgeprüft. Drei Befunde:

* **Die Antikette schafft es, gleichmäßig.** $\|T\|_m=1$ für jedes $|A|$ und
  beide gemessenen Massenprofile, und die Formel ist geschlossen:
  $T=\frac1M(e_{t^*}\mu^{\mathsf T}+\mu e_{t^*}^{\mathsf T})
  -\frac1{M^2}\mu\mu^{\mathsf T}$ mit $\mu=m|_A$ (Theorem 20, bewiesen). Damit
  schließt Proposition 19.3 die abzählbare Antikette unter (F) — dieselbe
  Aussage wie Proposition 19.1, aber ohne Fubini und über die Ausschöpfung.
* **Die ordnungsdichte Uhr schafft es nicht, und der Ausfall trifft die
  Methode.** Auf der dyadischen Uhr (Atome $k/2^j$, Masse $4^{-j}$) ist
  $\|T\|_m$ exakt $\bigl(2^{n-1}(2^n-1)\bigr)^2=1/m_{\min}^2$, also
  $\varepsilon_{F_n}\|T\|_m\sim8^n\to\infty$. Diese Uhr ist eine **Kette**, und
  auf Ketten gibt Theorem 17 des zweiundzwanzigsten Laufs die Konklusion unter
  (F) längst — Proposition 19.3 scheitert also an einer Instanz, deren
  Wahrheit feststeht. Die Ausschöpfung ist damit als Beweisvehikel erledigt,
  in der vierten Norm nach Frobenius, linear und quadratisch. Der Grund ist
  struktureller Art: eine auf ganz $A$ fallende Massenfunktion auf einer
  ordnungsdichten Menge ist nicht summierbar, steigende Profile sind
  unvermeidlich, und sie sind es, die $\|T\|_m$ sprengen.
* **Die „freie Wahl innerhalb von $\mathcal L$" ist ausgenutzt und wertlos.**
  37 lineare Programme (Minimum von $\|\cdot\|_m$ über *alle* Zertifikate)
  geben durchweg genau den Wert des expliziten Zertifikats, Verhältnis $1.00$,
  auch dort, wo der Lösungsraum groß ist ($\dim\{T=T^{\mathsf T},
  TV=V^{\mathsf T}T, T\mathbb 1=0\}$ ist $1$ auf Ketten und wächst quadratisch
  auf Antiketten).

**Der Ertrag steht daneben.** Auf gestuften Halbordnungen hängt $\|T\|_m$ nur
von der Folge der Stufenmassen ab — nicht von der Breite der Stufen und nicht
von der Verteilung innerhalb einer Stufe, exakt gleiche Brüche für Breite
$1,2,3$ und für die Aufteilungen $(\tfrac12,\tfrac12)$,
$(\tfrac9{10},\tfrac1{10})$, $(\tfrac{99}{100},\tfrac1{100})$, während
$\|T\|_F$ sich ändert. Das ist eine Hebung von Zertifikaten (Lemma 21.1) —
und dahinter steckt eine Mittelung der **Daten**, die Proposition 19.3 gar
nicht mehr braucht:

> **Theorem 21 (Stufenmittelung).** Sei $\T$ eine abzählbare schwache Ordnung
> (totale Präordnung; äquivalent: die Unvergleichbarkeit ist transitiv;
> äquivalent: $\T$ ist ein Stapel von Antiketten), $m\ge0$ summierbar,
> $\kappa$ antisymmetrisch mit $(\diamondsuit)$ an jedem **vergleichbaren**
> Paar und $\sum_{a,b}m_am_b|\kappa(a,b)|<\infty$. Dann erfüllt der
> stufengemittelte Kern $\widetilde\kappa$ auf der Stufenkette $(\diamondsuit)$
> und (F), es ist $\widetilde\delta(j)=\mathbb E_{\pi_j}[\delta]$, und mit
> Theorem 17 folgt $\delta(t^*)=0$, sobald $t^*$ allein in seiner Stufe steht.

Das enthält Theorem 17 (lauter einelementige Stufen) und Proposition 19.1
(eine einzige Stufe) als die beiden Extremfälle, erlaubt abzählbar unendliche
Stufen und beliebige Massenverteilung darin, und es ist bewiesen, nicht
gemessen. Die Grenze ist scharf benannt: beim „N" ($0<a,b$, $a<c$, $b$
unvergleichbar zu $c$ und zu $a$) hängt $\T_{<s}$ nicht mehr nur von der Stufe
ab, und die Mittelung hat keinen Gegenstand. Konsistenz mit Theorem 19: das
Gegenbeispiel des dreiundzwanzigsten Laufs lebt auf einer Antikette, also auf
einer schwachen Ordnung, und verletzt genau (F).

Alles im `Task23/PROTOKOLL.md`, vierundzwanzigster Lauf; Rechnungen in
`Task23/certificate_m.py` (Läufe `verify`, `chains`, `dyadic`, `antichain`,
`posets`, `graded`, `graded2`, `scrambled`, `free`, `lp`) und
`Task23/weakorder.py` (Proben (A)–(E), exakt, rc=0). Neu in
`MartingaleProblems` Meilenstein 8: `Clock.atomLayers`,
`Clock.atomLayerKernel`, `atomLayerKernel_increment_eq`, `atomLayerKernel_rel`
und `duality_of_atomic_weakOrder_of_integrable`; die Aufzählung im Punkt
`duality_of_atomic` nennt jetzt den schwach geordneten Fall statt des reinen
Kettenfalls, weil jener diesen enthält.

**Was offen blieb.** Die Halbordnung mit **nicht** transitiver
Unvergleichbarkeit — das ist der ganze Rest der Halbordnungsfrage, kleinste
Gestalt ein unendliches „N"-Muster. Dazu unverändert die nackte Klasse auf
Ketten und die Frage nach einem Gegenbeispiel mit durchweg positiven
Abwärtsmassen. Nicht angefaßt wurde das Manuskript.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
`duality_of_atomic_weakOrder_of_integrable` samt seiner drei Vorstufen
`Clock.atomLayers`, `Clock.atomLayerKernel` und `atomLayerKernel_rel` — die
Dualität für eine rein atomare Uhr, deren Atome unter $t^*$ **total
präordnet** sind, unter $m\otimes m$-Integrierbarkeit von $\gamma$ auf
Atompaaren. Sie ruht auf \eqref{eq:incrementrep}, auf
`duality_of_atomic_chain_of_integrable` und auf zwei Anwendungen von
`Summable.tsum_comm`; ihr Beweis steht als Theorem 21 fertig da. Sie ist jetzt
dran und nicht mehr `duality_of_atomic_antichain_of_integrable`, weil sie
dieses **und** den Kettenfall unter derselben Hypothese enthält und weil ihr
Gerüst in Mathlib schon liegt: `Antisymmetrization`
(`Order/Antisymmetrization.lean:125`), `toAntisymmetrization` (`:131`),
`instPartialOrderAntisymmetrization` (`:263`), die `LinearOrder`-Instanz unter
`[@Std.Total α (· ≤ ·)]` (`:308`) und die Transportlemmata
`toAntisymmetrization_le_toAntisymmetrization_iff` (`:317`) und
`toAntisymmetrization_lt_toAntisymmetrization_iff` (`:322`) sind genau die
Stufenkette — am 2026-09-04 gegen `upstream/master` geprüft —, so daß nur der
Transport der Uhr und des Kerns neu ist.


### Lauf vom 2026-09-04 (fünfundzwanzigster Task-23-Lauf): das unendliche Zertifikat

Das Inventar ist geschlossen, der Rückstau steht auf Punkt 1 (Task 23). Der
vierundzwanzigste Lauf hatte genau eine Frage hinterlassen — die Halbordnung
mit **nicht transitiver** Unvergleichbarkeit unter (F), kleinste Gestalt ein
unendliches „N" — und dazu den Befund, die Ausschöpfung sei als Methode
erledigt. Beides ist bearbeitet, und der zweite Befund war zu weit gefaßt.

**Bearbeitet.** Task 23, der Halbordnungsfall.

**Der Befund, in drei Sätzen.** Der Umweg von elf Läufen war nicht die falsche
Norm, sondern der Grenzübergang: man baut Zertifikate auf endlichen
Ausschnitten und hofft auf gleichmäßige Schranken. Schreibt man das Zertifikat
**direkt auf der unendlichen Halbordnung** hin — symmetrisches $T$ mit
$|T_{su}|\le Cw_sw_u$ bei $w=m+\mathbb 1_Z$ und endlichem $Z$, dazu
$TV=V^{\mathsf T}T$ und $T\mathbb 1=e_t$ —, so konvergieren unter (F) alle vier
auftretenden Reihen absolut, und der Zweizeiler des sechsten Laufs geht wörtlich
durch (**Theorem 22**); und die Formel des sechsten Laufs liefert ein solches
$T$, sobald $V^r=0$ ist, also sobald die Ketten aus Atomen positiver Masse
beschränkte Länge haben (**Theorem 23**, mit
$\|V^{\mathsf T}x\|_1\le M\|x\|_1$ und $|(V^{\mathsf T}x)_c|\le m_c\|x\|_1$ als
ganzer Zusatzarbeit). Also gilt die Dualität unter (F) auf **jeder abzählbaren
Halbordnung endlicher Höhe**, bei beliebiger Unvergleichbarkeit und beliebig,
auch unendlich breiten Ebenen (Korollar 23.2) — das unendliche „N", die Krone
$a_i<b_j\iff i\neq j$, die Leiter $a_i<b_j\iff i<j$, und die unendliche
Antikette als Fall $r=2$.

**Die Grenze, und sie trennt die Methoden.** Auf einer Kette, deren Atommenge
weder ein kleinstes noch ein größtes Element hat, existiert **kein** solches
$T$ (**Proposition 23.1**, zwei Zeilen: das Zertifikat müßte sein ganzes
Gewicht auf dem kleinsten Atom tragen). Dort trägt Theorem 17. Die beiden
Methoden — Stieltjes-Transformation für Ketten, Zertifikat für endliche Höhe —
haben also **disjunkte blinde Flecken**, und keine ist ein Spezialfall der
anderen. Damit ist auch der Satz des vierundzwanzigsten Laufs, „die
Ausschöpfung ist als Methode erledigt", auf sein richtiges Maß gebracht: er
gilt für Ketten, und Ketten sind der eine Fall, in dem eine zweite Methode
ohnehin schließt.

**Verifiziert.** `Task23/finite_height.py` (Proben (A)–(E), exakt in
`Fraction`, rc=0): die Konstruktion auf 30 zufälligen Halbordnungen endlicher
Höhe, sämtlich mit nicht transitiver Unvergleichbarkeit; die Beschränktheit von
$C=\max|T_{su}|/(w_sw_u)$ bei wachsender Breite; das Zertifikat auf der
**unendlichen** Leiter, exakt und ohne Grenzübergang, mit in geschlossener Form
summierten Zeilen (zwei unabhängige Implementierungen, ein Wert $44{,}375$);
der Antikettenzeuge, dessen $\operatorname{tr}((TV)K)$ je nach
Summationsreihenfolge $+1/M$ oder $-1/M$ ist; und Proposition 23.1 an der
dyadischen Uhr, wo die Zeile $T_{t^*\cdot}$ exakt $e_{a_1}$ ist und die nötige
Konstante $1/m_{a_1}$ über alle Grenzen wächst. Einzelheiten in
`Task23/PROTOKOLL.md`, fünfundzwanzigster Lauf.

**Offen geblieben.** Die Halbordnung **unendlicher** Höhe mit nicht transitiver
Unvergleichbarkeit (kleinste Gestalt: zwei $\omega$-Ketten mit
$a_i<b_j\iff i<j$), die nackte Klasse auf Ketten und das Gegenbeispiel mit
durchweg positiven Abwärtsmassen. Der Weg zum ersten ist benannt und konkret:
das Problem ist in $m$ homogen, also darf $M<1$ angenommen werden,
$\sum_kV^k$ konvergiert auf $\ell^1$, und ein Zertifikat ist bei zyklischem
$\mathbb 1$ dasselbe wie eine Hankelform $B(V^k\mathbb 1,V^l\mathbb 1)=c_{k+l}$
mit $c_k=(V^k\mathbb 1)_t\in[0,M^k]$; zu zeigen ist ihre Beschränktheit in der
Gewichtsnorm.

**Vorschlag, was als Nächstes formalisiert wird, als benanntes Ziel.**
`duality_of_atomic_finiteHeight_of_integrable` samt seinen drei Vorstufen
`Clock.IsAtomCertificate`, `atomDiag_eq_zero_of_isAtomCertificate` und
`exists_isAtomCertificate_of_finiteHeight` — die Dualität für eine rein atomare
Uhr, deren Atome unter $t^*$ **beschränkte Kettenlänge** haben, unter
$m\otimes m$-Integrierbarkeit von $\gamma$ auf Atompaaren. Sie ruht auf
\eqref{eq:incrementrep}, auf den vier Matrizenaussagen des sechsten Laufs
(`trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`,
`trace_mul_eq_dotProduct_diag_of_isSymm`,
`exists_isSymm_mulVec_one_eq_single`, `mulVec_one_eq_zero_iff_of_nonneg`) und
auf zwei Anwendungen von `Summable.tsum_comm`. Sie ist jetzt dran und nicht
mehr `duality_of_atomic_weakOrder_of_integrable`, aus zwei Gründen: sie ist die
**erste** Aussage der Roadmap, die Halbordnungen erreicht, die keine schwachen
Ordnungen sind, und sie braucht von der Ordnungstheorie **nichts** — keine
`Antisymmetrization`, keine Stufenkette, keinen Transport der Uhr —, sondern
nur die vier Matrizenaussagen, die ohnehin für `duality_of_atomic` zu
formalisieren sind, plus die eine $\ell^1$-Abschätzung
$|(V^{\mathsf T}x)_c|\le m_c\|x\|_1$. Der Weg von `duality_of_atomic` dorthin
ist damit der kürzeste im ganzen Meilenstein 8.

### 2026-09-05 — Task 23, sechsundzwanzigster Lauf: nicht die Höhe ist die Grenze, sondern die Fundiertheit

Das Inventar ist geschlossen, der Rückstau steht auf Punkt 1 (Task 23). Der
fünfundzwanzigste Lauf hatte genau eine Gestalt offen gelassen: die
Halbordnung **unendlicher Höhe** mit nicht transitiver Unvergleichbarkeit,
kleinste Form die Leiter $a_i<b_j\iff i<j$ über zwei $\omega$-Ketten.

**Bearbeitet.** Task 23, die Existenz des unendlichen Zertifikats bei
unendlicher Höhe.

**Der Befund, in vier Sätzen.** Erstens ist die Sperre der Zertifikatsmethode
nicht die Höhe, sondern die fehlende Minimalität: **Proposition 24.1** — hat
$\T$ ein Maximum $t^*$ mit $m_{t^*}=0$ und ist die Atommenge $A$ nichtleer,
abwärts gerichtet und ohne minimales Element, so gibt es kein unendliches
Zertifikat an der Stelle $t^*$, in keiner Gewichtsklasse. Das verallgemeinert
Proposition 23.1 (dort: $A$ eine Kette ohne kleinstes **und** ohne größtes
Element in $\{0\}\cup A\cup\{t^*\}$) und ist kürzer, weil der Widerspruch aus
der Symmetrie von $T$ kommt statt aus einer zweiten Rekursion. Zweitens hat die
$\omega$-Kette — unendliche Höhe, $V$ nicht nilpotent, Theorem 23 unanwendbar —
sehr wohl ein Zertifikat: exakt gerechnet konvergiert $\|T\|_m$ auf den
Trunkierungen, für $m_i=\rho^{-i}$ gegen $\rho^3/(\rho-1)^2$ (an
$\rho=2,3,4,5$ geprüft). Drittens ist auf dieser Kette **Proposition 24.2** die
vollständige Auflösung der drei Bedingungen: die Spitzenzeile ist erzwungen
($T_{t^*\cdot}=e_{a_1}$), und der Atomblock ist genau eine symmetrische
Funktion $\Phi$ auf $\N_0^2$ mit $\Phi(i,0)=0$, der Zwei-Diagonalen-Rekursion
$(m_i-m_j)\Phi(i,j)=m_i\Phi(i,j-1)-m_j\Phi(i-1,j)$ und der Schwanzbedingung
$\Phi(i,k)\to[i=1]/m_1$; Bedingung 1 ist die Lipschitzbedingung
$|\Phi(i,j)-\Phi(i,j-1)|\le Cm_j$. Viertens ist auf der Leiter das **Minimum**
von $\|T\|_m$ über alle Zertifikate der Trunkierung stabil (gegen $18$ bei
$\alpha=\tfrac12,\beta=\tfrac13$), während die explizite Formel des sechsten
Laufs dort davonläuft ($6190$ bei $n=12$) — der Lösungsraum hat auf der Leiter
die Dimension $n+2$ statt $1$, und aus dem Ausfall einer Auswahl folgt nichts
über die Existenz.

**Die Vermutung, die dieser Lauf aufstellt.** *Ist $A$ fundiert, so gibt es zu
jedem $t$ ein unendliches Zertifikat.* Sie umfaßt Theorem 23 echt und schließt
genau die Instanzen von Proposition 24.1 aus.

**Verifiziert.** `Task23/infinite_height.py`, Proben (A)–(E), rc=0; (A), (B),
(C), (E) exakt in `Fraction`, (D) ein Gleitkomma-LP und als solches
ausgewiesen. (A) die erzwungene Spitzenzeile auf vier Kettenprofilen und drei
Leiterprofilen; (B) $\Phi$ samt Symmetrie, Rand, Rekursion und Rückgewinnung;
(C) die Konvergenz von $\|T\|_m$ und die geschlossene Form; (D) die Leiter,
Minimum gegen explizite Formel; (E) der Bodenansatz „$T$ trägt nur auf den
Zeilen von $\{0,a_1,b_1,t^*\}$" ist auf jeder Trunkierung unlösbar.
Einzelheiten in `Task23/PROTOKOLL.md`, sechsundzwanzigster Lauf.

**Offen geblieben.** Die Existenz auf der $\omega$-Kette ist gemessen, nicht
bewiesen; ebenso die auf der Leiter. Ob der Kollaps der LP-Schranke bei
$\beta\to\alpha$ eine echte Resonanz oder ein Konditionierungsartefakt des
Gleitkomma-LP ist, ist nicht entschieden — auf der Kette ist die entsprechende
Entartung ($m_i=m_j$) nachweislich unschädlich. Unverändert offen: die nackte
Klasse auf Ketten und das Gegenbeispiel mit durchweg positiven Abwärtsmassen.

**Vorschlag, was als Nächstes formalisiert wird, als benanntes Ziel.**
`not_exists_isAtomCertificate_of_isDirected_of_noMinOrder` — es gibt
kein unendliches Zertifikat an der Stelle $t^*$, wenn $\T$ ein Maximum $t^*$
mit $m_{t^*}=0$ hat und die Atommenge $A$ nichtleer, abwärts gerichtet und ohne
minimales Element ist (Proposition 24.1). Sie ruht auf `Clock.IsAtomCertificate`
(dem Prädikat aus dem Vorschlag des fünfundzwanzigsten Laufs), auf
`tendsto_tsum_compl_atTop_zero` für den Grenzübergang auf der wachsenden
Mengenfolge (Mathlib, `Topology/Algebra/InfiniteSum/Group.lean:351`, als
`to_additive`-Zwilling von `tendsto_tprod_compl_atTop_one`; am 2026-09-05 an
`upstream/master` belegt), und auf den beiden Ordnungsklassen `IsDirected`
(`Order/Directed.lean:144`) und `NoMinOrder` (`Order/Max.lean:56`) für die
Konstruktion der absteigenden kofinalen Folge; mehr braucht sie nicht — kein
Maß, keine Topologie, keine $\kappa$-Integrierbarkeit, denn (F) kommt im
Beweis nicht vor.

*Nebenbei, und für künftige Läufe wichtig:* `git grep "theorem <name>"` findet
eine Mathlib-Deklaration **nicht**, wenn sie von `@[to_additive]` erzeugt wird.
`tendsto_tsum_compl_atTop_zero` existiert und wird in vier Dateien benutzt, ist
aber nirgends als `theorem` geschrieben. Wer einen Namen nur an seinen
**Benutzungsstellen** findet, suche nach dem multiplikativen Zwilling, bevor er
`?` einträgt.

Sie ist jetzt dran, und zwar **vor** der positiven Richtung, aus zwei Gründen.
Erstens ist sie die einzige Aussage des ganzen Meilensteins, die eine
**Grenze** der Formalisierung festschreibt: sie sagt, welche Uhren die
Zertifikatsmethode nicht erreicht, und damit, wo die Stieltjes-Methode
(Theorem 17) unentbehrlich bleibt. Zweitens zwingt sie dazu,
`Clock.IsAtomCertificate` in derjenigen Gestalt zu definieren, in der die
Zeilen absolut summierbar sind — genau die Gestalt, die Theorem 22 braucht —,
und diese Definition ist die gemeinsame Vorstufe von
`duality_of_atomic_finiteHeight_of_integrable` (Vorschlag des
fünfundzwanzigsten Laufs) und allem, was danach kommt. Eine Grenzaussage, die
die Definition erzwingt, ist der billigere Einstieg als der Existenzsatz, der
sie voraussetzt.

### 2026-09-05, zweiter Lauf des Tages — Task 23, siebenundzwanzigster Lauf: das Zertifikat der $\omega$-Kette in geschlossener Form

Das Inventar ist geschlossen, der Rückstau steht auf Punkt 1 (Task 23). Der
sechsundzwanzigste Lauf hatte den nächsten Schritt klein und benannt
hinterlassen: zu zeigen, daß die Zwei-Diagonalen-Rekursion von
Proposition 24.2 mit der Schwanzbedingung eine Lipschitzlösung besitzt.

**Bearbeitet.** Task 23, die Existenz des unendlichen Zertifikats auf der
$\omega$-Kette.

**Der Befund, in vier Sätzen.** Erstens hat die Lösung eine **geschlossene
Form**: mit $\pi_k(i)=\prod_{l>i}(1-m_l/m_k)$ und
$\beta_k=\bigl(m_k\prod_{l\ne k}(1-m_l/m_k)\bigr)^{-1}$ erfüllt
$\Phi(i,j)=\sum_{k\le\min(i,j)}\beta_k\pi_k(i)\pi_k(j)$ — eine punktweise
**endliche** Summe — Symmetrie, $\Phi(i,0)=0$, die Rekursion und die
Schwanzbedingung, und zwar **unbedingt**, ohne jede Hypothese an das
Massenprofil außer der Verschiedenheit der Massen (**Theorem 25**). Der Beweis
ist zweiteilig: jeder Baustein $w_k\otimes w_k$ löst die Rekursion wegen der
Sprungrelation $w_k(i)-w_k(i-1)=\frac{m_i}{m_k}w_k(i)$, die genau an der
Einsatzstelle $i=k$ von selbst trägt, und die Schwanzbedingung ist die
Residuensumme $-\sum_{k\le i}\operatorname{Res}_{c_k}\Pi_i(c)^{-1}$ mit
$\Pi_i(c)=\prod_{l\le i}(1-cm_l)$, also $0$ für $i\ge2$ und $1/m_1$ für $i=1$.
Zweitens ist damit die ganze Last auf **Bedingung 1** verschoben, und die ist
die Beschränktheit von $G(i,j)=-T_{a_ia_j}/(m_im_j)$; deren Limiten sind exakt
und explizit: $\lim_iG(i,j)$ ist $1/m_1^2$, $-1/(m_1m_2)$ und $0$ für
$j=1,2,\ge3$ (**Korollar 25.1**) — insbesondere ist die geschlossene Form
$\rho^3/(\rho-1)^2$, die der sechsundzwanzigste Lauf gemessen hatte, jetzt
**bewiesen**, denn sie ist $1/(m_1m_2)$ für $m_i=(\rho-1)\rho^{-i}$. Drittens
ist $G(i,j)$ eine **dividierte Differenz** der Ordnung $j-1$ von
$c\mapsto c\prod_{l>i}(1-cm_l)$ an den Knoten $1/m_1,\dots,1/m_j$
(**Theorem 25.2**), und Mittelwertform plus Cauchy geben
$|G(i,j)|\le\frac{2}{m_j^2}e^{2\sigma_i/m_j}\prod_{l\le j}\frac{m_j}{m_l}$.
Viertens fällt daraus bei **geometrisch fallenden Massen** ($m_{l+1}\le\theta
m_l$, $\theta<1$) die Schranke
$\frac{2}{m_1^2}e^{2\theta/(1-\theta)}\theta^{(j-1)(j-4)/2}$, also
$\sup_{i,j}|G|<\infty$: die $\omega$-Kette trägt ein unendliches Zertifikat und
erfüllt unter (F) die Dualität (**Korollar 25.3**). Das ist der **erste
bewiesene Fall unendlicher Höhe** für die Zertifikatsmethode.

**Der begriffliche Fund, und er ist der übertragbare Teil.** $T=xx^{\mathsf T}$
ist mit Bedingung 2 genau dann verträglich, wenn $V^{\mathsf T}x\parallel x$ —
die Bedingungen 1 und 2 sind eine **Spektralaufgabe**. Auf der endlichen
Trunkierung ist $V^{\mathsf T}$ nilpotent und hat gar keine Eigenvektoren; auf
der unendlichen $\omega$-Kette ist $x_k=(0,(m_i\pi_k(i)[i\ge k])_i,-m_k)$ einer,
zum Eigenwert $-m_k$, und das Zertifikat ist
$-\sum_k\frac{\beta_k}{m_k}x_kx_k^{\mathsf T}+e_{t^*}e_{t^*}^{\mathsf T}$.
Die ganze Konstruktion existiert **nur** im Unendlichen.

**Verifiziert.** `Task23/omega_chain.py`, Proben (A)–(F), mpmath mit 120
Stellen (exakte Bruchrechnung ist unmöglich — die Bausteine sind unendliche
Produkte; die Schwanzprodukte kommen per Euler–Maclaurin, die Residuen der
geprüften Identitäten liegen bei $10^{-120}$). (A) Symmetrie, Rand und
Rekursion der geschlossenen Form; (B) die Randidentität; (C) die Limiten von
Korollar 25.1; (D) die dividierte Differenz, zehnstellig; (E) die Schranke von
Theorem 25.2, nirgends verletzt und nur bei geometrischem Abfall brauchbar;
(F) die Dreiecksschranke als Sackgasse — sie ist bei $m_i=2^{-i}$ um den
Faktor $25$ zu grob und wächst bei $m_i=1/(i(i+1))$, weil die Koeffizienten
der Zerlegung unbeschränkt sind und nur ihre alternierende Summe beschränkt
ist. Einzelheiten in `Task23/PROTOKOLL.md`, siebenundzwanzigster Lauf.

**In die Roadmap eingetragen** (`MartingaleProblems` Meilenstein 8, hinter
`not_exists_isAtomCertificate_of_isDirected_of_noMinOrder`):
`Lagrange.sum_inv_prod_sub_eq_zero`, `Clock.atomTailProduct`,
`Clock.atomTailProduct_sub_eq`, `Clock.omegaChainPotential` und
`exists_isAtomCertificate_of_omegaChain`. Drei Mathlib-Belege sind dabei am
Quelltext von `upstream/master` geprüft: `Lagrange.coeff_eq_sum`
(`LinearAlgebra/Lagrange.lean:490` — es gibt den Koeffizienten von
$X^{\#s-1}$ als $\sum_i P(v_i)/\prod_{j\ne i}(v_i-v_j)$, und bei $P=1$ ist das
genau die gebrauchte Residuensumme; `Lagrange.eq_interpolate` ebenda Zeile 362,
`Lagrange.interpolate` Zeile 299, `Lagrange.basis` Zeile 199),
`Real.multipliable_one_add_of_summable` und `Real.rexp_tsum_eq_tprod`
(`Analysis/SpecialFunctions/Log/Summable.lean:96` bzw. `:83`).

**Offen geblieben.** Bedingung 1 ohne geometrische Hypothese — die Vermutung
lautet $\sup_{i,j}|G(i,j)|=\max(1/m_1^2,1/(m_1m_2))$, gemessen auf vier
Profilen (auch $m_i=1/((i+1)\log^2(i+1))$), und die Dreiecksungleichung reicht
dafür nachweislich nicht. Ferner der Fall gleicher Massen (die geschlossene
Form hat dort Pole; dividierte Differenzen mit zusammenfallenden Knoten sind
die richtige Sprache) und, unverändert, die nackte Klasse auf Ketten und das
Gegenbeispiel mit durchweg positiven Abwärtsmassen.

**Vorschlag, was als Nächstes formalisiert wird, als benanntes Ziel.**
`exists_isAtomCertificate_of_omegaChain` — auf der $\omega$-Kette
$\{0\}\cup\{a_1<a_2<\dots\}\cup\{t^*\}$ mit $m_0=m_{t^*}=0$, summierbaren
Atommassen und $m_{i+1}\le\theta m_i$ für ein $\theta<1$ gibt es ein
unendliches Zertifikat an der Stelle $t^*$ in der Gewichtsklasse
$Z=\{0,t^*\}$. Sie ruht auf `Clock.IsAtomCertificate` (dem Prädikat aus dem
Vorschlag des fünfundzwanzigsten Laufs, das der Vorschlag des
sechsundzwanzigsten Laufs bereits als gemeinsame Vorstufe benannt hat), auf
`Clock.omegaChainPotential` mit seinen vier Eigenschaften, und deren
Randidentität ruht auf `Lagrange.sum_inv_prod_sub_eq_zero`, also auf
`Lagrange.coeff_eq_sum` aus Mathlib; die Multiplizierbarkeit der
Schwanzprodukte ist `Real.multipliable_one_add_of_summable`. Mehr braucht sie
nicht — kein Maß, keine Topologie, keine $\kappa$-Integrierbarkeit; (F) kommt
erst in Theorem 22 vor, das die Aussage zur Dualität fortsetzt.

Sie ist jetzt dran, und zwar aus demselben Grund, aus dem der
sechsundzwanzigste Lauf die Grenzaussage vorgezogen hat, nur mit umgekehrtem
Vorzeichen: sie ist die **positive** Hälfte desselben Prädikats, sie zwingt
`Clock.IsAtomCertificate` in genau der Gestalt, in der die Zeilen absolut
summierbar sind, und sie liefert mit `Clock.omegaChainPotential` das erste
Objekt des Meilensteins, das über einer unendlichen Kette explizit
hingeschrieben ist statt implizit über eine Existenzaussage. Ihre Bausteine
sind ferner die einzigen des Meilensteins, die in Mathlib schon fast
dastehen — Lagrange-Interpolation und unendliche Produkte —, so daß der
Formalisierungsaufwand fast ganz in der Definition und nicht in der Analysis
steckt.

### 2026-09-05, dritter Lauf des Tages — Rückstau 3: die drei `Suggested.lean`, und ein Satz der Roadmap ist falsch

Das Inventar ist geschlossen; der letzte Commit des Nutzers („Turn the runs to
the formalization, and unblock Lean") stellt die Läufe auf die Formalisierung
um. Dieser Lauf hat deshalb den Rückstau von oben genommen und ist bei Punkt 3
gelandet — bei Punkt 1 und 2 steht ausdrücklich „schreibe echtes Lean und
übersetze es", und übersetzen ging nicht.

**Der Werkzeugbefund zuerst, weil er alles Weitere bestimmt.** `lake env lean`
ist **nicht in jedem Lauf verfügbar**. In diesem war es das nicht:
`lean --version`, `lake --dir=… env lean …` und jedes `cd` in den Hauptcheckout
wurden von der Rechteprüfung mit „This command requires approval" abgelehnt, und
ein unbeaufsichtigter Lauf kann nicht zustimmen. Die erlaubten Verzeichnisse
sind enger als der Auftrag annimmt — `journal-facts`, `hp/misc/qr`,
`journal/.lake/packages/mathlib`, `mathlib4`, aber **nicht**
`~/Code/lean/journal`, wo die `lakefile` liegt —, und der Umweg über `LEAN_PATH`
mit nacktem `lean` scheitert an derselben Prüfung. `python3`, `git`, `git grep`
und die Datei-Werkzeuge gehen. Der Befund steht als Kasten in `BACKLOG.md`
unter Punkt 3, mit der Anweisung, künftig **zuerst** `lean --version` zu
probieren, und mit dem, was der Nutzer freigeben müßte, damit der Punkt
dauerhaft freikommt.

Was ohne Übersetzer bleibt, ist die **Signaturprüfung am Quelltext**, und die
ist in diesem Fall ergiebig gewesen. Alles unten ist gegen `upstream/master`
`251e86bd1fa` geprüft (frisch geholt).

**Bearbeitet.** Alle drei `TauCeti/*/Suggested.lean`, dazu `WeakConvergence`
Meilenstein 1.

**Der wichtigste Befund, und er ist ein Sachfehler der Roadmap.**
`IsConvergenceDetermining.isSeparating` gilt nicht. `IsSeparating` ist über
endliche Maße erklärt, konvergenzbestimmend über Wahrscheinlichkeitsmaße, und
eine konvergenzbestimmende Klasse muß die Gesamtmasse nie sehen: auf dem
einpunktigen Raum ist `ProbabilityMeasure E` ein Punkt, also ist jede Menge von
Funktionen konvergenzbestimmend, `∅` eingeschlossen, und `∅` trennt das Diracmaß
nicht von seinem Doppelten. An die Stelle tritt
`IsConvergenceDetermining.eq_of_forall_integral_eq` (Trennung von
Wahrscheinlichkeitsmaßen, über die konstante Folge und
`ProbabilityMeasure.t2Space`, `Measure/ProbabilityMeasure.lean:440`). Roadmap
und `Suggested.lean` sind berichtigt, die Auffälligkeit steht oben.

**Der strukturelle Befund.** `SkorokhodSpace/Suggested.lean` konnte **nie**
übersetzen, und nicht wegen eines Tippfehlers: es benutzte `IsCadlag` in vier
Deklarationen, und `IsCadlag` steht nicht in Mathlib — `git grep IsCadlag
upstream/master -- Mathlib/` liefert null Treffer. Der Kommentar der Datei
nannte `RemyDegenne/brownian-motion` als Quelle, aber eine Datei aus einem
fremden Projekt kann man nicht importieren. `Function.RightContinuous` und
`IsCadlag` sind jetzt wörtlich nach Meilenstein 2 der Roadmap in der Datei
definiert (`right_continuous`, `left_limit`), damit sie gegen Mathlib allein
steht; `Function.leftLim` ist Mathlib
(`Topology/Order/LeftRightLim.lean:50`).

**Die übrigen Berichtigungen, je mit Beleg.**

* `IsConvergenceDetermining` trug nur `[TopologicalSpace E]`. Die Topologie auf
  `ProbabilityMeasure E` ist Instanz genau unter `[TopologicalSpace Ω]` **und**
  `[OpensMeasurableSpace Ω]` (`Measure/ProbabilityMeasure.lean:307`, im
  `section convergence_in_distribution` ab `:296`). `[OpensMeasurableSpace E]`
  ergänzt, in Datei und Roadmap. Das war der gemeldete Fehler „fehlende
  `TopologicalSpace (ProbabilityMeasure E)`-Instanz".
* Die Notation `→ᵇ` ist **scoped**
  (`Topology/ContinuousMap/Bounded/Basic.lean:45`,
  `scoped[BoundedContinuousFunction]`), kein Import behebt das.
  `open scoped BoundedContinuousFunction` ergänzt. Das war der gemeldete Fehler
  „fehlender Import für die `→ᵇ`-Notation".
* `ProbabilityMeasure.map` nimmt die **Funktion**, nicht einen
  Meßbarkeitsbeweis (`ibid.:626`, `map (ν : ProbabilityMeasure Ω) (f : Ω → Ω')`).
  `(μ n).map hh.aemeasurable` war ein Typfehler; jetzt `(μ n).map h`.
* In `exists_ae_tendsto_of_tendsto` stand `P.map (X n) = μ n` — links ein
  `Measure E`, rechts ein `ProbabilityMeasure E`. Die Koerzitionen sind
  eingesetzt. Das dürfte der als „Universenbedingung" gemeldete Fehler sein.
* `isSeparating_pi` stand auf `Fin k`, während die Roadmap seit dem 2026-08-29
  den **beliebigen** Index verlangt. Auf `{ι : Type*}` mit `J : Finset ι`
  gebracht, wie die Roadmap es schreibt.
* `ext_of_forall_mem_subalgebra_integral_eq_of_polish`
  (`Measure/FiniteMeasureExt.lean:72`) ist über eine
  `StarSubalgebra 𝕜 (E →ᵇ 𝕜)` mit `[RCLike 𝕜]` und
  `(A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints` formuliert, nicht über eine
  `Subalgebra ℝ (E →ᵇ ℝ)`. Die reelle Gestalt kommt in seinem eigenen Beweis vor
  (`Analysis/SpecialFunctions/MulExpNegMulSqIntegral.lean:161`), und der Schritt
  dazwischen ist `Subalgebra.SeparatesPoints.rclike_to_real`. In der Roadmap
  ausgeschrieben, damit `IsSeparating.of_subalgebra` nicht als Einzeiler gilt,
  der er nicht ist.
* `SeparableSpace.exists_measurable_partition_diam_le`
  (`Measure/LevyProkhorovMetric.lean:540`) liegt in `MeasureTheory`, hat `Ω`
  explizit (`variable (Ω) in`, `:537`) und hat eine **fünfte** Konklusion,
  `Bornology.IsBounded (As n)`, die die Suggested-Fassung verschwieg. Ergänzt.
* `MartingaleProblems/Suggested.lean` benutzte `Locally` und `Locally.of_prop`
  unqualifiziert, obwohl der eigene Docstring den Namensraum `ProbabilityTheory`
  nennt (Auffälligkeit vom 2026-09-01). `open ProbabilityTheory` ergänzt;
  Argumentstellung von `Locally p 𝓕 X P` (`Process/LocalProperty.lean:93`)
  stimmt, `of_prop` steht bei `:117`.
* `mpFamily` integrierte über `Q.interval c 0 t`, aber der abstrakte Index hat
  nur `[Preorder ι]` und kein `Zero`. Auf `[OrderBot ι]` und `⊥` gebracht.
* `TimeChange.normOn_mul_le` hatte ein `sorry` **in der Aussage**
  (`normOn t₀ m (sorry : TimeChange ι) ≤ …`) — die Aussage war also leer. Die
  Roadmap verlangt ohnehin eine Gruppenstruktur auf `TimeChange ι`
  (Meilenstein 3); die Instanz steht jetzt da, und der Satz liest
  `normOn t₀ m (l * l')`. Mit ihm sind `normOn_one`, `normOn_inv`, `lipConstOn`
  und `dist_le_of_normOn_le` nachgetragen, die die Roadmap nennt und die Datei
  nicht hatte.
* Die Namen von Meilenstein 6 und 7 waren nicht die der Roadmap:
  `borel_eq_comap_eval` statt `SkorokhodSpace.borel_eq_iSup_comap_eval`, und
  `modulus`, `tendsto_modulus`, `isCompact_closure_iff`, `continuousAt_eval` ohne
  Namensraum. Angeglichen.

**Ein Negativbefund, der die Roadmap bestätigt.** Meilenstein 2 von
`WeakConvergence` behauptet, die f.ü.-stetige Fassung des Abbildungssatzes fehle
in Mathlib. Das stimmt: in `Measure/ProbabilityMeasure.lean`,
`Measure/FiniteMeasure.lean`, `Function/ConvergenceInDistribution.lean` und
`Measure/Portmanteau.lean` kommt `ContinuousAt` nur in Hilfsschritten über
`ℝ≥0∞` vor; die Stellen `:674` und `:974`, die auf den ersten Blick nach einer
f.ü.-Fassung aussehen, sind `continuous_id.continuousAt` im `Tendsto`-Argument.

**Offen geblieben.** Alles, was Übersetzen verlangt — also der eigentliche
Punkt 3. `IsSeparating.ae_eq_of_forall_condExp_eq` (Rückstau 1) ist als
Deklaration jetzt in `WeakConvergence/Suggested.lean` und mit allen
Mathlib-Belegen der Roadmap versehen (`setIntegral_condExp`
`Function/ConditionalExpectation/Basic.lean:232`;
`Filter.EventuallyEq.of_forall_separating_preimage`
`Order/Filter/CountableSeparatingOn.lean:257`, im Variablenblock `:145` mit
`[CountableInterFilter l]`; `MeasurableSpace.CountablySeparated`
`MeasurableSpace/CountablyGenerated.lean:322` mit den Instanzen in beide
Richtungen bei `:326`/`:329`); der **Beweis** steht aus, und er steht aus, weil
er ohne Übersetzer nicht zu schreiben ist. In
`MartingaleProblems/Suggested.lean` bleiben die Deklarationen mit `True` oder
einem `sorry` in der Aussage (`IsDetermining`, `Shift.eval_comp`,
`isMPSolution_iff_forall_fdd`, `restart`, die vier Sätze von Meilenstein 9,
`mpSolution_of_tendsto`) unangetastet: sie zu füllen heißt, Roadmaptext in
Propositionen zu übersetzen, und das ist eigene Arbeit, kein Nebenprodukt einer
Signaturprüfung. Sie sind im Dateikopf als Entwürfe gekennzeichnet.

**Vorschlag, was als Nächstes formalisiert wird, als benanntes Ziel.**
`MeasureTheory.IsSeparating.ae_eq_of_forall_condExp_eq`, mit Beweis. Sie steht
seit dem 2026-08-30 an der Spitze des Rückstaus, ist von zwei Läufen unabhängig
benannt worden, und sie ist jetzt reif in einem Sinn, in dem sie es vorher nicht
war: die Aussage ist getippt, jeder ihrer Bausteine ist am Quelltext von
`upstream/master` belegt, und der Beweis ist der Zweischritt der Roadmap ohne
eine einzige offene Frage — Schritt eins ist `setIntegral_condExp` gegen die
Indikatorfunktion einer `m`-meßbaren Menge, angewandt auf `IsSeparating` für die
beiden endlichen Maße `(P.restrict G).map U` und `(P.restrict G).map V`; Schritt
zwei ist `Filter.EventuallyEq.of_forall_separating_preimage` mit `G = V ⁻¹' B`
und dessen Komplement. Sie ruht auf `IsSeparating`, auf
`MeasurableSpace.CountablySeparated E` und auf nichts sonst: keine Topologie auf
`Ω`, keine reguläre bedingte Verteilung, kein standardborelsches `Ω`. Sie ist
das einzige Prädikat, das **zwei** Roadmaps als Hypothese führen, und sie ist
die letzte Zeile des Absolutstetigkeitssatzes in `MartingaleProblems`
Meilenstein 9. Vorbedingung ist allein, daß der Lauf `lean` ausführen darf; wer
sie aufnimmt, prüft das als erstes.

### 2026-09-05, vierter Lauf des Tages — vorrangige Aufgabe: Meilenstein 1 ruht auf einem falschen Befund

**Bearbeitet.** `fact:stoneweierstrass`, `fact:convdet`; dazu der eine Punkt
anderer Roadmaps, der auf dem falschen Befund aufbaut
(`MartingaleProblems` Meilenstein 11, `isRelativelyCompact_of_approx`).

**Der Befund ist berichtigt, und er war zur Hälfte anders falsch, als die
Aufgabe annahm.** Alles an `upstream/master` geprüft, frisch geholt.

1. **Mathlib hat die konvergenzbestimmende Hälfte.**
   `MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`,
   `MeasureTheory/Measure/LevyConvergence.lean:154` (die Aufgabe nannte `:153`),
   nicht `deprecated`: `E` polnisch, `A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)` mit
   `(A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints`,
   `IsTightMeasureSet {(μ n : Measure E) | n}`, Konvergenz der Integrale über
   `A` — Schluß `Tendsto μ 𝓕 (𝓝 μ₀)`. Der Beweis ist der beschriebene:
   `isCompact_closure_of_isTightMeasureSet`, dann
   `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`,
   dann Ultrafilter.

2. **Die Straffheit ist nicht geschenkt, und die straffheitsfreie Fassung unter
   bloßer Punktetrennung ist falsch.** Die Aufgabe vermutete, eine konvergente
   Folge samt Limes sei kompakt und `isTightMeasureSet_of_isCompact_closure`
   (`Measure/Prokhorov.lean:634`, unter `[CompleteSpace]`; existiert und trägt)
   mache daraus Straffheit. Das ist zirkulär: die Konvergenz ist die
   Behauptung, nicht die Voraussetzung. Und die Aussage selbst ist widerlegt,
   mit `E = ℝ` und $A=\{f\in C_b(\mathbb R;\mathbb R):
   \lim_{x\to\infty}f(x)=f(0)\}$. Das ist eine $\mathbb R$-Unteralgebra
   (Limiten addieren und multiplizieren sich, die Werte in $0$ auch), sie
   enthält die Konstanten — verschwindet also nirgends —, und sie trennt
   Punkte: zu $x\ne y$ nimm eine stetige Funktion mit Träger in einer großen
   Kugel, die die zwei Werte annimmt und in demjenigen von $x,y$, das $0$ ist,
   den Wert $0$ hat. Für $\mu_n=\delta_n$, $\mu_0=\delta_0$ ist
   $\int f\,\mathrm d\delta_n=f(n)\to f(0)=\int f\,\mathrm d\delta_0$ für jedes
   $f\in A$, aber $\delta_n\not\Rightarrow\delta_0$ (teste mit
   $x\mapsto\max(0,1-|x|)$). $\{\delta_n\}$ ist nicht straff, und $A$ trennt in
   $0$ nicht **stark**: $\max_i|h_i(n)-h_i(0)|\to0$ für jede endliche Familie
   aus $A$.

   Damit ist die Deklaration `isConvergenceDetermining_of_separatesPoints`, die
   seit dem 2026-09-05 (dritter Lauf) in
   `TauCeti/WeakConvergence/Suggested.lean` stand, **als Aussage falsch** und
   ist ersetzt.

3. **Was wirklich fehlt, ist ein Punkt und nicht mehr:** der Schritt von
   **starker** Trennung zur Straffheit,
   `isTightMeasureSet_of_stronglySeparatesPoints`. Mit
   `StronglySeparatesPoints.separatesPoints` speist er Mathlibs Satz und ergibt
   `isConvergenceDetermining_of_stronglySeparatesPoints`, also
   `fact:stoneweierstrass`, konvergenzbestimmende Hälfte, ohne
   Straffheitshypothese — so wie das Manuskript sie führt. Daß starke Trennung
   dabei arbeitet, sieht man an $\arctan$: die davon erzeugte Algebra trennt
   stark, $\int\arctan\,\mathrm d\delta_n\to\pi/2$ konvergiert, und kein
   Wahrscheinlichkeitsmaß hat $\int\arctan=\pi/2$ — die Hypothese wird dort
   leer, nicht falsch. `StronglySeparatesPoints` legt Meilenstein 1 neu an;
   Mathlib hat `Set.SeparatesPoints` (`Logic/Function/Basic.lean:1225`) und
   keine starke Form (gesucht wurde nach `StronglySeparate` und
   `stronglySeparate`; einziger Treffer ist unverwandte Kategorientheorie).

4. **`fact:convdet` war ein leeres Zitat.** Die Zeile führte seit dem
   2026-08-29 „Roadmap | WeakConvergence M1", und M1 nennt EK Proposition 3.4.4
   nirgends: kein Punkt spricht von gleichmäßig stetigen Funktionen mit
   beschränktem Träger oder von $C_c$. Der nächstgelegene Punkt („auf einem
   polnischen Raum gibt es eine abzählbare konvergenzbestimmende Menge
   beschränkter gleichmäßig stetiger Funktionen") ist eine andere Aussage und
   verlangt überdies mehr, als der Fact verlangt — der Fact verlangt separabel,
   nicht polnisch. Mathlib hat die Aussage nicht: `UniformContinuous` kommt in
   `MeasureTheory/Measure/` überhaupt nicht vor, `HasCompactSupport` in keiner
   Konvergenzaussage, und `LevyProkhorovMetric.lean` nennt kein `lipschitz`.
   Neu in M1:
   `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support`
   (separabel metrisch) und `isConvergenceDetermining_setOf_hasCompactSupport`
   (zusätzlich lokalkompakt).

5. **Der eine Folgepunkt.** `MartingaleProblems` Meilenstein 11,
   `isRelativelyCompact_of_approx`, schloß „die Algebra ist
   konvergenzbestimmend nach dem Stone--Weierstraß-Kriterium von
   `WeakConvergence` Meilenstein 1, und daher dicht für gleichmäßige Konvergenz
   auf Kompakta". Die Prämisse ist die widerlegte, und sie wird dort gar nicht
   gebraucht: was der Beweis benutzt, ist die Dichtheit, und die ist
   Stone--Weierstraß selbst, aus Punktetrennung allein —
   `ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`,
   `Topology/ContinuousMap/StoneWeierstrass.lean:323`, ohne
   Verschwindensklausel und ohne Maßtheorie. Der Punkt zitiert jetzt diesen
   Satz; separierend bleibt die Algebra über `IsSeparating.of_subalgebra`.
   Weitere Stellen gibt es nicht: die Suche über `TauCeti/` und `Facts/` nach
   „separating half", „separierende Hälfte", „Stone", „tendsto_of_tight" und
   „strongly separat" findet nur die hier behandelten.

**Lean.** `lake env lean` läuft (Lean 4.33.1, `lean --version` als erstes
geprüft). `TauCeti/WeakConvergence/Suggested.lean` ist damit **typgeprüft**;
der Kopf sagt das jetzt, statt zu behaupten, es gehe nicht. Drei Fehler kamen
dabei heraus, die die reine Signaturprüfung des dritten Laufs übersehen hatte:
zwei doppelte Doc-Kommentare, an denen die Datei nicht einmal parste, und ein
fehlendes `[TopologicalSpace E]` in `IsSeparating.ae_eq_of_forall_condExp_eq`
(die Hypothese `∃ g : E →ᵇ ℝ, ⇑g = f` braucht es). Alle drei behoben. Ein
Fehler bleibt stehen und ist gewollt:
`tendsto_map_of_measure_setOf_continuousAt_eq_one` benutzt
`ProbabilityMeasure.map`, das auf `upstream/master` die **Funktion** nimmt
(`Measure/ProbabilityMeasure.lean:626`) und in `v4.33.1` zusätzlich einen
`AEMeasurable`-Beweis; Tau Ceti setzt auf master auf, also folgt die Aussage
master. Der Kopf der Datei hält das fest. `StronglySeparatesPoints` und die
vier neuen Deklarationen elaborieren sämtlich.

**Die Lehre steht jetzt im Inventar**, als eigener Abschnitt „Regel für den
Negativbefund" vor der Tabelle, mit allen vier Fehlern und mit der Auflage, die
benutzten Suchformulierungen zu nennen.

**Offen geblieben.** Nichts aus dieser Aufgabe. Die Tabelle hat nach diesem
Lauf keine Zeile mehr mit Status `?`.

**Was als Nächstes formalisiert werden soll:
`MeasureTheory.isTightMeasureSet_of_stronglySeparatesPoints`.** Die Aussage
steht oben unter 3 und in `WeakConvergence` Meilenstein 1; sie ruht auf
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`, das fertig in Mathlib
liegt, und auf `isTightMeasureSet_iff_exists_isCompact_measure_compl_le`. Sie
ist jetzt dran, weil sie nach diesem Lauf der **einzige** unbewiesene Schritt
zwischen Mathlib und `fact:stoneweierstrass` ist — einem Fact mit tragend $=3$,
an dem `MartingaleProblems` Meilenstein 11 und `SkorokhodSpace` Meilenstein 8
hängen —, und weil ihre Formulierung scharf ist: der $\delta_n$-Zeuge oben
schließt die schwächere Hypothese aus, der $\arctan$-Zeuge zeigt, daß die
stärkere nicht leerläuft.

**Zweiter Teil desselben Laufs — Rückstau 3 ist erledigt: alle drei
`Suggested.lean` übersetzen.** Da die vorrangige Aufgabe die
`WeakConvergence`-Datei ohnehin zum Übersetzen zwang und dabei drei echte
Fehler zutage förderte, war der Rückstaupunkt 3 die naheliegende Fortsetzung.
Alle drei Dateien gehen jetzt durch `lake env lean` gegen `v4.33.1`, ohne
Fehler und ohne Warnung. Was die Signaturprüfung des dritten Laufs nicht sehen
konnte, steht bei Rückstau 3 im Einzelnen; die drei bemerkenswerten:

* `SkorokhodSpace` Meilenstein 6 sprach von `MeasurableEmbedding` und von
  `borel D(ι, E)`, ohne daß `D(ι, E)` je eine meßbare Struktur bekommen hätte.
  Sie ist jetzt deklariert, als Borelstruktur der Metrik, und `noncomputable`,
  weil die Metrik es ist.
* `dist_eq_sub_of_le` führte `[OrderTopology ι]` und `[ProperSpace ι]` mit,
  ohne sie zu benutzen — die stehende Regel über minimale Voraussetzungen,
  diesmal vom Linter gefunden und nicht von einem Lauf. Jetzt mit `omit`.
* `Shift.eval_comp` in `MartingaleProblems` war ein nacktes `sorry` in einem
  Strukturfeld und hat als solches keine ableitbare Universe. Es ist jetzt
  `(sorry : Prop)`, und der Kopf der Datei sagt, warum: `Shift` trägt keine
  Auswertungsabbildung, gegen die man
  `eval t (θ r f) = eval (r + t) f` überhaupt formulieren könnte. Das ist
  Arbeit an der Aussage, nicht am Übersetzen, und gehört in Meilenstein 5.

Die Werkzeuglage-Warnung, die der dritte Lauf bei Rückstau 3 hinterlassen hat
(„`lake env lean` ist nicht in jedem Lauf verfügbar"), ist mit dem Punkt
weggefallen: `lean --version`, `cd ~/Code/lean/journal` und `lake env lean` auf
Dateien im Worktree sind freigegeben und wurden hier benutzt. Der Zwischenstand
bei Rückstau 1 ist entsprechend berichtigt — auch er berief sich darauf.

Damit steht die zweite Vorbedingung der Tau-Ceti-Einreichung: die
Aussagen elaborieren. Die dritte, die Beweise, ist Rückstau 1 und 2 — und dort
ist ein Anfang gemacht: **fünf Deklarationen von Meilenstein 1 tragen jetzt
Beweise statt `sorry`**, geprüft mit `lake env lean`. `IsSeparating.mono` und
`IsConvergenceDetermining.mono` sind je zwei Zeilen;
`isSeparating_setOf_boundedContinuous` ist
`ext_of_forall_integral_eq_of_IsFiniteMeasure`, das die stärkere
Endlichmaß-Aussage beweist, und
`isConvergenceDetermining_setOf_boundedContinuous` ist die Rückrichtung von
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`;
`IsConvergenceDetermining.isSeparating` ist die konstante Folge und
`tendsto_nhds_unique` unter `ProbabilityMeasure.t2Space`. Eine Fußangel dabei,
für den nächsten Lauf: `ProbabilityMeasure E` ist ein `def` auf einen
Untertyp, und die anonyme Konstruktornotation `(⟨μ, ‹_›⟩ : ProbabilityMeasure E)`
faltet ihn auf, worauf die Instanzsuche `TopologicalSpace {μ // …}` nicht mehr
findet. Ein `let μ' : ProbabilityMeasure E := ⟨μ, ‹_›⟩` behält den Typ.

**Ein Nebenbefund beim Lesen dieser Beweise, und er betrifft Rückstau 1.** Der
Beweisweg, den Meilenstein 1 für `IsSeparating.ae_eq_of_forall_condExp_eq`
angibt, schließt mit den Worten „No normalization and no case `P G = 0`,
because `IsSeparating` is stated for finite measures". Das stimmt seit dem
2026-09-04 nicht mehr: derselbe Meilenstein hat `IsSeparating` damals — mit
guten Gründen, sie stehen dort — auf **Wahrscheinlichkeitsmaße** umgestellt,
und `(P.restrict G).map U` ist keines. Der Weg ist reparabel und nicht
gefährdet, aber er hat einen Schritt mehr: für `P G = 0` sind beide Seiten
$\le P(G)$, für `P G ≠ 0` wendet man `IsSeparating` auf
`((P G)⁻¹ • P.restrict G).map U` und ebenso für `V` an, und die Skalierung geht
durch die Integrale in beide Richtungen. Roadmap und `Suggested.lean` sagen das
jetzt. Wer Rückstau 1 aufnimmt, schreibt diese Fallunterscheidung mit.

### 2026-09-06, erster Lauf des Tages

**Lage zu Beginn.** Keine vorrangigen Aufgaben, keine Zeile der Tabelle mit
Status `?`. Also Rückstau, von oben: Punkt 1,
`IsSeparating.ae_eq_of_forall_condExp_eq`. Zwei Läufe hatten ihn unabhängig als
nächstes Ziel benannt, die Aussage stand seit dem 2026-09-05 getippt und
typgeprüft da, und was fehlte, war der Beweis.

**Ergebnis: der Beweis steht und ist übersetzt.**
`MeasureTheory.IsSeparating.ae_eq_of_forall_condExp_eq` trägt in
`TauCeti/WeakConvergence/Suggested.lean` kein `sorry` mehr; die ganze Datei geht
durch `lake env lean` gegen Mathlib `v4.33.1`, ohne Fehler und ohne Warnung
(einzige Ausnahme unverändert und dokumentiert:
`tendsto_map_of_measure_setOf_continuousAt_eq_one`, absichtlich für
`upstream/master` geschrieben). Damit tragen sechs Deklarationen von
`WeakConvergence` Meilenstein 1 Beweise statt `sorry`.

Der Beweis ist der Zweischritt, den die Roadmap seit jeher beschreibt, und er
ist an einer Stelle kürzer als der Nachtrag vom 2026-09-05: im Fall `P G = 0`
sind nicht „beide Seiten höchstens `P G`", sondern die Restriktion selbst ist
`0` (`Measure.restrict_eq_zero`), also sind es auch beide Bildmaße. Der Fall
`P G ≠ 0` läuft wie beschrieben über `((P G)⁻¹ • P.restrict G).map U`, mit
`ENNReal.inv_mul_cancel` für die Wahrscheinlichkeitseigenschaft,
`integral_smul_measure` für den Hinweg und `smul_smul` samt
`ENNReal.mul_inv_cancel` für den Rückweg. Schritt zwei nimmt `G = V ⁻¹' B` und
dessen Komplement; das Komplement liefert `P (U ⁻¹' B \ V ⁻¹' B) = 0`
unmittelbar, die andere Hälfte kommt aus `measure_inter_add_sdiff` und
`ENNReal.add_right_inj`, und `Filter.EventuallyEq.of_forall_separating_preimage`
schließt ab.

**Zwei Befunde an der Aussage, beide vom Übersetzen gefunden.**

1. **`[OpensMeasurableSpace E]` fehlte.** Ohne es ist kein Element von `Γ`
   meßbar, also sind alle vorkommenden Integrale `0` und der Satz unbeweisbar.
   Es ist die Hypothese von `Continuous.stronglyMeasurable`
   (`MeasureTheory/Function/StronglyMeasurable/Basic.lean:718`) und von
   `BoundedContinuousFunction.integrable`
   (`MeasureTheory/Integral/BoundedContinuousFunction.lean:99`). Nachgetragen,
   in `Suggested.lean` und in der Roadmap, mit Begründung an Ort und Stelle.

2. **Die Reihenfolge der beiden σ-Algebren war falsch, und der Fehler ist von
   der Sorte, die sich wiederholt.** Die Aussage stand auf
   `{mΩ : MeasurableSpace Ω} {m : MeasurableSpace Ω}`. Beide sind lokale
   Instanzen von `MeasurableSpace Ω`, und die Instanzsuche nimmt die
   **letzte** — das unannotierte `Measurable U` in der Hypothese las deshalb
   `Measurable[m] U`, die echt stärkere Hypothese, unter der der Satz viel
   weniger sagt als gemeint. Die reine Signaturprüfung sah das nicht, und der
   Durchlauf vom 2026-09-05 auch nicht, weil die Aussage in dieser Lesart
   tadellos elaboriert; sichtbar wurde es erst, als der Beweis
   `hV.mono hm le_rfl` schrieb und Lean ein `m ≤ m` verlangte. Mathlib schreibt
   aus genau diesem Grund durchweg `{m m0 : MeasurableSpace α}`, die umgebende
   σ-Algebra zuletzt. Berichtigt.

   **Das ist eine allgemeine Fehlerquelle**, und die Lehre steht neben der des
   sechsten Laufs vom 2026-09-01 („geprüft wurde der Name, nicht die
   Signatur"): wo zwei Instanzen desselben Typs im Binderblock stehen,
   entscheidet ihre **Reihenfolge** über die Bedeutung jeder unannotierten
   Erwähnung, und eine Aussage kann fehlerfrei elaborieren und trotzdem das
   Falsche sagen. Wer eine Aussage mit zwei σ-Algebren, zwei Topologien oder
   zwei Maßen schreibt, annotiert entweder jede Erwähnung oder stellt die
   umgebende Struktur zuletzt. **Die anderen drei `Suggested.lean` sind
   daraufhin durchgesehen und sauber**: keine Deklaration führt zwei Instanzen
   derselben Struktur auf demselben Typ. `MartingaleProblems` hat genau ein
   `{m : MeasurableSpace Ω}` (Zeile 63) und daneben nur `MeasurableSpace` auf
   `ι`, `E` und `F`; `SkorokhodSpace` hat `MeasurableSpace ι`,
   `MeasurableSpace E` und die Borelstruktur auf `D(ι, E)`, sämtlich auf
   verschiedenen Typen; `KolmogorovExtension` hat gar keine `Suggested.lean`.

**Mitgefunden, zwei Veraltungen.** `measure_inter_add_diff` ist seit dem
2026-06-03 `deprecated` und heißt jetzt `measure_inter_add_sdiff`
(`Measure/MeasureSpace.lean:118`); `Set.diff_eq` ist `deprecated` zugunsten von
`Set.sdiff_eq`. Beide sind in v4.33.1 noch da, aber der Linter meldet sie —
ein Hinweis für Rückstau 5, dessen nächste Runde in etwa einer Woche fällig
ist: der billigste Weg zu den Veraltungen ist, jede `Suggested.lean` einmal
durch `lake env lean` zu schicken und die Warnungen zu lesen.

**Ein Unfall, der aufgeräumt gehört.** Ein `lake env lean` ohne den
vorangehenden `cd ~/Code/lean/journal` — das Arbeitsverzeichnis der Shell bleibt
zwischen Werkzeugaufrufen stehen — hat `lake` im Worktree gestartet, das
daraufhin anfing, sich ein eigenes Mathlib zu klonen, und
`/home/pfaffelh/Code/lean/journal-facts/.lake` mit 671 MB halbfertiger
Paketklone hinterlassen hat. Der Lauf konnte es nicht wieder löschen: die
Sandbox verbietet `rm` unterhalb des Worktrees. **Der Ordner ist unbrauchbar
und gehört von Hand gelöscht.** Die Regel steht jetzt oben in `BACKLOG.md`:
`lake env lean` immer mit dem `cd` im selben Befehl.

**Zweiter Teil desselben Laufs: `StronglySeparatesPoints.separatesPoints`.** Er
war als billigster Nachbar in Meilenstein 1 angesetzt und ist es auch gewesen —
sechs Zeilen: `δ := dist y x`, `dist_pos`, dann gibt `ε ≤ |f y - f x|` bei
`f x = f y` ein `ε ≤ 0`. Damit tragen **sieben** Deklarationen von Meilenstein 1
Beweise. Der Linter hat dabei noch einmal die stehende Regel über minimale
Voraussetzungen durchgesetzt: `[MeasurableSpace E]` kommt im Beweis nicht vor
und steht jetzt unter `omit`. Nicht angefaßt bleibt der dritte Nachbar,
`IsSeparating.of_subalgebra`: Mathlibs
`ext_of_forall_mem_subalgebra_integral_eq_of_polish`
(`Measure/FiniteMeasureExt.lean:72`) ist über einer `StarSubalgebra 𝕜 (E →ᵇ 𝕜)`
formuliert, unsere Aussage über einer `Subalgebra ℝ (E →ᵇ ℝ)`, und die
Übersetzung geht über die triviale Sternstruktur auf reellwertigen Funktionen
und über `RCLike.restrict_toContinuousMap_eq_toContinuousMapStar_restrict`
(dieselbe Stelle, die Mathlib in seinem eigenen Beweis benutzt). Das ist eine
eigene halbe Stunde und kein Nachbar mehr.

**Offen geblieben.** Nichts aus Rückstau 1; der Punkt ist gestrichen.

**Was als Nächstes formalisiert werden soll:
`MeasureTheory.induction_on_mulSystem`,** der funktionale
Monotone-Klassen-Satz — Rückstau 2, `WeakConvergence` Meilenstein 5, Task 25 in
`PLAN.md`. Er ruht auf `MeasurableSpace.comap`, auf monotoner Konvergenz und auf
`induction_on_inter`, das zugleich die Vorlage ist, und er deckt
`fact:monotoneclass`, tragend `4` — die höchste Zahl der Tabelle, und der
einzige Fact mit dieser Zahl, für den Mathlib nur die **Mengenfassung** hat. Er
ist jetzt dran, weil Rückstau 1 weg ist und weil er die drei bereits
formulierten Roadmap-Punkte freigibt, die auf ihm warten. Er ist allerdings
kein Ein-Lauf-Ziel: er braucht zuerst `IsMulSystem` und `generateFromFuns`, die
in keiner `Suggested.lean` stehen, und erst danach den Induktionssatz selbst.
Wer ihn aufnimmt, schreibe im ersten Lauf die beiden Definitionen samt
`isMulSystem_indicator_of_isPiSystem` und
`generateFromFuns (indicators of 𝒞) = generateFrom 𝒞` und übersetze sie; das
ist die Brücke zu `induction_on_inter`, und ohne sie hat der Induktionssatz
keine Aussage, gegen die er bewiesen werden könnte.

Zweiter Kandidat, kleiner und in einem Lauf zu schaffen:
`IsSeparating.of_subalgebra`, die dritte offene Deklaration von Meilenstein 1.
Sie ruht ganz auf `ext_of_forall_mem_subalgebra_integral_eq_of_polish`, und die
einzige Arbeit ist die Übersetzung zwischen `Subalgebra ℝ (E →ᵇ ℝ)` und
`StarSubalgebra ℝ (E →ᵇ ℝ)` über die triviale Sternstruktur, samt der
entsprechenden Übersetzung der Trennungshypothese. Sie ist dann dran, wenn
Meilenstein 1 geschlossen werden soll, bevor Meilenstein 5 aufgemacht wird —
denn `isTightMeasureSet_of_stronglySeparatesPoints`, der Vorschlag des Laufs
vom 2026-09-05, ist nach diesem Lauf der einzige Punkt von Meilenstein 1, der
echte neue Mathematik verlangt und nicht bloß Mathlib-Übersetzung.

### 2026-09-06, zweiter Lauf des Tages — Rückstau 2: der Unterbau von Meilenstein 5

**Lage zu Beginn.** Keine vorrangigen Aufgaben, keine Zeile der Tabelle mit
Status `?`. Also Rückstau, von oben: Punkt 1 ist seit dem ersten Lauf des Tages
gestrichen, Punkt 2 ist `MeasureTheory.induction_on_mulSystem`, der funktionale
Monotone-Klassen-Satz — `WeakConvergence` Meilenstein 5, `fact:monotoneclass`,
tragend `4`. Der erste Lauf des Tages hatte für den ersten Durchgang genau
vorgeschrieben, was zu tun ist: die beiden Definitionen samt Brücke schreiben
und übersetzen, bevor der Induktionssatz eine Aussage hat, gegen die er
bewiesen werden könnte.

**Der Negativbefund zuerst, mit der Liste, die die Regel verlangt.** Gesucht
wurde an `upstream/master` (`810b3888`, 2026-09-05) mit `git grep`, in Mathlibs
Vokabeln und nicht in unseren: `monotone class` (case-insensitiv, kein Treffer
in ganz `Mathlib/`), `MulSystem`, `generateFromFuns`, `multiplicative system`,
`monotone limits`, `bounded monotone convergence`, `functional monotone`,
`multiplicative family of functions`. Kein einziger Treffer. Mathlib hat die
Mengenfassung, und sie heißt `MeasurableSpace.induction_on_inter`
(`MeasureTheory/PiSystem.lean:713`) — die Roadmap nannte sie ohne Namensraum,
was in `MeasureTheory` zu lesen nahelag und falsch gewesen wäre; berichtigt.

**Ergebnis: zwölf Deklarationen von Meilenstein 5, alle mit Beweis und alle
übersetzt.** In `TauCeti/WeakConvergence/Suggested.lean` stehen jetzt, und die
ganze Datei geht durch `lake env lean` gegen `v4.33.1` ohne Fehler und ohne
andere Warnung als `declaration uses 'sorry'` (einzige Ausnahme unverändert und
dokumentiert: `tendsto_map_of_measure_setOf_continuousAt_eq_one`, absichtlich
für `upstream/master` geschrieben):

* `IsMulSystem`, `indicatorFuns` und `indicatorFuns_mono`;
* `isMulSystem_indicator_of_isPiSystem`;
* `generateFromFuns`, `measurable_generateFromFuns_of_mem`,
  `generateFromFuns_le_iff`, `generateFromFuns_mono`;
* `generateFromFuns_indicatorFuns`, die Brücke zu `induction_on_inter`;
* `ioiCells`, `isPiSystem_ioiCells` und
  `generateFromFuns_eq_generateFrom_ioiCells` — das π-System, an dem
  `induction_on_inter` angreift, und die Identität, die den funktionalen Satz
  auf den Mengensatz legt;
* `of_tendstoUniformly_of_mono_lim`, der erste der vier Beweisschritte.

Dazu als Aussage mit `sorry`: `induction_on_mulSystem`,
`ext_of_forall_integral_eq_of_isMulSystem`,
`integral_mul_eq_zero_of_isMulSystem` und
`condExp_eq_of_forall_integral_mul_eq`.

**Drei Befunde an den Aussagen, alle beim Aufschreiben gefunden, alle in der
Roadmap berichtigt.**

1. **`isMulSystem_indicator_of_isPiSystem` war in der Fassung der Roadmap
   falsch.** Sie sagte, für ein π-System `𝒞` bildeten die Indikatoren der
   Mengen aus `𝒞` ein multiplikatives System. Das gilt nicht: ein π-System muß
   `∅` nicht enthalten (Mathlibs `IsPiSystem` verlangt `s ∩ t ∈ C` nur für
   nichtleeren Schnitt, gerade deshalb), und für `s ∩ t = ∅` ist das Produkt
   der beiden Indikatoren die konstante `0`, also der Indikator von `∅` und von
   keiner anderen Menge. Kleinster Zeuge: `𝒞 = {{0}, {1}}` auf `ℕ`, ein
   π-System, dessen Bedingung leer erfüllt ist. Die Aussage steht jetzt über
   `indicatorFuns (insert ∅ 𝒞)`, und das kostet nichts, weil
   `MeasurableSpace.generateFrom_insert_empty` (`MeasurableSpace/Defs.lean:426`)
   und die mitbewiesene Brücke
   `generateFromFuns (indicatorFuns (insert ∅ 𝒞)) = generateFrom 𝒞` das `∅`
   wieder wegnehmen.

2. **`integral_mul_eq_zero_of_isMulSystem` fehlte die Hypothese über die
   Konstante.** Die Roadmap sagte: `∫ g * f ∂μ = 0` für alle `f ∈ K` gebe
   dasselbe für jede beschränkte `generateFromFuns K`-meßbare Funktion. Falsch
   für `K = {0}`: dann ist `generateFromFuns K = ⊥`, dessen beschränkte meßbare
   Funktionen auf nichtleerem `Ω` die Konstanten sind, und `∫ g * c ∂μ = 0`
   verlangt `∫ g ∂μ = 0`, was die Hypothese über `K` nicht hergibt. Ergänzt als
   eigene Hypothese `∫ g ∂μ = 0`; sie ist schwächer, als `(1 : Ω → ℝ) ∈ K` zu
   verlangen. Es ist dieselbe Lücke wie die Gesamtmasse in
   `ext_of_forall_integral_eq_of_isMulSystem` — dort hatte die Roadmap sie von
   Anfang an richtig, hier nicht, und beide Male ist der Grund derselbe: ein
   multiplikatives System muß die Konstanten nicht enthalten.

3. **Die `RCLike`-Varianten galten pauschal „für alles Obige", und für den
   Induktionssatz gibt es sie nicht.** Das Manuskript sagt es selbst, in
   `fact:submgreg`: „here, and in Fact~\ref{fact:monotoneclass}, $\K = \R$ is
   genuinely needed, an order being involved". Der monotone Limes braucht die
   Ordnung. Für die beiden Folgerungen gibt es sie sehr wohl, aber nicht auf
   dem in der Roadmap genannten Weg — `Re f · Re g` ist nicht `Re (f * g)`, das
   Zerlegen von `K` in Real- und Imaginärteil zerstört also die
   Multiplikativität. Der Weg, der trägt, steht jetzt dort: `A_ℝ`, die
   reellwertigen Elemente der von `K` und den Konstanten erzeugten
   `𝕂`-Algebra `A`, ist unter Multiplikation abgeschlossen, die Maße stimmen
   auf ihm aus Linearität überein, und
   `generateFromFuns A_ℝ = generateFromFuns K`, weil `Re f` und `Im f` für
   `f ∈ A` in `A_ℝ` liegen (dafür ist `K` als konjugationsabgeschlossen
   vorauszusetzen).

**Mitgefunden, zwei Kleinigkeiten am Übersetzen.** `generateFromFuns` braucht
`@[instance_reducible]`, weil es eine Definition von Klassentyp ist und der
Linter sonst meldet; Mathlib macht es bei `MeasurableSpace.generateFrom`
genauso (`MeasurableSpace/Defs.lean:329`). Und `MeasurableSet.empty` läßt sich
nicht gegen eine erwartete, nicht als Instanz vorliegende σ-Algebra
elaborieren — `MeasurableSpace.measurableSet_empty _` mit explizitem `m` tut es.

**Der eine bewiesene Beweisschritt, und warum gerade er.** Der Beweisweg, den
die Roadmap jetzt ausschreibt, hat vier Schritte: (i) Abschluß unter
gleichmäßigen Limiten; (ii) `P (φ ∘ (f₁,…,fₙ))` für stetiges `φ`, über Polynome
und Stone--Weierstraß auf dem kompakten Bild; (iii) die Indikatoren des
π-Systems `{⋂ i ∈ s, f i ⁻¹' Ioi (c i)}` und `induction_on_inter`; (iv)
einfache Funktionen und ein letzter monotoner Limes. Schritt (i) ist
`of_tendstoUniformly_of_mono_lim` und ist bewiesen: wähle zu jedem `k` ein
`m k` mit `|f (m k) x - g x| ≤ (1/2)^(k+2)` gleichmäßig und schiebe um
`(1/2)^k` nach unten; die Verschiebung macht die Folge monoton (die Rechnung
hat Luft: der Zuwachs ist mindestens `(1/2)^(k+3)`), läßt sie gleichmäßig
beschränkt und ändert den Limes nicht. Er benutzt die Multiplikativität nicht
und gilt für jede lineare Klasse — deshalb ist er ein eigenes Lemma und kein
Teil der Induktion. Der frühere Beweisentwurf im Docstring — Indikatoren von
`{f ≥ c}` als monotone Limiten von `min 1 (n * (f - c))⁺` — ist gestrichen: die
Mengen `{f₁ ≥ c₁} ∩ {f₂ ≥ c₂}` sind nicht wieder von dieser Gestalt, das
π-System kommt so nicht zustande.

**Das π-System, im selben Lauf mit erledigt.** Nachdem Schritt (i) stand, war
Schritt (iii) zur Hälfte greifbar und ist gemacht:
`generateFromFuns_eq_generateFrom_ioiCells` sagt
`generateFromFuns K = MeasurableSpace.generateFrom (ioiCells K)`, und
`isPiSystem_ioiCells` sagt, daß `ioiCells K` ein π-System ist. Die eine
Richtung ist `measurable_of_Ioi` (`Constructions/BorelSpace/Order.lean:653`;
sein `{mδ : MeasurableSpace δ}` ist strikt implizit und nicht
instanzimplizit, unifiziert also mit der erwarteten, nicht als Instanz
vorliegenden σ-Algebra), die andere eine Induktion über die Liste. Zwei
Entwurfsentscheidungen, die festgehalten gehören: **die einzelnen Urbilder
`f ⁻¹' Ioi c` bilden kein π-System**, deshalb sind die endlichen Schnitte in
die Familie eingebaut; und die Familie ist über eine
`List ((Ω → ℝ) × ℝ)` indiziert und nicht über ein `Finset (Ω → ℝ)` mit
Niveaufunktion, weil zwei Faktoren dasselbe `f` mit verschiedenen `c` nennen
dürfen — das Aneinanderhängen von Listen ist dann genau der Abschluß unter
Durchschnitt.

**Offen geblieben.** Der Induktionssatz selbst, also Schritt (ii), die
Approximationshälfte von (iii) und Schritt (iv), und mit ihm die drei
Folgerungen. Rückstau 2 bleibt deshalb stehen, mit Zwischenstand.

**Was als Nächstes formalisiert werden soll: Schritt (ii),
`MeasureTheory.of_continuous_comp_of_isMulSystem`** — für `f : Fin n → Ω → ℝ`
mit `f i ∈ K`, sämtlich beschränkt, und stetiges `φ : (Fin n → ℝ) → ℝ` gilt
`P (fun x => φ (fun i => f i x))`. Sie ruht auf drei Dingen, die alle
dastehen: `of_tendstoUniformly_of_mono_lim`, das dieser Lauf bewiesen hat und
das die gleichmäßige Approximation überhaupt erst zuläßt; der
Multiplikativität von `K` samt Linearität und Konstanten, die die Polynome in
`f₁,…,fₙ` abdecken; und
`ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints`
(`Topology/ContinuousMap/StoneWeierstrass.lean:297`, am 2026-09-06 an
`upstream/master` belegt, Namensraum `ContinuousMap`, Zeilen 58–352), angewandt
auf die von den Koordinaten erzeugte Unteralgebra über dem kompakten Bild von
`x ↦ (f₁ x, …, fₙ x)` in `Fin n → ℝ`. Sie ist jetzt dran, weil sie der einzige
verbleibende Schritt mit echtem mathematischem Inhalt ist: aus ihr folgt die
Approximationshälfte von (iii) durch stetige Funktionen, die von unten gegen
den Indikator einer Box wachsen, und Schritt (iv) ist danach Linearität und ein
letzter monotoner Limes.

Zweiter Kandidat, unverändert vom ersten Lauf des Tages:
`IsSeparating.of_subalgebra`, die dritte offene Deklaration von Meilenstein 1,
eine reine Übersetzung zwischen `Subalgebra ℝ (E →ᵇ ℝ)` und
`StarSubalgebra ℝ (E →ᵇ ℝ)`.

### 2026-09-06, dritter Lauf des Tages — vorrangige Aufgabe: charakteristische Funktionen als trennende Klasse

**Lage zu Beginn.** Die vorrangige Aufgabe vom 2026-09-06 stand ungestrichen da
und trug keinen Zwischenstand; kein Laufbericht deckte sie ab. Sie hat also
Vorrang vor dem Rückstau. Drei Punkte, alle drei erledigt; Punkt 3 negativ, und
das ist der eigentliche Ertrag.

**Punkt 1: der Befund ist am Quelltext bestätigt und eingetragen.** Geprüft an
`upstream/master` `810b3888` (2026-09-05) und an v4.33.1, beide Male mit
identischem Inhalt und nur verschobenen Zeilennummern:

* `Measure.ext_of_charFun` — master `:257`, v4.33.1 `:248` —, unter
  `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]` und
  `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`;
* `Measure.ext_of_charFunDual` — master `:462`, v4.33.1 `:453` —, unter
  `[NormedAddCommGroup E] [NormedSpace ℝ E]` und denselben drei
  Raum-Instanzen;
* beide über `ext_of_integral_char_eq` (master `:103`, v4.33.1 `:101`), dessen
  erste Beweiszeile
  `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`
  (`Measure/FiniteMeasureExt.lean:36`) auf `separatesPoints_charPoly`
  (`Analysis/Fourier/BoundedContinuousFunctionChar.lean:155`) anwendet;
* `charPoly` (`ibid.:141`) ist die von den Charakteren erzeugte
  `StarSubalgebra ℂ (V →ᵇ ℂ)`, gebaut als `(charAlgHom he hL).range` mit
  `star_mem'` aus `star_mem_range_charAlgHom`.

Keine der vier Deklarationen trägt `deprecated`; die Datei kennt das Attribut
überhaupt nicht, ebensowenig `BoundedContinuousFunctionChar.lean` und
`FiniteMeasureExt.lean`. Eingetragen ist das bei `fact:stoneweierstrass` und,
mit der Einschränkung von Punkt 2, bei `fact:sepcond`; dazu ein Punkt in
`WeakConvergence`, Abschnitt „What Mathlib already has", damit ein künftiger
Lauf den Weg nicht noch einmal sucht.

Zwei Beobachtungen, die über die Aufgabenstellung hinausgehen und die
Bauform von Meilenstein 1 stützen. Erstens ist `charPoly` eine
**Stern**-Unteralgebra, also genau die Konjugationsabgeschlossenheit, die
`fact:stoneweierstrass` für $\K=\C$ eigens verlangt („the one place in the
manuscript where the complex case is not automatic") — Manuskript und Mathlib
stolpern hier über dieselbe Stelle und lösen sie gleich. Zweitens trennt
`ext_of_charFun` **endliche** Maße, ist also stärker als unser `IsSeparating`,
das über Wahrscheinlichkeitsmaßen quantifiziert; die Richtung stimmt, es ist
eine Instanz und keine Abschwächung.

**Punkt 2: jede Fundstelle des Manuskripts, an der eine trennende Klasse
konkret instanziiert wird, mit der Antwort auf die Strukturfrage.** Die
Einschränkung ist wie in der Aufgabe vermutet ernst, und sie ist bindend: alle
drei Sätze verlangen, daß das Maß auf dem **Modul selbst** lebt —
`ext_of_integral_char_eq` unter `[AddCommGroup V] [Module ℝ V]
[PseudoEMetricSpace V] [CompleteSpace V] [SecondCountableTopology V]
[BorelSpace V]`, die beiden Folgerungen unter Innenprodukt- bzw. Banachraum.
\eqref{E2} gibt separabel metrisierbar, \eqref{E3} gibt polnisch, und keines
von beidem gibt eine Vektorraumstruktur.

| Fundstelle | trennende Klasse | Raum | lineare Struktur? |
|---|---|---|---|
| `ex:determining` (Z. 2355), \eqref{T2b}+\eqref{E2} | $\ZZ^\circ_t=\{\prod_i h_i(X_{t_i})\}$, $h_i\in\Cb(E)$ | Pfadraum $\DE$ bzw. $\CE$ über abstraktem $E$ | nein |
| `fact:fdd` (Z. 1439) | $\{x\mapsto\prod_k f_k(x_k)\}$ aus trennenden $M_k$ | $\prod_k S_k$, $(S_k,d_k)$ separabel | nein |
| `thm:absreg` (Z. 3081) | $\Phi\subset\Cb(E)$, trennend und mit abzählbarer punktetrennender Teilmenge | abstraktes $E$ unter \eqref{E2} | nein |
| `rem:EKrelcompact` (Z. 8338) | eine Algebra in $\dom(A)$, punktetrennend und nirgends verschwindend | $(E,r)$ polnisch | nein |
| `cor:uniqviadual`(i) (Z. 6879) | $\{f(\cdot,y):y\in E_2\}\subset\Bdd(E)$ | abstraktes $E$ unter \eqref{E2} | nein |
| `prop:rieszmarkov` (Z. 7225) | $\mathcal H_1=\operatorname{span}\{H(\cdot,y)\}$, konvergenzbestimmende Algebra mit Konstanten | $E_1$ kompakt metrisierbar | nein |
| `lem:histrestart`(iii) (Z. 7362), `prop:hawkesduality`(D2) (Z. 7622) | $\operatorname{span}\{H_r(\cdot,f)\}$, Laplace-Funktionale | $\hat E_r$ = endliche Zählmaße auf $[0,r]$ | **fast**, siehe unten |
| `prop:jumpwellposed` (Z. 7942) | $\Bdd(E)$ | abstraktes $E$ | nein (keine Wahl getroffen) |

Die Antwort ist also durchweg **nein**, und an den beiden Stellen, an denen
lineare Struktur überhaupt im Manuskript vorkommt, hilft sie nicht:

* **$E=\R^d$ (§7.5, `eq:sdegen` Z. 8081, `cor:sdewellposed`).** Hier läge die
  Struktur vor, aber das Manuskript instanziiert dort **keine** trennende
  Klasse: der $\R^d$-Weg läuft über `fact:strookvaradhan` (Stroock--Varadhan,
  Z. 8100) und `fact:yamadawatanabe`, nicht über `thm:absreg` oder
  `rem:EKrelcompact`. Die einzige konkrete Algebra in einem $\dom(A)$ über
  einem linearen Zustandsraum ist $C^\infty_c(\R^d)$, und sie ist kompakt
  getragen und reell — Charaktere sind weder das eine noch das andere. Auch
  `ex:invariance` (Z. 8779, $E=\R^d$) wählt keine trennende Klasse, sondern
  Generatorkonvergenz.
* **$E=\mathcal S'(\R^d)$ (`rem:E1why`, Z. 938).** Das ist die Stelle, an der
  Charaktere klassisch das Werkzeug sind (Bochner--Minlos), und genau dort
  greift Mathlib nicht: `ext_of_integral_char_eq` verlangt
  `[PseudoEMetricSpace V]`, und $\mathcal S'(\R^d)$ erfüllt nach
  `def:Ebundles` (Z. 902) gerade \eqref{E1} und **nicht** \eqref{E2}, ist also
  nicht metrisierbar; `ext_of_charFunDual` verlangt darüber hinaus eine Norm.
  Das Manuskript sagt an derselben Stelle selbst, daß §\ref{sec:cadlag} und
  §\ref{sec:convergence} dort nicht gelten und die Reparatur Mitomas Satz wäre.
  Mathlib bringt diesen Fall also nicht näher, und `rem:E1why` steht
  unverändert richtig da.

**Der Beinahe-Treffer, und warum er keiner ist.** Die einzige *konkrete*
trennende Klasse des ganzen Manuskripts ist die Hawkes-Dualität
(`set:hawkesdual`, Z. 7439): $H_t(\hat x,f)=\exp\{-\int_{[0,t]}f\dif\hat x\}$
auf $\hat E_t$ = endliche Zählmaße auf $[0,t]$, und
`prop:hawkesduality`(D2) begründet die Trennung mit „Laplace functionals
determining the law of a point process". Das ist strukturell dieselbe
Konstruktion wie `charPoly` — der Spann von Exponentialen einer bilinearen
Paarung —, und trotzdem ist Mathlibs Satz nicht anwendbar, aus zwei
unabhängigen Gründen. Erstens ist der Exponent **reell**: Mathlibs `char` ist
aus einem `AddChar ℝ Circle` gebaut, also Fourier und nicht Laplace, und
`ext_of_charFun` sagt über Laplace-Transformierte nichts. Zweitens ist
$\hat E_t$ unter Addition abgeschlossen, aber **kein $\R$-Modul** — die
Zählmaße sind ein Untermonoid der Maße, kein Untervektorraum —, und das ist die
Instanz `[Module ℝ V]`, an der `ext_of_integral_char_eq` hängt. Mitgeprüft:
Mathlib hat Punktprozesse überhaupt nicht; `git grep` an `upstream/master` nach
`Laplace functional`, `laplaceFunctional` und `PointProcess` über ganz
`Mathlib/` liefert **keine einzige Datei**. Die Aussage, die
`prop:hawkesduality`(D2) zitiert, ist damit weder in Mathlib noch in einer
Roadmap — sie steht aber auch in keinem `\begin{fact}`, gehört also nicht in
dieses Inventar, sondern unter die Auffälligkeiten (siehe unten).

**Punkt 3: der Negativbefund. Meilenstein 1 spart keinen Punkt ein.** Die
Aufgabe verlangt, das ebenso deutlich zu sagen wie einen Fund, und hier ist es,
Punkt für Punkt:

* `IsSeparating.of_subalgebra` ist die **allgemeine** Aussage über
  `Subalgebra ℝ (E →ᵇ ℝ)` auf polnischem $E$; `Measure.ext_of_charFun` ist eine
  einzelne Instanz davon über $\C$ und über einem Innenproduktraum und liefert
  sie nicht. Umgekehrt ist der Punkt durch den Befund eher **bestätigt**: sein
  Beleg `ext_of_forall_mem_subalgebra_integral_eq_of_polish` (`:72`) ist der
  polnische Zwilling genau des Satzes, den Mathlib in `ext_of_integral_char_eq`
  selbst benutzt.
* `isTightMeasureSet_of_stronglySeparatesPoints` bleibt unberührt:
  charakteristische Funktionen sagen über Straffheit nichts, und der Weg von
  starker Trennung zur Straffheit kommt in `CharacteristicFunction/` nicht vor.
* `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support` und
  `…_hasCompactSupport` bleiben unberührt: Charaktere haben keinen beschränkten
  Träger, und `fact:convdet` ist eine Aussage über separabel metrische Räume
  ohne lineare Struktur.
* Der Produktpunkt, der Punkt über abzählbare trennende Klassen und
  `IsSeparating.ae_eq_of_forall_condExp_eq` bleiben unberührt; alle drei sind
  über abstraktem $E$ formuliert, und die Tabelle oben zeigt, daß genau so die
  Fundstellen aussehen.

Es bleibt also bei den Punkten, die Meilenstein 1 hat. Der Ertrag ist ein
**Beleg für seine Bauform**, wie die Aufgabe es vorwegnimmt, und ein zweiter,
den sie nicht vorwegnimmt: die Strukturfrage ist an allen acht Fundstellen
verneint, und damit ist ausgeschlossen, daß ein späterer Lauf einen der Punkte
durch eine Charakter-Instanz zu ersetzen versucht. **Die Aufgabe ist erledigt
und nicht offen.**

**Zwei Auffälligkeiten, mitgefunden.**

1. **`def:separating` ist nur für $M\subset\Cb(S)$ erklärt, das Manuskript
   benutzt „trennend" aber auch für $\Bdd(E)$-Familien** —
   `cor:uniqviadual`(i) (Z. 6879: „$\{f(\cdot,y):y\in E_2\}\subset\Bdd(E)$ is
   separating for $\Prob(E)$") und `prop:jumpwellposed` (Z. 7942: „since
   $\Bdd(E)$ is separating"). Gemeint ist offensichtlich dieselbe Bedingung
   $\int f\dif P=\int f\dif Q\ \forall f\in M\Rightarrow P=Q$, die die
   Stetigkeit gar nicht braucht. Für die Formalisierung ist das folgenlos und
   sogar schon richtig entschieden: Meilenstein 1 erklärt
   `IsSeparating (Γ : Set (E → ℝ))` über **beliebigen** reellen Funktionen
   (`Suggested.lean:79`), nicht über `E →ᵇ ℝ`, und deckt beide Lesarten ab. Das
   Manuskript wird nicht geändert; festgehalten, damit niemand die
   Lean-Definition nachträglich an `def:separating` „angleicht" und sich die
   beiden Fundstellen verbaut.
2. **`prop:hawkesduality`(D2) zitiert eine Aussage ohne `\begin{fact}`** — die
   Bestimmung eines Punktprozesses durch sein Laplace-Funktional. Sie wird
   benutzt und nicht bewiesen, gehört also der Sache nach zur
   Voraussetzungsfläche, steht aber in keinem der 29 Facts und damit in keiner
   Zeile dieses Inventars. Mathlib hat sie nicht (Negativbefund oben, mit den
   drei Suchen). Das ist keine Lücke der Roadmaps im Sinne der Aufgabe — die
   Roadmaps decken die Facts ab —, sondern eine Beobachtung am Zuschnitt der
   Fact-Liste, und sie gehört dem Nutzer vorgelegt, bevor jemand daraus einen
   Roadmap-Punkt macht.

**Offen geblieben.** Nichts aus der Aufgabe. Der Rückstau ist unangetastet;
Punkt 2 (`induction_on_mulSystem`) steht mit dem Zwischenstand des zweiten
Laufs des Tages.

**Zweiter Teil desselben Laufs: `IsSeparating.of_subalgebra` ist bewiesen und
übersetzt.** Nachdem die vorrangige Aufgabe erledigt war, lag dieser Punkt so
nahe, daß er vor dem Rückstau drankam — er ist genau die Deklaration, an der
unser Prädikat an denjenigen Mathlib-Satz andockt, den Mathlib für
`ext_of_charFun` selbst benutzt, und beide vorigen Läufe hatten ihn als
Zweitkandidaten benannt. (Rückstau 2 bleibt damit unangetastet stehen; sein
nächster Schritt (ii) ist der Stone--Weierstraß-Brocken und kein Rest eines
Laufs.) `TauCeti/WeakConvergence/Suggested.lean` trägt an dieser Stelle kein
`sorry` mehr; die Datei geht durch `lake env lean` gegen `v4.33.1` ohne andere
Fehler als den unverändert dokumentierten von
`tendsto_map_of_measure_setOf_continuousAt_eq_one` (absichtlich für
`upstream/master` geschrieben) und ohne andere Warnung als
`declaration uses 'sorry'`. **Acht** Deklarationen von Meilenstein 1 tragen
jetzt Beweise.

Der Beweis ist die Übersetzung, die die Roadmap beschreibt, und sie ist kürzer
als dort veranschlagt: `Subalgebra.SeparatesPoints.rclike_to_real` und
`RCLike.restrict_toContinuousMap_eq_toContinuousMapStar_restrict` werden **nicht
gebraucht**. Sie sind der Weg von einer `StarSubalgebra` über $\C$ zu ihrem
reellen Teil; wir sind schon über $\R$ und brauchen nur die Gegenrichtung, das
Anheften der trivialen Sternstruktur. Zwei Schritte: `A` wird zur
`StarSubalgebra ℝ (E →ᵇ ℝ)` mit `star_mem'` aus `star g = g`, und da `A'` und
`A` **dasselbe** `carrier` haben und `toContinuousMapStarₐ ℝ` dieselbe
zugrundeliegende Funktion wie `toContinuousMapₐ ℝ`, ist die Trennungshypothese
wörtlich dieselbe Aussage und geht durch Zerlegen und Wiederzusammensetzen des
Zeugen (`⟨_, ⟨F, ⟨g, hg, rfl⟩, rfl⟩, hne⟩`). Danach ist es ein `exact` auf
`ext_of_forall_mem_subalgebra_integral_eq_of_polish (𝕜 := ℝ)`.

**Ein Befund am Übersetzen.** `star g = g` für `g : E →ᵇ ℝ` geht **nicht** mit
`star_trivial`: das verlangt `TrivialStar (E →ᵇ ℝ)`, und diese Instanz gibt es
in v4.33.1 nicht — Mathlib hat `TrivialStar ℝ`, aber nicht das Hochheben auf
die beschränkten stetigen Funktionen. Der Ersatz ist punktweise, `ext a; simp`,
und ist eine Zeile. Das ist dieselbe Sorte Fehler wie der Namensraumfehler vom
2026-09-01: die Instanz *klingt*, als müßte sie da sein, und ist es nicht.
An `upstream/master` nachgeprüft, und dort ist die Asymmetrie ebenso: für
`C(α, β)` gibt es `ContinuousMap.instTrivialStar`
(`Topology/ContinuousMap/Star.lean:54`), für `C_c(α, β)` gibt es sie
(`ContinuousMap/CompactlySupported.lean:405`), für `C(X, R)₀` gibt es sie
(`ContinuousMap/ContinuousMapZero.lean:318`) — und
`Topology/ContinuousMap/Bounded/Star.lean` enthält das Wort `TrivialStar`
kein einziges Mal. Das ist ein einzeiliger Beitrag nach oben, wenn jemand ihn
mitnehmen will; für uns kostet es die eine `ext`-Zeile.

**Dritter Teil desselben Laufs: Rückstau 2, die algebraische Hälfte von Schritt
(ii).** Danach war noch Zeit, und der Reihenfolge nach steht Rückstau 2 oben.
Der Schritt (ii) als Ganzes ist ein Mehr-Lauf-Ziel; was in diesem Lauf
vollständig ging, ist seine algebraische Hälfte, und sie ist bewiesen und
übersetzt: `mul_mem_span_insert_one_of_isMulSystem`, `of_mem_span_insert_one`
und `exists_bound_of_mem_span_insert_one`. Dazu die Aussage von (ii) selbst als
`of_continuous_comp_of_isMulSystem`, mit `sorry` — sie stand bisher in keiner
`Suggested.lean`. **Zwanzig** Deklarationen der Datei tragen jetzt Beweise; sie
geht unverändert durch `lake env lean` mit dem einen dokumentierten
master-Fehler als einziger Ausnahme.

**Und der Befund, der die Gestalt von (ii) festlegt.** Die naheliegende
Induktion über `Algebra.adjoin` **trägt nicht**: ihr `mul`-Fall verlangt, daß
`P` unter Produkten abgeschlossen ist, und genau das ist `P` nicht — es ist
linear, enthält die Konstanten und ist unter beschränkten monotonen Limiten
abgeschlossen, und mehr steht in den Hypothesen von `induction_on_mulSystem`
nicht. Die Multiplikativität muß in `K` bleiben. Das tragende Objekt ist
deshalb `Submodule.span ℝ (insert 1 K)`, die von `K` erzeugte Unteralgebra: der
Spann ist unter Multiplikation abgeschlossen, weil `K * K ⊆ K` ist und die
hinzugefügte `1` eine Einheit ist, und `P` gilt auf ihm allein aus Linearität.
Er liegt zwischen `K` und `P`, und (ii) zieht die Stone--Weierstraß-Approximanten
durch ihn hindurch. Das ist der Grund, warum die drei Lemmata eigene
Deklarationen sind und nicht Zeilen im Beweis von (ii). Mitgefunden: der
bessere Anker für die verbleibende Hälfte ist die **unbebündelte** ε-Fassung
`ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints`
(`StoneWeierstrass.lean:313`, in v4.33.1 wie auf master), die `φ` als Funktion
samt `Continuous`-Beweis nimmt; und `abs_add` heißt in v4.33.1 `abs_add_le`.
Beides steht im Zwischenstand von Rückstau 2.

**Was als Nächstes formalisiert werden soll: die Approximationshälfte von
`MeasureTheory.of_continuous_comp_of_isMulSystem`** — Rückstau 2, das der
Reihenfolge nach oben steht, und der einzige verbliebene Schritt des
funktionalen Monotone-Klassen-Satzes mit echtem Inhalt. Die Aussage steht seit
diesem Lauf getippt und typgeprüft da, die algebraische Hälfte ist bewiesen,
und was fehlt, sind drei Dinge in dieser Reihenfolge: die kompakte Box
`Set.pi univ (fun _ => Icc (-C) C)` in `Fin n → ℝ`, die die Bilder von
`x ↦ (f₁ x, …, fₙ x)` enthält (`IsCompact.pi`, aus der Beschränktheit der
`f i ∈ K`); die Punktetrennung der von den Koordinatenabbildungen erzeugten
Unteralgebra von `C(box, ℝ)` — zwei Punkte der Box unterscheiden sich in einer
Koordinate; und der Rückzug entlang `x ↦ (f₁ x, …, fₙ x)`, der die
Unteralgebra nach `Submodule.span ℝ (insert 1 K)` schickt. Danach schließen
`exists_mem_subalgebra_near_continuous_of_separatesPoints` (`:313`),
`of_mem_span_insert_one` und `of_tendstoUniformly_of_mono_lim` den Beweis. Sie
ist jetzt dran, weil sie drei fertige Roadmap-Punkte freigibt und weil ihre
Vorarbeiten sämtlich in derselben Datei stehen; sie deckt `fact:monotoneclass`,
tragend `4`.

Zweiter Kandidat, und er ist nach diesem Lauf der Punkt von Meilenstein 1, an
dem die längste Kette hängt:
`MeasureTheory.isTightMeasureSet_of_stronglySeparatesPoints` — für polnisches
`E`, eine `A : Subalgebra ℝ (E →ᵇ ℝ)`, die Punkte **stark** trennt, und eine
Familie `μ : ι → ProbabilityMeasure E` entlang eines `NeBot`-Filters, deren
Integrale über `A` gegen die eines `μ₀` konvergieren, gilt
`IsTightMeasureSet {(μ n : Measure E) | n}`. Sie ruht auf
`StronglySeparatesPoints.separatesPoints` (bewiesen, 2026-09-06, erster Lauf)
und speist `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
(`Measure/LevyConvergence.lean:154`), woraus
`isConvergenceDetermining_of_stronglySeparatesPoints` fällt — die
konvergenzbestimmende Hälfte von `fact:stoneweierstrass`, tragend `3`. (Offen
bleiben in Meilenstein 1 daneben die Punkte zu `fact:convdet`, die Produkte
über beliebigem Index, die Stabilität unter beschränkten punktweisen Limiten
und die abzählbaren Klassen; keiner von ihnen speist einen weiteren Punkt
desselben Meilensteins.) Der Lauf vom 2026-09-05 hat
mit dem Gegenbeispiel $E=\R$, $A=\{f:\lim_{x\to\infty}f=f(0)\}$,
$\mu_n=\delta_n$ belegt, daß die Straffheit dabei wirklich aus der starken
Trennung kommen muß und nicht geschenkt ist. Sie ist kein Ein-Lauf-Ziel; wer
sie aufnimmt, baue zuerst die Hilfsaussage, daß starke Trennung an einem Punkt
`x` eine endliche Familie aus `A` und ein `ε > 0` liefert, mit denen sich das
Komplement einer Kugel um `x` gleichmäßig von `x` trennen läßt, und übersetze
sie.

### 2026-09-06, vierter Lauf des Tages — Rückstau 1: die Aussagen von `MartingaleProblems` sind jetzt Aussagen

Keine vorrangige Aufgabe, kein `?` in der Tabelle; also der Rückstau von oben.
Sein erster Punkt, am 2026-09-06 vom Nutzer eingetragen, verlangt
`SkorokhodSpace/Suggested.lean` und `MartingaleProblems/Suggested.lean` „zum
Übersetzen zu bringen", weil sie „nie übersetzt" seien.

**Die Prämisse stimmt nicht, und das war in zwei Minuten geklärt.** Beide
Dateien gehen unverändert durch `lake env lean` gegen `v4.33.1`, jede ohne eine
einzige Fehlermeldung; es gibt nur `declaration uses 'sorry'`-Warnungen, 23 in
`SkorokhodSpace`, 20 in `MartingaleProblems`. Punkt 3 desselben Rückstaus hält
genau das für den 2026-09-05 fest, und beide Dateiköpfe tragen den Vermerk seit
damals. Die Berichtigung steht im Rückstau.

**Was der Punkt in Wahrheit meint, gilt aber, und es war die Arbeit dieses
Laufs: eine `True`-Aussage übersetzt zwar, belegt aber nichts.**
`MartingaleProblems/Suggested.lean` führte sieben Sätze, deren *Aussage* `True`
war, und drei Definitionen, deren Rumpf `sorry` war — die Meilensteine 3, 5, 9
und 10. Für sie ist das `rc=0` der Datei wertlos: `theorem restart : True`
typisiert und sagt nichts. Aus dem Roadmaptext sind daraus Propositionen
geworden; **die Datei geht danach wieder durch `lake env lean`, ohne Fehler**,
mit jetzt 37 Deklarationen, von denen 12 ein `sorry` tragen — und jedes dieser
`sorry` steht in einem *Beweis*, keines mehr in einer Aussage.

**Meilenstein 9, der ganze Block zur Quasi-Linksstetigkeit.** Neu als Aussage:
`IsCadlagPath` (die Pfadbedingung von `IsCadlag` der Roadmap **SkorokhodSpace**,
Meilenstein 2, ausgeschrieben — der Pfadraum steht in dieser Datei nicht zur
Verfügung), `IsSeparating` (dasselbe Prädikat wie in **WeakConvergence**
Meilenstein 1, dort über `Set (E → ℝ)`, hier über `Set (E → 𝕂)`),
`IsCompensatorFor` als Struktur mit den vier Feldern der Zerlegung,
`IsRegularizingClass` als deren Existenzquantifizierung, `CompactContainment`,
`exists_cadlag_modification_of_isRegularizingClass`, `IsQuasiLeftContinuous`
wörtlich in der Gestalt, die der Roadmaptext vorgibt,
`IsQuasiLeftContinuous.ae_eq_leftLim`, `IsL1LeftContinuousAlongStoppingTimes`,
`isQuasiLeftContinuous_of_isRegularizingClass`,
`isQuasiLeftContinuous_of_isMPSolutionFor` und
`not_isQuasiLeftContinuous_of_atom`.

Drei Befunde an den Aussagen, alle beim Aufschreiben gefunden:

* **`Adapted` ist nicht mehr, was die Roadmap „adapted" nennt.** Mathlibs
  `Adapted` (`Probability/Process/Adapted.lean:60`) ist seit dem 2026-01-13
  Meßbarkeit bezüglich `f i` und verlangt `[∀ i, MeasurableSpace (β i)]`; die
  Datei sagt es in ihrem eigenen Doc-Kommentar (`:59`). Der Begriff, den der
  Roadmaptext meint und aus dem `Martingale` gebaut ist
  (`Probability/Martingale/Basic.lean:53`), heißt jetzt `StronglyAdapted`
  (`Adapted.lean:105`) und verlangt statt dessen die Topologie. Für ein
  `𝕂`-wertiges `C` ist das nicht Kosmetik: `RCLike 𝕂` liefert keine
  `MeasurableSpace 𝕂`-Instanz, die Aussage mit `Adapted` elaboriert also gar
  nicht erst. Das ist der Fehlertyp der Regel für den Negativbefund, nur in der
  Zeit statt im Namensraum, und er trifft jede Roadmapstelle, die „adapted"
  sagt.
* **Der Kompensator muß im Existenzquantor der Hypothese stehen, nicht in dem
  von `IsRegularizingClass`.** Der Roadmaptext verlangt für
  `isQuasiLeftContinuous_of_isRegularizingClass`, daß „der zu `f` gehörige
  Kompensator `C`" rechtsstetig und `L¹`-linksstetig entlang Stoppzeiten sei.
  Wer `IsRegularizingClass` als Hypothese nimmt und die Zusatzbedingung daneben
  stellt, sagt etwas anderes: die beiden Existenzquantoren müssen dasselbe `C`
  binden, sonst darf ein zweites, schlechteres `C` die erste Bedingung erfüllen.
  Deshalb ist die Zerlegung als eigene Struktur `IsCompensatorFor` geschrieben,
  und die Hypothese des Satzes bindet `Y` und `C` selbst; `IsRegularizingClass`
  ist die Existenzquantifizierung darüber, und die Hypothese impliziert sie.
* **`not_isQuasiLeftContinuous_of_atom` braucht, daß das Atom von links
  erreichbar ist.** Der Roadmaptext nennt nur den Atomcharakter; für `u = ⊥` ist
  die Behauptung falsch, weil es dann keine Folge `s n ↑ u` gibt und die
  Quasi-Linksstetigkeit an `u` nichts verlangt. Die Aussage trägt die Hypothese
  jetzt explizit (`∃ s, StrictMono s ∧ (∀ n, s n < u) ∧ Tendsto s atTop (𝓝 u)`).

**Meilenstein 3.** `IsCanonical` und `IsDetermining` sind Aussagen, dazu
`isMPSolution_iff_forall_fdd` und `isMPSolution_iff_forall_fdd_continuous`.
Zwei Befunde: `IsDetermining` brauchte drei Argumente, die die alte Signatur
nicht hatte (`X`, die Filtration, und die quantifizierten Maße) — ohne sie ist
die Aussage nicht formulierbar; und das **Äquivalenz**-Kriterium gilt nur für
die *natürliche* Filtration von `X`, weil die rechte Seite ausschließlich gegen
Koordinaten testet. Das steht jetzt als Hypothese
`h𝓕 : ∀ s, 𝓕 s = ⨆ r ∈ Set.Iic s, MeasurableSpace.comap (X r) inferInstance` in
beiden Sätzen; ohne sie ist die Richtung von rechts nach links falsch.
Mitgefunden und für jede künftige Datei zu beachten: `°` ist in Lean kein
Bezeichnerzeichen (`error: expected token`), die kanonischen Versionen heißen
darum `𝓧₀`, `Y₀`.

**Meilenstein 5.** `Shift` stand mit
`eval_comp : ∀ (_r _t : ι) (_f : F), (sorry : Prop)` da, und der Kopf der Datei
nannte als Grund, `Shift` trage „keine Auswertungsabbildung, gegen die sich
`eval t (θ r f) = eval (r + t) f` formulieren ließe". Das ist behoben, indem die
Koordinaten `π : ι → F → E` **Parameter der Struktur** werden; damit ist das
Feld `π t (θ r f) = π (r + t) f`, und die Struktur sagt, was ein Shift ist. Dazu
neu `IsShiftSystem`, `restart` und `restart_canonical` — die Aussagen des
Meilensteins, mit `Z • P` als `P.withDensity (ENNReal.ofReal ∘ Z)`.

**Meilenstein 10, und die Frage, die ihn aufgehalten hätte, ist am Manuskript
entschieden.** Hypothese (a) verlangt, daß „die reellen Zufallsvariablen
`Y₀ r (X n)` für `r ∈ D ∩ Iic t` und `(Y₀ t - Y₀ s) * Z (X n)` in Verteilung
gegen ihre Gegenstücke konvergieren", und ob das **gemeinsam** (endliche
Teilfamilien als Vektor) oder **einzeln** gemeint ist, sind zwei verschiedene
Aussagen. Der Text entscheidet es, und zwar zweimal: `thm:absconv` benutzt seine
Hypothesen \ref{it:C1} und \ref{it:C3a} im Beweis ausschließlich durch
`fact:cmt` auf **je einen** Funktional (Schritt 0 auf $|Y^\circ_r|$, Schritt 1
auf $\psi=(Y^\circ_t-Y^\circ_s)Z^\circ_s$, Schritt 2 auf
$\varphi_N\circ Y^\circ_r$), ein gemeinsames Gesetz kommt nirgends vor; und
`rem:absconvtopfree` zieht das ausdrücklich zusammen: \eqref{eq:C1prime} sind
genau die beiden **einzelnen** Konvergenzen, „and nothing else", und ihr Ersatz
läßt „the theorem and its proof standing verbatim". Also einzeln. Der Satz steht
jetzt da, samt `TendstoLaw` — Verteilungskonvergenz von Zufallsvariablen auf
**verschiedenen** Räumen, geschrieben durch Testen gegen beschränkte stetige
Funktionen, weil Mathlibs `TendstoInDistribution` einen festen Raum hat — und
samt der zweiten Hälfte `isMPSolution_of_forall_condExp_eq_of_dense`, dem
Schritt von `D` nach `ι`, mit `hDmax` für das größte Element. Damit trägt die
Datei **keine `True`-Aussage mehr**: 37 Deklarationen, 12 mit `sorry`, und jedes
`sorry` steht in einem Beweis.

Offen und nicht angefaßt: `MPSolutions.isConvex` und `MPSolutions.integral_mem`
aus Meilenstein 5 stehen in der Datei überhaupt nicht; sie sind Aussagen über
Mischungen und brauchen die Modulstruktur auf `Measure Ω`, die zuerst zu belegen
ist. `SkorokhodSpace/Suggested.lean` ist in diesem Lauf nur übersetzt, nicht
durchgesehen; seine 23 `sorry` stehen sämtlich in Beweisen, keine Aussage ist
dort `True`.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
`IsQuasiLeftContinuous.ae_eq_leftLim` in **MartingaleProblems** Meilenstein 9
zu **beweisen**, nicht nur zu formulieren: für ein `t`, das kein Minimum ist,
liefert die Definition an den konstanten Stoppzeiten `τ n = s n` mit `s n ↑ t`
die Aussage `∀ᵐ ω, Function.leftLim (X · ω) t = X t ω`. Sie ist jetzt dran, weil
sie der einzige Punkt des Blocks ist, dessen Beweis **nur** aus der eigenen
Definition und Mathlib besteht — `MeasureTheory.isStoppingTime_const`
(`Probability/Process/Stopping.lean:78`), `stoppedValue_const` (`:805`) und
`Function.leftLim_eq_of_tendsto` (`Topology/Order/LeftRightLim.lean:66`) sind
alles, was sie braucht —, und weil sie damit die erste bewiesene Deklaration
dieser Datei wäre; sie stützt `fact:Dcountable` (tragend `4`), dessen
Schärfung sie ist. Zu klären ist dabei genau eine Sache, und sie gehört in den
Bericht: ob `¬ IsMin t` die Existenz der Folge `s n ↑ t` schon gibt oder ob die
Aussage `(𝓝[<] t).NeBot` als Hypothese tragen muß — `leftLim_eq_of_tendsto`
verlangt es, und auf einer Ordnung mit Sprüngen ist es echt stärker als
`¬ IsMin t`.

### 2026-09-06, fünfter Lauf des Tages — Rückstau 1: die ersten Beweise in `MartingaleProblems` und `SkorokhodSpace`, und zwei falsche Aussagen

Keine vorrangige Aufgabe, kein `?` in der Tabelle; also der Rückstau von oben.
Sein Punkt 1 und das benannte Ziel des vierten Laufs:
`IsQuasiLeftContinuous.ae_eq_leftLim` **zu beweisen**, nicht nur zu formulieren.
Erledigt, aber erst nachdem die Aussage berichtigt war — und dabei fiel dieselbe
Sorte Fehler noch einmal an, in `SkorokhodSpace`. Vier Deklarationen tragen
jetzt Beweise, die durch `lake env lean` gegen `v4.33.1` gehen; beide Dateien
melden `rc=0` ohne Fehler und ohne Linterwarnung.

**1. `IsQuasiLeftContinuous.ae_eq_leftLim` unter `¬ IsMin t` ist falsch.** Die
Frage, die der vierte Lauf für diesen Lauf notiert hatte („gibt `¬ IsMin t` die
Folge `s n ↑ t` schon her?"), ist damit beantwortet, und schärfer als erwartet:
`¬ IsMin t` gibt sie nicht, und die Aussage ist unter ihm nicht bloß
unbeweisbar, sondern **widerlegbar**. Auf $\iota=\N$ und $t=1$ ist jede
monotone, durch $1$ beschränkte Folge von Stoppzeiten schließlich konstant, also
gilt `IsQuasiLeftContinuous` leer; zugleich ist `𝓝[<] (1 : ℕ) = pure 0`, also
`Function.leftLim (X · ω) 1 = X 0 ω`, und für einen einpunktigen Raum mit
`X 0 ω ≠ X 1 ω` ist das nicht `X 1 ω`.

**Und eine zweite Hypothese fehlte, die man am Text nicht sieht.** Der
Allquantor über Folgen steht in `IsQuasiLeftContinuous` **außerhalb** des
`∀ᵐ ω`, die Ausnahmemenge hängt also von der Folge ab, und überabzählbar viele
Folgen lassen sich nicht vereinigen. Aus der Quasi-Linksstetigkeit kommt daher
nur die Konvergenz entlang **einer** Folge, während `Function.leftLim` der Limes
entlang des Filters `𝓝[<] t` ist. Der Schritt von der Folge zum Filter braucht
die Existenz des Linkslimes als Hypothese — die zweite Hälfte von
`IsCadlagPath`, die \EK{} an dieser Stelle ohnehin voraussetzt. Die Aussage
trägt jetzt eine monotone Folge `s n < t` mit `s n → t`, die Existenz des
Linkslimes und `[T2Space E]`; bewiesen über `tendsto_atTop_ciSup` und
`WithTop.coe_iSup` für `⨆ n, (s n : WithTop ι) = t`, `isStoppingTime_const`,
`stoppedValue_const` und `leftLim_eq_of_tendsto`. `[MeasurableSpace E]` wird
nicht gebraucht und ist `omit`.

**2. `IsCadlag.eq_of_eqOn_dense` unter bloßer Dichtheit ist falsch, und
\eqref{T2b} rettet es nicht ganz.** Beim Beweisen aufgefallen, mit zwei Zeugen:

* $\iota=[0,1]\cup\{2\}$ — nach Meilenstein 1 zulässig, denn der Index ist eine
  **abgeschlossene Teilmenge von** $\R$ und kein Intervall — hat in $1$ einen
  rechtsisolierten, nicht isolierten Punkt; mit $D=([0,1)\cap\Q)\cup\{2\}$ sind
  $f\equiv0$ und $g=\mathbb 1_{\{1\}}$ beide càdlàg, stimmen auf dem dichten $D$
  überein und sind verschieden.
* Unter \eqref{T2b} fällt dieser Zeuge weg, ein **größtes** Element aber nicht:
  auf $\iota=[0,1]$ mit $D=[0,1)\cap\Q$ trennen dieselben zwei Funktionen, weil
  `𝓝[>] 1 = ⊥` ist und die Rechtsstetigkeit in $1$ nichts sagt.

Die Hypothese, die der Beweis wirklich benutzt, ist die Rechtsdichtheit:
`∀ t, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot`. Sie impliziert `Dense D` und
verlangt für ein größtes Element gerade `t ∈ D` — genau das, was Billingsley für
$D([0,1])$ verlangt und was das Manuskript in `thm:absconv` selbst hinschreibt,
in `thm:fdd` aber nicht. Zwei Manuskript-Auffälligkeiten dazu stehen oben
(`thm:fdd`; und „\eqref{T3p} implies \eqref{T2b}", was für diskrete Indizes
wörtlich falsch ist, Zeuge $\Z$). Der Beweis braucht weder die
Ordnungstopologie noch `AdditiveDist` noch Properness — `omit` an drei
Instanzen, wie die stehende Regel es verlangt.

**3. Zwei Beweise, die dabei abfielen.** `isCompact_exhaustion` ist
`isCompact_closedBall` (`ProperSpace` allein; `LinearOrder`, `OrderTopology`
und `AdditiveDist` sind `omit`), und `monotoneOn_dist_basepoint` sind drei
Zeilen über `dist_eq_sub_of_le` und `dist_nonneg` (`AdditiveDist` allein).
Beide Roadmap-Stellen tragen den Vermerk samt der minimalen Voraussetzung.

**4. Und die unterste Schicht von Meilenstein 3 dazu.** Nach den drei Beweisen
war noch Zeit, und der Befund unter „Was als Nächstes zu tun ist" (unten) war
schon geschrieben; also ist er zur Hälfte gleich mit erledigt.

* **`Group (TimeChange ι)` ist konstruiert**, nicht mehr `sorry`. Multiplikation
  ist Komposition (`l * l' = l ∘ l'`, also `OrderIso.trans` in der anderen
  Reihenfolge), Eins ist `OrderIso.refl`, Inverses ist `OrderIso.symm`, und die
  Bi-Lipschitz-Felder kommen aus `TimeChange.exists_lipschitzWith_trans` (neu,
  über `LipschitzWith.comp` und `OrderIso.coe_trans`) und `OrderIso.symm_trans`.
  Die vier Gruppenaxiome sind `TimeChange.ext rfl` bis auf
  `OrderIso.self_trans_symm`; `TimeChange.ext` (neu, `@[ext]`) gilt, weil die
  beiden anderen Felder Propositionen sind.
* **`TimeChange.lipConstOn` und `TimeChange.normOn` sind definiert:**
  `lipConstOn t₀ m l = sInf {K : ℝ≥0 | LipschitzOnWith K l.toOrderIso
  (exhaustion t₀ m)}` und `normOn t₀ m l = Real.log (max (lipConstOn t₀ m l)
  (lipConstOn t₀ m l⁻¹))`. Damit sind `normOn_one`, `normOn_mul_le` und
  `dist_le_of_normOn_le` überhaupt erst Aussagen über etwas.
* **`TimeChange.normOn_inv` ist bewiesen**, in einer Zeile: `inv_inv` und
  `max_comm`.
* Die Frage zu `normOn_one`, die der Vorschlag unten stellt, ist am Quelltext
  entschieden und steht als Doc-Kommentar an der Aussage: der Satz **gilt** in
  beiden Fällen, aber aus zwei verschiedenen Gründen. Hat `exhaustion t₀ m`
  zwei verschiedene Punkte, so ist die Menge der zulässigen Konstanten der
  Identität `Set.Ici 1`, also `lipConstOn = 1` und `Real.log 1 = 0`; ist sie
  einpunktig — `m = 0` in einem diskreten Index —, so ist jede Konstante
  zulässig, also `lipConstOn = 0`, und es trägt der **Müllwert**
  `Real.log 0 = 0`. Der Beweis ist damit eine Fallunterscheidung und kein
  Einzeiler; er steht noch aus.
* Mitgefunden: die Datei importierte `Mathlib.Analysis.SpecialFunctions.Exp`,
  aber nicht `…Log.Basic`, und `Real.log` gab „Unknown constant". Dasselbe war
  am 2026-09-05 mit `Real.exp` passiert.

**Stand der beiden Dateien.** `MartingaleProblems/Suggested.lean`: 37
Deklarationen, 11 mit `sorry`, jede Aussage eine Aussage.
`SkorokhodSpace/Suggested.lean`: 16 `sorry` statt 23. Beide `rc=0`, ohne Fehler
und ohne Linterwarnung.

**Was in `SkorokhodSpace` als Nächstes zu tun ist, und es ist derselbe Befund
wie der vom vierten Lauf, nur eine Stufe tiefer.** Die Datei hat keine
`True`-Aussage, aber **fünf Deklarationen mit `sorry` im Rumpf einer
Definition**: `TimeChange.lipConstOn`, `TimeChange.normOn`,
`SkorokhodSpace.modulus`, die `Group (TimeChange ι)`-Instanz und die
`MetricSpace D(ι, E)`-Instanz. Für die Sätze darüber — `normOn_one`,
`normOn_inv`, `normOn_mul_le`, `dist_le_of_normOn_le`, `tendsto_modulus`,
`isCompact_closure_iff`, und die drei Instanzen `CompleteSpace`,
`SeparableSpace`, `PolishSpace` auf `D(ι, E)` — ist das `rc=0` genauso wertlos
wie für ein `theorem restart : True`: sie reden über `sorryAx`. Elf der
zwanzig verbleibenden `sorry` der Datei hängen daran.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
`TimeChange.normOn_one` und `TimeChange.normOn_mul_le` **zu beweisen**. Sie sind
jetzt dran, weil `normOn` seit heute definiert ist und beide damit über etwas
reden; weil sie zusammen die Längenfunktionseigenschaft ausmachen, aus der die
Dreiecksungleichung der Metrik von Meilenstein 4 kommt — der einzigen der fünf
`sorry`-Definitionen, die dann noch unterhalb von `D(ι, E)` steht —; und weil
für beide der Weg feststeht. `normOn_one` ist die im Punkt 4 beschriebene
Fallunterscheidung nach `(exhaustion t₀ m).Subsingleton`, in beiden Zweigen über
`csInf_le` und `le_csInf`, mit `LipschitzWith.id.lipschitzOnWith` als oberer und
`edist x y ≤ K * edist x y` bei $x\neq y$ als unterer Schranke. `normOn_mul_le`
ist `LipschitzOnWith.comp` plus `Real.log_mul`, und zu klären ist dabei genau
eine Sache, die in den Bericht gehört: `comp` verlangt, daß `l'` die Ausschöpfung
in sich abbildet, was eine Zeitänderung im Allgemeinen **nicht** tut — ob der
Meilenstein deshalb `normOn` auf `exhaustion t₀ (m+1)` für den inneren Faktor
messen muß, wie Billingsley es tut, oder ob die Ordnungserhaltung samt
`dist_le_of_normOn_le` genügt. Beides stützt `fact:Dcountable` (tragend `4`)
über die Meilensteine 3 und 4, deren ganze Metrik daran hängt.

### 2026-09-07, erster Lauf des Tages — Rückstau 1: die Länge der Zeitänderungen, und zwei weitere falsche Aussagen

Keine vorrangige Aufgabe, kein `?` in der Tabelle; also der Rückstau von oben,
und dort das benannte Ziel des fünften Laufs vom 2026-09-06:
`TimeChange.normOn_one` und `TimeChange.normOn_mul_le` **zu beweisen**. Das
erste ist bewiesen. Das zweite ist **falsch**, und zwar nicht knapp; die Frage,
die der Vorschlag für diesen Lauf offen ließ — „muß der Meilenstein `normOn` für
den inneren Faktor auf `exhaustion t₀ (m+1)` messen, wie Billingsley es tut,
oder genügt die Ordnungserhaltung?" — ist damit beantwortet, und die Antwort ist
keine von beiden: **die gefensterte Norm muß ganz weg.** Billingsley mißt die
Zeitänderung gar nicht auf dem Fenster, sondern **global**; lokalisiert werden
bei ihm nur die *Pfade*. Elf Deklarationen tragen jetzt Beweise, die durch
`lake env lean` gegen `v4.33.1` gehen (Lean `4.33.1`, commit `819816b2`, Mathlib
`0df444a3`); die Datei meldet `rc=0`, ohne Fehler und ohne Linterwarnung.

**1. `TimeChange.normOn_mul_le` ist falsch, mit einem Zeugen auf `ℝ`.** Der
Grund ist strukturell und kein Artefakt: `LipschitzOnWith.comp` verlangt, daß
der innere Faktor das Fenster in sich abbildet, und eine Zeitänderung tut das
nicht; außerhalb des Fensters ist der äußere Faktor durch `normOn` überhaupt
nicht eingeschränkt. Der Zeuge, mit $\iota=\mathbb R$, $t_0=0$, $m=1$, also
$B_1=[-1,1]$:

* $\lambda' (x) = 2x$, also `lipConstOn` $=2$, für die Inverse $1/2$, und
  $\mathrm{normOn}\,\lambda' = \log 2$.
* $\lambda$ die stückweis lineare Ordnungsisomorphie, die auf $(-\infty,1]$ die
  Identität ist und auf $[1,\infty)$ die Steigung $100$ hat. Auf $B_1$ sind
  $\lambda$ **und** $\lambda^{-1}$ die Identität, also
  $\mathrm{normOn}\,\lambda = \log 1 = 0$.
* $(\lambda\lambda')(x) = \lambda(2x)$ schickt $1/2$ auf $1$ und $1$ auf $101$;
  jede auf $B_1$ zulässige Konstante ist also $\ge 200$, und
  $\mathrm{normOn}(\lambda\lambda') \ge \log 200 > \log 2$.

Die Lücke ist beliebig groß zu machen: die Steigung $100$ ist frei. Damit fällt
auch die Bauform von Meilenstein 4: `distOn m` stand dort auf
`TimeChange.normOn m λ`, und ein `distOn` über einer nicht subadditiven Größe
hat keine Dreiecksungleichung. Es steht jetzt auf der globalen
`TimeChange.norm`, mit der Begründung im Meilenstein; ebenso
`SkorokhodSpace.tendsto_iff`. Die Aussage selbst steht als
`TimeChange.not_normOn_mul_le` in `Suggested.lean` — über dem **vollen** Bündel
von Meilenstein 1 quantifiziert, denn nur so widerlegt sie die Roadmap-Aussage
und nicht bloß eine allgemeinere —, mit der Rechnung im Doc-Kommentar und
`sorry` als Beweis.

**2. `TimeChange.dist_le_of_normOn_le` ist ebenfalls falsch, aus einem zweiten,
unabhängigen Grund: `TimeChange` hat keinen Anker.** Eine Translation von
$\mathbb R$ ist eine Ordnungsisomorphie mit `lipConst` $=1$ in beiden
Richtungen, hat also Norm $0$, und verschiebt jeden Punkt um denselben
beliebigen Betrag. Für $\gamma=0$ behauptet die Aussage
$\mathrm{dist}(\lambda t,t)\le 0$, also $\lambda=\mathrm{id}$ auf dem Fenster.
Billingsley bekommt den Anker geschenkt, weil sein $\Lambda$ aus den wachsenden
Homöomorphismen von $[0,\infty)$ auf sich besteht und die alle $0$ festhalten;
auf einem zweiseitigen Index muß er gefordert werden. Die Aussage heißt jetzt
`TimeChange.dist_le_of_norm_le` und trägt die Hypothese `l.toOrderIso t₀ = t₀`.
Die Zeitänderungen, die $t_0$ festhalten, sind eine Untergruppe, also übertragen
sich `norm_one`, `norm_inv` und `norm_mul_le` unverändert auf sie; das Infimum
in `distOn` läuft im Meilenstein jetzt über diese Untergruppe.

**3. Was gebaut ist.** Der ganze globale Unterbau von Meilenstein 3, bewiesen:

* `TimeChange.lipConst λ = sInf {K | LipschitzWith K λ}` und
  `TimeChange.lipschitzWith_lipConst`, die **Attainment** — genau der Punkt, den
  der Meilenstein als „das Infimum wird angenommen, weil `ι` ein metrischer Raum
  ist" beschreibt. Der Beweis dividiert: `ENNReal.div_le_iff_le_mul` mit
  `edist x y ≠ 0` und `≠ ⊤` macht aus `edist (λx) (λy) ≤ K * edist x y` die
  Aussage, daß der Quotient eine untere Schranke der zulässigen `K` ist, und
  `le_csInf` schließt ab. Für den Rückweg braucht es `ENNReal.coe_toNNReal`,
  weil der Quotient endlich ist.
* `TimeChange.lipConst_one` (`[Nontrivial ι]`, Wert `1`) und
  `TimeChange.lipConst_of_subsingleton` (Wert `0`): die beiden Hälften, die
  `normOn_one` schon am 2026-09-06 als Fallunterscheidung angekündigt hatte,
  hier global.
* `TimeChange.lipConst_mul_le`, `csInf_le'` auf `LipschitzWith.comp` der beiden
  angenommenen Konstanten, über `OrderIso.coe_trans` für `l * l' = l ∘ l'`.
* `TimeChange.norm`, `TimeChange.norm_inv`, `TimeChange.norm_one`,
  `TimeChange.norm_mul_le` — die Längenfunktion, vollständig. Der Schritt, der
  den Logarithmus überhaupt gutartig macht, ist eigens benannt:
  `TimeChange.one_le_max_lipConst`, $1\le\max(\mathrm{lipConst}\,\lambda,
  \mathrm{lipConst}\,\lambda^{-1})$ auf nichttrivialem Index, denn die beiden
  Konstanten multiplizieren sich zu mindestens $\mathrm{lipConst}\,1 = 1$, also
  auch das Quadrat ihres Maximums. Ohne ihn ist `Real.log_le_log` nicht
  anwendbar. Derselbe Schritt gibt `TimeChange.norm_nonneg`, auch bewiesen —
  ohne das ist das `max` in `distOn` nicht die gemeinte Größe.
* **Und dabei fiel ein zweites Symptom der falschen `normOn` an:
  `normOn` kann negativ sein.** `lipConstOn` mißt $\lambda$ auf dem Fenster und
  $\lambda^{-1}$ **ebenfalls auf dem Fenster**, nicht auf dessen Bild, also
  können beide zugleich $1/2$ sein: auf $\R$ mit $B_1=[-1,1]$ habe $\lambda$ die
  Steigung $1/2$ auf $[-1,1]$ und die Steigung $2$ auf $[-6,-5]$, wo es die
  Werte $[-1,1]$ annimmt. Dann ist $\mathrm{normOn}\,\lambda = -\log 2 < 0$. Die
  Bemerkung steht am Doc-Kommentar von `norm_nonneg`.
* `TimeChange.normOn_one`, das benannte Ziel, in der angekündigten Gestalt: die
  Fallunterscheidung nach `(exhaustion t₀ m).Subsingleton`, im ersten Zweig
  `lipConstOn = 0` und der Müllwert `Real.log 0 = 0`, im zweiten
  `lipConstOn = 1` über `csInf_le'` und `le_csInf`, mit derselben
  Divisionsrechnung wie oben.

**4. Vier Mathlib-Beobachtungen, alle beim Übersetzen angefallen und alle für
künftige Läufe teuer, wenn sie nicht dastehen.**

* **`ℝ≥0∞` ist nicht in `open scoped NNReal`.** Es braucht
  `open scoped ENNReal`. Der Parser meldet dafür „expected token" mitten in
  einem Typ, was nicht nach einer fehlenden Notation aussieht.
* **`mul_le_mul_left'` gibt es in `v4.33.1` nicht mehr** — „Unknown
  identifier"; ein Volltextlauf über `Mathlib/` findet nur noch
  `le_of_mul_le_mul_left'`. Was es gibt, ist `mul_le_mul_left`
  (`Algebra/Order/Monoid/Unbundled/Basic.lean:78`), und es ist trotz des Namens
  die **rechte** Multiplikation, mit der Hypothese als erstem Argument:
  `(bc : b ≤ c) (a : α) : b * a ≤ c * a`. `mul_le_mul'` (`:203`) ist
  unverändert.
* **`zero_le` nimmt sein Argument implizit**, `zero_le _` ist ein Typfehler
  („Function expected").
* **`push_neg` ist deprecated**, zugunsten von `push Not`. Hier durch
  `rw [not_le]` ersetzt, was ohnehin kürzer ist.

**Stand der Datei.** `SkorokhodSpace/Suggested.lean`: 15 `sorry` statt 16, und
die Zahl unterschätzt den Fortschritt, weil zwei der weggefallenen Aussagen
falsch waren und durch eine berichtigte und eine Widerlegung ersetzt sind. Von
den fünf Deklarationen mit `sorry` **im Rumpf einer Definition**, die der
fünfte Lauf vom 2026-09-06 als die eigentliche Schwäche der Datei benannt hat,
bleiben `SkorokhodSpace.modulus` und die `MetricSpace D(ι, E)`-Instanz; unter
der Instanz hängen `CompleteSpace`, `SeparableSpace`, `PolishSpace` und
`continuousAt_eval`.

**Was offen blieb.** `TimeChange.not_normOn_mul_le` trägt `sorry`. Die Rechnung
im Doc-Kommentar ist vollständig und elementar, aber sie ist nicht übersetzt;
dafür fehlt die stückweis lineare Ordnungsisomorphie von $\mathbb R$ als Term
(`StrictMono.orderIsoOfRightInverse`, `Order/Hom/Basic.lean:1206`, gibt sie her,
zusammen mit ihrer Inversen) und die drei `lipConstOn`-Auswertungen.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
`TimeChange.dist_le_of_norm_le` **zu beweisen**. Sie ist jetzt dran, weil sie
seit heute richtig ausgesprochen ist — mit dem Anker `λ t₀ = t₀` —, weil
`lipschitzWith_lipConst` seit heute das Werkzeug liefert, mit dem aus
`norm λ ≤ γ` überhaupt eine Abschätzung von `edist (λ t) (λ t₀)` wird, und weil
sie die letzte der drei Aussagen über `norm` ist, auf denen Meilenstein 4 die
Metrik aufbaut: Symmetrie aus `norm_inv`, Dreieck aus `norm_mul_le`, beide seit
heute bewiesen, und **Trennung** aus genau dieser. Der Weg steht fest und ist
kurz: für $t\ge t_0$ ist $\lambda t\ge\lambda t_0=t_0$, also gibt `AdditiveDist`
über `dist_eq_sub_of_le` die Identität
$\mathrm{dist}(\lambda t,t)=|\mathrm{dist}(t_0,\lambda t)-\mathrm{dist}(t_0,t)|$,
und `lipschitzWith_lipConst` für $\lambda$ und für $\lambda^{-1}$ klemmt
$\mathrm{dist}(t_0,\lambda t)$ zwischen $e^{-\gamma}\mathrm{dist}(t_0,t)$ und
$e^{\gamma}\mathrm{dist}(t_0,t)$ ein; der Fall $t\le t_0$ ist symmetrisch. Das
ist die erste Stelle des ganzen Meilensteins, an der `AdditiveDist` wirklich
gebraucht wird, und damit zugleich die Probe darauf, daß Meilenstein 1 die
richtige Klasse führt. Sie stützt `fact:Dcountable` (tragend `4`) über die
Meilensteine 3 und 4.

### 2026-09-07, zweiter Lauf des Tages — Rückstau 1: die Zeitänderungsschicht ist fertig, und der Zeuge gegen die gefensterte Norm ist übersetzt

Keine vorrangige Aufgabe, kein `?` in der Tabelle; also wieder der Rückstau von
oben und dort das benannte Ziel des ersten Laufs von heute,
`TimeChange.dist_le_of_norm_le` **zu beweisen**. Es ist bewiesen, und der
Restposten desselben Laufs, `TimeChange.not_normOn_mul_le`, gleich mit.
**Damit trägt die Zeitänderungsschicht der Meilensteine 3 und 4 kein `sorry`
mehr.** `SkorokhodSpace/Suggested.lean` geht durch `lake env lean` gegen
`v4.33.1` (Lean `4.33.1`, commit `819816b2`), ohne Fehler und ohne
Linterwarnung; 13 `sorry` statt 15.

**1. `dist_le_of_norm_le`, und eine Aussage von Meilenstein 1, die dabei
angefallen ist.** Der im Vorschlag skizzierte Weg trägt, aber er ist an einer
Stelle länger als angekündigt: `dist_eq_sub_of_le` verlangt $t_0\le s\le t$,
und der Beweis hat nur, daß $t$ und $\lambda t$ **auf einer Seite** von $t_0$
liegen — welche, entscheidet sich erst in der Fallunterscheidung, und
unterhalb von $t_0$ steht $t_0$ am falschen Ende der Additivität. Der
Zwischenschritt ist deshalb als eigene Aussage von Meilenstein 1
aufgeschrieben:

* `dist_eq_abs_sub_of_sameSide` — sind $s$ und $t$ beide $\ge t_0$ oder beide
  $\le t_0$, so ist $\mathrm{dist}(s,t)=|\mathrm{dist}(t_0,t)-
  \mathrm{dist}(t_0,s)|$. Vier Zweige (zwei Seiten, je `le_total s t`), in
  zweien davon `AdditiveDist.dist_add` direkt statt über `dist_eq_sub_of_le`,
  weil dort $t_0$ oben steht; der Absolutbetrag wird jedesmal aus
  `dist_nonneg` aufgelöst. Die Voraussetzung ist **nicht** entbehrlich: auf
  $\mathbb R$ mit $t_0=0$, $s=-1$, $t=1$ steht links $2$ und rechts $0$. Wie
  `dist_eq_sub_of_le` braucht sie `AdditiveDist` allein.

Der Satz selbst geht dann in einem Zug: `norm_nonneg` gibt $\gamma\ge0$,
`Real.log_le_iff_le_exp` macht aus $\log\max(\ldots)\le\gamma$ die Schranke
$\max\le e^\gamma$ (mit dem Subsingleton-Zweig eigens, weil dort
`lipConst = 0` und der Logarithmus sein Müllwert ist),
`lipschitzWith_lipConst.dist_le_mul` für $\lambda$ und für $\lambda^{-1}$
klemmt $d'=\mathrm{dist}(t_0,\lambda t)$ zwischen $e^{-\gamma}d$ und
$e^{\gamma}d$ ein, und $d\le m$ schließt ab.

**Zwei Befunde am Satz, beide vom Übersetzen und nicht vom Lesen.**

* **Er braucht weder `OrderTopology` noch `ProperSpace`**, gefunden vom
  `unusedSectionVars`-Linter und jetzt als `omit` festgehalten. Insbesondere
  geht die **Kompaktheit des Fensters nicht ein**: `exhaustion t₀ m` kommt nur
  über die Ungleichung $\mathrm{dist}(t_0,t)\le m$ vor. Das ist die stehende
  Regel über minimale Voraussetzungen, und sie fällt hier auf der richtigen
  Seite aus — der Satz ist allgemeiner, als der Meilenstein ihn führte.
* **Die bewiesene Schranke ist $(e^\gamma-1)\,m$, also die Hälfte der
  behaupteten $(e^\gamma-1)\,2m$.** Der Faktor $2$ ist Reserve, die der Beweis
  nicht braucht; die Aussage bleibt, wie sie ist, weil Meilenstein 4 sie so
  zitiert, aber der Meilensteintext hält den schärferen Wert jetzt fest. Der
  Grund, daß es reicht: im Zweig $d'\le d$ ist $d'\le d\le m$ ohnehin, und im
  anderen ist $d'-d\le(e^\gamma-1)d$ direkt.

**2. `not_normOn_mul_le` ist übersetzt, samt Zeugen.** Der erste Lauf von heute
hatte die Rechnung vollständig in den Doc-Kommentar geschrieben und als
`sorry` stehenlassen, weil „die stückweis lineare Ordnungsisomorphie von
$\mathbb R$ als Term" fehlte. Der Weg dorthin war kürzer als der dort genannte,
und er ist der eigentliche Ertrag dieses Punktes: **kein `if`, sondern ein
`max`.** Die Abbildung, die auf $(-\infty,1]$ die Identität ist und darüber
Steigung $100$ hat, ist

$$\lambda(x)=\max(x,\;100x-99),$$

denn $100x-99\le x$ gilt genau für $x\le1$; ihre Inverse ist
$\lambda^{-1}(y)=\min(y,(y+99)/100)$, von derselben Gestalt. Damit ist alles
ein Einzeiler: `max_lt_max` gibt die strenge Monotonie, `LipschitzWith.max`
(`Topology/MetricSpace/Lipschitz.lean:182`) und `LipschitzWith.min` (`:186`)
die beiden Lipschitz-Schranken, `StrictMono.orderIsoOfRightInverse`
(`Order/Hom/Basic.lean:1206`) macht daraus die Ordnungsisomorphie, und die
Rechtsinversenidentität ist ein einziges `rcases le_total y 1` mit
`min_eq_left`/`max_eq_left` bzw. `_right`. Mit `if` wären es vier Zweige je
Aussage gewesen und der Absolutbetrag in jedem.

Übersetzt sind: `TimeChange.steep` und `TimeChange.double` samt ihren acht
Hilfsaussagen, die vier `@[simp]`-Auswertungen (alle `rfl`),
`mem_exhaustion_real_iff`, und die drei Abschätzungen `normOn_steep_le`
($\le0$), `normOn_double_le` ($\le\log2$) und `le_normOn_steep_mul_double`
($\ge\log200$). Nur die letzte braucht das Infimum **von unten**, also
`le_csInf` samt Nichtleerheit aus `(steep * double).lipschitz`, ausgewertet an
den beiden Fensterpunkten $1/2$ und $1$: $(\lambda\lambda')(1/2)=\lambda(1)=1$
und $(\lambda\lambda')(1)=\lambda(2)=101$, also $100\le K\cdot\tfrac12$ und
$K\ge200$. Die beiden anderen sind `csInf_le'` auf einer vorgezeigten
zulässigen Konstante.

Mit angefallen und eingetragen: **`Real.instAdditiveDist`**, die erste der vier
laufenden Instanzen von Meilenstein 1. Sie war nötig, weil die Widerlegung
über dem vollen Bündel quantifiziert und deshalb an $\mathbb R$ instanziiert
werden muß; drei `abs_of_nonpos` auf `Real.dist_eq` und ein `ring`. Die
anderen drei Instanzen folgen aus ihr über `instAdditiveDistSubtype`.

**Was das für den Meilenstein bedeutet.** Meilenstein 4 hatte am ersten Lauf
von heute seine Bauform gewechselt — `distOn` steht seither auf der globalen
`TimeChange.norm` statt auf `normOn` —, und die Begründung dafür war eine
Rechnung im Doc-Kommentar. Sie ist jetzt ein Satz. Das ist der Unterschied,
den der Rückstaupunkt meint, wenn er sagt, das Typprüfen zähle nichts, solange
die Aussage nicht die Arbeit trägt.

**Stand der Datei.** 13 `sorry`: `exists_orderIso_isometry_real` (M1),
`countable_leftJumpSet` und `IsCadlag.measurable` (M2), und die zehn, die an
der `MetricSpace D(ι, E)`-Instanz hängen — die Instanz selbst, `CompleteSpace`,
`SeparableSpace`, `PolishSpace`, `continuousAt_eval`,
`measurableEmbedding_piDense`, `borel_eq_iSup_comap_eval`, `modulus`,
`tendsto_modulus`, `isCompact_closure_iff`. Von den fünf Definitionen mit
`sorry` **im Rumpf**, die der fünfte Lauf vom 2026-09-06 als die eigentliche
Schwäche der Datei benannt hat, sind noch zwei da: `SkorokhodSpace.modulus`
und die `MetricSpace`-Instanz.

**3. Im selben Lauf noch: der Klemmoperator, der letzte offene Punkt von
Meilenstein 1.** Er war als Ziel des nächsten Laufs vorgesehen und ist statt
dessen gleich mitgemacht worden, weil er kein Werkzeug brauchte, das nicht
schon dastand. Neun Deklarationen, alle bewiesen: `mem_exhaustion_self`,
`exhaustionMin` und `exhaustionMax` samt `isLeast_exhaustionMin` und
`isGreatest_exhaustionMax` — aus `IsCompact.exists_isLeast`
(`Topology/Order/Compact.lean:148`) und `IsCompact.exists_isGreatest` (`:160`)
auf dem seit dem 2026-09-06 kompakten `exhaustion`, mit `t₀` als
Nichtleerheitszeuge —, dann `clamp`, `monotone_clamp`, `continuous_clamp`,
`clamp_mem_exhaustion`, `clamp_eq_self` und `clamp_idem`.

**Und der Befund, der dabei anfiel, ist der interessante Teil.** Meilenstein 1
verlangte vom Klemmoperator nur, daß er monoton, stetig, idempotent und auf
`B m` die Identität sei. Das reicht nicht: daß
`min (max t (B m).min) (B m).max` **in `B m` liegt**, folgt aus dem Dastehen
zwischen kleinstem und größtem Element **nicht**, solange das Fenster keine
Ordnungsintervall ist. Es ist eines, aber das ist ein eigener Satz und noch
einmal `AdditiveDist`:

* `ordConnected_exhaustion` — oberhalb von $t_0$ gibt es
  `monotoneOn_dist_basepoint`, unterhalb wird die Additivität vom anderen Ende
  gelesen ($x\le z\le t_0$ gibt $\mathrm{dist}(x,t_0)=\mathrm{dist}(x,z)+
  \mathrm{dist}(z,t_0)$, also $\mathrm{dist}(z,t_0)\le\mathrm{dist}(x,t_0)$).
  Weder Ordnungstopologie noch Eigentlichkeit gehen ein.

Damit ist `AdditiveDist` an drei Stellen dieses Laufs die tragende Hypothese
gewesen und an keiner entbehrlich — Meilenstein 1 führt die richtige Klasse,
und das ist jetzt dreifach geprüft statt einmal behauptet.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
**`SkorokhodSpace.restrictExhaustion` und `SkorokhodSpace.distOn`**, die beiden
Daten der Metrik von Meilenstein 4. `restrictExhaustion t₀ m f = f ∘ clamp t₀ m`
ist seit heute hinschreibbar und braucht als einzige Aussage, daß es wieder
càdlàg ist — `clamp` ist monoton und stetig, also bleibt Rechtsstetigkeit
erhalten und der Linkslimes existiert. Darauf steht dann
`distOn t₀ m f g = ⨅ λ, max (TimeChange.norm λ) (⨆ t ∈ B m, dist (…))`, wobei
das Infimum über die **Untergruppe der Zeitänderungen mit `λ t₀ = t₀`** läuft
(so verlangt es `dist_le_of_norm_le`, und diese Untergruppe ist als solche noch
nicht definiert — das ist die zweite Zutat, `TimeChange.fixing t₀` als
`Subgroup (TimeChange ι)`). Es ist jetzt dran, weil es der einzige verbliebene
Weg zur `MetricSpace D(ι, E)`-Instanz ist, an der zehn der dreizehn `sorry` der
Datei hängen, und weil seit heute jede Aussage über `norm` bereitsteht, die
ihre drei Axiome brauchen: Symmetrie aus `norm_inv`, Dreieck aus
`norm_mul_le`, Trennung aus `dist_le_of_norm_le`. Zu prüfen ist dabei zuerst,
ob das Supremum über `B m` überhaupt endlich ist — der Meilenstein verlangt
das ausdrücklich, und für einen unbeschränkten càdlàg-Pfad auf einem kompakten
Fenster ist es die Stelle, an der `isCompact_exhaustion` zum ersten Mal
wirklich gebraucht wird. Das stützt `fact:Dcountable` (tragend `4`) über die
Meilensteine 4, 5 und 6.

### 2026-09-07, dritter Lauf des Tages — Rückstau 1: die beiden Daten der Metrik stehen, und eine Aussage von Meilenstein 2 ist unter ihrem Bündel falsch

Keine vorrangige Aufgabe, kein `?` in der Tabelle; also wieder der Rückstau von
oben und dort das benannte Ziel des zweiten Laufs von heute:
`SkorokhodSpace.restrictExhaustion` und `SkorokhodSpace.distOn` samt der
Untergruppe `TimeChange.fixing t₀`. Alle drei stehen, und im selben Lauf ist
auch das benannte Ziel des *nächsten* Laufs gefallen, die Dreiecksungleichung.
**Meilenstein 4 hat damit seine beiden Daten und jedes Axiom außer der
Trennung**, und die Prüffrage des Vorschlags — ob das Supremum überhaupt endlich
ist — ist als Satz beantwortet. `SkorokhodSpace/Suggested.lean` geht durch
`lake env lean` gegen `v4.33.1`, ohne Fehler und ohne Linterwarnung; 94
Deklarationen, 13 `sorry`, also genau die dreizehn des zweiten Laufs. Die
fünfzehn neuen Deklarationen sind alle bewiesen.

**1. Die Untergruppe, und warum sie eine sein muß.** `TimeChange.fixing t₀` ist
`{l | l.toOrderIso t₀ = t₀}` als `Subgroup (TimeChange ι)`; `mul_mem'` ist
`OrderIso.trans_apply` und zweimal Einsetzen, `inv_mem'` geht über die
Injektivität von `l` statt über ein Rückwärts-`rw`, das sonst auch die beiden
anderen `t₀` des Ziels träfe. `TimeChange.mem_fixing_iff` ist `Iff.rfl` und die
einzige Schnittstelle, die der Rest braucht. Der Grund, weshalb die Anker eine
**Untergruppe** bilden müssen und nicht bloß eine Teilmenge, ist die
Axiomenliste selbst: die Symmetrie liest `norm_inv` an `l⁻¹` ab, das Dreieck
`norm_mul_le` an `l * l'`, und beide Male muß das Ergebnis wieder ein
zulässiger Index des Infimums sein.

**2. `restrictExhaustion`, und die Aussage von Meilenstein 2, die dafür
gefehlt hat.** `restrictExhaustion t₀ m f = f ∘ clamp t₀ m` ist hinschreibbar,
seit `clamp` steht, aber daß es wieder càdlàg ist, war keine Aussage der
Roadmap. Sie ist es jetzt, als `IsCadlag.comp_monotone_continuous` in
Meilenstein 2: für càdlàg `f` und monotones stetiges `g : ι → ι` ist `f ∘ g`
càdlàg. Beide Felder brauchen die Monotonie, und auf verschiedene Weise. Rechts
bildet `g` die Menge `Set.Ioi a` nach `Set.Ici (g a)` ab, und **dort** ist die
Rechtsstetigkeit von `f` lesbar — über `continuousWithinAt_Ioi_iff_Ici`
(`Topology/Order/LeftRight.lean:79`, `PartialOrder` allein). Links zerfällt der
Beweis: entweder ist `g` links von `x` schon konstant, und dann ist es `f ∘ g`
auf dem ganzen Intervall zwischen den beiden gleichen Werten, oder es ist
`g y < g x` für **jedes** `y < x`, und dann strebt `g` von echt unten gegen
`g x`, so daß der Linkslimes von `f` an `g x` der von `f ∘ g` an `x` ist. Der
erste Zweig ist die einzige Stelle des Meilensteins, an der die
Ordnungstopologie vorkommt, über `Ioo_mem_nhdsLT`
(`Topology/Order/OrderClosed.lean:282`, unter `ClosedIicTopology`).

**3. Der Befund, und er ist der wertvollste des Laufs:
`IsCadlag.isBounded_image_of_isCompact` ist unter dem Bündel (A) falsch.** Die
Roadmap führte den Satz — das Bild einer kompakten Menge unter einer
càdlàg-Abbildung ist beschränkt — unter (A), also unter
`[Preorder ι] [TopologicalSpace ι]`, mit der Begründung, der Index steuere
„compactness of the domain and nothing else" bei. Das stimmt nicht. Der Beweis
zerlegt eine Umgebung eines Punktes in ihre beiden einseitigen Hälften, über
`nhdsLT_sup_nhdsGE` (`Topology/Order/LeftRight.lean:101`), also über
`Set.Iio x ∪ Set.Ici x = univ` — und das ist die Linearität. Genau da ist die
Aussage auch falsch:

* $\iota=\N\cup\{\omega\}$, topologisch die Einpunktkompaktifizierung des
  diskreten $\N$, geordnet so, daß $\N$ seine übliche Ordnung trägt und
  $\omega$ zu allem **unvergleichbar** ist. Jeder Punkt von $\N$ ist isoliert
  und $\mathrm{Iio}\,\omega=\mathrm{Ioi}\,\omega=\emptyset$, also ist
  $\mathcal N_{<x}=\mathcal N_{>x}=\bot$ an jedem $x$ und **jede** Funktion
  $f:\iota\to\R$ ist càdlàg; $\iota$ ist kompakt; $f(n)=n$ hat unbeschränktes
  Bild. Was fehlt, ist genau die Zerlegung: $\omega$ hat Umgebungen, die
  koendlich viel von $\N$ enthalten, und dort sagt kein Feld von `IsCadlag`
  etwas.

Bewiesen ist der Satz jetzt unter `[LinearOrder ι] [TopologicalSpace ι]`, und
die Ordnungstopologie geht **nicht** ein — vom `unusedSectionVars`-Linter
bestätigt und als `omit` festgehalten. Das ist eine Stufe, die das Bündelschema
des Meilensteins bisher nicht hatte: schwächer als (A′), das die
Ordnungstopologie mitnimmt, und stärker als (A). Der Roadmaptext trägt Satz,
Zeuge und Bündel seit heute; der Punkt ist aus der (A)-Liste in die (A′)-Liste
gewandert, mit der Notiz, was von (A′) er wirklich verbraucht.

**4. `distOn`, und die zwei Stellen, an denen ein bedingt vollständiges
Supremum ein Müllwert sein könnte.** Die Definition ist Billingsleys `d°ₘ`
wörtlich: Infimum über `TimeChange.fixing t₀` von
`max (norm λ) (⨆ t, dist (restrictExhaustion f (λ t)) (restrictExhaustion g t))`.
In `ℝ` ist `⨆` `sSup (range …)` und `⨅` `sInf (range …)`, und beide sind `0`,
wenn die Menge unbeschränkt ist. Also gehören zwei Sätze zur Definition, und
beide stehen:

* `bddAbove_range_dist_restrictExhaustion` — über
  `isBounded_range_restrictExhaustion`, der Beschränktheit des trunkierten
  Pfades. Sie ist `IsCadlag.isBounded_image_of_isCompact` auf
  `isCompact_exhaustion`, und **das ist die einzige Stelle in den Meilensteinen
  3 und 4, an der die Kompaktheit des Fensters überhaupt gebraucht wird** — die
  Frage, die der Vorschlag des zweiten Laufs zuerst geprüft haben wollte.
  `dist_le_of_norm_le` braucht sie ausdrücklich nicht.
* `bddBelow_range_distOn` — `TimeChange.norm_nonneg`, also der Satz des ersten
  Laufs von heute, an der Stelle, für die er gedacht war.

Das Supremum läuft über **ganz** `ι` und nicht über `B m`. Die beiden stimmen
überein, weil beide Pfade außerhalb des Fensters konstant sind; und über `ι` zu
quantifizieren ist das, was die Umindizierung in `distOn_comm` zu einer
Bijektion des Index macht statt zu einer einer Teilmenge, die die Zeitänderung
gar nicht erhalten muß. Das ist kein Schönheitsargument, sondern der Grund,
warum der Beweis in vier Zeilen durchgeht.

**5. Zwei der drei Axiome.** `distOn_nonneg` ist `le_ciInf` auf `norm_nonneg`.
`distOn_self` ist `ciInf_le` an der `1` der Untergruppe, plus `norm_one` und
`ciSup_const` — die Nichtleerheit von `ι`, die letzteres braucht, ist `⟨t₀⟩`,
und ohne das Argument `t₀` wäre die Aussage über einem leeren Index eine über
`sSup ∅`. `distOn_comm` ist der erste Satz, der die Untergruppenstruktur
wirklich benutzt: `λ ↦ λ⁻¹` ist eine Bijektion von `TimeChange.fixing t₀`,
`norm_inv` läßt die Norm stehen, und das Supremum wird längs der Bijektion `λ`
von `ι` umindiziert, was `dist (f (λ t)) (g t)` gliedweise in
`dist (g (λ⁻¹ s)) (f s)` überführt. Die Umindizierung ist im Beweis als
Hilfsaussage `hre` ausgeschrieben, weil Mathlibs `Equiv.iSup_comp`
(`Order/CompleteLattice/Basic.lean:185`) für **vollständige** Verbände gilt und
`ℝ` keiner ist; sie ist eine Gleichheit von `Set.range`s und dann
`congrArg sSup`.

**6. Und das dritte Axiom gleich mit: `distOn_triangle`.** Es war als Ziel des
nächsten Laufs vorgesehen und ist im selben Lauf gefallen, weil nach Punkt 5
jede Zutat dastand. Es ist die **zweite** Stelle, an der die Anker eine
Untergruppe sein müssen und keine bloße Menge: der Zeuge für die Verkettung ist
`λ * λ'`, und der muß wieder zulässig sein. Das `max` zerfällt in seine beiden
Hälften, `norm_mul_le` trägt die eine und die Dreiecksungleichung von `E` die
andere, mit dem mittleren Pfad ausgewertet an `λ' t` — und das ist der zweite,
unabhängige Grund dafür, das Supremum über ganz `ι` zu nehmen: das Bild des
Fensters unter `λ'` ist nicht das Fenster. Das Infimum wird nicht angenommen,
also läuft das Argument über ein `ε`; die Auswahl ist als eigene Aussage
`SkorokhodSpace.exists_lt_distOn_add` aufgeschrieben, `exists_lt_of_ciInf_lt`
(`Order/ConditionallyCompleteLattice/Indexed.lean:451`) auf
`bddBelow_range_distOn`. Von den Metrikaxiomen fehlt damit allein die
**Trennung**.

Ein Nebenbefund am Rande: `omit [AdditiveDist ι]` trägt für `distOn_triangle`
**nicht**, obwohl es für `distOn_nonneg`, `distOn_self` und `distOn_comm`
trägt. Der Grund ist `bddAbove_range_dist_restrictExhaustion`, das über
`isCompact_exhaustion` und `clamp` an der Klasse hängt — die
Dreiecksungleichung ist damit die einzige der vier, die die Kompaktheit des
Fensters wirklich verbraucht, und das paßt zu Punkt 4: sie ist die einzige, die
das Supremum von unten abschätzt.

**Was offen bleibt.** Die dreizehn `sorry` sind unverändert die des zweiten
Laufs: `exists_orderIso_isometry_real` (M1), `countable_leftJumpSet` und
`IsCadlag.measurable` (M2) und die zehn, die an der `MetricSpace D(ι, E)`-
Instanz hängen. Von den beiden Definitionen mit `sorry` **im Rumpf** sind
weiterhin beide da, `SkorokhodSpace.modulus` und die `MetricSpace`-Instanz —
aber die Instanz hat seit heute zwei ihrer drei Axiome und beide Daten.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
**`countable_leftJumpSet`** — die Abzählbarkeit der Sprungmenge einer
càdlàg-Abbildung, Meilenstein 2, seit dem 2026-09-05 ein `sorry`. Es ist jetzt
dran, weil es seit heute **auf dem kritischen Weg zur Trennung liegt**, dem
einzigen fehlenden Metrikaxiom, und damit zur `MetricSpace D(ι, E)`-Instanz, an
der zehn der dreizehn `sorry` der Datei hängen. Der Weg zur Trennung, damit die
Reihenfolge sichtbar ist: aus `distOn t₀ m f g = 0` liefert
`exists_lt_distOn_add` zu jedem `n` ein $\lambda_n$ mit
$\mathrm{norm}\,\lambda_n\le 1/n$ **und** $\sup_t\mathrm{dist}(F(\lambda_n
t),G(t))\le1/n$; `dist_le_of_norm_le` (bewiesen, zweiter Lauf von heute) macht
daraus $\lambda_n t\to t$ gleichmäßig auf dem Fenster, also
$G(t)=\lim_n F(\lambda_n t)$. Weil $\lambda_n t$ von **beiden** Seiten kommen
darf, gibt das $G(t)=F(t)$ zunächst nur an den Stetigkeitsstellen von $F$; und
daß die Stetigkeitsstellen den Rest tragen, ist genau
`IsCadlag.eq_of_eqOn_dense` (bewiesen, 2026-09-06) — deren Hypothese aber
verlangt, daß jeder Punkt in der Menge liegt oder von rechts aus ihr
approximierbar ist, und das ist die Abzählbarkeit des Komplements, also
`countable_leftJumpSet`. Ohne sie steht die Trennung ohne Unterbau. Der Weg für
`countable_leftJumpSet` selbst steht im Meilenstein 2 und ist unverändert:
`largeLeftJumpSet f ε` hat keinen Häufungspunkt — ein solcher lieferte eine
monotone Folge gegen ihn, und der einseitige Limes dort widerspräche der
Sprunghöhe —, trifft also jede kompakte Menge in einer endlichen, und die
σ-Kompaktheit des Index (aus `isCompact_exhaustion`, jeder Index von
Meilenstein 1 hat sie) macht daraus die Abzählbarkeit. Das stützt
`fact:Dcountable` (tragend `4`) über die Meilensteine 4, 5 und 6.

### 2026-09-07, vierter Lauf des Tages — vorrangige Aufgabe: acceptance examples, vollständig

Die am 2026-09-07 gestellte vorrangige Aufgabe, **erledigt in einem Lauf**.
Ergänzt sind die Abschnitte `**Acceptance examples.**` für **alle 27**
Meilensteine der vier Roadmaps: `WeakConvergence` (5), `SkorokhodSpace` (8),
`KolmogorovExtension` (3) und `MartingaleProblems` (1–11). Die Meilensteine 12
und 13 von `MartingaleProblems` haben, wie ausdrücklich verlangt, **keine**
bekommen — sie sind *roadmap-for-a-roadmap*. Kein Fact hat den Status
gewechselt, keine Meilensteinaussage wurde geändert, das Manuskript ist
unberührt; `python3 check.py` meldet `clean` (132 Seiten). Die Beispiele stehen
jeweils am Ende des Meilensteins, wie es `VORBILD-OneParameterSemigroups.md`
Punkt 4 der Checkliste verlangt.

**Der Maßstab, an dem ich sie gemessen habe.** Ein acceptance example ist eine
Instanz, an der die API rechnet, und ein gutes deckt einen Fall ab, in dem eine
naheliegende falsche Definition scheitert. Ich habe deshalb je Meilenstein
mindestens ein **Paar** geschrieben — die Instanz, an der es geht, und die
danebenliegende, an der es nicht geht —, statt vier positive Instanzen
aufzuzählen. Herkunft, in der von der Aufgabe verlangten Reihenfolge: das
Manuskript (`ex:atomicdiscontinuity`, `ex:invariance`, `ex:determining`,
`prop:hawkesduality`), dann die Zeugen, die diese Läufe selbst gefunden haben
(die `∅`-Klasse auf dem einpunktigen Raum, der `δ n`-Zeuge gegen die
straffheitsfreie Fassung, `ι = ℕ ∪ {ω}`, das maximale Element außerhalb von `D`,
`steep * double` gegen die gefensterte Norm, die Translationen gegen den Anker),
und erst dann Neues.

**Was dabei an Rechnung angefallen ist**, denn drei Beispiele sind mehr als ein
Zitat:

1. **Die trigonometrische Algebra auf `ℝ` trennt Punkte, aber nicht stark**
   (`WeakConvergence` M1). Sie ist eine `ℝ`-Unteralgebra von `ℝ →ᵇ ℝ` — die
   Produktformeln schreiben `cos(tx)cos(sx)` als Kombination von `cos((t±s)x)`
   —, enthält die Konstanten bei `t = 0` und trennt Punkte. Stark trennt sie
   **nicht**: für feste `t 1, …, t k` ist der Abschluß von
   `{(t i · u mod 2π) | u ≥ R}` eine abgeschlossene Untergruppe des Torus, die
   `0` enthält, also gibt es beliebig weit entfernte `y` mit
   `max i |h i y - h i x|` beliebig klein. Da die Charaktere nach Lévy trotzdem
   konvergenzbestimmend sind (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`),
   ist damit **belegt**, daß `isConvergenceDetermining_of_stronglySeparatesPoints`
   keine Äquivalenz werden darf. Das ist der Ertrag der Aufgabe vom 2026-09-06
   an einer Stelle, an der er sich rechnet.
2. **Der schrumpfende Buckel entscheidet zwischen den beiden Normen**
   (`SkorokhodSpace` M5). `x n = 1_{[1/2, 1/2+1/n)}` ist Cauchy unter
   Billingsleys älterem `sup t, dist (λ t) t` — die stückweise lineare
   Zeitänderung paßt die beiden Buckel exakt aufeinander und verschiebt Punkte
   um höchstens `|1/n - 1/m|` — und hat keinen Grenzwert; unter
   `TimeChange.norm` ist dieselbe Folge **nicht** Cauchy, weil jene Zeitänderung
   um den Faktor `n/m` staucht und ihre Norm `|log (n/m)|` ist, was längs
   `m = 2n` nicht gegen `0` geht. `CompleteSpace (D ι E)` ist also ein Satz über
   die logarithmische Norm von Meilenstein 3 und für die naive falsch. Das ist
   das schärfste Beispiel der beiden Roadmaps.
3. **Die Ordnungskonvexität der Fenster ist ein Satz über `AdditiveDist`, nicht
   über `clamp`** (`SkorokhodSpace` M1). Auf der Dreipunktordnung `{0 < 1 < 2}`
   mit `dist 0 1 = 2`, `dist 1 2 = 1`, `dist 0 2 = 1` — eine Metrik, `2 ≤ 1+1` —
   ist `B 1` um `t₀ = 0` die Menge `{0, 2}`, nicht ordnungskonvex, und
   `clamp 1 1 = min (max 1 0) 2 = 1` verläßt das Fenster. Die Metrik ist nicht
   additiv, und genau das ist der Punkt. Dazu paßt die zweite Instanz derselben
   Sorte: `dist x y = min 1 |x - y|` auf `ℝ` induziert die Ordnungstopologie und
   ist nicht additiv, und `orderIso_isometry_real` scheitert daran, weil eine
   beschränkte Metrik keine Isometrie auf eine unbeschränkte abgeschlossene
   Teilmenge von `ℝ` zuläßt.

**Zwei Korrekturen an eigenen Entwürfen**, beide beim Nachrechnen gefunden und
vor dem Schreiben behoben: der Mittelwert von `X n k = k/n` auf der
Gleichverteilung über `{0,…,n}` ist exakt `1/2` und nicht `(n+2)/(2(n+1))`; und
die Folge `1_{(1-1/n,∞)}`, die ich zuerst als Beispiel für einen nicht-càdlàg
punktweisen Limes hatte, ist selbst nicht càdlàg — das richtige Beispiel ist
`1_{[1+1/n,∞)}`, dessen punktweiser Limes `1_{(1,∞)}` ist und dessen
`D ι E`-Limes `1_{[1,∞)}`.

**Die zweite Hälfte**, im selben Lauf und mit denselben Regeln geschrieben.
`KolmogorovExtension` und `MartingaleProblems` 1–11. Drei Befunde daraus, die
über das Beispielschreiben hinausgehen:

4. **Der schärfste Prüfstein von `KolmogorovExtension` ist Mathlibs eigenes
   Produktmaß.** `MeasureTheory.Measure.infinitePi` ist für einen **beliebigen**
   Index und **ohne jede topologische Voraussetzung** gebaut (am Quelltext
   geprüft: `upstream/master:Mathlib/Probability/ProductMeasure.lean`, die
   Variablenblöcke tragen nur `[∀ i, IsProbabilityMeasure (μ i)]`, der Beweis
   läuft über `piContent_tendsto_zero`). Also muß `projectiveLimit` auf der
   Produktfamilie mit ihm übereinstimmen, per `IsProjectiveLimit.unique` — ein
   Vergleich zweier unabhängig gebauter Objekte. Nebenbei ist damit belegt, daß
   die innere Regularität von Meilenstein 1 **hinreichend und nicht notwendig**
   ist: auf `ℝ` mit der abzählbar-koabzählbaren σ-Algebra hat das Maß
   `μ A = if A abzählbar then 0 else 1` überhaupt keine meßbare kompakte Menge
   positiven Maßes, und der projektive Limes existiert trotzdem.
5. **Der Diamant und die Antikette tragen `MartingaleProblems` Meilenstein 8
   an zwei verschiedenen Stellen.** Der Diamant mit $m_c^2=m_am_b$ entscheidet
   die **Konvention** — prädiktabel geht, optional ist falsch —, die Antikette
   von `ex:antichain` entscheidet die **Integrierbarkeit**, und zwar dreifach
   auf einmal: sie widerlegt die Ausdehnung von `duality_of_atomic` auf
   abzählbare Atommengen, das Weglassen der $m\otimes m$-Integrierbarkeit in
   `duality_of_atomic_antichain_of_integrable`, und — weil ihr $\Phi$ nur drei
   Werte annimmt — jeden Ersatz der Integrierbarkeit durch Beschränktheit von
   $\Phi$. Beide Zeugen standen schon im Roadmaptext; als acceptance example
   sind sie jetzt an der Stelle, an der ein Implementierer sie rechnet.
6. **Zwei Roadmaps benennen dieselbe Instanz jetzt gleich.** Das
   `ex:determining`-Produkt $\prod h_i(X_{t_i})$ ist in `MartingaleProblems` M3
   die bestimmende Klasse und in `WeakConvergence` M5 das multiplikative System
   `K`, an dem `condExp_eq_of_forall_integral_mul_eq` die Martingaleigenschaft
   prüft; `ex:invariance` steht in `MartingaleProblems` M10 als Prüfung aller
   drei Hypothesen (a)–(c) und in `SkorokhodSpace` M8 als Straffheits- plus
   fdd-Instanz; `ex:atomicdiscontinuity` steht in `WeakConvergence` M2,
   `SkorokhodSpace` M4 und `MartingaleProblems` M1, M9, M10. Das war die
   Nebenabsicht der Aufgabe und ist erreicht: die Beispiele verzahnen die vier
   Roadmaps sichtbar, statt sie nebeneinanderzustellen.

**Am Quelltext belegt** wurden in diesem Lauf zwei Namen, beide auf
`upstream/master`: `MeasureTheory.Measure.infinitePi` samt
`isProjectiveMeasureFamily_pi` und `piContent_tendsto_zero`
(`Mathlib/Probability/ProductMeasure.lean`), und
`ProbabilityTheory.poissonMeasure`
(`Mathlib/Probability/Distributions/Poisson/Basic.lean:41`, Namensraum
`ProbabilityTheory`, Notation `Po(r)`) — letzteres, weil das acceptance example
von `MartingaleProblems` M4 den Sprungprozeß mit `lam ≡ 1`,
`mu x = δ (x+1)` gegen die Poissonverteilung rechnet und dafür der Name
stimmen muß. `PMF.poisson`, was ich zuerst schreiben wollte, gibt es nicht.

**Was offen bleibt.** Nichts an dieser Aufgabe. Die Checkliste in
`VORBILD-OneParameterSemigroups.md` hat mit Punkt 4 jetzt drei von sechs
Punkten erledigt; offen sind dort Punkt 2 (jede Stelle entschärfen, die
`brownian-motion` oder `kolmogorov_extension4` als Spezifikation statt als
Zitat führt), Punkt 5 (KI-Attribution in die PR-Beschreibung) und Punkt 6
(`Exchangeability` und `OptimalTransport` querlesen).

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
**`SkorokhodSpace.countable_leftJumpSet`** — die Abzählbarkeit der Sprungmenge
einer càdlàg-Abbildung, `SkorokhodSpace` Meilenstein 2, seit dem 2026-09-05 ein
`sorry`. Der dritte Lauf von heute hat es schon vorgeschlagen, und dieser Lauf
verstärkt den Vorschlag um ein Argument, das vorher nicht dastand: das
acceptance example, das ich für Meilenstein 2 geschrieben habe, **pinnt die
Beweisform**. Der Pfad
`f = ∑' n, 2⁻¹ ^ n * Set.indicator (Set.Ici (1/(n+1))) 1` ist càdlàg — der
Linkslimes bei `0` ist `0`, und rechtsstetig ist er dort, weil die Restmasse
jenseits von `1/(n+1)` gerade `2⁻¹ ^ n` ist — und seine `leftJumpSet`
**hat** den Häufungspunkt `0`, während jede `largeLeftJumpSet f ε` endlich ist.
Ein Beweis, der zeigen will, daß `leftJumpSet` keinen Häufungspunkt hat,
scheitert damit an einer konkreten Instanz; die Zerlegung über `ε` ist keine
Bequemlichkeit, sondern notwendig. Worauf es ruht: `IsCadlag`, die
Häufungspunktaussage über `largeLeftJumpSet` (Meilenstein 2, (B) allein) und
`isCompact_exhaustion` von Meilenstein 1 für die σ-Kompaktheit. Warum jetzt: es
liegt weiterhin auf dem kritischen Weg zur Trennung, dem einzigen fehlenden
Metrikaxiom von Meilenstein 4, an dem zehn der dreizehn `sorry` von
`SkorokhodSpace/Suggested.lean` hängen — und es stützt `fact:Dcountable`
(tragend `4`) über die Meilensteine 4, 5 und 6.

Als zweites, kleineres Ziel im selben Lauf, falls das erste früh fällt:
**`SkorokhodSpace.tendsto_distOn_slidingStep`**, das acceptance example von
Meilenstein 4 als Lean-Aussage — für `f = Set.indicator (Set.Ici 1) 1` und
`g ε = Set.indicator (Set.Ici (1+ε)) 1` auf `ι = ℝ`, `E = ℝ` gilt
`distOn t₀ m f (g ε) ≤ Real.log (1 + ε)` für `ε ≤ 1 ≤ m`, mit der stückweise
linearen Zeitänderung als Zeugen. Es braucht die `MetricSpace`-Instanz **nicht**
— `distOn` ist definiert und seine beiden Schranken sind bewiesen —, es ist
`ciInf_le` an einem expliziten Zeugen plus `norm`-Rechnung auf einer
Streckung, und es wäre der erste Beleg dafür, daß `distOn` wirklich die
`J₁`-Metrik ist und nicht die Supremumsmetrik. Ein acceptance example, das als
übersetzte Deklaration dasteht, ist nach den Regeln dieses Projekts der
stärkste Beleg, den ein Meilenstein haben kann.

### 2026-09-07, fünfter Lauf des Tages — Rückstau 1: die Sprungtheorie braucht das Bündel (B) nicht, und die Trennung braucht die Stetigkeitsstellen nicht

Keine vorrangige Aufgabe, kein `?` in der Tabelle; also der Rückstau von oben
und dort das benannte Ziel des dritten Laufs von heute:
**`countable_leftJumpSet`**. Es steht, mit Beweis, dazu die
Stetigkeitscharakterisierung — und im selben Lauf ist die **Trennung** von
Meilenstein 4 gefallen, das Ziel, das dieser Bericht erst als das des nächsten
Laufs vorsehen wollte. `SkorokhodSpace/Suggested.lean` geht durch
`lake env lean` gegen `v4.33.1`, ohne Fehler und ohne Linterwarnung; 12 `sorry`
statt 13, und elf neue Deklarationen, alle bewiesen. Acht davon sind die
Sprungtheorie:
`IsCadlag.tendsto_leftLim`, `largeLeftJumpSet`,
`IsCadlag.dist_leftLim_le_of_Ioo_subset`,
`IsCadlag.eventually_dist_leftLim_lt`,
`IsCadlag.finite_largeLeftJumpSet_inter`, `countable_leftJumpSet`,
`IsCadlag.continuousAt_iff_notMem_leftJumpSet` und
`IsCadlag.continuous_iff_leftJumpSet_eq_empty`; die drei anderen sind die
Trennung, `IsCadlag.eq_of_forall_exists_dist_le`,
`SkorokhodSpace.eq_of_distOn_eq_zero` und
`SkorokhodSpace.eq_of_forall_distOn_eq_zero` (Punkt 6).

**1. Der Befund, und er ist der wertvollste des Laufs: die Sprungtheorie steht
unter (A′), nicht unter (B).** Meilenstein 2 führte drei Aussagen — die
Häufungspunktfreiheit von `largeLeftJumpSet`, die Stetigkeitscharakterisierung
und die Abzählbarkeit von `leftJumpSet` — seit dem 2026-08-29 unter dem Bündel
(B), also unter „lineare Ordnung, Ordnungstopologie **und** eine abzählbare
dichte Menge `D`, aus der heraus jeder nicht-maximale Punkt von rechts
erreichbar ist". Der Beweis verbraucht von `D` **nichts**. Er benutzt die
lineare Ordnung, die Ordnungstopologie (über
`mem_nhdsLT_iff_exists_Ioo_subset'`, `mem_nhdsGE_iff_exists_Ico_subset'`,
`Ioi_mem_nhds` und `leftLim_eq_of_eq_bot`) und für die Abzählbarkeit die
σ-Kompaktheit des Index; `AdditiveDist` ist an allen acht Deklarationen
`omit`, `ProperSpace` an allen bis auf `countable_leftJumpSet`, und dort nur
für `isCompact_exhaustion`. Die drei Punkte sind im Roadmaptext in die
(A′)-Liste gewandert, mit der Notiz, was von (A′) sie wirklich verbrauchen;
unter (B) bleiben genau zwei, `IsCadlag.measurable` und
`IsCadlag.eq_of_eqOn_dense`. Das ist die stehende Regel über minimale
Voraussetzungen an der Stelle, an der sie etwas kostet: (B) ist mit dem Index
von Meilenstein 1 unvergleichbar, also galt die Sprungtheorie unter (B) für den
diskreten Index gar nicht, sondern mußte dort nur „instanziierbar" sein. Sie
gilt dort jetzt.

**2. Die Aussage, die der Roadmap gefehlt hat, und warum sie die Gestalt des
Beweises bestimmt.** `IsCadlag.dist_leftLim_le_of_Ioo_subset`: bleibt `f` auf
`Set.Ioo a y` und in `y` selbst `r`-nah an **einem** Punkt `c` von `E`, so ist
der Sprung von `f` in `y` höchstens `2r`. Sie wird zweimal angewandt, links von
`x` mit `c` = Linkslimes dort und rechts mit `c` = Wert dort, und sie ist der
einzige Ort, an dem `Function.leftLim` direkt vorkommt. Der entartete Fall ist
in ihr keine Ausnahme, sondern der Grund, sie über den *Sprung* zu formulieren
und nicht über den Linkslimes: wo `𝓝[<] y = ⊥` ist, *ist* der Linkslimes der
Wert (`leftLim_eq_of_eq_bot`), und der Sprung ist `0` — eine Aussage über den
Linkslimes allein wäre dort falsch, weil `y` selbst nicht in `Ioo a y` liegt.

**3. Die Häufungspunktaussage in ihrer scharfen Form.**
`IsCadlag.eventually_dist_leftLim_lt` sagt: **jeder** Punkt `x` des Index — auch
einer, der selbst springt — hat eine Umgebung, auf der `x` der einzig mögliche
Sprung der Höhe `ε` ist. Der Punkt selbst läßt sich nicht ausschließen, eine
càdlàg-Funktion darf an jeder einzelnen Stelle springen; und er muß es nicht,
denn eine Menge, die eine Umgebung jedes Punktes des Index in höchstens einem
Punkt trifft, trifft schon jede kompakte Menge in einer endlichen — das ist
`IsCadlag.finite_largeLeftJumpSet_inter` über `IsCompact.elim_nhds_subcover`,
mit `Set.finite_singleton` je Überdeckungsstück. Die Zerlegung der Umgebung ist
`nhdsLT_sup_nhdsGE` und damit dieselbe wie in
`IsCadlag.isBounded_image_of_isCompact` vom dritten Lauf; die beiden entarteten
Fälle — `x` ein kleinstes Element, wo `Set.Iio x = ∅` und der Filter `⊥` ist,
und `x` ein größtes, wo `Set.Ici x = {x}` ist — tragen keinen Inhalt und werden
getrennt erledigt.

**4. Die Abzählbarkeit, und der leere Index.** `countable_leftJumpSet` zerlegt
über die Sprunghöhe (`exists_nat_one_div_lt`) und über die Ausschöpfung
(`exists_nat_ge` auf `dist t₀ x`), also in eine abzählbare Vereinigung endlicher
Mengen. Die Ausschöpfung braucht einen Basispunkt, den ein **leerer** Index
nicht hat; der Fall steht als eigener Zweig (`isEmpty_or_nonempty`) und ist
`Set.finite_univ`. Das ist keine Pedanterie: Meilenstein 1 verlangt vom Index
keine Nichtleerheit, und von den laufenden Instanzen ist `Set.Icc (0:ℝ) T` für
`T < 0` leer.

**5. Die Stetigkeitscharakterisierung, im selben Lauf mitgenommen.**
`IsCadlag.continuousAt_iff_notMem_leftJumpSet` und die globale Fassung
`IsCadlag.continuous_iff_leftJumpSet_eq_empty`. Hin ist es
`ContinuousWithinAt.leftLim_eq` auf der Einschränkung auf `Set.Iic x`, zurück
`IsCadlag.tendsto_leftLim`, entlang `f⁻ x = f x` umgeschrieben, plus die
Rechtsstetigkeit und wieder `nhdsLT_sup_nhdsGE`. Sie ist der nächste Baustein
auf dem Weg zur Trennung: dort wird `G t = F t` zunächst nur an den
Stetigkeitsstellen von `F` gewonnen, und „Stetigkeitsstelle" heißt ab jetzt
„nicht in `leftJumpSet F`", was `countable_leftJumpSet` abzählbar macht.

**6. Und im selben Lauf die Trennung, das letzte Metrikaxiom von Meilenstein 4 —
über einen Weg, der die Dichtheit der Stetigkeitsstellen *nicht* braucht.**
`SkorokhodSpace.eq_of_distOn_eq_zero`: aus `distOn t₀ m f g = 0` folgt
`(restrictExhaustion t₀ m f).toFun = (restrictExhaustion t₀ m g).toFun`, dazu
`SkorokhodSpace.eq_of_forall_distOn_eq_zero` für den Übergang von allen Fenstern
zu den Pfaden. **Meilenstein 4 hat damit alle vier Axiome von `distOn` als
Sätze.**

Der klassische Beweis (Billingsley) liest `G = F` an den Stetigkeitsstellen von
`F` und beruft sich dann auf deren Dichtheit. Das ist eine Aussage über den
**Index**, und für einen Index von Meilenstein 1 — eine abgeschlossene Teilmenge
von `ℝ`, kein Intervall — ist sie in dieser Stärke nicht verfügbar: die
Sprungmenge ist zwar abzählbar, aber abzählbare Komplemente sind in einem
beliebigen abgeschlossenen `ι` nicht rechtsdicht. (Daß sie es *doch* sind, ließe
sich über Cantor--Bendixson zeigen — eine nichtleere abzählbare abgeschlossene
Menge hat isolierte Punkte, und an isolierten Punkten springt nichts —, aber das
ist ein Umweg über die Perfektmengen-Theorie und über
`exists_orderIso_isometry_real`, das selbst noch ein `sorry` ist.)

Der Weg, der stattdessen trägt, spielt die Zeitänderung gegen ihre Inverse aus
und ist als eigene Aussage von Meilenstein 2 aufgeschrieben,
`IsCadlag.eq_of_forall_exists_dist_le`: zwei càdlàg-Abbildungen stimmen in `t`
überein, sobald beliebig nah an `t` und **rechts davon** die eine gegen den Wert
der anderen in `t` mit beliebig kleinem Fehler auswertbar ist. Zu gegebenem `ε`
liefert `exists_lt_distOn_add` ein `λ` mit `norm λ < ε` und
`dist (F (λ s)) (G s) < ε` für **jedes** `s`. Entweder ist `λ t ≥ t` — dann ist
`F (λ t)` nah an `F t`, weil `F` rechtsstetig ist —, oder `λ t < t`, und dann
ist `t < λ⁻¹ t`, `G (λ⁻¹ t)` ist nah an `G t`, weil `G` rechtsstetig ist, und
die Voraussetzung an der Stelle `λ⁻¹ t` gelesen ist `dist (F t) (G (λ⁻¹ t)) < ε`.
**Beide Zweige nähern sich von rechts** — der einzigen Seite, die eine
càdlàg-Abbildung kontrolliert —, und vom Index geht nur
`TimeChange.dist_le_of_norm_le` ein. Der Beweis ist reine ε-δ-Rechnung
(`Metric.tendsto_nhdsWithin_nhds`), ohne Teilfolgen und ohne Filter; die
Verkleinerung `δ ↦ (exp δ − 1)·2m < ρ` steht als eigener Schritt, weil
`dist_le_of_norm_le` die Verschiebung nur in dieser Form beschränkt.

Bemerkenswert ist, was der Lauf damit über seine eigene Vorbereitung sagt:
`countable_leftJumpSet` und die Stetigkeitscharakterisierung waren als
Vorstufen der Trennung geplant und sind für **diesen** Beweis der Trennung
**nicht nötig**. Sie bleiben richtig und tragend — `fact:Dcountable` ruht auf
ihnen, und Meilenstein 8 braucht sie —, aber der kritische Weg zur
`MetricSpace`-Instanz lief nicht über sie. Das ist kein Argument gegen die
Reihenfolge, sondern eine Notiz für den nächsten Vorschlag: der angenommene
kritische Weg war nicht der kürzeste.

**Was offen bleibt.** Die zwölf `sorry` sind `exists_orderIso_isometry_real`
(M1), `IsCadlag.measurable` (M2) und die zehn an der
`MetricSpace D(ι, E)`-Instanz. Von den Definitionen mit `sorry` im Rumpf sind
weiterhin `SkorokhodSpace.modulus` und die `MetricSpace`-Instanz da; letztere
hat beide Daten und **alle** Axiome von `distOn`.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
**Die Instanz `MetricSpace D(ι, E)` selbst**, also
`dist f g = ∑' m, 2⁻¹ ^ m * min 1 (distOn t₀ m f g)` von Meilenstein 4, mit den
vier Axiomen aus `distOn_nonneg`, `distOn_self`, `distOn_comm`,
`distOn_triangle` und `eq_of_forall_distOn_eq_zero` — gliedweise, denn `min 1 ·`
erhält die Dreiecksungleichung, und die Summierbarkeit ist die geometrische
Reihe. Worauf sie ruht, steht damit vollständig; an ihr hängen zehn der zwölf
`sorry` der Datei. **Eine Vorfrage stand dabei im Weg und ist in diesem Lauf
entschieden und in die Roadmap eingetragen:** die Metrik braucht einen
Basispunkt, den der Typ `D(ι, E)` nicht kennt — `distOn` ist gleich doppelt an
`t₀` verankert, über das Fenster `exhaustion t₀ m` **und** über die Untergruppe
`TimeChange.fixing t₀` —, während die Datei sie als parameterlose `instance`
führt und deshalb gar nicht definierbar hätte sein können. Meilenstein 4 führt
sie seit diesem Lauf als `SkorokhodSpace.metricSpace (t₀ : ι)`, eine `def` mit
dem Basispunkt als Parameter; die Instanz ist die am ausgezeichneten Punkt eines
Index, der einen hat, und das ist `0` für alle vier laufenden Instanzen. Nicht
behauptet und deshalb auch nicht in die Roadmap geschrieben ist, daß zwei
Basispunkte dieselbe Topologie geben — das ist plausibel, aber die
Untergruppen `TimeChange.fixing t₀` sind für verschiedene `t₀` verschieden, und
ein Beweis dafür liegt nicht vor. `fact:Dcountable` (tragend `4`) und
`fact:fddconv` (tragend `1`) hängen über die Meilensteine 5, 6 und 8 daran.

### 2026-09-07, sechster Lauf des Tages — Rückstau 1: `MartingaleProblems`, zwei Beweise, ein halber Zeuge und eine leere Schärfeaussage

Die vorrangigen Aufgaben sind leer — die acceptance examples des vierten Laufs
decken alle siebenundzwanzig Meilensteine ab (5 + 8 + 3 + 11, gezählt gegen
`grep -c '^## Milestone'`) —, und keine Zeile der Tabelle steht auf `?`. Also
Rückstau, Punkt 1, und dort die Datei, die er ausdrücklich nennt:
`MartingaleProblems/Suggested.lean`, seit dem 2026-09-06 unberührt, während
`SkorokhodSpace` viermal drankam.

**Ausgangslage, gemessen und nicht erinnert.** Ein Durchlauf von
`lake env lean` gegen v4.33.1 vor jeder Änderung: rc = 0, elf `sorry`, keine
weitere Warnung. Am Ende: rc = 0, **zehn** `sorry`, keine weitere Warnung, 50
Deklarationen statt 38.

**Bearbeitet.**

* **`Clock.interval_union` ist bewiesen** — der erste `sorry` der Datei und die
  Additivität, auf der nach der Roadmap („the only property used downstream")
  jedes Kompensatorargument von Meilenstein 1 ruht. Beide Konventionen, beide
  Hälften: die Zerlegung von `Set.Iic u \ Set.Iic s` in
  `(Set.Iic t \ Set.Iic s) ∪ (Set.Iic u \ Set.Iic t)`, dieselbe für `Set.Iio`,
  dazu die Disjunktheit. Der Beweis braucht **nur** `[Preorder ι]` und
  Transitivität, wie die Roadmap behauptet; nirgends geht Vergleichbarkeit ein,
  und das ist genau der Grund, aus dem die Uhr die Differenz von Abwärtsmengen
  nimmt und nicht `Set.Ico`.

* **`not_isQuasiLeftContinuous_of_not_ae_tendsto` ist neu und bewiesen** — die
  Umkehrung von `IsQuasiLeftContinuous.ae_eq_leftLim`, die einzige Richtung, die
  ein Gegenbeispiel braucht: aus einer monotonen Folge `s : ℕ → ι` mit
  `∀ n, s n ≤ t` und `⨆ n, s n = t`, entlang der `X (s n)` fast sicher **nicht**
  gegen `X t` läuft, folgt `¬ IsQuasiLeftContinuous X 𝓕 P`. Die konstanten
  Stoppzeiten `τ n = s n` sind das, worauf die Definition getestet wird; deshalb
  muß kein Linkslimes existieren, und weder `[T2Space E]` noch eine Topologie
  auf dem Index über die Ordnung hinaus geht ein (`omit [MeasurableSpace E]
  [TopologicalSpace ι] [OrderTopology ι]`, vom Linter bestätigt). Damit ist der
  Zeuge auf die Konstruktion der Lösung reduziert und auf sonst nichts.

* **Der Zeuge selbst ist gebaut und übersetzt, bis auf die
  Martingaleigenschaft**, als Namensraum `AtomWitness` in derselben Datei, elf
  Deklarationen, alle bewiesen:
  `coinMeasure = 2⁻¹ • (Measure.dirac true + Measure.dirac false)` samt
  `IsProbabilityMeasure`-Instanz und `coinMeasure {true} = 2⁻¹`; die Uhr
  `atomClock u` mit `measurableSpace = ⊤` und `q = Measure.dirac u`, samt
  `atomClock_apply_singleton : (atomClock u).q {u} = 1` und der Folgerung
  `≠ 0` — über `⊤` ist jede Abwärtsmenge meßbar, und die endliche Masse ist die
  eines Wahrscheinlichkeitsmaßes;
  `coinProcess u t ω = if u ≤ t then ω else false` samt seinen beiden
  Auswertungslemmata; `isCadlagPath_coinProcess`, für **jedes** `u` und jedes
  `ω`, weil der Pfad zu beiden Seiten von `u` lokal konstant ist; und
  `not_isQuasiLeftContinuous_coinProcess`, für **jede** Filtration. Über
  `Ω = E = Bool` ist die Münze zugleich Stichprobenpunkt und Zustand, was den
  Prozeß ohne Produktkonstruktion hinschreibbar macht. Was zur vollen Aussage
  fehlt, ist genau zweierlei: die Filtration (`⊥` unterhalb von `u`, `⊤` von `u`
  an) und die Martingaleigenschaft von
  `mpFamily A (atomClock u) Clock.Conv.optional (coinProcess u)`.

**Der Befund, und er ist der eigentliche Ertrag des Laufs:
`not_isQuasiLeftContinuous_of_atom` war als Aussage leer.** Sie behauptet die
Schärfe der Atomlosigkeit in `isQuasiLeftContinuous_of_isMPSolutionFor` und
quantifizierte dabei existentiell über `A`, ohne eine Bedingung an `A`. Mit
`A = ∅` ist `mpFamily A Q c X` leer, `IsMPSolution` gilt dann von **jedem** Maß,
und irgendein nicht quasi-linksstetiger Prozeß über `Q.q = Measure.dirac u`
erledigt die Aussage, ohne irgend etwas über Atome zu zeigen. Eine
Schärfeaussage, die einen leeren Zeugen zuläßt, ist keine.

Die Aussage trägt seit diesem Lauf **jede** Hypothese von
`isQuasiLeftContinuous_of_isMPSolutionFor` außer `hQ` in ihrer Konklusion:
`IsProbabilityMeasure P`, die Schranken und die Stetigkeit von `hA`,
`IsSeparating (Prod.fst '' A)` und die fast sicher càdlàg-Pfade. `IsSeparating`
ist dabei das, was `A ≠ ∅` erzwingt — über `Bool` trennt die leere Klasse
`Measure.dirac true` nicht von `Measure.dirac false` —, und
`IsProbabilityMeasure P` schließt `P = 0` aus demselben Grund aus (unter `P = 0`
gilt jede fast sichere Aussage, also auch die Quasi-Linksstetigkeit selbst). Die
Roadmap führt die Begründung im Meilenstein 9 mit. Das Muster ist dasselbe wie
beim Diamant-Gegenbeispiel und bei der leeren Klasse: ein existentiell
quantifiziertes Datum ohne Bedingung macht eine Negativaussage wertlos, und
diese Datei führt mehrere solche Existenzaussagen — wer die nächste anfaßt,
prüft sie zuerst gegen den trivialen Zeugen.

**Mitgefunden, am Übersetzen und nicht am Lesen.**

* `Set.mem_diff` ist `deprecated`, Nachfolger `Set.mem_sdiff` — und der muß
  **qualifiziert** geschrieben werden: unter `open Filter Set`, wie diese Datei
  es tut, ist `mem_sdiff` zwischen `Set.mem_sdiff` und `Filter.mem_sdiff`
  mehrdeutig. Lean meldet dann „Ambiguous term", ohne daß der Beweis scheitert —
  er geht per Definitionsgleichheit durch —, und der Linter meldet zusätzlich
  ein `simp`-Argument als unbenutzt, das es in Wahrheit nicht ist.
* `lt_of_not_le` gibt es in v4.33.1 nicht; `not_le.1` tut es.
* `ℝ≥0∞` ist **scoped**-Notation und in dieser Datei nicht verfügbar, weil ihr
  `open`-Kopf `ENNReal` nicht nennt. Ausgeschrieben `ENNReal`, statt den Kopf zu
  ändern.
* `omit … in` steht **vor** dem Doc-Kommentar, nicht zwischen ihm und der
  Deklaration; dazwischen meldet Lean „unexpected token 'omit'".
* `ENNReal.inv_two_add_inv_two` (`Basic/ENNReal/Inv.lean:525` auf
  `upstream/master`) ist das Lemma, das `simp` für `2⁻¹ + 2⁻¹ = 1` fehlt.

**Was als Nächstes formalisiert werden soll.**
`AtomWitness.isMPSolution_coinProcess` und damit die Vervollständigung von
`not_isQuasiLeftContinuous_of_atom`. Die Aussage: für `u : ι` löst
`coinProcess u` unter `coinMeasure`, der Uhr `atomClock u` und der
Filtration `fun t ↦ if u ≤ t then ⊤ else ⊥` das Martingalproblem zu
`A = {(fun b ↦ if b then 1 else 0, fun _ ↦ 2⁻¹)}` in der Konvention
`Clock.Conv.optional`. Sie ruht auf drei Rechnungen und keiner Theorie: dem
Mengenintegral gegen `Measure.dirac` über `Q.interval c ⊥ t`, das für
`¬ u ≤ ⊥` gerade `if u ≤ t then p.2 (X u ω) else 0` ist; der bedingten
Erwartung gegen `⊥`, die die Konstante `∫ Y t ∂P` ist; und der Bilanz
`p.1 true − p.1 false = p.2 true + p.2 false`, die die Martingaleigenschaft über
`u` hinweg **genau** ausdrückt und der Grund ist, aus dem in `A` das feste `2⁻¹`
steht und nicht irgendein Kompensator. Sie ist jetzt dran, weil die andere
Hälfte des Zeugen steht und übersetzt ist, weil die Roadmap sie als acceptance
example von Meilenstein 9 führt („the pair fixes where atomlessness is a
hypothesis and where it is not"), und weil sie die einzige der zehn
verbleibenden `sorry` der Datei ist, die eine Konstruktion und kein Satz ist.

### 2026-09-07, siebter Lauf des Tages — Rückstau 1: der Atom-Zeuge ist fertig, und die Konvention ist keine Wahl

Keine vorrangige Aufgabe, keine Zeile der Tabelle auf `?`. Also Rückstau, Punkt
1, und dort das benannte Ziel des sechsten Laufs: `isMPSolution_coinProcess`.
**Es steht, und mit ihm `not_isQuasiLeftContinuous_of_atom` selbst.**
`MartingaleProblems/Suggested.lean` geht durch `lake env lean` gegen `v4.33.1`,
rc = 0, ohne Fehler und ohne Linterwarnung; **neun** `sorry` statt zehn, und zehn
neue Deklarationen, alle bewiesen:

`integrable_bool`, `integral_coinMeasure`, `coinPair`, `coinClass`,
`isSeparating_coinClass`, `atomClock_real_of_mem`, `atomClock_real_of_notMem`,
`integral_coinPair_snd`, `coinFiltration`, `isMPSolution_coinProcess`.

Damit trägt die einzige Schärfeaussage der Roadmap zur Atomlosigkeit einen
vollständigen, übersetzten Zeugen: eine Uhr mit einem Atom bei `u`, eine Lösung
des Martingalproblems zu einer **trennenden** Klasse, càdlàg-Pfade — und keine
Quasi-Linksstetigkeit. Kein Fact wechselt den Status; `fact:cadlagext`,
`fact:submgreg`, `fact:optsampl`, `fact:doob` und `fact:stoppedlocalmg` stehen
weiter auf Meilenstein 9, dessen Text jetzt die zehn Namen führt.

**1. Der Befund, und er ist der Ertrag des Laufs: die Konvention ist keine Wahl,
sondern erzwungen.** Der Zeuge löst das Martingalproblem in
`Clock.Conv.optional` und in der anderen Konvention **nicht**, und zwar aus
einem Grund, der nichts mit dem konkreten `coinPair` zu tun hat. In
`Clock.Conv.predictable` ist das Kompensationsintervall `Set.Iio t \ Set.Iio ⊥`,
und `Set.Iio ⊥` ist leer, weil `x < ⊥` unter `[OrderBot ι]` nie gilt; das
Intervall ist also `Set.Iio t`, und die Uhr `Measure.dirac u` lädt es genau dann,
wenn `u < t`. Der Kompensator feuert dann **echt nach** `u`, während der Pfad
schon **bei** `u` springt. Die Martingaleigenschaft an der Stelle `t = u`, gegen
die triviale σ-Algebra darunter gelesen, ist
`2⁻¹ * (p.1 true + p.1 false) = p.1 false`, also `p.1 true = p.1 false`: jede
prädiktable Fassung dieses Zeugen hat ein **konstantes** `p.1`, und eine
konstante Funktion trennt `Measure.dirac true` nicht von `Measure.dirac false`.
Die Hypothese `IsSeparating (Prod.fst '' A)`, die der sechste Lauf gegen den
leeren Zeugen eingezogen hat, schließt also zugleich die prädiktable Konvention
aus. Das ist kein Mangel der Schärfeaussage — sie quantifiziert über `c`
existentiell —, und es verträgt sich mit
`isQuasiLeftContinuous_of_isMPSolutionFor`, das über `c` universell
quantifiziert: unter `Clock.IsAtomless` fallen die beiden Konventionen zusammen,
eine Schärfeaussage braucht also nur eine von beiden. Im Roadmaptext von
Meilenstein 9 steht die Rechnung jetzt mit.

**2. Der Zeuge braucht auf dem Index keine Topologie.** Alle zehn neuen
Deklarationen tragen `omit [TopologicalSpace ι] [OrderTopology ι]` (bei den
beiden Uhrmassen zusätzlich `omit [OrderBot ι]`), vom Linter bestätigt und nicht
geraten. Insbesondere `isMPSolution_coinProcess`: die Martingaleigenschaft ist
reine Ordnungs- und Maßrechnung. Die Topologie des Index kommt erst in
`not_isQuasiLeftContinuous_of_atom` selbst vor, und dort an genau einer Stelle —
`⨆ n, s n = u` aus `Tendsto s atTop (𝓝 u)`, über `tendsto_atTop_ciSup` und
`tendsto_nhds_unique`, wofür die Ordnungstopologie das `T2Space` liefert. Das
ist dieselbe Rechnung wie in `IsQuasiLeftContinuous.ae_eq_leftLim` und die
einzige Rolle, die die Topologie im ganzen Gegenbeispiel spielt.

**3. Die zwei Rechnungen, aus denen der Beweis besteht.** Der Kompensator ist
`setIntegral_const` gegen `Measure.dirac u`: das Intervall
`Set.Iic t \ Set.Iic ⊥` enthält `u` genau dann, wenn `u ≤ t` — hier, und nur
hier, geht `¬ u ≤ ⊥` ein, das aus `s 0 < u` und `not_lt_bot` kommt —, also ist
der Kompensator `2⁻¹` von `u` an und `0` davor (`integral_coinPair_snd`, über
`atomClock_real_of_mem` bzw. `atomClock_real_of_notMem`). Der Prozeß ist damit
`0` strikt vor `u` und `(if ω then 1 else 0) - 2⁻¹` von `u` an. Die
Martingaleigenschaft zerfällt in zwei Fälle: oberhalb von `u` ist `𝓕 s` die
ganze σ-Algebra und `Y t = Y s`, also `condExp_of_stronglyMeasurable`; unterhalb
ist `𝓕 s = ⊥` und `Y s = 0`, also `condExp_bot`, und was zu zeigen bleibt, ist
`∫ Y t = 0` — das ist `integral_coinMeasure`, `2⁻¹(1 - 2⁻¹) + 2⁻¹(0 - 2⁻¹) = 0`.
Die Konstante `2⁻¹` in `coinPair.2` ist deshalb keine Wahl, sondern die Bilanz
`p.1 true - p.1 false = p.2 true + p.2 false`.

**4. Die Trennung auf `Bool`, in vier Zeilen und mit einem Mathlib-Satz, den das
Inventar noch nicht kannte.** `isSeparating_coinClass`: der Indikator von
`{true}` ist `Set.indicator {true} 1`, sein Integral ist `μ.real {true}`
(`integral_indicator_const`, `MeasureTheory/Integral/Bochner/Set.lean:531`), und
`MeasureTheory.ext_iff_measureReal_singleton`
(`MeasureTheory/Measure/Dirac.lean:118`) macht aus „gleich auf allen Singletons"
die Gleichheit der Maße; die Masse von `{false}` ist der Rest, über
`measureReal_add_measureReal_compl` (`Measure/Real.lean:223`) und `probReal_univ`
(`Measure/Typeclasses/Probability.lean:118`). Eine trennende Klasse mit **einem**
Element, und das ist die kleinste, die es auf `Bool` gibt.

**Am Quelltext belegt** wurden in diesem Lauf, alle in `v4.33.1` und keine
`deprecated`: `memLp_top_of_bound` (`Function/LpSeminorm/Basic.lean:538`),
`MemLp.integrable` (`Function/L1Space/Integrable.lean:659`),
`measurable_of_finite` (`MeasurableSpace/Basic.lean:291`),
`Bool.instMeasurableSpace = ⊤` und `Bool.instMeasurableSingletonClass`
(`MeasurableSpace/Instances.lean:26,56`), `DiscreteTopology Bool`
(`Topology/Order.lean:574`), `integral_smul_measure`, `integral_add_measure`,
`integral_dirac` (`Integral/Bochner/Basic.lean:1014,974,1106`),
`Measure.dirac_apply'` (`Measure/Dirac.lean:44`), `setIntegral_const`
(`Integral/Bochner/Set.lean:527`), `condExp_bot` und
`condExp_of_stronglyMeasurable`
(`Function/ConditionalExpectation/Basic.lean:288,142`) samt der Instanz
`isFiniteMeasure_trim` (`Measure/Trim.lean:124`), die den `SigmaFinite`-Beweis
der zweiten liefert, ohne daß er hingeschrieben werden muß.

**Mitgefunden, am Übersetzen und nicht am Lesen.**

* Ein `if u ∈ S then _ else _` in einer **Aussage** verlangt
  `Decidable (u ∈ S)`, und für ein Kompensationsintervall gibt es die Instanz
  nicht; `classical` im Beweis hilft nicht, weil die Aussage vor dem Beweis
  elaboriert wird. Statt `open scoped Classical` stehen dort zwei Lemmata,
  `atomClock_real_of_mem` und `atomClock_real_of_notMem` — kürzer und an der
  Anwendungsstelle bequemer, weil die Fallunterscheidung dort ohnehin steht.
* In einem **Strukturfeld** (`mono'`, `le'` von `Filtration`) ist das Ziel nicht
  betareduziert: es steht `(fun t ↦ if u ≤ t then _ else ⊥) a ≤ …`, und
  `rw [if_pos ha]` findet sein Muster nicht. Ein `show` mit der reduzierten
  Gestalt behebt es; `simp only [if_pos ha, le_refl]` schließt dann.
* Der Linter für unbenutzte Abschnittsvariablen meldet **kaskadierend**, eine
  Deklaration je Durchlauf: erst nach dem `omit` an der ersten kam die Meldung
  an der zweiten. Vier Durchläufe für vier `omit`.

**Was in `MartingaleProblems` offen bleibt.** Die neun `sorry` der Datei sind
`isMPSolution_iff_forall_fdd` und sein Nachbar (Meilenstein 3), die beiden
Markov-Aussagen der Verschiebung (Meilenstein 5),
`exists_cadlag_modification_of_isRegularizingClass`, die beiden Sätze zur
Quasi-Linksstetigkeit (Meilenstein 9), `mpSolution_of_tendsto` (Meilenstein 10)
und `isMPSolution_of_forall_condExp_eq_of_dense`.

**Und im selben Lauf, weil Zeit blieb: die Metrik von `SkorokhodSpace`
Meilenstein 4 ist gebaut und bewiesen.** Das war das benannte Ziel des fünften
Laufs von heute. `SkorokhodSpace/Suggested.lean` geht durch `lake env lean`,
rc = 0, ohne Fehler und ohne Warnung; sieben neue Deklarationen, alle bewiesen:
`SkorokhodSpace.totalDist` — `∑' m, 2⁻¹ ^ m * min 1 (distOn t₀ m f g)` —,
`summable_totalDist`, `totalDist_self`, `totalDist_comm`, `totalDist_triangle`,
`eq_of_totalDist_eq_zero` und `SkorokhodSpace.metricSpace (t₀ : ι)`, die
`MetricSpace D(ι, E)`-Struktur mit dem Basispunkt als Parameter, wie
Meilenstein 4 sie verlangt.

Alles daran ist gliedweise. Die Summierbarkeit ist die geometrische Reihe, weil
`min 1 ·` den Summanden auf `2⁻¹ ^ m` deckelt — und die Trunkierung ist nicht
Kosmetik, sondern nötig: `distOn t₀ m f g` wächst mit dem Fenster und ist in `m`
unbeschränkt. Die Dreiecksungleichung ist `Summable.tsum_le_tsum` gegen
`Summable.tsum_add`, auf der Subadditivität von `min 1 ·` über den nichtnegativen
Reellen (`min_def` und `split_ifs <;> linarith`, acht Fälle). Die Trennung ist
`Summable.le_tsum`: eine Reihe nichtnegativer Glieder verschwindet nur, wenn
jedes Glied verschwindet, also ist `min 1 (distOn t₀ m f g) = 0` für jedes `m`,
also `distOn = 0`, und `eq_of_forall_distOn_eq_zero` vom fünften Lauf macht
daraus die Gleichheit der Pfade. `AdditiveDist ι` verbrauchen von den fünf
Aussagen nur die beiden letzten, vom Linter bestätigt.

**Die Zahl der `sorry` in `SkorokhodSpace` bleibt trotzdem bei zwölf, und das
ist der Befund dieser Hälfte.** Der parameterlose `instance : MetricSpace D(ι, E)`
darunter bleibt stehen: was ihm fehlt, ist kein Axiom, sondern der
**Basispunkt**. Zehn spätere Deklarationen der Datei elaborieren gegen ihn, und
sie auf `SkorokhodSpace.metricSpace t₀` umzuschreiben ist eine Signaturänderung
an zehn Stellen und kein Beweis; nicht behauptet ist dabei — und deshalb steht
es auch nicht in der Roadmap —, daß zwei Basispunkte dieselbe Topologie geben,
denn die Untergruppen `TimeChange.fixing t₀` sind für verschiedene `t₀`
verschieden. Der Doc-Kommentar des `instance` sagt jetzt genau das, statt wie
bisher die vier Axiome mitzuzählen.

**Mitgefunden.** `summable_geometric_of_lt_one` läßt sich nicht als drittes
Argument von `Summable.of_nonneg_of_le` schreiben — die Vergleichsfunktion ist
dort noch eine Metavariable, und `norm_num` sieht `0 ≤ ?r`; die geometrische
Reihe gehört in ein eigenes `have`. Und `simp` normalisiert `2⁻¹ ^ m` zu
`(2 ^ m)⁻¹`, womit ein vorbereitetes `∀ m, 2⁻¹ ^ m * … = 0` nicht mehr paßt;
`show` plus `tsum_congr` plus `tsum_zero` ist der Weg, der nicht daran vorbeiläuft.
Eine `def` mit Klassentyp will `@[instance_reducible]`, sonst warnt der Linter —
dieselbe Meldung wie bei `generateFromFuns` am 2026-09-06.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
**`SkorokhodSpace.IsCadlag.measurable`** — daß eine càdlàg-Abbildung meßbar ist,
Meilenstein 2, seit dem 2026-09-05 ein `sorry` und einer von nur noch zwei in der
Datei, die nicht an der parameterlosen Instanz hängen. Worauf sie ruht: auf dem
Bündel (B), das die Roadmap für genau diese Aussage führt — die abzählbare
dichte Menge `D`, aus der heraus jeder nicht-maximale Punkt von rechts erreichbar
ist. Der Weg ist die Approximation von rechts entlang `D`: die Approximanten
nehmen abzählbar viele Werte an und sind darum meßbar, die Rechtsstetigkeit gibt
den punktweisen Limes, und `measurable_of_tendsto_metrizable`
(`MeasureTheory/Constructions/BorelSpace/Metrizable.lean:51`, am Quelltext
geprüft) trägt ihn. Die Sprungtheorie des fünften Laufs liegt daneben bereit —
`countable_leftJumpSet`, `IsCadlag.continuousAt_iff_notMem_leftJumpSet` und
Mathlibs `measurableSet_of_continuousAt`
(`Constructions/BorelSpace/Basic.lean:252`), das die Menge der Stetigkeitsstellen
als meßbar ausweist —, falls die Ausnahmemenge einzeln behandelt werden muß.
Warum jetzt: `fact:Dcountable` (tragend `4`) verlangt über Meilenstein 8 die
Fassung **für ein Maß**, und deren Fubini-Argument über die Sprunghöhen braucht
die Meßbarkeit der Pfadabbildung als erstes Datum — ohne sie ist der Schritt von
der Pfadaussage zur Maßaussage nicht einmal formulierbar. Als zweites, kleineres
Ziel im selben Lauf: `AtomWitness` um die Umkehrung ergänzen — daß die Uhr
`atomClock u` **nicht** atomlos ist, `¬ (atomClock u).IsAtomless`, zwei Zeilen
aus `atomClock_apply_singleton_ne_zero` und `measure_mono` an der Stelle `t = u`
(die Menge `{v | u ≤ v ∧ v ≤ u}` enthält `u`), die die Schärfeaussage
sichtbar an die Hypothese `hQ` von `isQuasiLeftContinuous_of_isMPSolutionFor`
bindet.
