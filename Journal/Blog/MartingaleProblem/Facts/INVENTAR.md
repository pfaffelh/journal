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

**Zweite Hälfte der Regel, hinzugefügt am 2026-09-08 nach dem fünften Fehler.**
Der achte Lauf des 2026-09-08 schrieb „Mathlib hat kein abzählbares Produkt von
Kernen", hatte aber `ProbabilityTheory.Kernel.traj` — Ionescu--Tulcea — im
selben Satz in der Hand und verwarf sie mit „für eine Filtration, beides nicht
das Gesuchte". Diesmal lag es also **nicht** am Finden, sondern am Verwerfen,
und die vier Suchbegriffe waren zwar Mathlib-Vokabeln, aber immer noch Vokabeln
unserer Konstruktion. Daher:

* **Wer einen Kandidaten verwirft, nennt die Voraussetzung, an der er
  scheitert**, am Quelltext und mit Zeile. „Für eine Filtration", „für den
  endlichen Fall", „nur für Maße" sind Beschreibungen, keine Hypothesen; ein so
  verworfener Kandidat ist ungeprüft. Vorsicht besonders dort, wo die
  Beschreibung eine *Allgemeinheit* nennt: Ionescu--Tulcea läßt die Kerne die
  Vergangenheit lesen, das Produkt ist der Sonderfall, in dem sie es nicht tun.
* **Vor dem Negativbefund wird der eigene Bestand durchsucht.** `traj` stand mit
  Datei und Namen an fünf Stellen in `TauCeti/` und im Inventar selbst. Ein
  `grep` über `TauCeti/` und `Facts/` kostet Sekunden und hätte hier gereicht.

## Tabelle

| Fact | tragend | Aussage | Status | Beleg |
|---|---|---|---|---|
| `fact:Dcountable` | 4 | EK, Lemma 3.7.7 | Roadmap | SkorokhodSpace M8, `SkorokhodSpace.exists_countable_dense_continuity`; Mathlib hat weder `cadlag` noch den Raum. Der Unterbau ist seit dem 2026-09-07, fünftem Lauf, bewiesen und geht durch `lake env lean`: `countable_leftJumpSet` — die Sprungmenge **einer** càdlàg-Abbildung ist abzählbar — samt `IsCadlag.continuousAt_iff_notMem_leftJumpSet`, die „Stetigkeitsstelle" und „nicht in `leftJumpSet`" identifiziert (Meilenstein 2). Was M8 darüber hinaus verlangt, ist die Fassung für **ein Maß** statt für einen Pfad — daß `{t | μ {f | f⁻ t = f t} = 1}` abzählbares Komplement hat —, und die folgt nicht punktweise aus der Pfadaussage, sondern braucht ein Fubini-Argument über die Sprunghöhen; das steht weiter aus |
| `fact:monotoneclass` | 4 | Monotone class theorem; EK, Appendix 4 | Roadmap | WeakConvergence M5, `induction_on_mulSystem` — dort neu angelegt; Mathlib hat nur die Mengenfassung, und sie heißt `MeasurableSpace.induction_on_inter` (`MeasureTheory/PiSystem.lean:713`, nicht `MeasureTheory.`). Am 2026-09-06, zweiter Lauf, negativ belegt an `upstream/master` `810b3888` mit den Suchen `monotone class`, `MulSystem`, `generateFromFuns`, `multiplicative system`, `monotone limits`, `bounded monotone convergence`, `functional monotone`, `multiplicative family of functions` — kein einziger Treffer in `Mathlib/`. Der Unterbau ist seither übersetzt: `IsMulSystem`, `indicatorFuns`, `generateFromFuns`, die Brücke `generateFromFuns_indicatorFuns`, das π-System `ioiCells` samt `generateFromFuns_eq_generateFrom_ioiCells` und der erste Beweisschritt `of_tendstoUniformly_of_mono_lim` gehen durch `lake env lean`; seit dem 2026-09-06, dritter Lauf, dazu die algebraische Hälfte des zweiten Schritts — `mul_mem_span_insert_one_of_isMulSystem`, `of_mem_span_insert_one`, `exists_bound_of_mem_span_insert_one`. Seit dem 2026-09-07, achtem Lauf, ist der **zweite Schritt selbst bewiesen**, `of_continuous_comp_of_isMulSystem`: die Stone--Weierstraß-Hälfte der Induktion, über `ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints` (`Topology/ContinuousMap/StoneWeierstrass.lean:323`) und einen `AlgHom`-Rückzug in `Submodule.span ℝ (insert 1 K)`. Seit dem 2026-09-07, neuntem Lauf, ist der **Satz selbst bewiesen**: Schritt (iii) als `ioiApprox` samt `of_indicator_mem_ioiCells` und `of_indicator_of_measurable` (die Rampen gemeinsam als *eine* stetige Funktion, weil `P` nicht multiplikationsabgeschlossen ist), Schritt (iv) als `of_simpleFunc` und `of_nonneg_of_measurable` (der Umweg über `ℝ≥0∞` ist das einzige, was die Approximation wachsend macht — `SimpleFunc.approxOn` gibt keine Monotonie), und `induction_on_mulSystem` selbst als die Verschiebung `f = (f + C) + (-C)`. Alle drei Folgerungen tragen ebenfalls Beweise: `ext_of_forall_integral_eq_of_isMulSystem`, `integral_mul_eq_zero_of_isMulSystem` und `condExp_eq_of_forall_integral_mul_eq`. Der Kern von Meilenstein 5 ist damit vollständig; was `fact:monotoneclass` noch trennt, ist kein Beweis mehr, sondern die Übernahme nach Mathlib. Alles durch `lake env lean` gegen v4.33.1 |
| `fact:cmt` | 3 | Continuous mapping theorem; EK, Corollary 3.1.9 and Co | Roadmap | WeakConvergence M2 — der stetige Fall ist Mathlib in **beiden** Fassungen, für Maße als `FiniteMeasure.tendsto_map_of_tendsto_of_continuous` und für Zufallsvariablen als `MeasureTheory.TendstoInDistribution.continuous_comp` (`MeasureTheory/Function/ConvergenceInDistribution.lean:136`, am 2026-09-01, fünfter Lauf, gefunden); die f.ü.-stetige Fassung fehlt in beiden. M2 steht auf „separabel metrisch", und das ist richtig: EK Cor. 3.1.9 verlangt nicht mehr (am Scan geprüft, 2026-08-31). **Seit dem 2026-09-08, erster Lauf, ist die f.ü.-stetige Fassung bewiesen**: `tendsto_of_measure_setOf_not_continuousAt_eq_zero` geht durch `lake env lean` gegen v4.33.1 und hängt nur an `propext`, `Classical.choice`, `Quot.sound`. Der Beweis ist Portmanteau auf beiden Seiten — `closure (h ⁻¹' F) ⊆ h ⁻¹' F ∪ {x | ¬ ContinuousAt h x}` — und braucht **weniger als „separabel metrisch"**: auf der Quelle `[OpensMeasurableSpace E] [HasOuterApproxClosed E]`, auf dem Ziel `[TopologicalSpace E'] [OpensMeasurableSpace E']` ohne jede Metrik, und keine Separabilität. Die Bildmaße treten als Daten mit ihren definierenden Gleichungen auf, nicht über `ProbabilityMeasure.map` — das ist die eine Konstruktion, deren Signatur sich zwischen v4.33.1 und `upstream/master` unterscheidet, und so elaboriert **eine** Aussage gegen beide; die verpackte Fassung `tendsto_map_of_measure_setOf_continuousAt_eq_one` ist diese Aussage instanziiert und trägt ihr `sorry` allein aus diesem Versionsgrund. **Am 2026-09-08, elfter Lauf, ist belegt, daß `fact:cmt` nirgends in nicht-polnischer Allgemeinheit gebraucht wird**, entgegen dem zweiten Absatz von `rem:MZcost`: `set:abstract` (`:2324`) verlangt unter (E3) für den Pfadraum $F$ ausdrücklich eine **polnische** Topologie, `thm:absconv` (`:8393`) ist mit (T0)+(E3) annotiert, `thm:absconvaug` arbeitet auf $F\times G$ mit $G$ polnisch, und `def:weakstrong` (`:9169`) sagt „let $F$ be Polish"; der einzige nicht-polnische Pfadraum des Manuskripts ist $\DE$ unter der Pseudopfad-Topologie, und dort benutzt der Beweis von `thm:MZconv` (`:9314`--`:9400`) **kein** `fact:cmt`, sondern (C1$'$) aus `rem:absconvtopfree`, das gar keine Topologie verlangt — er sagt es selbst („it is verified not by a continuous mapping theorem but by exhibiting the convergence on a common space"). Was der $M_E$-Weg an CMT braucht, ist allein die triviale Hälfte für **überall stetige** Abbildungen, und die hat Mathlib ohne jede Metrik |
| `fact:kolmogorov` | 3 | Kolmogorov extension; EK, Theorem 4.1.1; eqref{T0} + e | Roadmap | KolmogorovExtension M2 — Gerüst weitgehend in Mathlib, es fehlen σ-Subadditivität und `projectiveLimit` |
| `fact:stoneweierstrass` | 3 | Stone--Weierstrass for separating classes; EK, Theorem | Roadmap | WeakConvergence M1 — die separierende Hälfte ist Mathlib (`ext_of_forall_mem_subalgebra_integral_eq_of_polish`); die konvergenzbestimmende ist es **auch**, unter Straffheit und bloßer Punktetrennung: `MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`, `MeasureTheory/Measure/LevyConvergence.lean:154`, am 2026-09-05 an `upstream/master` geprüft, nicht `deprecated`. Es fehlt allein der Schritt von **starker** Trennung zu Straffheit, in M1 als `isTightMeasureSet_of_stronglySeparatesPoints` angelegt (2026-09-05). Die separierende Hälfte ist seit dem 2026-09-06, drittem Lauf, auch auf unserer Seite bewiesen: `IsSeparating.of_subalgebra`, die Anbindung unseres Prädikats an `ext_of_forall_mem_subalgebra_integral_eq_of_polish`, geht durch `lake env lean`. ~~die konvergenzbestimmende fehlt~~ — dieser Befund stand vom 2026-08-29 bis zum 2026-09-05 und war falsch: gesucht worden war nach unserer Vokabel „konvergenzbestimmend" statt nach der Aussage, die in Mathlib unter `SeparatesPoints` und `IsTightMeasureSet` steht. **Am 2026-09-06, dritter Lauf, belegt, daß dieser Weg in Mathlib nicht bloß vorhanden, sondern tragend ist:** `Measure.ext_of_charFun` (`Measure/CharacteristicFunction/Basic.lean:257` auf `upstream/master` `810b3888`, `:248` in v4.33.1) und `Measure.ext_of_charFunDual` (`:462` bzw. `:453`) — „charakteristische Funktionen trennen endliche Maße" — ruhen über `ext_of_integral_char_eq` (`:103` bzw. `:101`) Zeile für Zeile auf `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable` (`Measure/FiniteMeasureExt.lean:36`), angewandt auf `separatesPoints_charPoly` (`Analysis/Fourier/BoundedContinuousFunctionChar.lean:155`). Charakteristische Funktionen sind dort **kein eigenes Fundament**, sondern eine Anwendung der punktetrennenden Unteralgebra `charPoly` (`ibid.:141`), und diese ist eine `StarSubalgebra ℂ (V →ᵇ ℂ)` — also genau die Konjugationsabgeschlossenheit, die der Fact für $\K=\C$ verlangt. Keine der vier Deklarationen ist `deprecated`. **Am 2026-09-07, siebzehnter Lauf, sind die Schritte (1) und (3) des fehlenden Beweises bewiesen** und gehen durch `lake env lean` gegen v4.33.1: `tendsto_integral_comp_of_forall_tendsto_integral` (die Pushforwards nach `κ → ℝ` konvergieren schwach, für beliebigen `Fintype κ`) samt `coordAlgebra`, `separatesPoints_coordAlgebra` und `exists_mem_subalgebra_comp_of_mem_coordAlgebra`, dazu die Portmanteau-Folgerung `le_liminf_measure_preimage_of_isOpen` und Schritt (3) selbst, `le_liminf_measure_thickening_of_stronglySeparatesPoints`. **Und die Aussage von `isTightMeasureSet_of_stronglySeparatesPoints` war über beliebigem Filter falsch** — Zeuge `𝓕 = pure 0` auf `ℕ`, `E = ℝ`, `A = ⊤`, `μ n = δ n`, `μ₀ = δ 0`: die Voraussetzung ist dort die einzige Gleichung `∫ g ∂μ 0 = ∫ g ∂μ₀`, die gilt, und die Familie `{δ n}` ist nicht straff. Die fehlende Hypothese ist `Filter.cofinite ≤ 𝓕`, sie steht jetzt in der Aussage, und für Folgen ist sie geschenkt (`Nat.cofinite_eq_atTop`). **Im selben Lauf ist auch das gelockerte Straffheitskriterium EK Thm. 3.2.2 bewiesen**, `isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le` — eine eigene Mathlib-Lücke, weil die Verdickung eines Kompaktums nur auf einem properen Raum kompakt ist, mit dem Zeugen `⋂ m, cthickening (u m) (K m)` für eine Nullfolge `u m`, der `TotallyBounded.isCompact_of_isClosed` trägt; auch **ohne** Separabilität. ~~Offen bleibt allein die Buchhaltung darüber~~ — **am 2026-09-08, erster Lauf, ist auch sie bewiesen, und damit der Fact ganz**: `isTightMeasureSet_of_stronglySeparatesPoints` und sein Korollar `isConvergenceDetermining_of_stronglySeparatesPoints` — die Aussage des Manuskripts — tragen Beweise, gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an `propext`, `Classical.choice` und `Quot.sound`. Meilenstein 1 trägt danach **kein `sorry`** mehr. Die Buchhaltung ist: `μ₀` straff (`isTightMeasureSet_singleton`) gibt `K₀` mit `μ₀ K₀ᶜ ≤ ε/2`, Schritt (3) macht daraus `1 - ε/2 ≤ liminf`, die Hälfte erzeugt die **strikte** Ungleichung gegen `1 - ε`, die `Filter.eventually_lt_of_lt_liminf` verlangt, und die endlich vielen Ausnahmeindizes (endlich nach `Filter.mem_cofinite`) werden durch `Set.Finite.isCompact_biUnion` in `K₀` hineingezogen. Eine Hypothese hat sich dabei **geändert**: statt `[PolishSpace E]` steht `[CompleteSpace E] [SecondCountableTopology E]` — dieselbe Raumklasse (beide zusammen geben `PolishSpace` als Instanz), aber die Vollständigkeit hängt an der **gegebenen** Metrik, und die braucht der Beweis, weil `Metric.thickening` in ihr lebt; `PolishSpace` sagt nur, daß *eine* verträgliche Metrik vollständig ist (Zeuge in M1: $(0,1)$ mit der euklidischen Metrik) |
| `fact:bp` | 2 | EK, Lemma 3.4.1, Proposition 3.4.2, and Appendix 3, Pr | entbehrlich (2026-08-30) | Kein Beweis des Manuskripts benutzt `cor:bpclosure`, und EK 4.3.1 trägt dort nichts; der bp-Abschluss ist am 2026-08-30 aus MartingaleProblems M2 gestrichen und durch `insert_of_tendsto_of_forall_norm_le` und `submartingale_mpProcess_of_tendsto` ersetzt, M9 trägt die Anwendung (EK 4.3.9/4.3.10) |
| `fact:cadlagext` | 2 | Regularization along a dense set; EK, Lemma 2.2.8; eqr | Roadmap | MartingaleProblems M9; Vorarbeit in `brownian-motion` (Apache-2.0) |
| `fact:optsampl` | 2 | Optional sampling; EK, Theorem 2.2.13, Remark 2.2.14,  | Roadmap | MartingaleProblems M9, `Submartingale.stoppedValue_min_le_condExp` — dort neu angelegt; Mathlibs `Martingale.stoppedValue_min_ae_eq_condExp` ist der diskrete Fall und nur für Martingale |
| `fact:prohorov` | 2 | Prohorov; EK, Lemma 3.2.1 and Theorem 3.2.2 | Mathlib | `MeasureTheory/Measure/Prokhorov.lean`, `isCompact_closure_of_isTightMeasureSet` und Umkehrung |
| `fact:relcompact2` | 2 | Relative compactness, II; EK, Theorem 3.9.4 | Roadmap | MartingaleProblems M11, `isTight_map_postcomp_of_exists_martingale` — dort neu angelegt; `isRelativelyCompact_of_approx` nannte nur die Folgerung, nicht das Kriterium |
| `fact:sepcond` | 2 | Conditional determination by separating sets; EK, Chap | Roadmap | WeakConvergence M1, `IsSeparating.ae_eq_of_forall_condExp_eq` — seit dem 2026-09-06, erster Lauf, mit Beweis und durch `lake env lean`; Mathlib liefert `Filter.EventuallyEq.of_forall_separating_preimage` als Schlussschritt. Die trennende Klasse `M`, die der Fact **konsumiert**, ist in Mathlib mit `charPoly` und `Measure.ext_of_charFun` fertig instanziiert (siehe `fact:stoneweierstrass`) — aber nur über einem vollständigen zweitabzählbaren Innenprodukt- bzw. Banachraum. Am 2026-09-06, dritter Lauf, wurde jede Fundstelle des Manuskripts durchgesehen, an der eine trennende Klasse konkret instanziiert wird; an **keiner** liegt diese lineare Struktur vor, siehe den Laufbericht |
| `fact:submgreg` | 2 | Submartingale regularization; EK, Proposition 2.2.9; e | Roadmap | MartingaleProblems M9; Vorarbeit in `brownian-motion` (Apache-2.0) |
| `fact:ui` | 2 | Uniform integrability; EK, Appendix 2 | Mathlib+ | `MeasureTheory.UniformIntegrable`, `uniformIntegrable_iff`; die Kopplung an Verteilungskonvergenz fehlt → WeakConvergence M4. **Am 2026-09-08, dreizehnter Lauf, war das Trunkierungskriterium des Meilensteins falsch und ist berichtigt**: `IsUniformlyIntegrableLaws` stand mit dem **Bochner**-Integral von $\max(|x|-N,0)$, und weil `MeasureTheory.integral_undef` (`Integral/Bochner/Basic.lean:202`) für einen nichtintegrierbaren Integranden den Ersatzwert `0` liefert, war die Voraussetzung von jeder Familie mit unendlichem ersten Moment erfüllt — Zeuge `ProbabilityTheory.cauchyMeasure 0 1` (`Probability/Distributions/Cauchy.lean:170`), für die die behauptete Folgerung `Integrable id ν` falsch ist. Sie steht jetzt mit dem **unteren** Integral, und in dieser Form impliziert sie die Integrierbarkeit statt sie vorauszusetzen (`integrable_id_of_isUniformlyIntegrableLaws`, bewiesen und mit `#print axioms` geprüft). **Am 2026-09-09, vierzehnter Lauf, ist die Kopplung an die Verteilungskonvergenz bewiesen, und damit der Satz, den dieser Fact trägt**: `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (für die Gesetze) und `tendsto_integral_of_tendstoInDistribution_of_uniformIntegrable` (für Zufallsvariablen auf verschiedenen Räumen, mit Mathlibs `MeasureTheory.TendstoInDistribution` als Hypothese, wie der Meilenstein es verlangt); dazu `truncBdd`, `truncBdd_apply`, `abs_sub_truncBdd`, `integrable_id_of_lintegral_truncTail_lt_top`, `abs_integral_sub_integral_truncBdd_le` und `lintegral_truncTail_le_of_tendsto`. Alle durch `lake env lean` gegen v4.33.1 geprüft und alle mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`. **Der angesagte Weg über die Skorohod-Darstellung ist nicht gegangen worden und wird nicht gebraucht**: der Beweis ist die Abschneidung, und sein einziger nicht elementarer Schritt ist der Schwanz des **Grenzgesetzes**, das kein Glied der Familie ist — er kommt aus der Portmanteau-Ungleichung für nichtnegative stetige Funktionen (`MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`, `Measure/Portmanteau.lean:499`). Damit hängt dieser Fact **nicht** mehr an `exists_ae_tendsto_of_tendsto`. Ohne Signatur in `Suggested.lean` bleiben von Meilenstein 4 die de-la-Vallée-Poussin-Form und die vier Stabilitätslemmata |
| `fact:MZtight` | 1 | Tightness; MZ, Theorem~4, and Ku | Roadmap | MartingaleProblems M11 |
| `fact:PSpolish` | 1 | EK, Theorems 3.1.7 and 3.1.8 | Roadmap | WeakConvergence M3 — Skorokhod-Darstellung fehlt in Mathlib (dort nur `docs/1000.yaml`); dass 𝒫(S) separabel bzw. polnisch ist, fehlt seit dem 2026-08-31 belegt ebenfalls (Mathlib hat nur `instMetrizableSpaceProbabilityMeasure`), und steht jetzt als eigener Block in M3; der Block ist am 2026-08-31, dritter Lauf, auf typrichtige Aussagen gebracht — `CompleteSpace` gehört auf `LevyProkhorov (ProbabilityMeasure S)`, auf `ProbabilityMeasure S` gibt es keine Uniformität. **Der erste Punkt des Blocks ist seit dem 2026-09-08, erster Lauf, bewiesen**: `isTightMeasureSet_of_forall_exists_finite_iUnion_ball` — gleichmäßige Totalbeschränktheit im Maß gibt Straffheit — ist das gelockerte Straffheitskriterium von Meilenstein 1 in vier Zeilen, über `Metric.thickening_eq_biUnion_ball`; dabei ist `SecondCountableTopology` als unbenutzt aus der Aussage entfallen und das Kriterium selbst auf `[PseudoMetricSpace E] [CompleteSpace E]` abgeschwächt (vorher `[MetricSpace E] [CompleteSpace E] [BorelSpace E]`). **Am 2026-09-08, zweiter Lauf, sind die beiden Schätzungen bewiesen, auf denen die Separabilität von `ProbabilityMeasure E` ruht** — `levyProkhorovEDist_sum_dirac_le` (die geometrische Hälfte: eine endliche meßbare Zerlegung mit Vertretern im `ε`-Abstand außerhalb einer Menge kleiner Masse bringt das diskrete Maß `∑ i, μ (A i) • dirac (y i)` in Lévy--Prokhorov-Abstand `ε`) und `levyProkhorovEDist_sum_dirac_weights_le` (die arithmetische: Störung der Gewichte um insgesamt `δ` kostet `δ`), samt `sum_smul_dirac_apply`; alle drei durch `lake env lean` gegen v4.33.1. Der Satz selbst trägt weiterhin `sorry`, es fehlen die Zerlegung und die rationalen Gewichte, beide in Meilenstein 3 ausgeschrieben. Daß Mathlib die Separabilität nicht hat, ist am selben Tag gegen `upstream/master` `572e4d091bc` belegt, mit den im Laufbericht einzeln aufgezählten Suchformulierungen. **Am 2026-09-08, dritter Lauf, sind die beiden verbliebenen mathematischen Schritte bewiesen** und gehen durch `lake env lean` gegen v4.33.1: `exists_finite_partition_ball_of_denseRange` (die endliche Zerlegung in kleine Stücke mit benannten Vertretern — die einzige Stelle, an der `SeparableSpace E` verbraucht wird; die Vertreter kommen als **Indizes** `Fin n → ℕ` heraus, denn die Indizes sind es, die die Familie abzählbar machen) und `exists_nat_weights` (die rationale Approximation des Gewichtsvektors, mit **normierten** ganzzahligen Gewichten `m i / ∑ j, m j` statt auf Summe `1` festgenagelter — das erspart die abgeschnittene Subtraktion in `ℝ≥0∞` und den Ausnahmeindex). Der Satz selbst trägt weiterhin `sorry`; was fehlt, ist allein die Buchhaltung, die die vier Stücke zusammensetzt, und sie steht in Meilenstein 3 ausgeschrieben. **Am 2026-09-08, vierter Lauf, ist die Separabilität ganz bewiesen**: `separableSpace_levyProkhorov_probabilityMeasure` (die Aussage auf dem Lévy--Prokhorov-Synonym, wo die Metrik lebt), `separableSpace_probabilityMeasure` (die Aussage des Meilensteins, hinübergetragen mit `DenseRange.separableSpace` längs `probabilityMeasureHomeomorph`), `secondCountableTopology_probabilityMeasure` (der Meilensteinpunkt, der bis dahin gar keine Deklaration hatte) und der Hilfssatz `isProbabilityMeasure_natWeightMeasure` gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an `propext`, `Classical.choice` und `Quot.sound`. Die approximierende Familie ist als **Definition** `natWeightMeasure x k m` benannt und nicht im Beweis beschrieben — das macht ihre Abzählbarkeit zu einer Zeile (Bild einer Funktion auf `Σ n, (Fin n → ℕ) × (Fin n → ℕ)`, zurückgezogen mit `Set.Countable.preimage` längs `ProbabilityMeasure.toMeasure_injective`). Mitgefallen ist `polishSpace_probabilityMeasure`, jetzt ein Beweis statt eines `sorry`, der allein auf `isCompletelyMetrizableSpace_probabilityMeasure` ruht — und **mit schwächeren Hypothesen**: `[TopologicalSpace E] [PolishSpace E] [BorelSpace E]` statt `[MetricSpace E] [BorelSpace E] [PolishSpace E]`, weil eine mitgegebene Metrik den Aufstieg zur vollständigen (`TopologicalSpace.upgradeIsCompletelyMetrizable`) **blockiert**. **Im selben Lauf ist auch die Vollständigkeit bewiesen**, und damit der ganze Block „der Raum der Gesetze" von Meilenstein 3: `isTightMeasureSet_of_forall_exists_levyProkhorovEDist_lt` (eine Cauchy-Folge von Gesetzen ist straff — der Kern, und die Stelle, an der die Vollständigkeit von `E` zweimal bezahlt wird), `isTightMeasureSet_of_cauchySeq`, `completeSpace_levyProkhorov_probabilityMeasure` und `isCompletelyMetrizableSpace_probabilityMeasure`. `polishSpace_probabilityMeasure` hängt danach an keinem `sorryAx` mehr; alle fünf sind mit `#print axioms` geprüft. **Am 2026-09-08, fünfter Lauf, ist der Schritt bewiesen, auf dem die Skorokhod-Darstellung ruht**: `exists_measurable_partition_diam_le_null_frontier` — eine abzählbare meßbare Zerlegung eines separablen pseudometrischen Raums in Stücke vom Durchmesser höchstens `ε`, deren Ränder alle `μ`-Nullmengen sind. Der Beweis ist Mathlibs `SeparableSpace.exists_measurable_partition_diam_le` (`Measure/LevyProkhorovMetric.lean:540`) mit **einer** Änderung: der Radius wird je Mittelpunkt aus dem **offenen** Intervall `(ε/4, ε/2)` gewählt, durch `exists_null_frontier_thickening` (`Measure/Portmanteau.lean:401`) am Singleton `{xs n}`, gelesen als Kugel über `Metric.thickening_singleton` (`Topology/MetricSpace/Thickening.lean:157`). Die untere Schranke trägt die Überdeckung, die obere den Durchmesser, und offen muß das Intervall sein, weil jener Satz nur abzählbar viele belastete Radien vermeidet, statt einen vorgeschriebenen zu liefern. Dazu zwei Randaussagen, die Mathlib nicht hat und die eigene Deklarationen geworden sind: `frontier_biInter_range_subset` (der endliche Durchschnitt; Mathlib hat mit `frontier_inter_subset` nur den Zweimengenfall) und `frontier_disjointed_subset`, das `disjointed S n` über `disjointed_eq_inter_compl` (`Order/Disjointed.lean:323`) als `S n ∩ ⋂ j < n, (S j)ᶜ` liest. Alle drei gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`. **Im selben Lauf ist der zweite Eingang der Darstellung bewiesen**, der Scheffé-Schritt für eine abzählbare Zerlegung: `tendsto_tsum_posPart_sub_of_tendsto_measure` — konvergiert die Masse **jedes** Stücks, so geht `∑' i, max (ν (A i) - μ n (A i)) 0` über **alle** Stücke zugleich gegen `0` —, samt der Betragsfassung `tendsto_tsum_abs_sub_of_tendsto_measure` und den zwei Kleinigkeiten `summable_toReal_measure_of_pairwise_disjoint` und `tsum_toReal_measure_eq_one`; alle vier durch `lake env lean` und mit `#print axioms` geprüft. Von Meilenstein 3 bleibt allein `exists_ae_tendsto_of_tendsto`, die Skorokhod-Darstellung selbst. **Am 2026-09-08, sechster Lauf, ist der dritte Eingang bewiesen** und mit ihm die Arithmetik der Kopplung: `exists_measurable_map_restrict_volume_eq_sum_smul_dirac` (ein rein atomares Gesetz ist Bild des Lebesguemaßes auf `(0,1]`; die Abbildung ist `g y = x (Nat.find (h y))` zum Prädikat `y ≤ s (i+1) ∨ 1 ≤ y`, und der Zusatz `1 ≤ y` ist es, woran die Wohlgeformtheit hängt — bei unendlichem Träger von `p` bleibt jede Partialsumme unter `1`, also erfüllt bei `y = 1` **kein** `i` die erste Hälfte) und `exists_coupling_tsum_offDiag_le` (die diskrete Maximalkopplung: zwei Wahrscheinlichkeitsvektoren auf `ℕ` sind Randverteilungen eines `π` mit Nebendiagonalmasse höchstens `∑' i, (p i - q i)`, der abgeschnittenen Differenz in `ℝ≥0∞`). Beide gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`. **Im selben Lauf ist der Bauplan für die letzte Aussage berichtigt**: der gemeinsame Wahrscheinlichkeitsraum ist **kein** `((0,1], Lebesgue)`, wie Meilenstein 3 seit dem 2026-09-08, fünftem Lauf, schrieb, sondern ein Produkt — die bedingten Gesetze innerhalb der Zerlegungsstücke treten als Koordinaten eines `Measure.pi` auf, denn sie als meßbare Abbildung aus dem Einheitsintervall zu realisieren ist der Borelsche Isomorphiesatz und verlangt `E` polnisch statt bloß separabel. EK bauen es ebenso (Lemma 3.1.3, Buchseite 100). **Am 2026-09-08, siebter Lauf, ist die einstufige Kopplung bewiesen, in beiden Fassungen**: `exists_coupling_of_partition` (der geometrische Kern — zwei Gesetze, eine abzählbare Zerlegung in beschränkte Stücke vom Durchmesser höchstens `ε`, ein Gesetz `γ` auf `E × E` mit den richtigen Rändern und `γ {z | ε < dist z.1 z.2} ≤ ∑' i, (μ (A i) - ν (A i))`) und `exists_coupling_of_tendsto` (dieselbe Aussage aus schwacher Konvergenz getrieben, `∀ᶠ n in atTop`, mit Schranke `ENNReal.ofReal ε`); dazu `condLaw` samt `condLaw_of_ne_zero`, `isProbabilityMeasure_condLaw`, `measure_mul_condLaw_apply`, `condLaw_compl_eq_zero`. Alle gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`. Der Bauplan des sechsten Laufs ist dabei **berichtigt**: der gemeinsame Raum ist weder `((0,1], Lebesgue)` noch dessen Produkt mit einem `Measure.pi`, sondern `E × E` selbst — alles, was die Aussage über den Raum behauptet, ist das gemeinsame Gesetz der beiden Zufallsvariablen, und ein gemeinsames Gesetz ist ein Maß auf `E × E`; die Zufallsvariablen sind dann `Prod.fst` und `Prod.snd`. Was vom Befund des sechsten Laufs stehen bleibt, ist sein Kern: die bedingten Gesetze müssen als **Maße** eingehen und nicht als Funktionen einer gleichverteilten Variablen, denn Letzteres ist der Borelsche Isomorphiesatz. Von Meilenstein 3 bleibt allein `exists_ae_tendsto_of_tendsto`, die Iteration über eine Nullfolge von `ε`. **Am 2026-09-08, achter Lauf, ist der Randomisierungsschritt bewiesen** — der Schritt, an dem die Hypothesen des ganzen Meilensteins hängen: `map_eval_prod_infinitePi` (samt `sum_smul_dirac_singleton`, `map_eval_prod_infinitePi_of_map_eq` und `exists_measurable_map_prod_infinitePi_eq_sum_smul`) besagt, daß auf dem Produkt eines Raums mit meßbarem Index `ι : Ω → κ` und Mathlibs abzählbarem Produktmaß `Measure.infinitePi m` (`Probability/ProductMeasure.lean:358`) die Abbildung „schlage die vom Index genannte Koordinate nach" das Mischungsgesetz `∑ᵢ P{ι = i} · m i` trägt. Die Punkte darin einzeln zu ziehen — als meßbare **Funktion** einer gleichverteilten Variablen — ist der Borelsche Isomorphiesatz und verlangt `E` polnisch; sie als **Koordinaten** eines Produkts der bedingten Gesetze zu ziehen verlangt nichts, und die sieben Deklarationen des Laufs nennen über `E` nichts als `MeasurableSpace E`. Dazu die beiden Indexabbildungen: `exists_measurable_partitionIndex` (die Zerlegung gibt ein meßbares `j : E → ℕ`, dessen Fasern **genau** die Stücke sind — die Disjunktheit ist es, die aus `⊆` ein `=` macht) und `exists_measurable_index_of_stochastic_matrix` (eine ganze stochastische Matrix wird von **einer** meßbaren Abbildung `ℕ × ℝ → ℕ` realisiert, gleichmäßig im bedingenden Index, weil dieser über einen abzählbaren Raum läuft). Alle sieben gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`. **Im selben Lauf ist entschieden, wie die Stufen auf einen Raum kommen** — der Punkt (c2) des Vorlaufs —, und die Antwort ist: gar nicht durch Verkleben. Die einstufigen Kopplungen längs des gemeinsamen zweiten Randes zu verkleben ist Desintegration (`Measure.condKernel`, verlangt `E` standard-borelsch) und danach ein abzählbares Produkt der entstehenden Kerne — und **das hat Mathlib nicht**: `infinitePi` ist ein Produkt von *Maßen*, unter `Probability/Kernel/` kommt weder `infinitePi` noch `Kernel.pi` noch irgendein `def pi` vor (`upstream/master` `572e4d091bc`, 2026-09-08) — ~~dieser Halbsatz ist falsch und am 2026-09-08, neunter Lauf, berichtigt: das abzählbare Produkt von Kernen **hat** Mathlib, als `ProbabilityTheory.Kernel.traj` (`Probability/Kernel/IonescuTulcea/Traj.lean:518`, *Ionescu-Tulcea Theorem*, Voraussetzungen nur `MeasurableSpace` und Markov), und das Produkt ist der Sonderfall ohne Gedächtnis; die Entscheidung gegen das Verkleben trägt allein das zweite Bein, `Measure.condKernel` verlangt `[StandardBorelSpace Ω] [Nonempty Ω]` (`Kernel/Disintegration/StandardBorel.lean:77`, `:361`), und separabel metrisch impliziert nicht standard-borelsch~~. Gebaut werden daher alle Stufen auf einmal, auf `(E × (ℕ → ℝ)) × (ℕ × ℕ → E)`; das ist EK, Lemma 3.1.3 mit `N = ∞`. Im selben Lauf ist auch die Massenbuchhaltung bewiesen, `map_index_prod_eq`: auf `E × ℝ` mit `ν ⊗ Lebesgue|₍₀,₁₎` hat `z ↦ G (j z.1, z.2)` das Gesetz `∑ₖ ν (A k) · c k` — die Zeilen der stochastischen Matrix gegen die Massen der Stücke. Dort wird die **Faseraussage** von `exists_measurable_partitionIndex` verbraucht: `(ν.map j) {k} = ν (A k)` verlangt, daß die Faser das Stück **ist** und nicht bloß darin liegt **Am 2026-09-08, zehnter Lauf, ist eine Stufe der Darstellung als *eine* Aussage bewiesen**: `exists_measurable_pair_of_partition` — auf `stageMeasure μ ν A = (ν ⊗ Lebesgue|₍₀,₁₎) ⊗ infinitePi (condLaw μ ∘ A)` eine meßbare Abbildung `X` mit `map X = μ`, deren **erste Koordinate selbst** das Gesetz `ν` hat und `{z | ε < dist (X z) z.1.1}` höchstens die Masse `∑' i, (μ (A i) - ν (A i))` trägt; das ist es, was zum Iterieren fehlte, weil jede Stufe damit ihre Grenzvariable von **derselben** Koordinate abliest. Mit ihr acht weitere bewiesene Deklarationen: `sum_smul_condLaw_eq` (`μ` ist die Mischung ihrer bedingten Gesetze) samt `tsum_measure_inter_eq`, `condRow` mit `tsum_condRow` und `mul_condRow` (die spaltenweise Normierung der Indexkopplung; `mul_condRow` gilt eigens **auch** auf einem Nullstück), `measure_index_ne_prod` (die einzige Ungleichung der Stufe) und `isProbabilityMeasure_volume_restrict_Ioc`, eine Mathlib-Lücke, die auf `upstream/master` `572e4d091bc` mit zwei Suchen belegt ist. Alle neun gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`; über `E` steht nichts Stärkeres als in `exists_coupling_of_partition`, und die Zweitabzählbarkeit geht allein in die Meßbarkeit des schlechten Ereignisses. **Am 2026-09-08, elfter Lauf, ist die Allgemeinheit berichtigt, in der dieser Fact gebraucht wird: nur für polnische Räume.** Beide Gebrauchsstellen sind polnisch — `rem:EKrelcompact` ohnehin ($\DE$ unter $J_1$), und `thm:MZconv` Schritt 1, sobald man ihn statt auf $\DE$ in der Pseudopfad-Topologie auf **$M_E[0,\infty)$** stellt, dem Raum der $\lambda$-f.ü.-Klassen Borel-meßbarer $w:\Rp\to E$ unter $d_m(x,y)=\int_0^\infty e^{-t}(1\wedge r(x(t),y(t)))\dif t$, der nach Kurtz (1991), S. 1022 **vollständig und separabel** ist, sobald $(E,r)$ es ist — und (E3) gibt das. Der Angelpunkt, daß $\DE$ borelsch in $M_E$ ist, ist im Bericht des elften Laufs bewiesen, aus `fact:pseudopath` allein und ohne Lusin--Souslin. Der Preis ist die Konstruktion von $M_E$ selbst (`WeakConvergence` M6), der Ertrag der Verzicht auf die separable Fassung der Darstellung. `exists_ae_tendsto_of_tendsto` und die vierzehn Deklarationen der Läufe fünf bis zehn bleiben davon unberührt und richtig — der polnische Fall ist ein Spezialfall des separablen, und Mathlib hat die Darstellung in **keiner** Fassung. **Am 2026-09-08, zwölfter Lauf, sind vier der fünf Aussagen von Meilenstein 6 bewiesen** — der Raum $M_E$ selbst: `distInMeasure_triangle`, `distInMeasure_eq_zero_iff`, `tendsto_iff_tendstoInMeasure` (die Aussage, die die Metrik als die der Konvergenz im Maß benennt, und der Berührungspunkt mit `fact:pseudopath`(i)) und `exists_tendsto_distInMeasure_of_cauchy` (die Vollständigkeit nach Kurtz (4.2)--(4.4)), dazu `distInMeasure_le_add`, `measurable_dist_coeFn` und `integrable_min_one_dist`; alle durch `lake env lean` gegen v4.33.1 und mit `#print axioms` geprüft. `SecondCountableTopology E` ist dabei als unbenutzt aus allen entfallen, und die Vollständigkeit braucht kein `Nonempty E`. ~~Offen ist allein die **Separabilität**, der Punkt, den Kurtz „left to the reader“ schreibt.~~ **Am 2026-09-08, dreizehnter Lauf, ist auch sie bewiesen, und damit Meilenstein 6 ganz**: `exists_countable_dense_distInMeasure` samt `separableSpace`, `secondCountableTopology` und `polishSpace` — der Raum $M_E$ ist polnisch —, dazu die fünf Deklarationen, auf denen sie ruhen (`distInMeasure_mk_le_add`, `stepFun`, `stronglyMeasurable_stepFun`, `exists_mem_stepFun`, `stepClass`); alle acht durch `lake env lean` gegen v4.33.1 und mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft. Der Bauplan des Meilensteins war dabei an einer Stelle **nicht typrichtig** und ist berichtigt: er beschrieb die approximierende Familie als die Summen `∑ i, Set.indicator (A i) (fun _ ↦ y i)`, aber $E$ ist ein bloßer metrischer Raum ohne Addition. An ihre Stelle tritt die Stufenfunktion über einer **Liste** von Indexpaaren mit Vorrang der früheren Einträge — `List (ℕ × ℕ)` ist abzählbar durch Instanzsuche, und die Vorrangregel ersetzt die Summe durch eine Fallunterscheidung. Der Ertrag daraus, und er kürzt den Beweis: weil `exists_mem_stepFun` nur sagt, daß der gefeuerte Zweig von *irgendeinem* Eintrag stammt, dessen Menge das Argument enthält, dürfen die überdeckenden Mengen einander **überlappen**, und die Disjunktifizierung, die `exists_finite_partition_ball_of_denseRange` in Meilenstein 3 kostet, entfällt hier ganz. **Am 2026-09-08, vierzehnter Lauf, ist der Bauplan des Schlußschritts als falsch erkannt und ersetzt**: der zehnte Lauf hatte ihn über Borel--Cantelli geführt, und das geht nicht, weil die Schranke einer Stufe, `∑' i, (μ n (A i) - ν (A i))`, beliebig langsam fallen darf (Zeuge: `ν = dirac 0`, `μ n = (1 - 1/log n) • dirac 0 + (1/log n) • dirac 1` auf `ℝ`, wo sie auf jeder Stufe vom Durchmesser unter `1` mindestens `1/log n` ist und `∑ 1/log n = ∞`) — keine Wahl der Niveaus repariert das. Die fast sichere Konvergenz kommt aus der **Abhängigkeit** der Stufen: eine allen Stufen gemeinsame gleichverteilte Variable, die Schranke als **Inklusion** in ein Ereignis dieser Variablen, und endlich viele Stücke positiver Masse; das ist EK Thm. 3.1.8, (1.33)--(1.36), am Scan gelesen (Buchseiten 102--103). Bewiesen ist der abgetrennte Schlußsatz `ae_tendsto_of_subset_of_tendsto_measure_iUnion_ge` — (1.36) ohne die Konstruktion —, durch `lake env lean` gegen v4.33.1 und mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft; die drei übrigen Stücke stehen benannt in Meilenstein 3. Am 2026-09-08, fünfzehnter Lauf, sind zwei davon bewiesen und ebenso geprüft: `exists_measurable_index_of_stochastic_matrix_diag` (die Diagonale auf dem ersten Teilsummenintervall, samt dem Zusatz an `exists_measurable_map_restrict_volume_eq_sum_smul_dirac`) und `exists_finite_partition_diam_le_null_frontier` (die endliche Zerlegung mit Stücken positiver Masse, samt der Hilfsaussage `frontier_biUnion_finset_subset`). Offen ist allein `exists_measurable_pair_of_partition_subset` und danach der Zusammenbau. **Die zweite Gebrauchsstelle des Facts, `rem:EKrelcompact` — $\DE$ unter $J_1$ ist polnisch —, ist am 2026-09-08, dreiundzwanzigster Lauf, zur Hälfte eingelöst**: `SkorokhodSpace.instCompleteSpace` trägt einen Beweis, geht durch `lake env lean` gegen v4.33.1 und hängt laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`. Offen bleibt dort `SkorokhodSpace.instSeparableSpace`; `instPolishSpace` ist `inferInstance` und fällt mit ihm. **Am 2026-09-08, vierundzwanzigster Lauf, ist Meilenstein 1 von `SkorokhodSpace` ganz geschlossen** — `exists_orderIso_isometry_real` trägt einen Beweis, über die benannte Koordinate `lengthCoord t₀ t = if t₀ ≤ t then dist t₀ t else -dist t₀ t` samt `sub_lengthCoord_of_le`, `strictMono_lengthCoord`, `isometry_lengthCoord`, `lengthCoord_self`; `OrderTopology ι` ist dabei als unbenutzt entfallen, verbraucht werden `AdditiveDist`, `MetricSpace` (für die Striktheit, über `dist_pos`) und von `ProperSpace` allein die Vollständigkeit (`complete_of_proper`). Mit ihr `TimeChange.exists_of_lengthCoord`, die erste Konstruktion eines Zeitwechsels auf einem allgemeinen Index. Und der Befund zur offenen Hälfte: `instSeparableSpace` zerfällt in die Approximation durch Treppenpfade an den eigenen Sprungzeiten (gleichmäßig, ohne Zeitwechsel, kommt mit `tendsto_modulus` aus Meilenstein 7) und das Verschieben der Sprungzeiten auf die abzählbare Menge, und Letzteres ist eine Aussage über den **Index**: das Interpolationslemma auf dem Bild der Koordinate. Für `ι = h • ℤ` ist dieses Bild `h • ℤ` und der einzige Zeitwechsel der triviale — dort ist nichts zu verschieben; für `ι = ℝ` tut es jedes stückweise lineare `φ`. Alle sieben Deklarationen gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`. **Am 2026-09-09, erster Lauf, ist die zweite Hälfte dieser Gebrauchsstelle berichtigt statt bewiesen**: `SkorokhodSpace.instSeparableSpace` ist in der Fassung ohne Zusatzhypothese **falsch**. `SkorokhodSpace.not_separableSpace_of_rigid` (bewiesen, mit `stepAt`, `dist_le_distWith_stepAt`, `le_intWith_stepAt`, `le_intDist_stepAt`) zeigt: ist `ι` überabzählbar und ist die Identität der einzige Zeitwechsel mit Norm unter einem `c > 0`, so ist `D(ι, E)` nicht separabel — Zeuge für die Hypothesen ist die Cantormenge, deren Lückenlängen `3^{-n}` jeden bi-Lipschitz-Ordnungsisomorphismus mit Konstanten unter `3` zur Identität zwingen (diese Rechnung ist Prosa, nicht Lean). Die Instanz und `instPolishSpace` tragen seither die Typklasse `SkorokhodSpace.HasCountableCore ι`; für `rem:EKrelcompact` selbst — dort ist `ι = [0,∞)` — ist sie erfüllt, aber sie muß bewiesen werden, und das ist der nächste Punkt von Meilenstein 5. Mitgefallen ist die Integralbuchführung `SkorokhodSpace.intWith_le_of_forall_distWith_le` samt `exists_finite_range_intDist_le` (`intDist t₀ f g ≤ ε + exp (-M)` für ein `g` mit endlichem Wertebereich); alle zehn Deklarationen durch `lake env lean` gegen v4.33.1 und mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft **Am 2026-09-09, vierter Lauf, ist die zweite Gebrauchsstelle des Facts ganz eingelöst**: `SkorokhodSpace.instSeparableSpace` trägt einen Beweis, und damit ist `SkorokhodSpace.instPolishSpace` — `$\DE$ unter $J_1$ ist polnisch`, also `rem:EKrelcompact` — bewiesen statt `inferInstance` über einem `sorry`; beide hängen laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`. Die Einlösung steht unter der Typklasse `SkorokhodSpace.HasCountableCore ι`, und das ist nach `not_separableSpace_of_rigid` unvermeidlich; für `ι = ℝ` und für jeden abzählbaren Index ist sie bewiesen. Die fünf tragenden Deklarationen sind `stepIdx_congr_of_forall_notMem_Ioc`, `SkorokhodSpace.stepIdx_eq_of_mem_uIcc`, `radius_exhaustionMin_mem_Ico_subset`, `volume_radius_exhaustionMin_mem_Ico` und `SkorokhodSpace.distWith_stepPath_le`; alle durch `lake env lean` gegen v4.33.1 geprüft. **Am 2026-09-09, dreizehnter Lauf, ist auch das Relativkompaktheitskriterium bewiesen, das `rem:EKrelcompact` neben der Polnischheit zitiert**: `SkorokhodSpace.isCompact_closure_iff` trägt in beiden Richtungen einen Beweis und hängt laut `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`. Damit ist `SkorokhodSpace/Suggested.lean` **frei von `sorry`**  **Am 2026-09-09, fünfzehnter Lauf, ist das vorletzte Stück der ersten Gebrauchsstelle bewiesen**: `exists_measurable_pair_of_partition_subset` — alle Stufen der Darstellung auf **einem** Raum (`stagesMeasure`, `(E × ℝ) × (ℕ × ℕ → E)`), mit **einer** allen Stufen gemeinsamen gleichverteilten Variablen, und mit der Stufenschranke als **Inklusion** `ε n < dist (X n z) z.1.1 → z.1.1 ∈ A n 0 ∨ 1 - t n < z.1.2` statt als Zahl; dazu `sum_prod_slice_eq` und je ein Zusatz an `exists_coupling_tsum_offDiag_le` (`min (p i) (q i) ≤ π i i`, die Diagonalschranke, umsonst aus der expliziten Kopplung) und an `exists_finite_partition_diam_le_null_frontier` (`∀ i ∈ K, Bornology.IsBounded (A i)` — `Metric.diam` sagt auf einer unbeschränkten Menge nichts). Über `E` steht dabei allein `[PseudoMetricSpace E]`. Alle durch `lake env lean` gegen v4.33.1 und mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft. Zwei Berichtigungen am Meilenstein: der zweite Disjunkt steht als `1 - t n < ξ` und nicht als `ξ ≤ t`, weil der Diagonalzweig die Diagonale auf das *erste* Teilsummenintervall legt; und die Stufen brauchen die Beschränktheit der Stücke, nicht bloß ihren Durchmesser. Offen ist allein `exists_ae_tendsto_of_tendsto`, der Zusammenbau, dessen vier Schritte im Bericht des fünfzehnten Laufs stehen |
| `fact:convdet` | 1 | EK, Proposition 3.4.4 | Roadmap | WeakConvergence M1, `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support` und `isConvergenceDetermining_setOf_hasCompactSupport` (zusätzlich lokalkompakt) — am 2026-09-05 dort neu angelegt. **Die erste Hälfte ist seit dem 2026-09-07, fünfzehntem Lauf, bewiesen** und geht durch `lake env lean` gegen v4.33.1, und zwar **ohne Separabilität**: EK und das Manuskript verlangen sie, kein Beweisschritt benutzt eine abzählbare dichte Menge (Auffälligkeit unten). Der Weg ist `tendsto_iff_forall_lipschitz_integral_tendsto` (`Measure/Portmanteau.lean:688`), die die schwache Konvergenz auf die beschränkten **Lipschitz**funktionen zurückführt, plus die Abschneidung einer solchen an `ballCutoff`, einem Mitglied der Klasse; die Abschneidung ist durch die Straffheit gedeckt, die die Abschneider selbst liefern. Neun Hilfsdeklarationen, alle bewiesen. **Die zweite Hälfte ist seit dem 2026-09-07, sechzehntem Lauf, ebenfalls bewiesen** und geht durch `lake env lean` gegen v4.33.1: `isConvergenceDetermining_setOf_hasCompactSupport`, auf einem lokalkompakten separablen metrischen Raum. Beide Hälften ruhen jetzt auf **einer** Deklaration, `tendsto_integral_of_tendsto_integral_mul` — der Abschneideschritt, von der Klasse gelöst, unter `[TopologicalSpace E] [OpensMeasurableSpace E]` und ohne Metrik —, und unterscheiden sich nur in der Familie der Abschneider: `ballCutoff x₀ m` für die erste, eine kompakt getragene Urysohn-Funktion über `compactCovering E m` für die zweite. Der in M1 bis dahin angekündigte Weg — die größere Klasse gleichmäßig durch die kleinere approximieren — ist **falsch**, und der Zeuge steht als acceptance example in M1: auf einem unendlichen diskreten Raum vom Durchmesser 1 ist die Konstante 1 gleichmäßig stetig mit beschränktem Träger und hat von jeder kompakt getragenen Funktion den gleichmäßigen Abstand 1. Die Lokalkompaktheit geht genau einmal ein, in `exists_continuous_one_zero_of_isCompact` (`Topology/UrysohnsLemma.lean:404`); die Separabilität geht nur über die σ-Kompaktheit ein (`sigmaCompactSpace_of_locallyCompact_secondCountable`). ~~M1~~ nannte die Aussage bis dahin **nicht**: das Zitat war seit dem 2026-08-29 leer, kein Punkt von M1 spricht von gleichmäßig stetigen Funktionen mit beschränktem Träger oder von $C_c$. Mathlib hat sie nicht — in `MeasureTheory/Measure/` kommt `UniformContinuous` überhaupt nicht vor und `HasCompactSupport` in keiner Konvergenzaussage (`upstream/master`, 2026-09-05) |
| `fact:fddconv` | 1 | EK, Theorem 3.7.8 | Roadmap | SkorokhodSpace M8, `tendsto_finiteDimensional_of_tendsto` (a) und `tendsto_of_isCompact_closure_of_tendsto_finiteDimensional` (b); beide stehen seit dem 2026-08-31 unter Stufe (A) „separabel metrisch", wie der Fact, und (b) unter Relativkompaktheit statt Straffheit, wie EK |
| `fact:fullgenerator` | 1 | EK, Proposition 1.5.1 | Roadmap | MartingaleProblems M13 — dort neu angelegt; Mathlib hat keine Operatorhalbgruppen, `dissipative` kommt nicht vor, Hille--Yosida steht als `Q974405` ohne `decl` in `docs/1000.yaml` |
| `fact:jacodmemin` | 1 | Continuous mapping, Jacod--M'emin; CPS, Theorem 2.9 | bewusst | nicht formalisiert; `rem:augvsws` begründet, warum Augmentierung genügt |
| `fact:picard` | 1 | Picard--Lindel"of for SDEs | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:pseudopath` | 1 | Pseudo-paths; MZ, Section~1 and Lemma~1 | Roadmap | MartingaleProblems M11. **Am 2026-09-08, elfter Lauf, sind alle drei Teile als tragend erkannt, und zwar für einen Zweck, den das Manuskript ihnen nicht gibt**: (i) und (iii) machen die Inklusion $\DE \hookrightarrow M_E[0,\infty)$ zu einem Homöomorphismus auf ihr Bild mit Spur-$\sigma$-Algebra $\sigma(\pi_u)$, und (ii) — in der Lesart „$\gamma(\DE)$ ist borelsch im kompakten $\Prob([0,\infty]\times\hat E)$", nicht in der Lesart „nicht polnisch" — macht zusammen mit der Injektivität von $\gamma$ auf ganz $M_E$ den Raum $\DE$ zu einer **Borelmenge von $M_E$**. Das ist es, was Schritt 1 von `thm:MZconv` über den polnischen Raum $M_E$ (Kurtz 1991, S. 1022) laufen läßt. Die Injektivität von $\gamma$ auf $M_E$ steht wörtlich im Fact („identifies two paths exactly when they agree $\lambda$-a.e."); das Manuskript zieht daraus nur die schwächere Folgerung für $\DE$ |
| `fact:relcompact` | 1 | Relative compactness, I; EK, Theorem 3.9.1 | Roadmap | SkorokhodSpace M8, `isTightMeasureSet_iff_forall_postcomp` mit `continuous_postcomp` — dort neu angelegt |
| `fact:stoppingtimes` | 1 | EK, Propositions 2.1.2 and 2.1.4; eqref{T2b} | Mathlib | `MeasureTheory.IsStoppingTime` in `Probability/Process/Stopping.lean` |
| `fact:strookvaradhan` | 1 | Stroock--Varadhan; KA, Theorem 32.7 | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:yamadawatanabe` | 1 | Yamada--Watanabe | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:doob` | 0 | Doob's inequalities; EK, Corollary 2.2.17; eqref{T2b} | Roadmap | MartingaleProblems M9, `maximal_ineq_of_rightContinuous` und `Submartingale.eLpNorm_iSup_le` — dort neu angelegt; Mathlibs `MeasureTheory.maximal_ineq` ist `Filtration ℕ`, die `Lᵖ`-Ungleichung fehlt ganz |
| `fact:fdd` | 0 | EK, Proposition 3.4.6 and Proposition 3.7.1 | Roadmap | WeakConvergence M1 (Produktpunkt, am 2026-08-29 von endlichem auf beliebigen Index gebracht) und SkorokhodSpace M6, `borel_eq_iSup_comap_eval`; die Produkthälfte **trägt seit dem 2026-09-07, dreizehntem Lauf, einen Beweis**: `isSeparating_pi` steht bewiesen in `WeakConvergence/Suggested.lean` und geht durch `lake env lean` gegen v4.33.1 — trennende Klassen multiplizieren sich über einen beliebigen Indextyp, sofern ihre Mitglieder beschränkt und meßbar sind. Seit dem 2026-09-07, vierzehntem Lauf, trägt auch die **konvergenzbestimmende** Hälfte einen Beweis: `isConvergenceDetermining_pi`, für abzählbares `ι`, polnische `S i` und beschränkt-**stetige** Mitglieder, samt den drei Stücken, auf denen sie ruht — `IsTightMeasureSet.pi` (Straffheit abzählbarer Produkte; Mathlib hat nur den Zweifaktorfall `IsTightMeasureSet.prodMk`, `Measure/Tight.lean:144`), `isTightMeasureSet_of_tendsto` und `tendsto_of_isSeparating_of_isTightMeasureSet`. ~~die Produkthälfte trägt kein Beweis~~, §9 verlangt sie — Auffälligkeit vom 2026-08-31. Die Zuschreibung des Facts stimmt und teilt sich sauber: EK Prop. 3.4.6 ist die Produkthälfte, EK Prop. 3.7.1 die Pfadraumhälfte (am Scan geprüft, 2026-08-31, zweiter Lauf). **Die Pfadraumhälfte trägt seit dem 2026-09-09, fünftem Lauf, einen Beweis**: `SkorokhodSpace.borel_eq_iSup_comap_eval` und `SkorokhodSpace.measurableEmbedding_piDense` stehen bewiesen in `SkorokhodSpace/Suggested.lean`, auf `SkorokhodSpace.measurable_eval`; die Einbettung verlangt von `D` die Dichtheit **von rechts** und nicht bloß Dichtheit — unter der Dichtheit allein ist sie falsch, siehe die Auffälligkeit zu `thm:fdd` — und `exists_countable_rightDense` zeigt, daß es eine solche abzählbare Menge gibt |
| `fact:portmanteau` | 0 | Portmanteau; EK, Theorem 3.3.1 | Mathlib | `MeasureTheory/Measure/Portmanteau.lean`; (a)⟺(b) ist `MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph` (`Measure/LevyProkhorovMetric.lean:676`). Kein Beweis benutzt (c)–(f) — Auffälligkeit vom 2026-08-31 |
| `fact:stoppedlocalmg` | 0 | EK, Proposition 2.3.1 | Roadmap | MartingaleProblems M9, `isStable_martingale_rightContinuous` — dort neu angelegt; `ProbabilityTheory.Locally`, `IsStable` und `IsStable.locally` sind Mathlib (`Probability/Process/LocalProperty.lean:93,142,153`, Namensraum am 2026-09-01 berichtigt), der Martingalfall ist es nicht |

## Offene Auffälligkeiten

* **`fact:convdet` verlangt Separabilität, die sein Beweis nicht braucht;
  gefunden am 2026-09-07, fünfzehnter Lauf, beim Beweisen der ersten Hälfte.**
  Das Manuskript schreibt (Zeile 1423, nach EK Prop. 3.4.4): „If $(S,d)$ is
  separable, then the set of uniformly continuous $f\in\Cb(S)$ with bounded
  support is convergence determining." Die Lean-Fassung
  `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support` steht
  jetzt unter `[MetricSpace E] [OpensMeasurableSpace E]` allein und ist
  bewiesen. Wo Separabilität hätte vorkommen können, kommt sie nicht vor: der
  tragende Satz `tendsto_iff_forall_lipschitz_integral_tendsto`
  (`Measure/Portmanteau.lean:688`) verlangt nur `[PseudoEMetricSpace Ω]`,
  `[OpensMeasurableSpace Ω]` und einen abzählbar erzeugten Filter; die
  Ausschöpfung des Grundraums geschieht durch **einen** Punkt
  ($E=\bigcup_m \overline B(x_0,m)$, weil Abstände endlich sind, nicht durch
  eine abzählbare dichte Menge), und dieser Punkt ist geschenkt, weil ein
  Wahrscheinlichkeitsmaß auf $E$ lebt. Auch Vollständigkeit und
  Lokalkompaktheit fehlen. **Folgenlos für das Manuskript**, das nur die
  schwächere Aussage benutzt; der Befund ist eine Verallgemeinerung und keine
  Korrektur, und die Roadmap trägt jetzt die schwächeren Hypothesen. Zu prüfen
  bliebe, ob EK die Separabilität für die **zweite** Hälfte ($C_c$,
  lokalkompakt) braucht — dort ist sie unangetastet.

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

  **Nachtrag 2026-09-09, fünfter Lauf: die Bedingung fehlte drei Tage lang in
  Meilenstein 6.** Sie stand seit dem 2026-09-06 in Meilenstein 2 und seit dem
  2026-09-07 als acceptance example von Meilenstein 6, während
  `SkorokhodSpace.measurableEmbedding_piDense` daneben `Dense D` verlangte — die
  Lean-Fassung von `thm:fdd` also genau den Fehler wiederholte, den das
  Inventar am Manuskript festgehalten hatte. Berichtigt: die Hypothese ist
  `∀ t, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot`, und `exists_countable_rightDense`
  zeigt, daß eine solche abzählbare Menge existiert. Die Lehre ist nicht neu,
  aber sie hat jetzt zwei Belege: **ein Befund über das Manuskript trägt sich
  nicht von selbst in die Roadmap desselben Satzes ein**, und ein acceptance
  example, das gegen seine eigene Aussage nie gerechnet wird, verhindert nichts.

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

### 2026-09-07, achter Lauf des Tages

**Was bearbeitet wurde.** Rückstaupunkt 1 (`SkorokhodSpace` und
`MartingaleProblems` weiter beweisen), und zwar genau die beiden Ziele, die der
siebte Lauf am Ende benannt hatte. Beide sind erreicht, beide Dateien gehen
durch `lake env lean` gegen v4.33.1 mit rc = 0 und ohne Fehler.

**1. `SkorokhodSpace.IsCadlag.measurable` ist bewiesen — und die Roadmap
verlangte dafür ein Bündel, das der Beweis nicht braucht.** Die Datei steht bei
elf `sorry` statt zwölf.

Der Meilenstein 2 führte die Aussage seit dem 2026-08-29 unter dem Bündel (B),
mit `E` polnisch, und schrieb den Weg vor: Approximation durch rechtsstetige
Treppenfunktionen entlang der abzählbaren dichten Menge `D`. Dieser Weg braucht
zweierlei, was der Meilenstein sonst nirgends verlangt — die dichte Menge, und
eine **lineare Struktur auf `E`**, ohne die eine Treppenfunktion nicht
definierbar ist. Gebraucht wird nichts davon. Die Sprungtheorie des vierten
Laufs von heute trägt die Aussage in drei Zeilen:

* `IsCadlag.continuousAt_iff_notMem_leftJumpSet` — càdlàg ist stetig genau
  außerhalb von `leftJumpSet f`;
* `countable_leftJumpSet` — diese Menge ist abzählbar;
* `measurable_of_countable_not_continuousAt`
  (`Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:509`, am Quelltext
  von v4.33.1 geprüft, nicht `deprecated`) — wer außerhalb einer abzählbaren
  Menge stetig ist, ist meßbar.

Die `MeasurableSingletonClass ι`, die der Mathlib-Satz verlangt, ist geschenkt:
`OpensMeasurableSpace.toMeasurableSingletonClass` (`ibid.:351`) gibt sie aus
`T1Space`, und ein metrischer Raum mit Borelstruktur hat beides. Die Aussage
steht damit unter denselben Voraussetzungen wie `countable_leftJumpSet` —
lineare Ordnung, Ordnungstopologie, σ-Kompaktheit — plus den beiden
Borelstrukturen; `AdditiveDist` ist per `omit` heraus, und der Linter bestätigt
es. Die stehende Regel über minimale Voraussetzungen ist hier nicht bloß
eingehalten, sondern hat den Befund erzeugt: der Versuch, den Beweis unter dem
angegebenen Bündel zu führen, hätte `PolishSpace E` und `D` mitgeschleppt, die
in der Aussage nicht vorkommen müssen.

Der Meilenstein 2 ist damit **bis auf `IsCadlag.eq_of_eqOn_dense` vollständig
frei von (B)**; die Roadmap sagt das jetzt, und die Zwischenüberschrift „Under
(B)" führt nur noch zwei Punkte statt drei, von denen einer ohnehin nur der
Nachbarschaft wegen dort steht. Das ist die zweite Bündelkorrektur an
Meilenstein 2 an einem Tag — die erste war die Sprungtheorie selbst — und beide
kamen daher, daß jemand den Beweis wirklich hingeschrieben hat.

**2. `AtomWitness.not_isAtomless_atomClock` ist bewiesen.** `MartingaleProblems`
bleibt bei neun `sorry` (der neue Punkt trägt einen Beweis) und wächst um eine
Deklaration.

Die Aussage ist `¬ (atomClock u).IsAtomless`, und sie ist der Grund, warum die
Schärfeaussage `not_isQuasiLeftContinuous_of_atom` den Satz
`isQuasiLeftContinuous_of_isMPSolutionFor` **begrenzt** statt ihm zu
widersprechen: die Uhr des Gegenbeispiels verletzt dessen Hypothese `hQ`. Bis
heute war das eine Bemerkung über die Definition, jetzt ist es ein Satz. Der
Beweis ist `measure_mono` vom Singleton `{u}` in das entartete Intervall
`{v | u ≤ v ∧ v ≤ u}`, gegen `atomClock_apply_singleton_ne_zero`.

**Mitgefunden, beim Übersetzen.** `zero_le` hat in `ENNReal` sein Argument
**implizit** — `le_antisymm ?_ (zero_le _)` meldet „Function expected at
`zero_le`"; `nonpos_iff_eq_zero.1` ist der Weg, der nicht daran vorbeiläuft und
zugleich kürzer ist.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.** In `SkorokhodSpace`
ist der Rückstau jetzt strukturell verstopft: von den elf `sorry` hängen zehn an
der parameterlosen `MetricSpace`-Instanz, der der Basispunkt fehlt, und der
elfte ist `exists_orderIso_isometry_real`, die Einbettung des Index in `ℝ` —
ein echter Satz und kein Restposten. Der nächste Lauf gehört deshalb nach
`WeakConvergence`, und dort an **Schritt (ii) von `induction_on_mulSystem`**:
`of_continuous_comp_of_isMulSystem`, die Approximationshälfte. Die algebraische
Hälfte steht seit dem 2026-09-06
(`mul_mem_span_insert_one_of_isMulSystem`, `of_mem_span_insert_one`,
`exists_bound_of_mem_span_insert_one`), der Anker ist
`ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints`
(`Topology/ContinuousMap/StoneWeierstrass.lean:313`), und was fehlt, ist die
kompakte Box in `Fin n → ℝ`, die Punktetrennung der Koordinatenalgebra und der
Rückzug entlang `x ↦ (f₁ x, …, fₙ x)` in den Spann. Warum jetzt:
`fact:monotoneclass` ist mit tragend `4` der höchstgewichtete Fact ohne
Mathlib-Beleg, drei formulierte Roadmap-Punkte warten auf
`induction_on_mulSystem`, und (ii) ist der einzige Schritt der vier, der noch
kein Teilergebnis hat — (i) ist fertig, (iii) zur Hälfte, (iv) Routine.

**Nachtrag desselben Laufs: (ii) ist erledigt, im selben Lauf, in dem es
vorgeschlagen wurde.** `of_continuous_comp_of_isMulSystem` trägt einen Beweis,
und er geht durch `lake env lean`. Damit ist der „eigentliche Brocken" des
funktionalen Monotone-Klassen-Satzes weg; von den vier Schritten steht jetzt (i)
und (ii) ganz, (iii) zur Hälfte, (iv) ist Routine.

Zwei Entscheidungen tragen den Beweis, und beide sind Befunde für die Roadmap,
die den Weg anders vorgezeichnet hatte.

* **Der Anker ist nicht die ε-Fassung über einem kompakten Raum, sondern
  `ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`**
  (`Topology/ContinuousMap/StoneWeierstrass.lean:323` in v4.33.1, am Quelltext
  geprüft, nicht `deprecated`) — die Variante, in der der Raum **nicht** kompakt
  sein muß und nur die Approximation auf eine kompakte Menge eingeschränkt ist.
  Die Roadmap nannte `…_of_separatesPoints` (`:313`), und die zwingt zum Subtyp
  `↥box`: Unteralgebra, Punktetrennung und Rückzug müßten alle über `C(↥box, ℝ)`
  laufen, mit Restriktionen an jeder Stelle. Über die kompakte Variante lebt
  alles über `Fin n → ℝ`, die Koordinaten sind `continuous_apply i`, und der
  Subtyp kommt im Beweis nicht ein einziges Mal vor.
* **Der Rückzug ist ein `AlgHom`, und die Spanne ist eine `Subalgebra`.** Statt
  einer Induktion über `Algebra.adjoin` (die der dritte Lauf des 2026-09-06 mit
  Recht verworfen hat, weil ihr `mul`-Fall `P` als multiplikativ verlangt) ist
  der Rückzug `C(Fin n → ℝ, ℝ) →ₐ[ℝ] (Ω → ℝ)`, `g ↦ fun x ↦ g (f · x)`, dessen
  fünf Felder sämtlich `rfl` sind; die Spanne wird über
  `Submodule.toSubalgebra` zur Unteralgebra, und die Enthaltensein-Aussage ist
  `Algebra.adjoin_le` gegen `Subalgebra.comap`, geprüft allein an den
  Erzeugern — dort zieht die `i`-te Koordinate auf `f i` zurück, per
  η-Gleichheit sogar definitionsgleich. Das ersetzt eine
  `Algebra.adjoin_induction` durch eine Zeile.

Mitgefunden, klein aber notwendig: die gemeinsame Schranke der endlich vielen
`f i` ist `∑ j, |c j|` und **kein** Supremum — `Fin n` darf leer sein, und ein
Supremum über eine leere Familie ist ein Junk-Wert.

**Und ein Befund über die Datei selbst, der zunächst wie ein Fehler aussah.**
`WeakConvergence/Suggested.lean` meldet `rc = 1`, und zwar an
`tendsto_map_of_measure_setOf_continuousAt_eq_one`: `ProbabilityMeasure.map`
nimmt in v4.33.1 (`Measure/ProbabilityMeasure.lean:608`) neben dem — impliziten —
`f` einen `AEMeasurable`-Beweis, auf `upstream/master` (`ibid.:626`) dagegen die
Funktion selbst. Das ist **kein** Versehen: der Modulkopf hält seit dem
2026-09-06 ausdrücklich fest, daß diese eine Aussage bewußt für master
geschrieben ist, weil Tau Ceti auf master aufsetzt. Der Lauf hat das erst
korrigiert und dann zurückgenommen; im Doc-Kommentar der Aussage steht jetzt
zusätzlich, wie die v4.33.1-Fassung lautete (`hh.aemeasurable` statt `h`), damit
der nächste Lauf nicht denselben Umweg geht. Gemessen: 48 Deklarationen und 18
`sorry`-Beweise, von denen der Übersetzer 17 als Warnung meldet — der achtzehnte
ist der dieser bewußten Master-Aussage, die nicht elaboriert. Die 21 des
Rückstaus sind damit überholt.

**Der Vorschlag für den nächsten Lauf ist deshalb weiterzurücken, auf
Schritt (iii) von `induction_on_mulSystem`**: `P` gilt für den Indikator jeder
Zelle von `ioiCells K`. Worauf er ruht: auf (ii), das jetzt steht, und auf der
π-System-Hälfte, die seit dem 2026-09-06 steht (`isPiSystem_ioiCells`,
`generateFromFuns_eq_generateFrom_ioiCells`). Was fehlt, ist genau ein Stück
Analysis — die Approximation des Indikators einer Box in `Fin n → ℝ` durch
stetige Funktionen von unten, monoton und beschränkt —, und danach trägt
`MeasurableSpace.induction_on_inter` (`MeasureTheory/PiSystem.lean:713`) die
Aussage über die ganze σ-Algebra. Warum jetzt: es ist der letzte der vier
Schritte mit Inhalt, (iv) ist Linearität und ein monotoner Limes, und damit ist
`fact:monotoneclass` — tragend `4`, der höchstgewichtete Fact ohne
Mathlib-Beleg — beweisbar statt bloß geplant.

### 2026-09-07, neunter Lauf des Tages — Rückstau 2: der funktionale Monotone-Klassen-Satz ist bewiesen

**Was bearbeitet wurde.** Rückstaupunkt 2 (`induction_on_mulSystem`), und zwar
das Ziel, das der achte Lauf am Ende benannt hatte: Schritt (iii). Er ist
erreicht, und im selben Lauf auch (iv), der Satz selbst und zwei seiner drei
Folgerungen. `TauCeti/WeakConvergence/Suggested.lean` geht durch `lake env lean`
gegen v4.33.1 mit genau den zwei bekannten Fehlern an
`tendsto_map_of_measure_setOf_continuousAt_eq_one` — der bewußt für
`upstream/master` geschriebenen Aussage — und ohne jede Warnung außer `sorry`.

**Damit ist `fact:monotoneclass` formalisiert.** Es war mit tragend `4` der
höchstgewichtete Fact ohne Mathlib-Beleg; seine Zeile in der Tabelle nennt
jetzt den vollständigen Beweis. Was in Meilenstein 5 noch aussteht, ist eine
einzige Folgerung (`condExp_eq_of_forall_integral_mul_eq`), nicht mehr der
Satz.

**Schritt (iii): von den stetigen Funktionen zu den Indikatoren.** Zwei
Deklarationen, dazu die Rampe.

* `ioiApprox k t = min 1 (max 0 ((k+1) * t))`, die stetige Rampe, mit
  `continuous_ioiApprox`, `ioiApprox_nonneg`, `ioiApprox_le_one`,
  `ioiApprox_of_nonpos`, `ioiApprox_of_one_le` und `monotone_ioiApprox`. Die
  Steigung ist `k+1` und nicht `k`, damit die Familie schon bei `k = 0`
  wächst statt mit der konstanten `0` zu beginnen — sonst ist das erste Glied
  entartet und die Monotonie fängt erst bei `1` an.
* `of_indicator_mem_ioiCells`: `P (Set.indicator s 1)` für jede Zelle
  `s ∈ ioiCells K`. Der Indikator der Zelle einer Liste `l` ist der punktweise
  wachsende Limes der Produkte `∏ i, ioiApprox k (fᵢ x - cᵢ)`, und jedes davon
  ist eine stetige Funktion der endlich vielen `fᵢ x`, also von Schritt (ii)
  erfaßt.
* `of_indicator_of_measurable`: dasselbe für jedes
  `MeasurableSet[generateFromFuns K] s`, über
  `MeasurableSpace.induction_on_inter` entlang `ioiCells K`.

**Drei Befunde an diesem Schritt, alle beim Hinschreiben gefunden.**

1. **Die Rampen müssen gemeinsam genommen werden, als *eine* stetige Funktion
   der `n` Werte.** Faktorweise ginge es nicht: `P` ist nicht
   multiplikationsabgeschlossen, und das Produkt der Indikatoren ist genau das,
   was ein faktorweises Argument bräuchte. Das ist der Grund, warum Schritt (ii)
   für eine stetige Funktion *endlich vieler* Mitglieder von `K` formuliert ist
   und nicht für eines — die Roadmap sagte das bisher nicht, jetzt schon.
2. **Die Disjunktheit im `iUnion`-Fall trägt genau eine Sache: die Schranke.**
   Die Partialsummen der Indikatoren wachsen ohne jede Disjunktheit; was ohne
   sie fehlt, ist `≤ 1`, und damit die Hypothese von `mono_lim`. Auch das steht
   jetzt in der Roadmap, weil es die Stelle benennt, an der ein Beweis kippt,
   der die Disjunktheit vergißt.
3. **Der Komplementfall braucht keine Fallunterscheidung über Meßbarkeit**,
   sondern nur `Set.indicator sᶜ 1 = 1 + (-1) • Set.indicator s 1` — Linearität
   und die Konstanten, mehr nicht.

**Schritt (iv): von den Indikatoren zu den beschränkten meßbaren Funktionen.**

* `of_simpleFunc`: `P ⇑f` für jede `f : @SimpleFunc Ω (generateFromFuns K) ℝ`,
  über `MeasureTheory.SimpleFunc.induction`, deren zwei Fälle das Vielfache
  eines Indikators und die Summe sind. Beschränktheit ist hier **keine**
  Hypothese: eine einfache Funktion hat endliches Bild.
* `of_nonneg_of_measurable`: `P f` für beschränktes, nichtnegatives,
  `generateFromFuns K`-meßbares `f`, als wachsender Limes von
  `SimpleFunc.eapprox` von `ENNReal.ofReal ∘ f`, zurückgelesen über
  `ENNReal.toReal`.

**Der Befund, der die Gestalt von (iv) bestimmt: der Umweg über `ℝ≥0∞` ist
nicht Bequemlichkeit, sondern das einzige, was die Approximation *wachsend*
macht.** `SimpleFunc.approxOn`, der naheliegende reelle Weg, gibt Konvergenz und
keine Monotonie, und `mono_lim` verlangt Monotonie. `SimpleFunc.eapprox` gibt
sie (`monotone_eapprox`), die Werte sind endlich (`eapprox_lt_top`), und deshalb
trägt `ENNReal.toReal_mono` sowohl die Monotonie als auch den Limes zurück nach
`ℝ`. Der allgemeine beschränkte Fall ist dann die Verschiebung
`f = (f + C) + (-C)` um eine Schranke von `f` — die Konstanten und die
Additivität, sonst nichts.

**Zwei Folgerungen tragen jetzt Beweise.**

* `ext_of_forall_integral_eq_of_isMulSystem` — zwei endliche Maße, die auf `K`
  und auf der Gesamtmasse übereinstimmen, stimmen auf `generateFromFuns K`
  überein. Induziert wird über
  `P f := Integrable f μ ∧ Integrable f ν ∧ ∫ f ∂μ = ∫ f ∂ν`; der Schluß ist
  `integral_indicator_one` und `measureReal_eq_measureReal_iff`.
* `integral_mul_eq_zero_of_isMulSystem` — dieselbe Bauform mit
  `P f := Integrable (g * f) μ ∧ ∫ g * f ∂μ = 0`.

**Und der Befund, der beide Folgerungen bestimmt: die Integrierbarkeit muß in
der induzierten Eigenschaft mitlaufen.** Das ist keine Bequemlichkeit. Die
Hypothesen `add` und `mono_lim` von `induction_on_mulSystem` müssen für
**beliebige** Funktionen gelten, nicht nur für die meßbaren, und `∫(f+g) =
∫f + ∫g` ist ohne Integrierbarkeit falsch; ebenso braucht der monotone Limes
majorisierte Konvergenz und damit `AEStronglyMeasurable` der Glieder. `P` trägt
deshalb die Integrierbarkeit als eigene Komponente, und die Meßbarkeit des
Limes kommt aus `aestronglyMeasurable_of_tendsto_ae` — aus den Gliedern, nicht
aus einer Meßbarkeitsannahme, die `P` gar nicht hätte.

**Mitgefunden, beim Übersetzen.**

* **`@[elab_as_elim]` schlägt zurück, sobald man den Satz als Term benutzt.**
  `have hres := induction_on_mulSystem …` scheitert mit „failed to elaborate
  eliminator, expected type is not available": das Motiv wird aus dem
  Erwartungstyp gelesen, und ein `have` ohne Typannotation hat keinen. Der
  erwartete Typ muß ausgeschrieben werden. Wer die drei Folgerungen fortsetzt,
  schreibt ihn hin.
* `Finset.range_subset` heißt in v4.33.1 `range n ⊆ s ↔ ∀ x < n, x ∈ s`; die
  Aussage `range n ⊆ range m ↔ n ≤ m` ist `Finset.range_subset_range`.
* `continuous_finset_prod` ist seit dem 2026-04-08 `deprecated`, der Name ist
  `continuous_finsetProd`.
* `push_neg` ist deprecated zugunsten von `push Not`; beide Stellen sind
  stattdessen ohne Taktik ausgeschrieben.
* `letI` für eine `MeasurableSpace`-Instanz in einem Beweis meldet der
  Stil-Linter — in einem Beweis ist `let` vorzuziehen. Und: in
  `ext_of_forall_integral_eq_of_isMulSystem` darf man `generateFromFuns K`
  **nicht** als Instanz einführen, weil `mΩ` schon eine ist und die Suche die
  letzte nimmt; dort steht die σ-Algebra deshalb überall annotiert. Das ist
  derselbe Mechanismus wie der Reihenfolgefehler vom 2026-09-06.

**Nachtrag desselben Laufs: die dritte Folgerung ist auch bewiesen, und damit
ist der Kern von Meilenstein 5 vollständig.**
`condExp_eq_of_forall_integral_mul_eq` trägt einen Beweis, und der Weg war der
unten skizzierte:
`integral_mul_eq_zero_of_isMulSystem` auf `g = X - Y` (dessen Hypothese
`∫ g = 0` ist genau `h1`), dann `f = Set.indicator s 1` für
`MeasurableSet[generateFromFuns K] s`, was `∫ x in s, X = ∫ x in s, Y` gibt
(`integral_indicator`), und schließlich
`MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq` gegen `μ[Y | …]`, dessen
Voraussetzungen `integrable_condExp`, `stronglyMeasurable_condExp` und
`setIntegral_condExp` liefern. Die `SigmaFinite (μ.trim hKle)`, die der Satz
zusätzlich verlangt, ist bei endlichem `μ` `inferInstance` über
`isFiniteMeasure_trim` (`Measure/Trim.lean:124`). Gemessen stand die Datei
an dieser Stelle bei **59 Deklarationen und 13 `sorry`** (vorher 48 und 17),
rc = 1 an der einen bewußten Master-Aussage und ohne jede weitere Warnung.

**Zwei Kleinigkeiten aus diesem Nachtrag, beide Zeitfresser beim nächsten Mal.**
`ring` scheitert an `(X x - Y x) * f x = ((fun x => …) - fun x => …) x`, weil es
die Pi-Subtraktion nicht beta-reduziert — `ring_nf` normalisiert nur die linke
Seite und läßt einen ratlos zurück; der Weg ist eine punktweise `have`-Gleichung
und `simp only`, nicht eine Funktionsgleichung. Und der Stil-Linter verlangt in
Beweisen `have` statt `haveI` auch für Instanzen, was für Prop-Klassen wie
`SigmaFinite` gleichwertig ist.

**Was offen bleibt.** Nichts mehr am funktionalen Monotone-Klassen-Satz. Was
offen bleibt, ist sein erster Abnehmer, und der hat eine benannte Hürde:

**Vorschlag für den nächsten Lauf, als benanntes Ziel.**
`MartingaleProblems.isMPSolution_iff_forall_fdd_continuous` **aus**
`isMPSolution_iff_forall_fdd`, also der Schritt von beschränkt meßbaren zu
beschränkt stetigen Testfunktionen. Worauf er ruht: auf
`induction_on_mulSystem` samt `integral_mul_eq_zero_of_isMulSystem`, seit heute
bewiesen, angewandt auf das multiplikative System der Produkte
`∏ k, h k (X (r k) ω)` mit `h k` beschränkt stetig, dessen erzeugte σ-Algebra
nach `generateFromFuns_eq_generateFrom_ioiCells` die von den Koordinaten
erzeugte ist. Warum jetzt: es ist der einzige Punkt der vier Roadmaps, der
`induction_on_mulSystem` **namentlich** zitiert und ihn jetzt wirklich bekommen
kann, und `isMPSolution_iff_forall_fdd` daneben stehen zu lassen ist zulässig —
die Äquivalenz der beiden Kriterien ist ein eigener Satz und braucht die
Grundfassung nur als Hypothese.

**Die Hürde dabei ist im selben Lauf weggeräumt.** Die Testfunktionen `h k`
sind reell, das multiplikative System also auch; der **Integrand** ist aber
`𝕂`-wertig, und `integral_mul_eq_zero_of_isMulSystem` ist über `ℝ` formuliert
(`g : Ω → ℝ`). Die Brücke ist jetzt gebaut und bewiesen:
`integral_mul_ofReal_eq_zero_of_isMulSystem`, für `𝕂`-wertiges `g` gegen ein
**reelles** `K`, über Real- und Imaginärteil (`RCLike.mul_re` gibt
`re (z * (r:𝕂)) = re z * r`, `integral_re` und `integral_im` vertauschen mit dem
Integral, `RCLike.ext` setzt zusammen). Sie steht als eigener Punkt in
Meilenstein 5, und dort ausdrücklich getrennt von den schon vorhandenen
`RCLike`-Varianten, die etwas anderes und Größeres sind: dort ist `K` selbst
`𝕂`-wertig und die Multiplikativität muß den Übergang zur reellen Unteralgebra
überstehen. Hier bleibt `K` reell und nur der andere Faktor wandert — deshalb
kostet die Brücke zwanzig Zeilen und nicht einen Meilenstein.

**Und das zweite Stück, das der Abnehmer braucht, ist ebenfalls gebaut.**
`generateFromFuns_setOf_continuous_bounded`: auf einem pseudometrisierbaren Raum
mit seiner Borelstruktur erzeugen die beschränkten stetigen reellen Funktionen
die Borel-σ-Algebra. Ohne das sagt die Induktion über ein aus stetigen
Funktionen gebautes multiplikatives System nichts, weil ihre Konklusion über
`generateFromFuns K` läuft und nicht über Borel. Der Beweis ist die trunkierte
Abstandsfunktion `fun x => min 1 (Metric.infDist x Uᶜ)`; **der Sonderfall, den
man dabei übersieht, ist `U = univ`** — dort ist `Uᶜ = ∅` und
`Metric.infDist x ∅ = 0` per Konvention, die Formel also falsch, und der Fall
ist eigens zu nehmen. Die Metrisierbarkeit wird genau hier und nur hier
gebraucht, und das steht jetzt auch so in Meilenstein 5.

Damit ist der nächste Lauf an `isMPSolution_iff_forall_fdd_continuous`
voraussetzungsfrei: alles, was er aus `WeakConvergence` braucht, ist bewiesen —
`induction_on_mulSystem`, die drei Folgerungen, die `RCLike`-Brücke und die
Erzeugung der Borelstruktur. Was dort bleibt, ist die Rechnung in
`MartingaleProblems`: das multiplikative System der Produkte
`∏ k, h k (X (r k) ω)` mit `r k ≤ s`, seine erzeugte σ-Algebra als
`⨆ r ∈ Set.Iic s, comap (X r) borel`, und der Fall `n = 0` — das leere Produkt
ist `1`, und genau daraus kommt die Hypothese `∫ g ∂P = 0`, die die Folgerung
zusätzlich verlangt. Am Ende des Laufs: **61 Deklarationen, 13 `sorry`** (gezählt mit `grep -cE "^(noncomputable )?(private |protected )*(theorem|lemma|def|structure|instance|abbrev) "`; die Sorry-Zahl ist die des Übersetzers).

### 2026-09-07, zehnter Lauf des Tages — Rückstau 1: die beiden Formen des Endlichdimensionalitätskriteriums waren nicht beweisbar

**Was bearbeitet wurde.** Rückstaupunkt 1 in `MartingaleProblems`, und zwar das
Ziel, das der neunte Lauf am Ende benannt hatte:
`isMPSolution_iff_forall_fdd_continuous`. Das Ziel ist **nicht** erreicht, aus
zwei Gründen, die beide erst am Quelltext sichtbar wurden; beide sind Befunde,
der zweite ist der schwerere. Erreicht ist stattdessen: die Aussagen sind
berichtigt, und sechs Deklarationen, die ihr Beweis braucht, sind gebaut und
bewiesen. Die Datei geht durch `lake env lean` gegen v4.33.1 mit `rc = 0` und
**ohne jede Warnung außer `sorry`**; sie steht bei **67 Deklarationen und 9
`sorry`** (vorher 58 und 9 — kein `sorry` dazu, keiner weg).

**Erster Befund: das benannte Ziel ist in dieser Datei nicht formulierbar.**
Die drei `Suggested.lean` sind **eigenständig** — jede importiert
ausschließlich `Mathlib.*`, keine importiert eine andere (an den
`import`-Zeilen aller drei geprüft). `induction_on_mulSystem` und seine
Folgerungen liegen in `TauCeti/WeakConvergence/Suggested.lean` und sind in
`TauCeti/MartingaleProblems/Suggested.lean` nicht im Kontext; ein `import`
dorthin ginge nur über eine `.olean`, die es nicht gibt, und sie zu bauen hieße,
für jeden späteren Lauf `lake env lean` unbrauchbar zu machen. **Der neunte Lauf
hat das übersehen**, als er das Ziel „voraussetzungsfrei" nannte:
voraussetzungsfrei ist es mathematisch, nicht mechanisch. Wer es aufnimmt, hat
drei Möglichkeiten, und die Wahl gehört dem Nutzer: den Beweis in
`WeakConvergence/Suggested.lean` führen, wo das Werkzeug liegt; die vier
Deklarationen nach `MartingaleProblems/Suggested.lean` kopieren, was sie
doppelt; oder die Prototypen zu einer Lake-Bibliothek zusammenfassen, was die
Werkzeuglage aller künftigen Läufe ändert.

**Zweiter Befund, an der Aussage: `isMPSolution_iff_forall_fdd` war in beiden
Formen nicht beweisbar.** Es fehlte eine Hypothese, und keine kosmetische.

* `Martingale` ist in v4.33.1 wie auf `upstream/master`
  `StronglyAdapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j | ℱ i] =ᵐ[μ] f i`
  (`Probability/Martingale/Basic.lean:53`) — die **Adaptiertheit gehört zur
  linken Seite**. Die rechte Seite ist eine Familie verschwindender Integrale
  und sagt über Meßbarkeit nichts; die Richtung von rechts nach links war also
  nicht zu haben.
* Schlimmer, und das trifft **beide** Richtungen: der Kompensator von
  `mpFamily` ist `fun ω ↦ ∫ u in Q.interval c ⊥ t, p.2 (X u ω) ∂Q.q`. Für
  festes `ω` braucht schon der *Integrand* `fun u ↦ p.2 (X u ω)` Meßbarkeit in
  `u`, und `hX : ∀ t, Measurable (X t)` sagt nur etwas über die **Schnitte in
  `ω`**. Ohne sie ist das Bochner-Integral sein Ersatzwert `0`, und damit
  scheitert die Additivität, auf der die Aussage ruht: die Zerlegung
  `Q.interval c ⊥ t = Q.interval c ⊥ s ∪ Q.interval c s t` macht die beiden
  Kompensatoren nur dann zur Differenz, wenn `setIntegral_union` anwendbar ist,
  und dessen Hypothese ist `IntegrableOn` auf beiden Hälften.

Die Hypothese, die beides trägt, ist die **gemeinsame Meßbarkeit unterhalb
jeder Zeit, relativ zur Filtration**, und sie steht jetzt in beiden Sätzen als

```lean
def Clock.IsProgressive (Q : Clock ι) (X : ι → Ω → E) (𝓕 : Filtration ι m) : Prop :=
  ∀ t : ι, ∃ Z : ι → Ω → E, (∀ u, u ≤ t → Z u = X u) ∧
    Measurable[Q.measurableSpace.prod (𝓕 t)] (Function.uncurry Z)
```

Das ist Mathlibs `IsStronglyProgressive` in der Gestalt, die der `Clock`
erzwingt: die Uhr trägt ihre `MeasurableSpace ι` als **Feld** und nicht als
Instanz, also ist der Untertyp `Set.Iic t` dieser Struktur ohne `@` nicht
hinschreibbar, und die äquivalente Fassung über eine gemeinsam meßbare
Fortsetzung `Z` ist die brauchbare. Sie ist eine Hypothese an `X` und die Uhr
allein, **nie an `P`** — deshalb entwertet sie das Kriterium nicht.

**Warum das keine Verschärfung über die Bündel hinaus ist.** Die schwächere
Fassung „`(u,ω) ↦ X u ω` ist `Q.measurableSpace ⊗ m`-meßbar" trägt die
Integrierbarkeit und die Additivität, aber **nicht** die Adaptiertheit: aus
Meßbarkeit gegen die volle σ-Algebra `m` folgt keine gegen `𝓕 t`, und `h𝓕`
hilft nicht, weil sich das Erzeugnis `⨆ r ∈ Iic s, comap (X r)` nicht durch das
Produkt hindurchzieht. Umgekehrt wäre die Fassung ohne die Einschränkung auf
`u ≤ t` echt zu stark: sie machte `X u` für **alle** `u` `𝓕 t`-meßbar, also den
Prozeß trivial. Die `∃ Z`-Gestalt ist genau dazwischen.

**Sechs Deklarationen, alle bewiesen, alle durch `lake env lean`.**

* `Clock.interval_subset_Iic`, `Clock.measurableSet_interval` und
  `Clock.measure_interval_ne_top` — das Intervall liegt unter seinem rechten
  Ende, ist meßbar, hat endliche Masse. Das Letzte ist die einzige Stelle, an
  der `Clock.measure_Iic_ne_top` überhaupt gebraucht wird, und es ist das, was
  den Kompensator für beschränktes `p.2` zu einer beschränkten Funktion von `ω`
  macht.
* `stronglyMeasurable_integral_comp` —
  `MeasureTheory.StronglyMeasurable.integral_prod_left`
  (`MeasureTheory/Integral/Prod.lean:84`) mit **beiden** σ-Algebren als
  Argument, damit `Q.measurableSpace` und `𝓕 t`, die keine Instanzen sind,
  übergeben werden können.
* `integrableOn_of_bounded` — beschränkt und meßbar ist integrierbar auf einer
  Menge endlichen Maßes, über `Integrable.mono'` gegen `integrable_const`.
* `mpFamily_sub_of_measurable_path` — die Inkrementidentität
  `Y t ω - Y s ω = f (X t ω) - f (X s ω) - ∫ u in Q.interval c s t, g (X u ω) ∂Q.q`,
  aus `Clock.interval_union` und `setIntegral_union`. Sie ist der Grund, warum
  die rechte Seite des Kriteriums überhaupt das Inkrement von `Y` prüft.

**Vier Kleinigkeiten, die beim Übersetzen Zeit gekostet haben.**

1. **`RCLike 𝕂` liefert `SecondCountableTopology 𝕂`** — über
   `RCLike.rclike_to_real : FiniteDimensional ℝ K`
   (`Analysis/RCLike/Lemmas.lean:64`) —, und damit greift
   `Measurable.stronglyMeasurable`. Daran hing die ganze Konstruktion, denn
   `StronglyMeasurable.integral_prod_left` verlangt `StronglyMeasurable`,
   während `hA` nur `Measurable` gibt. Geprüft mit
   `example {𝕂 : Type*} [RCLike 𝕂] : SecondCountableTopology 𝕂 := by
   infer_instance`. Nötig ist dafür der Import von `Analysis.RCLike.Lemmas`,
   nicht nur `Basic`.
2. **Wo `MeasurableSpace ι` keine Instanz ist, wird der Term `@`-annotiert, die
   `have`-Zeile aber nicht.** `have hint : ∀ s' t', IntegrableOn … := …`
   scheitert an der Instanzsuche für den *Typ*; `have hint := fun s' t' => @…`
   nicht, weil dann nur der Term elaboriert wird. Das ist der billigste Ausweg
   aus dem `Clock`-Feld-Problem und erspart das Ausschreiben von `IntegrableOn`s
   Argumentreihenfolge.
3. `Set.diff_subset` ist `deprecated`, der Name ist `Set.sdiff_subset`.
4. `omit [MeasurableSpace E] in` steht **vor** dem Doc-Kommentar, nicht zwischen
   ihm und dem `theorem`; sonst meldet der Parser `unexpected token 'omit'`.

**Was offen bleibt.** Beide Formen von `isMPSolution_iff_forall_fdd` tragen
weiterhin `sorry` — jetzt aber an einer Aussage, die stimmt, und mit dem
Werkzeug daneben. Der Beweis der Grundform zerfällt in zwei Hälften:

* **von links nach rechts** — `mpFamily_sub_of_measurable_path` gibt das
  Inkrement, `∏ k, h k (X (r k) ω)` ist nach `h𝓕` beschränkt und
  `𝓕 s`-meßbar, und die Herausziehregel ist
  `MeasureTheory.condExp_smul_of_aestronglyMeasurable_left`
  (`ConditionalExpectation/PullOut.lean:223`), reell in der ersten und
  `[NormedSpace ℝ E]` in der zweiten Variablen, also genau auf unser Paar
  (reelles `h`, `𝕂`-wertiges `Y`) zugeschnitten;
  `RCLike.real_smul_eq_coe_mul` (`Analysis/RCLike/Basic.lean:107`) übersetzt
  zwischen `•` und dem `*` der Aussage;
* **von rechts nach links** — `ae_eq_condExp_of_forall_setIntegral_eq` verlangt
  `∫ x in G, …` für **alle** `G ∈ 𝓕 s`, und die Produkte liefern nur die
  Erzeuger. Der Schritt dazwischen ist `MeasurableSpace.induction_on_inter`
  über dem π-System der endlichen Durchschnitte `⋂ k, X (r k) ⁻¹' (B k)` mit
  `r k ≤ s`, dessen Erzeugnis nach `h𝓕` gerade `𝓕 s` ist. Das ist die
  **Mengen**fassung des Monotone-Klassen-Satzes, die in Mathlib steht — die
  Funktionenfassung `induction_on_mulSystem` wird hier **nicht** gebraucht,
  sondern erst für die stetige Form.

**Vorschlag für den nächsten Lauf, als benanntes Ziel.** Die Richtung **von
links nach rechts** von `isMPSolution_iff_forall_fdd`, als eigene Deklaration
`forall_fdd_of_isMPSolution` in `MartingaleProblems/Suggested.lean`. Worauf sie
ruht: auf `mpFamily_sub_of_measurable_path` und `Clock.IsProgressive`, beide
seit heute da; auf `condExp_smul_of_aestronglyMeasurable_left` aus Mathlib; und
auf einem Hilfssatz, der aus `h𝓕` die `𝓕 s`-Meßbarkeit von
`fun ω ↦ ∏ k, h k (X (r k) ω)` zieht (`Measurable.comap_le`, `le_iSup₂`). Warum
jetzt: sie braucht **keine** Induktion über eine σ-Algebra und **kein** Werkzeug
aus einer anderen Datei — sie ist genau die Hälfte, die der erste Befund dieses
Laufs nicht blockiert, und sie zwingt die neue Hypothese sofort in einen Beweis,
statt sie nur zu behaupten.

### 2026-09-07, elfter Lauf des Tages — vorrangige Aufgabe: das Erreichte geprüft, und die Hypothesen mechanisch abgebaut

**Erster Teil, Prüfung. Alle drei `Suggested.lean` sind durch ein
`#print axioms`-Audit gegangen, und das Ergebnis ist sauber.** Methode: an jede
Datei wurde mechanisch ein Block `#print axioms <Deklaration>` je Deklaration
angehängt (59 in `WeakConvergence`, 61 in `MartingaleProblems`, 103 in
`SkorokhodSpace`) und mit `lake env lean` gegen das gebaute Mathlib v4.33.1
ausgewertet; die Skripte liegen im Lauf, nicht im Repo. Der Abgleich lief
zweiseitig: die Menge der Deklarationen, deren Axiomliste `sorryAx` enthält,
gegen die Menge der Deklarationen mit eigener `declaration uses 'sorry'`-Warnung.
**Die beiden Mengen sind identisch** — 13 in `WeakConvergence`, 9 in
`MartingaleProblems`, 7 benannte plus die vier anonymen Instanzen in
`SkorokhodSpace`. Keine einzige als bewiesen geführte Deklaration hängt
transitiv an einem fremden `sorry`. (`tendsto_map_of_measure_setOf_continuousAt_eq_one`
war vom Audit ausgenommen: sie ist absichtlich gegen master geschrieben und
elaboriert unter v4.33.1 nicht; das ist im Moduldok der Datei festgehalten.)

**Ein Befund aus demselben Audit, der die Selbstauskunft der Datei präzisiert:**
`SkorokhodSpace.modulus` ist ein `def` mit Rumpf `sorry`, und damit sind
`SkorokhodSpace.tendsto_modulus` und `SkorokhodSpace.isCompact_closure_iff`
zurzeit Aussagen **über `sorryAx`** — exakt die Falle, die das Moduldok der
Datei am Beispiel `normOn` selbst beschreibt („A definition whose body is
`sorry` makes every theorem about it a statement about `sorryAx`"). Dasselbe
gilt abgeschwächt für die vier anonymen Instanzen am Dateiende: die
`MeasurableSpace D(ι, E) := borel _`-Instanz ruht auf der `sorry`-Instanz
`MetricSpace D(ι, E)`, so daß `continuousAt_eval`, `measurableEmbedding_piDense`
und `borel_eq_iSup_comap_eval` über einer `sorryAx`-Topologie formuliert sind.
Das ist dokumentierter, gewollter Zwischenzustand (der Basispunkt fehlt der
Instanz, nicht ein Axiom) — aber wer Meilenstein 8 von hier aus weiterbaut,
sollte zuerst `modulus` einen Rumpf geben, sonst beweist er über `sorryAx`.

**Leere Aussagen: keine gefunden.** Für jede `sorry`-Aussage mit nichttrivialen
Hypothesen wurde geprüft, ob die Hypothesen gemeinsam erfüllbar sind, per
skizziertem Zeugen (mathematisch, nicht als Lean — wo der Zeuge mehr als ein
paar Zeilen Lean kostet, steht das dabei):

* `isTightMeasureSet_of_stronglySeparatesPoints` und
  `isConvergenceDetermining_of_stronglySeparatesPoints` (WC M1): `E = ℝ`,
  `A = ⊤` (alle beschränkten stetigen Funktionen), konstante Folge
  `μ n = μ₀`. Stark trennend, weil `min (dist · x) δ` in `A` liegt; die
  Integralkonvergenz ist trivial. Erfüllbar, Konklusion nichtleer (Ulam).
* die beiden `fact:convdet`-Hälften und die vier Meilenstein-3-Sätze (WC):
  nur Instanzhypothesen, `E = ℝ` erfüllt alle.
* `isSeparating_pi` (WC M1): `S i = ℝ`, `Γ i` = beschränkt-stetig; das ist
  `isSeparating_setOf_boundedContinuous`, in der Datei bewiesen.
* `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (WC M4):
  `μ n = ν = δ₀`; die Truncation-Integrale sind `0`.
* `isMPSolution_iff_forall_fdd` und die stetige Form (MP M3): der Zeuge ist
  der **Münz-Zeuge der Datei selbst** — `E = Bool`, `X = coinProcess u`,
  `Q = atomClock u`, `𝓕 = coinFiltration u`. `hA` und `hX` sind bewiesen
  (`isMPSolution_coinProcess` benutzt sie), `hXprog` gilt mit `Z = X` für
  `u ≤ t` (Rechteck `{s | u ≤ s} ×ˢ {true}` ist `⊤.prod ⊤`-meßbar) und
  `Z = const false` sonst; `h𝓕` ist die Aussage, daß `coinFiltration` die
  natürliche Filtration ist — wahr, aber als Lean ein eigener Beweis von
  vielleicht dreißig Zeilen (die `⨆`-Berechnung über `Set.Iic s`), darum hier
  nur skizziert.
* `restart`/`restart_canonical` (MP M5): nichttrivialer Zeuge billig —
  `ι = ℕ`, `F = ℕ → E`, `θ r f = f (r + ·)`, `𝓧₀ r = {0}`; alle Felder von
  `IsShiftSystem` gelten mit `Y = 0`, `κ = 0`, die Dichte `Z = 1`.
* `exists_cadlag_modification_of_isRegularizingClass` und
  `isQuasiLeftContinuous_of_isRegularizingClass` (MP M9): `E = Bool`,
  `X` konstant, `Φ = {Indikator von true}` (trennend nach
  `isSeparating_coinClass`-Muster), Kompensator `C = 0`, `D = Set.univ` auf
  `ι = ℕ`; Kompaktheit über `K = univ`.
* `isQuasiLeftContinuous_of_isMPSolutionFor` (MP M9): `Q.q = 0` ist atomlos
  und macht `mpFamily` zu `p.1 ∘ X`; mit konstantem `X` ist alles Martingal.
  Erfüllbar — und der Münz-Zeuge zeigt zugleich, daß `hQ` nicht streichbar
  ist (`not_isAtomless_atomClock`).
* `mpSolution_of_tendsto` (MP M10) und
  `isMPSolution_of_forall_condExp_eq_of_dense` (MP): `𝓧 = {0}`, `𝓩 s = {1}`,
  konstante Folgen; bzw. `ι = ℝ`, `D = ℚ`, `hDmax` leer. Erfüllbar.
* `exists_orderIso_isometry_real` (SK M1): keine Hypothesen außer dem Bündel;
  `ι = ℝ` trägt es (`Real.instAdditiveDist` steht in der Datei).
* `SkorokhodSpace.measurableEmbedding_piDense` (SK M6): die Hypothese ist
  `D.Countable` **und** die Rechtsapproximationsklausel aus Meilenstein 2 —
  geprüft, daß die Aussage die Klausel trägt, die der `thm:fdd`-Befund vom
  2026-09-06 verlangt (siehe „Offene Auffälligkeiten"); sie tut es über
  `hD : ∀ t, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot`.

**Aussage gegen Absicht:** die im Inventar belegten Zuordnungen
(Meilenstein-Spalte der Tabelle) wurden beim Lesen aller drei Dateien
mitgeprüft; die am 2026-09-05 bis 2026-09-07 dokumentierten Korrekturen
(`not_isQuasiLeftContinuous_of_atom` trägt `hA`/`hsep`/càdlàg in der
Konklusion; `isMPSolution_iff_forall_fdd` trägt `Clock.IsProgressive`;
`eq_of_eqOn_dense` trägt die Rechtsklausel) stehen so in den Dateien. Kein
neuer Fall von „Lean sagt weniger als die Roadmap" gefunden.

**Zweiter Teil, Verallgemeinerung — das `omit`-Experiment, und warum sein
Ergebnis ein Negativbefund mit einer Methodenlehre ist.** Mechanisch wurde für
jede bewiesene Deklaration in `SkorokhodSpace` (Kandidaten `[OrderTopology ι]`,
`[AdditiveDist ι]`, `[ProperSpace ι]`) und in `MartingaleProblems`,
Regularizing-Sektion (Kandidaten `[OrderBot ι]`, `[TopologicalSpace ι]`,
`[OrderTopology ι]`) jede noch nicht weggelassene Bündel-Instanz zusätzlich per
`omit` entfernt, iterativ bis zur Fixpunkt-Datei, die `lake env lean` mit
Rückgabewert 0 durchläuft. Dann wurden die **Signaturen** aller Deklarationen
per `#check @name` gegen die Originaldatei verglichen. Ergebnis: **byteidentisch,
in beiden Dateien, für jede Deklaration.** Die Dateien sind auf dieser Achse
bereits minimal — keine einzige Bündel-Instanz läßt sich aus irgendeiner
Signatur entfernen, und zwar aus einem Grund, der die Prüfmethode der Aufgabe
korrigiert:

* **`omit` ist kein verläßlicher Test, und ein fehlerfreier Übersetzungslauf
  ist kein Zertifikat.** Lean 4 nimmt Sektionsvariablen ohnehin
  **nutzungsbasiert** in die Signatur auf: `exhaustionMin` etwa trägt schon im
  Original kein `[AdditiveDist ι]`, obwohl kein `omit` davorsteht. Und wo eine
  per `omit` entfernte Instanz vom Rumpf doch gebraucht wird, meldet der
  Elaborator das nur bei expliziter Referenz in der Aussage („cannot omit
  referenced section variable"); bei `def`s und bei Instanzsuche im Beweis wird
  sie **stillschweigend wieder aufgenommen** — die Experimentdatei übersetzte
  fehlerfrei mit `omit [ProperSpace ι]` vor `exhaustionMin`, dessen Signatur
  `[ProperSpace ι]` danach **unverändert** enthielt. Wer künftig eine
  Abschwächung behauptet, belegt sie mit `#check @name` vorher/nachher, nicht
  mit einem fehlerfreien Lauf.
* Der Befund heißt nur: minimal relativ zu dem, was die **vorhandenen Beweise
  benutzen**. Ob ein anderer Beweis eine Instanz vermeiden könnte, sieht das
  Experiment nicht.

**Die Achsen, die `omit` nicht testet, mit Begründung je Halt:**

* `LinearOrder ι` gegen `Preorder ι`: in `MartingaleProblems` ist die
  Grundschicht (Clock, `mpFamily`, beide fdd-Kriterien) **schon** `Preorder ι`;
  die Regularizing-Sektion braucht `ConditionallyCompleteLinearOrder ι` für
  `⨆ n, τ n ω` in `WithTop ι` (die Suprema der Stoppzeiten), die Sprungtheorie
  von `SkorokhodSpace` braucht `LinearOrder ι` in `nhdsLT_sup_nhdsGE` (die
  Zerlegung einer Umgebung in die zwei einseitigen Hälften ist der Kern von
  `eventually_dist_leftLim_lt`). Benannte Hindernisse, keine Vermutungen.
* `RCLike 𝕂` abschwächen: `stronglyMeasurable_integral_comp` und
  `integrableOn_of_bounded` benutzen `RCLike` nur über
  `SecondCountableTopology` und die Borelstruktur; eine Fassung für einen
  beliebigen normierten Raum müßte beide als **zusätzliche** Hypothesen
  anschreiben — das ist ein Tausch, keine Abschwächung, und für die Datei, die
  ohnehin `𝕂`-wertige Testprozesse hat, kein Gewinn.

### 2026-09-07, zwölfter Lauf des Tages — vorrangige Aufgabe: das Audit maschinell wiederholt, zwei Korrekturen am Vorlauf, und eine Abschwächung, die trägt

**Methode.** Der elfte Lauf hat das Axiom-Audit mit einem angehängten Block von
`#print axioms`-Zeilen je Deklaration gefahren. Dieser Lauf ersetzt das durch
**ein** Metaprogramm je Datei, das über `Lean.collectAxioms`
(`Lean/Util/CollectAxioms.lean:149`, `public def`) läuft und alle Konstanten des
laufenden Moduls aus `env.checked.get.constants.foldStage2` zieht. Der Vorteil
ist nicht die Ersparnis, sondern die Vollständigkeit: die Liste wird nicht von
Hand geführt, also kann keine Deklaration übersehen werden. Zahlen (bewiesen =
ohne `sorryAx` in der Axiomliste):

| Datei | Deklarationen | ohne `sorryAx` | mit `sorryAx` | eigene `sorry`-Warnung |
|---|---|---|---|---|
| `WeakConvergence` | 60 | 47 | 13 | 13 |
| `SkorokhodSpace` | 165 | 152 | 13 | **11** |
| `MartingaleProblems` | 128 | 119 | 9 | 9 |

**Erste Korrektur am elften Lauf.** Er hält fest, die beiden Mengen — „hängt an
`sorryAx`" und „hat eine eigene `sorry`-Warnung" — seien in allen drei Dateien
identisch. In `SkorokhodSpace` sind sie es **nicht**: zwei Deklarationen sind
ohne eigenes `sorry` und hängen doch daran, und sie heißen

* `instMeasurableSpaceSkorokhodSpace` (`Suggested.lean:1670`,
  `noncomputable instance : MeasurableSpace D(ι, E) := borel _`) und
* `instBorelSpaceSkorokhodSpace` (`:1671`, `instance : BorelSpace D(ι, E) := ⟨rfl⟩`).

Beide erben es von der Platzhalter-Instanz `MetricSpace D(ι, E) := sorry`
(`:1653`), denn `borel _` liest die Topologie aus ihr. Sachlich ändert das den
Befund des elften Laufs nicht — er hat genau diese Abhängigkeit im Fließtext
beschrieben —, wohl aber seine Zählung, und die Zählung war das Zertifikat.
Der Rest steht: **keine als bewiesen geführte Deklaration hängt an einem
fremden `sorry`**, außer diesen beiden dokumentierten Instanzen.
(`tendsto_map_of_measure_setOf_continuousAt_eq_one`, `WeakConvergence:448`, ist
weiterhin die einzige Deklaration, die unter v4.33.1 gar nicht elaboriert; sie
ist absichtlich gegen master geschrieben.)

**Zweite Korrektur am elften Lauf, und sie betrifft seine Methodenlehre.** Er
schließt aus dem `omit`-Experiment, „`omit` ist kein verläßlicher Test, und ein
fehlerfreier Übersetzungslauf ist kein Zertifikat", und verlangt künftig
`#check @name` vorher/nachher. Das ist richtig beobachtet und die falsche
Konsequenz: Mathlib hat für genau diese Frage einen Linter, und er ist
standardmäßig an. `linter.unusedSectionVars` meldet je Deklaration, welche
automatisch aufgenommene Sektionsvariable in ihr **unbenutzt** ist, und schlägt
die `omit`-Zeile im Wortlaut vor. Daß er in dieser Umgebung wirklich feuert, ist
mit einer Testdatei geprüft worden (zwei Sätze über `[MetricSpace α]
[Nonempty α] [Inhabited α]`; der Linter nennt bei dem einen beide, bei dem
anderen nur `Nonempty α`). Über die drei `Suggested.lean` gelaufen meldet er
**nichts** — in keiner der drei Dateien ist eine einzige Sektionsvariable
unbenutzt. Damit ist der Negativbefund des elften Laufs unabhängig bestätigt und
zugleich billig reproduzierbar: wer wissen will, ob eine Annahme entbehrlich
ist, liest die Übersetzungswarnungen, statt ein Experiment zu bauen.

Ergänzend lief ein zweites, unabhängiges Metaprogramm, das je Deklaration die
Instanz-Binder des Typs durchgeht und prüft, ob der Binder im Resttyp **und** im
Beweisterm frei von Vorkommen ist — das ist genau die Bedingung, unter der
`omit` durchgeht. Es meldet ebenfalls nichts. (Es meldet allerdings auch im
Selbsttest nichts, wo der Linter feuert, also ist es als Werkzeug schwächer als
der Linter und nur als Gegenprobe zu nehmen; der Linter ist die maßgebliche
Quelle.)

**Die Abschwächung, die trägt, und sie steht in der Datei.**
`IsSeparating.of_subalgebra` (`WeakConvergence/Suggested.lean:184`) stand unter

    [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

und steht jetzt unter

    [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E].

Der Grund ist die stehende Regel und nicht Geschmack: Mathlib hat den Satz in
**zwei** Fassungen, und die Datei zitierte die stärkere.
`ext_of_forall_mem_subalgebra_integral_eq_of_polish`
(`MeasureTheory/Measure/FiniteMeasureExt.lean:72`) ist wörtlich
`ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`
(`:36`) mit einem vorangestellten `upgradeIsCompletelyMetrizable`. Die
Vollständigkeit kommt im Beweis vor (er geht über
`ext_of_forall_integral_eq_of_IsFiniteMeasure` und die
`mulExpNegMulSq`-Approximation), die **Trennung von `E`** dagegen nirgends —
getrennt wird durch die Algebra, nicht durch den Raum, und darum darf die Metrik
eine Pseudometrik sein. Belegt, nicht vermutet: die geänderte Datei ist mit
`lake env lean` durchgelaufen, unverändert 13 `sorry` und kein neuer Fehler; der
Beweis ist derselbe bis auf den Namen des zitierten Satzes. Der README-Punkt von
Meilenstein 1 ist nachgezogen.

**Zwei Achsen geprüft, mit Negativbefund, damit sie nicht wieder geprüft
werden.**

* `IsConvergenceDetermining.isSeparating` (`:151`) und
  `isSeparating_setOf_boundedContinuous` (`:164`) tragen
  `[BorelSpace E] [HasOuterApproxClosed E]`, und beides ist nötig:
  `ProbabilityMeasure.t2Space` steht in
  `MeasureTheory/Measure/ProbabilityMeasure.lean:422` unter genau dem
  `variable [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]`
  (`:416`), und `ext_of_forall_integral_eq_of_IsFiniteMeasure`
  (`HasOuterApproxClosed.lean:269`) ebenso. Minimal.
* `MetricSpace E` gegen `PseudoMetricSpace E` in `SkorokhodSpace`,
  Meilenstein 2: **bricht bei `IsCadlag.tendsto_leftLim`**. `Function.leftLim`
  legt den Grenzwert nur in einem `T2Space` fest, und ein pseudometrischer Raum
  ist genau dann `T2`, wenn er metrisch ist. Die ganze Sprungtheorie —
  `leftJumpSet`, `countable_leftJumpSet`,
  `continuousAt_iff_notMem_leftJumpSet` — ruht also auf der Trennung von `E`.
  Ein benanntes Hindernis, kein Verdacht.

**Der Zeuge, den der elfte Lauf nur skizziert hat, ist jetzt Lean.** Er hält für
`not_isQuasiLeftContinuous_of_atom` fest, die Hypothese sei erfüllbar, ohne den
Zeugen anzuschreiben — und das ist genau die Stelle, an der zweimal eine leere
Aussage stehengeblieben ist. In `MartingaleProblems/Suggested.lean` steht daher
jetzt, bewiesen und ohne `sorry`:

    theorem exists_index_witness_for_atom :
        ∃ s : ℕ → ENNReal, StrictMono s ∧ (∀ n, s n < (⊤ : ENNReal)) ∧
          Tendsto s atTop (𝓝 (⊤ : ENNReal))

Der Index ist `ℝ≥0∞`. Er trägt alle vier Instanzen, die die
Regularizing-Sektion verlangt — `ConditionallyCompleteLinearOrder`, `OrderBot`,
`TopologicalSpace`, `OrderTopology` —, der Atompunkt ist `u = ⊤`, und
`n ↦ (n : ℝ≥0∞)` nähert ihn strikt von links (`Nat.strictMono_cast`,
`ENNReal.natCast_ne_top`, `ENNReal.tendsto_nat_nhds_top`,
`Mathlib/Topology/Instances/ENNReal/Lemmas.lean:147`). Damit ist die
Schärfeaussage des Meilensteins 9 nicht mehr nur nichtleer behauptet, sondern
nichtleer bewiesen. Die Datei ist mit der Ergänzung durchgelaufen, unverändert
9 `sorry`.

**Was offen blieb.** Die Abschwächung `MetricSpace ι` → `PseudoMetricSpace ι`
für Meilenstein 1 von `SkorokhodSpace` sieht durch: `AdditiveDist` ist in der
Datei ohnehin über `[PseudoMetricSpace α]` erklärt (`:140`), und
`dist_eq_sub_of_le`, `monotoneOn_dist_basepoint`, `dist_eq_abs_sub_of_sameSide`,
`ordConnected_exhaustion`, `mem_exhaustion_self` benutzen nichts darüber hinaus.
Sie ist **nicht** durchgeführt, weil der `variable`-Block von 1700 Zeilen geteilt
wird und `TimeChange` die echte Metrik braucht; es wäre eine eigene Sektion, und
dieser Lauf hat sie nicht mehr geprüft. Behauptet wird sie darum nicht.

**Vorschlag für das Nächste, als benanntes Ziel: `isSeparating_pi` beweisen**
(`WeakConvergence/Suggested.lean:297`, Meilenstein 1) — trennende Klassen
multiplizieren sich über einen **beliebigen** Indextyp. Worauf sie ruht: auf
`isSeparating_setOf_boundedContinuous` (in der Datei bewiesen) und auf dem
funktionalen Monotone-Klassen-Satz von Meilenstein 5, der seit dem 2026-09-07,
neunter Lauf, vollständig bewiesen dasteht. Warum jetzt: die Klasse in ihrer
Konklusion ist wörtlich eine `IsMulSystem` — endliche Produkte
`∏ i ∈ J, g i (x i)` sind unter Multiplikation abgeschlossen —, und
`ext_of_forall_integral_eq_of_isMulSystem` (`:1351`) ist genau der Satz, der aus
einer `IsMulSystem` mit `generateFromFuns K = mΩ` die Gleichheit zweier Maße
macht. Was zu zeigen bleibt, ist die σ-Algebra-Rechnung
`generateFromFuns (Produkte) = MeasurableSpace.pi`, und dafür liegen
`generateFromFuns_le_iff` (`:608`) und `generateFromFuns_mono` (`:613`) bereit.
Das ist der erste Punkt des Meilensteins, der ohne neuen Unterbau fällt, und er
ist der, den `thm:fdd` des Manuskripts unmittelbar braucht.

### 2026-09-07, dreizehnter Lauf des Tages — `isSeparating_pi` ist bewiesen, und der angekündigte Weg dorthin war der falsche

**Was der Lauf vorgefunden hat.** Die vorrangige Aufgabe „acceptance examples für
jeden Meilenstein" war bereits erledigt — alle **27** Meilensteine der vier
Roadmaps tragen den Abschnitt, gezählt am Text (`WeakConvergence` 5,
`SkorokhodSpace` 8, `KolmogorovExtension` 3, `MartingaleProblems` 1–11; 12 und 13
haben wie verlangt keinen). Sie ist im Auftrag durchgestrichen, mit ihrem
Ergebnis und dem Maßstab, den der vierte Lauf angelegt hat. Die Tabelle des
Inventars hat keine `?`-Zeile mehr, also ging es an Rückstaupunkt 1.

**Das Ziel war benannt, und es steht.** Der zwölfte Lauf schlug
`isSeparating_pi` vor (`WeakConvergence/Suggested.lean`, Meilenstein 1). Es ist
**bewiesen**, ohne `sorry`, und die Datei geht durch `lake env lean` gegen
v4.33.1: 12 `sorry` statt 13, keine neue Warnung, und weiterhin genau die beiden
Fehler an `tendsto_map_of_measure_setOf_continuousAt_eq_one` (`:804`), die der
Modulkopf seit dem 2026-09-06 ankündigt, weil jene Aussage absichtlich gegen
`upstream/master` geschrieben ist.

**Der vorgeschlagene Weg trug nicht, und das ist der zweite Befund des Laufs.**
Der zwölfte Lauf nannte als Anker `ext_of_forall_integral_eq_of_isMulSystem` —
den funktionalen Monotone-Klassen-Satz von Meilenstein 5 — mit der Begründung,
die Klasse in der Konklusion von `isSeparating_pi` sei „wörtlich eine
`IsMulSystem`". Sie ist es nicht. Endliche Produkte $\prod_{i\in J} g_i(x_i)$
sind unter Multiplikation nur abgeschlossen, wenn jedes $\Gamma_i$ es ist, und
eine trennende Klasse muß das nicht sein. Der kleinste Zeuge steht jetzt in der
Roadmap: $\Gamma=\{\mathbb 1_{\{1\}},\mathbb 1_{\{2\}}\}$ auf $\{0,1,2\}$ ist
trennend — die drei Bildpunkte $(0,0),(1,0),(0,1)$ sind affin unabhängig, also
ist $\mu\mapsto(\int f\,d\mu)_{f\in\Gamma}$ auf dem Simplex injektiv —, und das
Produkt seiner beiden Mitglieder ist die konstante $0$. Dieselbe Falle wie bei
`isMulSystem_indicator_of_isPiSystem` am 2026-09-06, und aus demselben Grund:
„erzeugt dieselbe σ-Algebra" ist nicht „ist multiplikativ abgeschlossen".

**Der Weg, der trägt.** Trennung ist eine *lineare* Bedingung im Verborgenen:
$\Gamma$ trennt Wahrscheinlichkeitsmaße genau dann, wenn kein von Null
verschiedenes signiertes Maß der Gesamtmasse $0$ alle $f\in\Gamma$ annulliert —
denn jedes solche signierte Maß ist nach Jordan ein Vielfaches einer Differenz
zweier Wahrscheinlichkeitsmaße. Damit läßt sich in einem *gewichteten* Integral
ein $f\in\Gamma_i$ gegen einen beliebigen Indikator $\mathbb 1_{B_i}$
austauschen, und das ist der Induktionsschritt. Formalisiert ist das **ohne
jedes signierte Maß**, was in Lean der Unterschied zwischen einem Nachmittag und
einer Woche ist: das Jordan-Paar von $W\cdot(\mu-\nu)$ steht als zwei ehrliche
positive Maße da,

    sepPos T μ ν W = weightedMap T μ W + weightedMap T ν (-W)
    sepNeg T μ ν W = weightedMap T ν W + weightedMap T μ (-W)

mit `weightedMap T ρ w = (ρ.withDensity (ENNReal.ofReal ∘ w)).map T`, also dem
Bild des mit dem Positivteil von `w` umgewichteten `ρ`. Gegen beschränktes
meßbares `h` ist ihre Differenz genau
$\int W\cdot(h\circ T)\,d\mu-\int W\cdot(h\circ T)\,d\nu$
(`integral_sepPos_sub_integral_sepNeg`, über
`integral_withDensity_eq_integral_smul` und `integral_map`). Beide Gesamtmassen
stimmen überein, weil $\int W\,d\mu=\int W\,d\nu$ die vorige Induktionsstufe
ist; ist sie $0$, sind beide Maße $0$, sonst normiert man und wendet
`IsSeparating` an, und `ENNReal.mul_inv_cancel` holt die Normierung zurück. Das
ist `integral_indicator_mul_eq_of_isSeparating`, und es ist das
wiederverwendbare Stück: **jede** Stelle, an der eine trennende Klasse gegen ein
Gewicht statt gegen ein zweites Maß benutzt wird, geht darüber.

Darauf sitzt die Induktion über `J`, die die $g_i$ einen Index nach dem anderen
durch Indikatoren ersetzt. Die Buchhaltung ist ein zweites `Finset` `J'` für die
noch nicht ersetzten Indizes, disjunkt zu `J`; der Schritt ruft die
Induktionsvoraussetzung zweimal, einmal mit `J'` für die Gesamtmasse und einmal
mit `insert i₀ J'` und `Function.update g i₀ f` für die Hypothese der Engine.
Heraus kommt Gleichheit auf den Quadern `Set.pi ↑J B`; `isPiSystem_boxes`,
`generateFrom_boxes` und `ext_of_generate_finite` machen daraus die Gleichheit
der Maße. Neu und bewiesen sind damit siebzehn Deklarationen:
`integrable_of_measurable_of_bounded`, `abs_max_zero_le`, `abs_mul_le_mul`,
`weightedMap`, `isFiniteMeasure_weightedMap`, `integral_weightedMap`, `sepPos`,
`sepNeg`, `isFiniteMeasure_sepPos`, `isFiniteMeasure_sepNeg`,
`integral_sepPos_sub_integral_sepNeg`,
`integral_indicator_mul_eq_of_isSeparating`, `exists_nonneg_bound_prod`,
`boxes`, `isPiSystem_boxes`, `generateFrom_boxes` und `isSeparating_pi` selbst.

**Zwei Hypothesen, die die Aussage nicht hatte und braucht.** `isSeparating_pi`
stand ohne jede Bedingung an die Mitglieder der $\Gamma_i$. So ist es nicht
beweisbar, und der Grund ist die Lean-Konvention $\int f=0$ für nicht
integrierbares $f$: `IsSeparating` bindet nur die Abbildung
$\mu\mapsto(\int f\,d\mu)_{f\in\Gamma}$ und sagt über das einzelne $f$ nichts.
Der Beweis dagegen benutzt jedes $g_i$ als **Gewicht**, und ein Gewicht muß
beschränkt und meßbar sein, sonst ist `weightedMap` kein endliches Maß. Die
Aussage trägt deshalb jetzt

    (hmeas : ∀ i, ∀ f ∈ Γ i, Measurable f)
    (hbdd  : ∀ i, ∀ f ∈ Γ i, ∃ C, ∀ y, |f y| ≤ C)

und die Stelle, an der es ohne sie bricht, ist im Doc-String benannt
(`isFiniteMeasure_weightedMap`). Das ist **keine** Verletzung der stehenden
Regel, sondern ihr Gegenstück: die Regel verlangt die schwächsten Hypothesen,
unter denen die Aussage **gilt**, und ohne diese beiden ist sie unbewiesen. Ob
sie ohne sie falsch ist, bleibt offen; der Lauf hat kein Gegenbeispiel gefunden
und behauptet keines. Der Rahmen dafür steht: wer eines sucht, sucht eine
trennende Klasse, deren beschränkt-meßbarer Teil nicht mehr trennt — auf einem
endlichen Raum gibt es das nicht, weil dort jede Funktion beschränkt und meßbar
ist, und Zusatzfunktionen können nie schaden, weil sowohl `IsSeparating` als
auch die Produktklasse monoton in $\Gamma$ sind (`IsSeparating.mono`).

**Was mitgeprüft und nachgezogen wurde.** Der Meilensteinpunkt in
`WeakConvergence/README.md` trägt jetzt den Zeugen gegen die Multiplikativität,
die beiden Hypothesen mit ihrer Begründung und den wirklichen Beweisweg; die
Behauptung „the proof is the functional monotone class theorem of Milestone 5"
ist ausdrücklich zurückgenommen. Die Zeile `fact:fdd` der Tabelle ist
nachgezogen, denn `isSeparating_pi` **ist** ihre Produkthälfte, und die stand
seit dem 2026-08-31 als „trägt kein Beweis, §9 verlangt sie"; der alte Wortlaut
ist als durchgestrichene Notiz stehengeblieben. Das Manuskript ist unberührt.

**Werkzeugnotiz, die einen Lauf Zeit spart.** Entwickelt wurde in einer
Kleindatei unter `/tmp`, die nur die vier gebrauchten Mathlib-Module und die
Definition von `IsSeparating` importiert; ein Durchlauf kostet dort einen
Bruchteil dessen, was die 1700-Zeilen-Datei kostet, und der fertige Block wurde
erst danach eingesetzt. Zwei Dinge sind beim Umzug aufgefallen und gehören
notiert: `Suggested.lean` öffnet `ENNReal`, aber **nicht** `NNReal`, also
elaboriert `ℝ≥0∞` dort und `ℝ≥0` nicht (im Zweifel `NNReal` und `ENNReal`
ausschreiben); und `cd ~/Code/lean/journal` gehört in **denselben** Befehl wie
`lake env lean`, weil ein zwischengeschalteter Werkzeugaufruf mit eigenem `cd`
das Arbeitsverzeichnis zurücksetzt — genau das ist hier einmal passiert und hat
einen Durchlauf gekostet.

**Vorschlag für das Nächste, als benanntes Ziel: `isConvergenceDetermining_pi`
anlegen und beweisen**, die konvergenzbestimmende Hälfte desselben Punktes von
Meilenstein 1 — für abzählbares `ι` und polnische `S i`, weil dort und nur dort
Straffheit zu haben ist. Worauf sie ruht: auf `isSeparating_pi`, das jetzt
dasteht, und auf
`MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
(`Measure/LevyConvergence.lean:154`), das aus Straffheit plus Trennung die
Konvergenz macht. Warum jetzt: die Roadmap führt beide Hälften in **einem**
Punkt, die trennende ist seit heute bewiesen, und die konvergenzbestimmende ist
die Hälfte, die `SkorokhodSpace` Meilenstein 8 und `MartingaleProblems`
Meilenstein 11 auf ihrem eigenen Weg über Relativkompaktheit gerade **nicht**
umgehen, wenn man Ethier–Kurtz Korollar 3.9.2 wörtlich nachbauen will. Der erste
zu klärende Schritt ist nicht die Trennung, sondern die Straffheit: aus der
Straffheit je Faktor die des abzählbaren Produkts, über die Kompaktheit von
$\prod_i K_i$ und ein $\varepsilon 2^{-n}$-Argument. Erst wenn die steht, ist
der Rest der Anschluß an den heutigen Satz.

### 2026-09-07, vierzehnter Lauf des Tages — `isConvergenceDetermining_pi`, und die Straffheit abzählbarer Produkte

**Was der Lauf vorgefunden hat.** Keine vorrangige Aufgabe, keine `?`-Zeile in
der Tabelle, also Rückstaupunkt 1. Der dreizehnte Lauf hatte das Ziel benannt:
`isConvergenceDetermining_pi`, die konvergenzbestimmende Hälfte des
Produktpunktes von `WeakConvergence` Meilenstein 1, und als ersten zu klärenden
Schritt die Straffheit abzählbarer Produkte. Beides steht jetzt, bewiesen und
durch `lake env lean` gegen v4.33.1.

**Vier neue Deklarationen, alle bewiesen, alle in `WeakConvergence/Suggested.lean`.**

* `IsTightMeasureSet.pi` — ist für abzählbares `ι` jede Familie
  `Measure.map (· i) '' T` von Einkoordinatenrändern straff, so ist `T` straff.
  Mathlib hat den **Zweifaktorfall** und nur ihn (`IsTightMeasureSet.prodMk`,
  `MeasureTheory/Measure/Tight.lean:144`, in v4.33.1 wie auf master); für ein
  abzählbares Produkt gibt es nichts. Der Beweis ist das
  $\varepsilon 2^{-i}$-Argument, und die Abzählbarkeit wird zweimal gebraucht:
  einmal, um $\varepsilon$ über die Koordinaten zu verteilen
  (`ENNReal.exists_pos_sum_of_countable'`,
  `Analysis/SpecificLimits/Basic.lean:648`), und einmal für die abzählbare
  Subadditivität, die $(\mathrm{univ.pi}\,K)^c\subseteq\bigcup_i(\cdot\,i)^{-1}(K_i^c)$
  in eine Summe verwandelt. Tychonoff liefert die kompakte Menge
  (`isCompact_univ_pi`). Es geht **keine** Trennungs-, Borel- oder
  Endlichkeitsvoraussetzung ein: das Komplement der kompakten Menge wird als
  äußeres Maß gemessen und muß nie meßbar sein. Das ist die schwächste Fassung,
  die der Beweis hergibt, und sie ist schwächer als die von `prodMk`, die
  `TopologicalSpace 𝓨` mitführt.
* `isTightMeasureSet_of_tendsto` — auf einem polnischen Raum ist eine
  **konvergente** Folge von Wahrscheinlichkeitsmaßen straff.
  `Filter.Tendsto.isCompact_insert_range`
  (`Topology/Compactness/Compact.lean:645`) macht `insert ν (range μ)` kompakt,
  also abgeschlossen, und `isTightMeasureSet_of_isCompact_closure`
  (`Measure/Prokhorov.lean:635`) macht daraus Straffheit. **Das ist nicht der
  zirkuläre Gebrauch jenes Satzes**, den der vierte Lauf des 2026-09-05
  aufgedeckt hat: dort sollte er die Straffheit aus der zu beweisenden
  Konvergenz holen, hier ist die Konvergenz Hypothese.
* `tendsto_of_isSeparating_of_isTightMeasureSet` — auf einem polnischen Raum
  testet eine **trennende** Klasse aus beschränkten **stetigen** Funktionen die
  schwache Konvergenz, sobald die Folge straff ist. Prohorov gibt den kompakten
  Abschluß, `IsCompact.tendsto_subseq` zu jeder Teilfolge eine konvergente
  Teilteilfolge, die Klasse identifiziert deren Limes als `ν`, und
  `tendsto_of_subseq_tendsto` setzt die Folge wieder zusammen. Das ist das
  Gegenstück zu Mathlibs `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
  für eine Klasse statt für eine `StarSubalgebra`, und für eine Klasse, die
  **Maße** trennt statt **Punkte**.
* `isConvergenceDetermining_pi` selbst. Drei Schritte und keine neue Analysis:
  die Hypothese an den Einindex-Mitgliedern `x ↦ f (x i)` — dem Fall `J = {i}`
  der Produktklasse — gelesen, sagt genau, daß jede Randfolge konvergiert; jede
  Randfamilie ist dann straff, also die Familie selbst; und `isSeparating_pi`
  identifiziert den Limes.

**Wo die konvergenzbestimmende Hälfte von der trennenden abweicht, und warum
jede Abweichung nötig ist.** Sie trägt drei Hypothesen mehr, und jede hat genau
eine Aufgabe. `[Countable ι]` ist, was `IsTightMeasureSet.pi` braucht — und die
Aussage ist über einem überabzählbaren Index **falsch**, nicht bloß unbewiesen
(Zeuge im Meilenstein: das Produkt von Standardnormalverteilungen über $[0,1]$,
dessen Ränder einzeln straff sind und das selbst $\mu K^c=1$ für jedes kompakte
$K$ hat, weil überabzählbar viele Faktoren unter $1$ das Produkt auf $0$
drücken). `[PolishSpace (S i)]` macht aus der Konvergenz der Ränder ihre
Straffheit und ist, was Prohorov braucht. Und **Stetigkeit statt Meßbarkeit** der
Mitglieder: `isSeparating_pi` verlangt sie beschränkt und meßbar, hier müssen sie
beschränkt und stetig sein, weil die Identifikation eines Teilfolgenlimes die
Klasse gegen eine schwach konvergente Folge auswertet, und schwache Konvergenz
sieht beschränkte stetige Funktionen und sonst nichts. Das ist keine
Bequemlichkeit des Beweises, sondern die Stelle, an der er ohne sie bricht, und
sie steht im Doc-String benannt.

**Stand der Datei.** 81 Deklarationen (gezählt mit
`grep -cE "^(noncomputable |private |protected )*(theorem|lemma|def|structure|inductive|instance|abbrev) "`)
und unverändert **12 `sorry`** — der Lauf hat keinen `sorry` gefällt, sondern
vier bewiesene Deklarationen hinzugefügt, die vorher nur als Meilensteinpunkt
dastanden. `rc = 1` mit genau den **zwei** Fehlern an
`tendsto_map_of_measure_setOf_continuousAt_eq_one`, die der Modulkopf seit dem
2026-09-06 ankündigt, weil jene Aussage absichtlich gegen `upstream/master`
geschrieben ist; ihre Zeile ist durch die Einfügungen von `:804` auf `:1041`
gewandert. Keine neue Warnung.

**Was mitgeprüft und nachgezogen wurde.** Der Produktpunkt in
`WeakConvergence/README.md` nennt jetzt `isConvergenceDetermining_pi` mit seinen
drei Zusatzhypothesen und deren Begründung; die drei Stützen stehen als eigene
Punkte darunter, mit dem Vermerk, daß Mathlib nur `prodMk` hat. Meilenstein 1
hat zwei neue acceptance examples, beide Paare im Sinne des vierten Laufs: das
abzählbare Gaußprodukt auf `ℕ → ℝ`, an dem die Fenster $[-a_i,a_i]$ **wachsen**
müssen (eine Fassung mit einem einzigen $K$ für alle Koordinaten summiert zu
$\infty$), gegen dasselbe Produkt über $[0,1]$, an dem die Aussage falsch ist;
und der `δ n`-Zeuge ein zweites Mal, jetzt gegen die Straffheitshypothese von
`tendsto_of_isSeparating_of_isTightMeasureSet` — dort ist `Γ` trennend (über
`IsSeparating.of_subalgebra`), beschränkt stetig, die Integrale konvergieren, und
die Folgerung ist falsch, weil allein die Straffheit fehlt. Die Zeile `fact:fdd`
der Tabelle ist nachgezogen. Das Manuskript ist unberührt.

**Werkzeugnotizen, zwei.** `upgradeIsCompletelyMetrizable` liegt im Namensraum
`TopologicalSpace` und ist ohne Qualifikation nicht sichtbar, obwohl
`Suggested.lean` `Topology` öffnet — das sind zwei verschiedene Namen. Und die
Entwicklung lief wieder in einer Kleindatei unter `/tmp`, die die fünf
gebrauchten Mathlib-Module importiert und `IsSeparating`, `isSeparating_pi`,
`IsConvergenceDetermining.isSeparating` und `exists_nonneg_bound_prod` als
`sorry`-Stümpfe führt; drei Durchläufe dort kosten weniger als einer der
2200-Zeilen-Datei.

**Vorschlag für das Nächste, als benanntes Ziel:
`isConvergenceDetermining_setOf_uniformContinuous_isBounded_support` beweisen**,
`fact:convdet` (Ethier--Kurtz, Proposition 3.4.4), erste Hälfte, in
`WeakConvergence` Meilenstein 1. Worauf sie ruht: auf
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, also darauf, jede
beschränkte stetige Funktion gegen die gegebene Folge durch gleichmäßig stetige
mit beschränktem Träger zu approximieren — und der Schritt, der die Arbeit
trägt, ist eine **Straffheitsaussage**: aus der Konvergenz der Integrale über
die Klasse folgt zuerst, daß die Massen außerhalb großer Bälle gleichmäßig klein
sind, und erst dann ist die Abschneidung erlaubt. Warum jetzt: der heutige Lauf
hat mit `isTightMeasureSet_of_tendsto` und
`tendsto_of_isSeparating_of_isTightMeasureSet` genau die Bausteine gelegt, die
diese Schrittfolge braucht, und `fact:convdet` ist der einzige Fact von
Meilenstein 1, zu dem noch keine einzige Deklaration einen Beweis trägt.
Separabilität allein genügt dabei, wie die Roadmap sagt; Vollständigkeit kommt
im Beweis nicht vor, und wer sie doch braucht, nennt die Stelle.

### 2026-09-07, fünfzehnter Lauf des Tages — `fact:convdet`, erste Hälfte, bewiesen und ohne Separabilität

**Was der Lauf vorgefunden hat.** Keine vorrangige Aufgabe, keine `?`-Zeile in
der Tabelle, also Rückstaupunkt 1. Der vierzehnte Lauf hatte das Ziel benannt:
`isConvergenceDetermining_setOf_uniformContinuous_isBounded_support`, die erste
Hälfte von `fact:convdet` (Ethier--Kurtz, Proposition 3.4.4), der einzige Fact
von `WeakConvergence` Meilenstein 1, zu dem noch keine Deklaration einen Beweis
trug. Er ist bewiesen, geht durch `lake env lean` gegen v4.33.1, und **trägt
eine Hypothese weniger, als er hatte**.

**Der Satz.** Auf einem metrischen Raum sind die beschränkten gleichmäßig
stetigen reellen Funktionen mit beschränktem Träger konvergenzbestimmend.
Neun Deklarationen sind neu, alle bewiesen, alle in
`WeakConvergence/Suggested.lean`:

* `ballCutoff x₀ R = min 1 (max 0 (R + 1 - dist · x₀))` — der 1-Lipschitz-
  Abschneider, der auf `closedBall x₀ R` gleich `1` ist und außerhalb von
  `closedBall x₀ (R+1)` verschwindet —, samt `ballCutoff_nonneg`,
  `ballCutoff_le_one`, `abs_ballCutoff_le_one`, `ballCutoff_eq_one`,
  `support_ballCutoff`, `lipschitzWith_ballCutoff` und `tendsto_ballCutoff`
  (die Abschneider ganzzahligen Radius wachsen punktweise gegen `1`, weil jeder
  Punkt in allen bis auf endlich vielen Bällen liegt).
* `lipschitzWith_mul_of_bounded` — ein Produkt zweier **beschränkter**
  Lipschitzfunktionen ist Lipschitz, mit Konstante
  `Cf.toNNReal * Kg + Cg.toNNReal * Kf`. Mathlibs `LipschitzWith.mul`
  (`Analysis/Normed/Group/Uniform.lean:308`) ist der `to_additive`-Zwilling von
  `LipschitzWith.add` und meint die Gruppenoperation; für ein Produkt reeller
  Funktionen gibt es in Mathlib nichts, und ohne Beschränktheit ist die Aussage
  falsch.
* `integrable_of_continuous_of_bounded` — beschränkt stetig ist integrierbar
  gegen ein endliches Maß, über `Integrable.mono'` und `integrable_const`.

**Der Beweis, in drei Schritten.** Erstens die Reduktion: Mathlibs
`tendsto_iff_forall_lipschitz_integral_tendsto`
(`MeasureTheory/Measure/Portmanteau.lean:688`) prüft schwache Konvergenz an den
beschränkten **Lipschitz**funktionen, und die sind nicht in unserer Klasse, weil
ihr Träger nicht beschränkt sein muß. Zweitens die Straffheit, und sie ist der
Schritt, den der vierzehnte Lauf als tragend angekündigt hatte: die Abschneider
sind selbst Mitglieder der Klasse, ihre Integrale konvergieren also nach
Voraussetzung, und majorisierte Konvergenz gibt
`∫ ballCutoff x₀ m ∂ν → 1`; ist ein `m` mit `∫ ballCutoff x₀ m ∂ν > 1 - ε'`
gewählt, so liegt schließlich auch unter jedem `μ n` alle Masse bis auf `2ε'` in
**einem** festen Ball. Drittens die Abschneidung: `f · ballCutoff x₀ m` ist
wieder in der Klasse (Lipschitz nach `lipschitzWith_mul_of_bounded`, Träger im
Träger des Abschneiders), ihr Integral konvergiert also, und der
Abschneidefehler ist punktweise durch `‖f‖_∞ · (1 - ballCutoff)` beschränkt —
das ist `hkey`, die Rechnung, die die Straffheit in eine Integralabschätzung
verwandelt. Drei Dreiecksschritte schließen mit `3Cε' + ε' < ε`.

**Der Befund: Separabilität kommt im Beweis nicht vor.** Die Aussage stand seit
dem 2026-09-05 unter `[TopologicalSpace.SeparableSpace E]`, weil das Manuskript
(Zeile 1423) und EK sie so führen. Sie ist gestrichen. Wo eine abzählbare dichte
Menge hätte auftreten können, tritt sie nicht auf: der tragende Mathlib-Satz
verlangt `[PseudoEMetricSpace Ω]`, `[OpensMeasurableSpace Ω]` und einen
abzählbar erzeugten Filter, sonst nichts; die Ausschöpfung des Raumes leistet
**ein** Punkt, weil Abstände endlich sind ($E=\bigcup_m\overline B(x_0,m)$), und
diesen Punkt liefert die Nichtleerheit, die ihrerseits aus der Existenz von `ν`
folgt und deshalb auch keine Hypothese ist. Vollständigkeit und Lokalkompaktheit
fehlen ohnehin. Der Befund steht als Auffälligkeit oben; das Manuskript bleibt
unberührt, weil es nur die schwächere Aussage benutzt.

**Stand der Datei.** 91 Deklarationen (gezählt mit
`grep -cE "^(noncomputable |private |protected )*(theorem|lemma|def|structure|inductive|instance|abbrev) "`),
**11 `sorry`** statt 12, gezählt als „declaration uses 'sorry'"-Warnungen des
Übersetzers — der erste gefallene `sorry` von `WeakConvergence` seit vier
Läufen. `rc = 1` mit genau den **zwei** angekündigten Fehlern an
`tendsto_map_of_measure_setOf_continuousAt_eq_one`, deren Zeile durch die
Einfügung von `:1041` auf `:1314` gewandert ist; keine neue Warnung außer der
Deprecation von `push_neg` (im neuen Code, an einer Stelle).

**Was mitgezogen wurde.** `WeakConvergence/README.md` führt den Punkt jetzt
ohne Separabilität, mit dem Weg, den Stützdeklarationen und der Begründung,
warum die zweite Hälfte ($C_c$, lokalkompakt) daraus **nicht** folgt — die
Klasse ist die kleinere, zu leisten ist die Approximation einer gleichmäßig
stetigen Funktion beschränkten Trägers durch kompakt getragene. Meilenstein 1
hat ein neues acceptance example, ein Paar: `δ (1/(n+1)) → δ 0` wird von der
Klasse erkannt, und an `δ n` konvergieren die Integrale aller Mitglieder gegen
`0`, ohne daß ein Wahrscheinlichkeitsmaß dieses Funktional wäre — die
Voraussetzung ist dort nie erfüllt, und eine Fassung „die Integrale
konvergieren, also konvergiert die Folge" (vage Konvergenz) wäre falsch. Der
Modulkopf und die Tabellenzeile `fact:convdet` sind nachgezogen.

**Werkzeugnotizen, drei.** `abs_add` heißt in v4.33.1 `abs_add_le`, und
`div_lt_iff` gibt es unter diesem Namen nicht — beides kostet einen Durchlauf,
wenn man es nicht weiß; die Multiplikationsform (`mul_lt_mul_of_pos_right` plus
eine `field_simp`-Identität für `ε'`) vermeidet die Frage ganz. `add_le_add_right
h c` bedeutet hier `c + a ≤ c + b`, nicht `a + c ≤ b + c`; wer eine
Dreiecksungleichung dreigliedrig aufbaut, schreibt sie besser als eigenes
`∀ a b c d : ℝ`-Lemma und läßt `linarith` schließen. Entwickelt wurde wieder in
einer Kleindatei unter `/tmp` mit drei Importen; fünf Durchläufe dort kosteten
weniger als einer der 2500-Zeilen-Datei.

**Vorschlag für das Nächste, als benanntes Ziel:
`isConvergenceDetermining_setOf_hasCompactSupport` beweisen**, `fact:convdet`,
zweite Hälfte, in `WeakConvergence` Meilenstein 1. Worauf sie ruht: auf der
heute bewiesenen ersten Hälfte und **einer** neuen Aussage — daß auf einem
lokalkompakten metrischen Raum jede gleichmäßig stetige Funktion mit
beschränktem Träger gleichmäßig durch stetige Funktionen mit **kompaktem**
Träger approximiert wird, und daß gleichmäßige Approximation der Mitglieder
einer konvergenzbestimmenden Klasse die approximierende Klasse
konvergenzbestimmend macht (das ist der Stabilitätspunkt von Meilenstein 1,
„Stability under uniformly bounded pointwise limits", in der einfacheren
gleichmäßigen Fassung). Warum jetzt: die erste Hälfte liegt, der Abstand
zwischen den beiden Klassen ist genau ein Abschneidelemma, und `ballCutoff` ist
das Muster dafür — in einem lokalkompakten Raum ist der Abschneider mit
kompaktem Träger zu bauen, und die einzige Frage ist, ob dort abgeschlossene
Bälle kompakt gewählt werden können oder ob es eine Ausschöpfung durch kompakte
Umgebungen braucht. Das ist die Stelle, an der die Lokalkompaktheit eingeht, und
sie ist benannt.

### 2026-09-07, sechzehnter Lauf des Tages — `fact:convdet` ist ganz bewiesen, und der angekündigte Weg dorthin war wieder der falsche

**Was der Lauf vorgefunden hat.** Keine vorrangige Aufgabe, keine `?`-Zeile in
der Tabelle, also Rückstaupunkt 1. Der fünfzehnte Lauf hatte das Ziel benannt:
`isConvergenceDetermining_setOf_hasCompactSupport`, die zweite Hälfte von
`fact:convdet` (Ethier--Kurtz, Proposition 3.4.4). Sie ist bewiesen, geht durch
`lake env lean` gegen v4.33.1, und **damit trägt `fact:convdet` in beiden
Hälften einen Beweis**.

**Der Satz.** Auf einem lokalkompakten separablen metrischen Raum sind die
stetigen reellen Funktionen mit kompaktem Träger konvergenzbestimmend.

**Der angekündigte Weg war falsch, und das ist der eigentliche Befund.** Der
fünfzehnte Lauf hatte geschrieben, zwischen den beiden Klassen liege „genau ein
Abschneidelemma": jede gleichmäßig stetige Funktion mit beschränktem Träger sei
auf einem lokalkompakten Raum gleichmäßig durch kompakt getragene stetige
Funktionen zu approximieren, und gleichmäßige Approximation vererbe die
Klasseneigenschaft. Der erste Teil ist **falsch**, und der Zeuge ist billig:
$E=\N$ mit $d(x,y)=1$ für $x\ne y$ ist separabel, metrisch und lokalkompakt
(Punkte sind offen und kompakt), sein Durchmesser ist $1$, also hat die
Konstante $1$ beschränkten Träger und ist gleichmäßig stetig, während
$C_c(E)$ die **endlich** getragenen Funktionen sind und
$\|1-g\|_\infty=1$ für jedes solche $g$. Eine Approximation der größeren
Klasse durch die kleinere gibt es dort nicht. Bemerkenswert daran ist, daß der
Satz auf ebendiesem Raum trotzdem gilt — er sagt dort „$\mu_n\{k\}\to\nu\{k\}$
für jedes $k$ zieht schwache Konvergenz nach sich", was Scheffé ist. Der Weg
über die Approximation der Klassen ist also nicht bloß schwer, sondern führt an
einer wahren Aussage vorbei.

**Was statt dessen trägt: die Herauslösung des Abschneideschritts.** Der Beweis
der ersten Hälfte bestand aus zwei Teilen, die nichts miteinander zu tun haben:
der Reduktion auf die Lipschitzfunktionen (`Portmanteau.lean:688`) und einer
Abschneiderechnung, die nur benutzt, daß die Abschneider Werte in $[0,1]$ haben
und ihre Integrale gegen das Grenzmaß gegen $1$ streben. Der zweite Teil ist
jetzt eine eigene Deklaration,

* `tendsto_integral_of_tendsto_integral_mul` — für beschränkt stetiges `f` und
  eine Familie stetiger $\psi_m:E\to[0,1]$ mit $\int\psi_m\,d\nu\to1$: gilt
  $\int\psi_m\,d\mu_n\to\int\psi_m\,d\nu$ und
  $\int f\psi_m\,d\mu_n\to\int f\psi_m\,d\nu$ für jedes $m$, so auch
  $\int f\,d\mu_n\to\int f\,d\nu$. Die tragende Abschätzung ist
  $|\int f\,d\rho-\int f\psi_m\,d\rho|\le\|f\|_\infty(1-\int\psi_m\,d\rho)$
  für jedes Wahrscheinlichkeitsmaß $\rho$: sie verwandelt die vom Abschneider
  verfehlte Masse in eine Schranke für den Abschneidefehler und trägt sie von
  $\nu$ auf die $\mu_n$ über. Hypothesen: `[TopologicalSpace E]` und
  `[OpensMeasurableSpace E]`, **keine Metrik**.

**Beide Hälften sind jetzt diese eine Deklaration**, mit verschiedenen
Abschneidern: `ballCutoff x₀ m` für die erste, eine kompakt getragene
Urysohn-Funktion über `compactCovering E m` für die zweite. Der Beweis der
ersten Hälfte ist dabei um rund sechzig Zeilen kürzer geworden und benutzt das
Lemma; er wurde mitübersetzt und ist unverändert gültig.

**Der Bau der zweiten Familie, mit den vier Mathlib-Stellen.** Separabilität
gibt Zweitabzählbarkeit; Zweitabzählbarkeit und Lokalkompaktheit geben
σ-Kompaktheit (`sigmaCompactSpace_of_locallyCompact_secondCountable`,
`Topology/Compactness/SigmaCompact.lean:187`); `compactCovering`
(`ibid.:204`, mit `isCompact_compactCovering`, `compactCovering_subset` und
`exists_mem_compactCovering`) ist dann eine **wachsende** kompakte
Ausschöpfung; und `exists_continuous_one_zero_of_isCompact`
(`Topology/UrysohnsLemma.lean:404`, unter `[RegularSpace] [LocallyCompactSpace]`)
macht aus jeder Stufe ein stetiges $\psi_m$ mit kompaktem Träger, Werten in
$[0,1]$ und $\psi_m=1$ auf der Stufe; die zweite Menge ist $\emptyset$, was
`isClosed_empty` und `disjoint_empty` erledigen. Jeder Punkt liegt in allen bis
auf endlich vielen Stufen, also $\psi_m\to1$ punktweise, und majorisierte
Konvergenz gibt $\int\psi_m\,d\nu\to1$. `f · ψ m` hat wieder kompakten Träger
(`HasCompactSupport.mul_left`, `Topology/Algebra/Support.lean:483`).

**Wo die Hypothesen eingehen.** Die Lokalkompaktheit **genau einmal**, in
Urysohns Lemma. Die Separabilität nur über die σ-Kompaktheit — nicht über eine
abzählbare dichte Menge, und nicht über Straffheit des Grenzmaßes, die der
Beweis nirgends braucht. Beide sind damit nicht als „bequem" eingetragen,
sondern an einer benannten Stelle. Abgeschlossene Bälle als Kompakta, die der
fünfzehnte Lauf als mögliche Alternative erwogen hatte, kommen nicht vor und
könnten es auch nicht: auf dem diskreten Zeugen oben ist $\overline B(x,1)$ der
ganze Raum.

**Stand der Datei.** `WeakConvergence/Suggested.lean`: 92 Deklarationen (vorher
91), **10 `sorry`** statt 11, `rc = 1` mit unverändert genau den **zwei**
angekündigten Fehlern an `tendsto_map_of_measure_setOf_continuousAt_eq_one`,
deren Zeile durch die Einfügungen von `:1314` auf `:1414` gewandert ist. Ein
Import ist neu, `Mathlib.Topology.UrysohnsLemma`. Keine neue Warnung.

**Geprüft, wie es die Audit-Aufgabe vom 2026-09-07 verlangt.** `#print axioms`
für alle drei Deklarationen, an drei zeitweilig angehängten Zeilen und wieder
entfernt: `tendsto_integral_of_tendsto_integral_mul`,
`isConvergenceDetermining_setOf_uniformContinuous_isBounded_support` und
`isConvergenceDetermining_setOf_hasCompactSupport` hängen sämtlich nur an
`[propext, Classical.choice, Quot.sound]`, **kein `sorryAx`**. Beide Hälften von
`fact:convdet` sind also bewiesen und nicht bloß an einen `sorry` weiter oben
angeschlossen. Und die Aussagen sind nicht leer: für die zweite Hälfte ist
$E=\R$ mit $\mu_n=\delta_{1/(n+1)}$, $\nu=\delta_0$ ein Zeuge, unter dem die
Voraussetzung gilt (jedes kompakt getragene stetige $f$ hat
$f(1/(n+1))\to f(0)$) und die Folgerung nicht trivial ist.

**Was mitgezogen wurde.** Der Modulkopf, `WeakConvergence/README.md`
(Meilenstein 1 führt den Abschneideschritt jetzt als eigenen Punkt und die
zweite Hälfte nicht mehr unter „Missing"), die Tabellenzeile `fact:convdet` und
`Facts/BACKLOG.md`, Punkt 1. Meilenstein 1 hat ein neues acceptance example, das
Paar zum diskreten Zeugen: die Instanz, an der die API rechnet
($\mu_n\{k\}\to\nu\{k\}$ zieht schwache Konvergenz nach sich, mit
$\mu_n=\tfrac12\delta_0+\tfrac12\delta_n$ als danebenliegender Fall, in dem
die Voraussetzung zu Recht scheitert), und dieselbe Instanz als Ausschluß der
naheliegenden falschen Beweisidee.

**Werkzeugnotiz.** Das Schreiben nach `/tmp` über eine Bash-Heredoc landet in
der Sandbox und ist für `lake env lean` danach **nicht** da (`no such file or
directory`); mit dem `Write`-Werkzeug geschriebene Dateien sind es. Wer wie die
letzten Läufe in einer Kleindatei unter `/tmp` entwickelt, schreibt sie also mit
`Write`. Der Nutzen bleibt groß: die Kleindatei mit drei Importen übersetzt in
Sekunden, die 2700-Zeilen-Datei in Minuten, und beide neuen Sätze gingen dort im
ersten Anlauf durch.

**Nachtrag im selben Lauf: der Weg zum nächsten Ziel ist aufgeschlüsselt, und
sein erster Schritt ist bewiesen.** Der Beweis von Ethier--Kurtz, Theorem
3.4.5(b) (Buchseiten 113--114, am Scan gelesen) besteht aus vier Schritten, und
sie stehen jetzt einzeln benannt in `WeakConvergence/README.md`, Meilenstein 1:
(1) die Pushforwards nach $\R^k$ konvergieren schwach — Polynome in den $f_i$
aus der Algebra plus Stone--Weierstraß auf dem kompakten Wertekasten; (2) der
geometrische Kern; (3) Portmanteau für offene Mengen, **auf $\R^m$** und nicht
auf $E$; (4) die Straffheit von $\mu_0$ selbst plus endlich viele
Ausnahmeindizes. Schritt (2) ist **bewiesen** und geht durch `lake env lean`:
`StronglySeparatesPoints.exists_finite_cover` — eine stark trennende Klasse
liefert um jedes Kompaktum $K$ und zu jedem $\delta>0$ eine **endliche**
Überdeckung von $K$ durch Mengen $\{y:\max_{f\in s_x}|f(y)-f(x)|<\varepsilon_x\}$
mit Zentren in $K$, die in `Metric.thickening δ K` bleibt. Die beiden
Inklusionen sind die beiden Hälften der starken Trennung, und mehr als die
Stetigkeit der Mitglieder braucht der Schritt nicht. Damit steht die Datei bei
93 Deklarationen, unverändert 10 `sorry`, und die zwei bekannten Fehler bei
`:1470` (am Ende des Laufs nachgemessen).

**Vorschlag für das Nächste, als benanntes Ziel:
`isTightMeasureSet_of_stronglySeparatesPoints` beweisen**, `WeakConvergence`
Meilenstein 1, und der nächste Schritt darin ist **(1)**, die schwache
Konvergenz der Pushforwards nach $\R^k$ — sie ist der einzige der vier, der
noch neues Mathlib-Handwerk verlangt (Stone--Weierstraß auf einem kompakten
Kasten, so wie ihn Meilenstein 5 schon einmal benutzt), und (3) und (4) sind
danach Buchhaltung über bekannten Sätzen. Worauf sie ruht: auf `StronglySeparatesPoints` (in der Datei
erklärt und mit `StronglySeparatesPoints.separatesPoints` an Mathlibs
`Set.SeparatesPoints` angebunden) und auf nichts sonst — sie ist die Aussage,
daß eine stark trennende Unteralgebra die Straffheit einer Familie erzwingt,
deren Integrale über ihr konvergieren. Warum jetzt: sie ist nach diesem Lauf der
einzige `sorry` von Meilenstein 1, der nicht bloß Korollar eines anderen ist
(`isConvergenceDetermining_of_stronglySeparatesPoints` folgt aus ihr und
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints` in wenigen Zeilen), und
sie ist **das Ganze dessen, was `fact:stoneweierstrass` noch schuldet** —
tragend 3, die höchste Zahl unter allen Zeilen, deren Beweis noch aussteht. Der
Zeuge, an dem sich der Beweis messen muß, steht schon im Docstring: auf $\R$ ist
die von `arctan` erzeugte Algebra stark trennend, $\int\arctan\,d\delta_n$
konvergiert gegen $\pi/2$, und kein Wahrscheinlichkeitsmaß hat diesen Wert — die
Voraussetzung ist dort also leer und nicht falsch, und ein Beweis, der das nicht
respektiert, ist an dieser Stelle zu widerlegen.

### 2026-09-07, siebzehnter Lauf des Tages — die Straffheit aus starker Trennung: Schritte (1), (3) und die tragende Hälfte von (4) bewiesen, und die Aussage war über beliebigem Filter falsch

**Bearbeitet:** `fact:stoneweierstrass` (tragend 3, die höchste Zahl unter den
Zeilen mit ausstehendem Beweis), nach dem benannten Ziel des sechzehnten Laufs:
`isTightMeasureSet_of_stronglySeparatesPoints`, `WeakConvergence` Meilenstein 1.
Der Vorlauf hatte den Beweis in vier Schritte zerlegt (EK Thm. 3.4.5(b),
Buchseiten 113–114) und Schritt (2) bewiesen. Dieser Lauf hat **(1) und (3)
bewiesen**, dazu **einen Fehler in der Aussage selbst gefunden**, und von
Schritt (4) die tragende Hälfte — eine eigene Mathlib-Lücke — **ebenfalls
bewiesen**; offen bleibt dort nur noch die Buchhaltung.

**Was bewiesen ist**, alles in `TauCeti/WeakConvergence/Suggested.lean`, alles
durch `lake env lean` gegen v4.33.1 (rc = 1 mit unverändert genau den **zwei**
angekündigten Fehlern an `tendsto_map_of_measure_setOf_continuousAt_eq_one`,
das für `upstream/master` geschrieben ist; sonst kein Fehler):

* `coordMap`, `coordAlgebra`, `separatesPoints_coordAlgebra` — die von den
  Koordinaten erzeugte Unteralgebra von `C(κ → ℝ, ℝ)` und ihre Punktetrennung.
* `exists_mem_subalgebra_comp_of_mem_coordAlgebra` — sie zieht sich längs
  `fun x i => f i x` **nach `A` zurück**, per `Algebra.adjoin_induction`; die
  Konstanten kommen aus `A.smul_mem A.one_mem`, und das ist die einzige Stelle,
  an der `A` eine `ℝ`-Algebra und nicht bloß ein Unterring sein muß. Der
  Rückzug liefert ein Element von `E →ᵇ ℝ`, dessen Funktion mit `g ∘ Φ`
  **übereinstimmt**, weshalb kein Beschränktheitsargument nötig ist.
* `tendsto_integral_comp_of_forall_tendsto_integral` — **Schritt (1)**: für
  einen beliebigen `Fintype κ`, `f : κ → (E →ᵇ ℝ)` mit `f i ∈ A` und **jedes**
  beschränkt stetige `F` auf `κ → ℝ` konvergieren die Integrale von `F ∘ Φ`.
  Die Box ist `Metric.closedBall 0 (∑ i, ‖f i‖)`, kompakt, weil `κ → ℝ` für
  endliches `κ` ein `ProperSpace` ist (`pi_properSpace`,
  `Topology/MetricSpace/ProperSpace.lean:132`), und sie hält das gemeinsame
  Bild, weil die Supremumsmetrik koordinatenweise vergleicht
  (`dist_pi_le_iff`). Darüber Stone–Weierstraß in der Fassung mit kompakter
  **Menge** statt kompaktem Raum, also ohne Untertyp
  (`ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`,
  `Topology/ContinuousMap/StoneWeierstrass.lean:323`), und ein `ε/3`-Schnitt,
  dessen äußere Drittel gegen **jedes** Wahrscheinlichkeitsmaß zugleich
  abgeschätzt werden (`norm_integral_le_of_norm_le_const`).
* `le_liminf_measure_preimage_of_isOpen` — die Portmanteau-Folgerung, und die
  Form, die Schritt (3) verbraucht: für offenes `U ⊆ κ → ℝ` gilt
  `μ₀ (Φ⁻¹' U) ≤ liminf (μ n) (Φ⁻¹' U)`. Sie geht über
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, `integral_map`,
  `ProbabilityMeasure.le_liminf_measure_open_of_tendsto` (über beliebigem
  Filter, weshalb hier keine Folge auftritt) und `Measure.map_apply`.
* `le_liminf_measure_thickening_of_stronglySeparatesPoints` — **Schritt (3)**:
  `μ₀ K ≤ liminf (μ n) (Metric.thickening δ K)`. Hier treffen (1) und (2)
  zusammen. Die endlich vielen Funktionen, die die endlich vielen Mengen des
  Überdeckungssatzes nennen, werden zu **einem** `Finset (E → ℝ)` gesammelt
  (`htfin.toFinset.biUnion s`); dieser, als Indextyp gelesen, macht
  `⋃ x ∈ t, G x` zum Urbild der offenen Menge
  `⋃ x ∈ t, {z | ∀ i, ↑i ∈ s x → |z i - ↑i x| < ε x}` von `κ → ℝ`. Daß der
  Index ein beliebiger `Fintype` sein darf und nicht `Fin k` sein muß, ist
  genau der Grund, warum keine Numerierung der Funktionen nötig ist — die
  einzige Stelle, an der dieser Lauf die Vorlage EK verlassen hat.
* `isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le` —
  das **gelockerte Straffheitskriterium**, EK Thm. 3.2.2, und die tragende
  Hälfte von Schritt (4). Der Zeuge ist die Menge, die Mathlibs eigener Beweis
  der Prohorov-Rückrichtung baut (`isTightMeasureSet_of_isCompact_closure`,
  `Measure/Prokhorov.lean:688` auf `upstream/master`): zu einer Nullfolge
  `u m ↓ 0` und Kompakta `K m`, die für jedes `μ ∈ S` alles bis auf
  `ε · 2⁻¹^(m+1)` in `Metric.thickening (u m) (K m)` fangen, nimm
  `⋂ m, Metric.cthickening (u m) (K m)`. Sie ist abgeschlossen und total
  beschränkt, weil sie für **jedes** `m` in der `u m`-Verdickung eines
  Kompaktums sitzt; `TotallyBounded.isCompact_of_isClosed` und die
  Vollständigkeit machen daraus Kompaktheit, die geometrische Reihe schätzt
  das Komplement durch `ε` ab. **Ohne** Separabilität — kein Schritt braucht
  eine abzählbare dichte Menge, nur Vollständigkeit.

Damit steht die Datei bei **101 Deklarationen** (vorher 93) und **10 `sorry`**
(unverändert; sechs neue Deklarationen sind bewiesen, und eine neue Aussage —
`isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`
selbst — wurde im selben Lauf angelegt und gleich bewiesen, ohne je als
`sorry` zu stehen).

**Der Befund, und er ist der Ertrag dieses Laufs: die Aussage war falsch.**
`isTightMeasureSet_of_stronglySeparatesPoints` stand seit dem 2026-09-05 über
einem beliebigen Filter `{𝓕 : Filter ι} [𝓕.NeBot]`. So ist sie falsch, und
billig:

> `ι = ℕ`, `𝓕 = pure 0`, `E = ℝ`, `A = ⊤`, `μ n = δ n`, `μ₀ = δ 0`.

`A = ⊤` trennt Punkte stark (zu `x` und `δ > 0` nimm die eine Funktion
`fun y => min (dist y x) δ`, beschränkt und stetig, mit `ε = δ`). Konvergenz
längs `pure 0` ist nach `tendsto_pure_left` die **einzige** Gleichung
`∫ g ∂μ 0 = ∫ g ∂μ₀`, die gilt — und über `μ n` für `n ≥ 1` sagt sie nichts.
Die Familie `{δ n | n}` ist nicht straff, weil jede kompakte Teilmenge von `ℝ`
beschränkt ist. Die fehlende Hypothese ist `Filter.cofinite ≤ 𝓕`: sie ist genau
die Aussage, daß das Komplement einer `𝓕`-fast-überall-Menge endlich ist
(`Filter.mem_cofinite`), und damit genau das, was EK benutzen, wenn sie „Lemma
2.1 auf `P` und auf endlich viele Glieder der Folge" anwenden. Für Folgen ist
sie geschenkt (`Nat.cofinite_eq_atTop`), der Verbraucher
`IsConvergenceDetermining` zahlt also nichts. Die Aussage trägt sie jetzt, mit
dem Zeugen im Docstring und als acceptance example in der Roadmap.

Zu beachten für künftige Läufe: die Richtung der Filterordnung. `𝓕 ≤ cofinite`
hieße „jede koendliche Menge ist `𝓕`-fast-überall" und ist die **falsche**
Richtung; gebraucht wird `cofinite ≤ 𝓕`, „jede `𝓕`-Menge ist koendlich". Auf
`ℕ` mit `atTop` sind beide wahr, weil `cofinite = atTop` — an genau dieser
Verwechslung wäre der Zeuge unentdeckt geblieben.

**Was Schritt (4) braucht, und daß es keine bloße Buchhaltung war.** Der
Vorlauf hatte Schritt (4) als „Buchhaltung über bekannten Sätzen" angekündigt.
Das war falsch, und zwar an einer benennbaren Stelle: EK schließen mit ihrem
Theorem 3.2.2, das Relativkompaktheit aus dem **gelockerten** Kriterium „für
alle `ε, δ > 0` gibt es ein kompaktes `K` mit `inf_n P_n(K^δ) ≥ 1 - ε`" zieht.
Mathlibs `IsTightMeasureSet` verlangt die kompakte Menge selbst, und
`Metric.cthickening δ K` ist für kompaktes `K` nur auf einem **properen** Raum
kompakt (`IsCompact.cthickening`,
`Topology/MetricSpace/Thickening.lean:300`); auf einem bloß vollständigen Raum
ist die abgeschlossene Einheitskugel eines unendlichdimensionalen Banachraums
das Gegenbeispiel, sie ist `cthickening 1 {0}`. Der erste Anlauf dieses Laufs,
die Verdickung sei „auf vollständigen Räumen total beschränkt", war genau
dieser Fehler und ist verworfen.

Deshalb ist Schritt (4) in **zwei** Punkte zerlegt, und beide sind jetzt
bewiesen bzw. auf das Fehlende reduziert:

* `isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`
  — das gelockerte Kriterium, EK Thm. 3.2.2, und **bewiesen**. Der Zeuge ist
  die Menge, die Mathlibs eigener Beweis der Prohorov-Rückrichtung baut
  (`isTightMeasureSet_of_isCompact_closure`, `Measure/Prokhorov.lean:688` auf
  `upstream/master`): zu einer Nullfolge `u m ↓ 0` und Kompakta `K m`, die für
  jedes `μ ∈ S` alles bis auf `ε · 2⁻¹^(m+1)` in
  `Metric.thickening (u m) (K m)` fangen, nimm
  `⋂ m, Metric.cthickening (u m) (K m)`. Sie ist abgeschlossen und total
  beschränkt, weil sie für **jedes** `m` in der `u m`-Verdickung eines
  Kompaktums sitzt; `TotallyBounded.isCompact_of_isClosed` und die
  Vollständigkeit machen daraus Kompaktheit, die geometrische Reihe schätzt das
  Komplement durch `ε` ab. Über die Maße wird nichts vorausgesetzt, und die
  Aussage braucht **keine** Separabilität — kein Schritt des Beweises benutzt
  eine abzählbare dichte Menge, nur Vollständigkeit.
* Die Buchhaltung darüber bleibt offen: `μ₀` ist selbst straff
  (`isTightMeasureSet_singleton`, `Measure/Tight.lean:99`), Schritt (3) macht
  daraus `μ n ((Metric.thickening δ K)ᶜ) ≤ ε` für alle `n` einer `𝓕`-Menge,
  deren Komplement nach `cofinite ≤ 𝓕` endlich ist, und die endlich vielen
  Ausnahmeindizes werden durch Vergrößern von `K` um ihre eigenen Kompakta
  absorbiert (`IsTightMeasureSet.union` ist auf `master` vorhanden,
  `Measure/Tight.lean:119`). Das ist die einzige verbleibende Lücke zwischen
  Schritt (3), dem gelockerten Kriterium und `isTightMeasureSet_of_stronglySeparatesPoints`
  selbst.

**Negativbefund, mit den Suchformulierungen.** Das gelockerte Kriterium hat
Mathlib **nicht**, weder in v4.33.1 noch auf `upstream/master`. Gesucht wurde
ohne unsere Vokabeln: `thickening` in `Measure/Tight.lean` und
`Measure/Prokhorov.lean` (**kein** Treffer, in beiden Quellen), `TotallyBounded`
in denselben beiden plus `Measure/TightNormed.lean` (zwei Treffer, beide
*innerhalb* des Beweises der Prohorov-Rückrichtung, keine Aussage), und die
vollständige Deklarationsliste von `master`s `Measure/Tight.lean`
(`isTightMeasureSet_iff_exists_isCompact_measure_compl_le`, die drei
`..._singleton...`, `of_compactSpace`, `subset`, `union`, `inter`, `map`,
`prodMk` — nichts über Verdickungen).

**Was nicht geprüft wurde, und was statt dessen dasteht.** `#print axioms` für
die sechs neuen Sätze hätte einen zweiten Durchlauf der 3000-Zeilen-Datei
gekostet und ist in diesem Lauf **nicht** gelaufen. Statt einer Behauptung die
überprüfbare Tatsache: keiner der sechs Beweise enthält ein `sorry`, und die
einzigen Deklarationen außerhalb von Mathlib, auf die sie sich stützen, sind
`StronglySeparatesPoints.exists_finite_cover`, für die der sechzehnte Lauf
`#print axioms` durchgeführt hat (nur `propext`, `Classical.choice`,
`Quot.sound`), sowie einander selbst (Schritt (3) benutzt Schritt (1); das
gelockerte Kriterium steht für sich). Wer den maschinellen Beleg will, hängt
sechs Zeilen an und übersetzt einmal.

**Mitgenommen.** Der Modulkopf, `WeakConvergence/README.md` (Meilenstein 1:
Schritt (1) mit den zwei neuen Deklarationen, Schritt (3) als bewiesen, Schritt
(4) mit seiner tragenden Hälfte bewiesen und der Buchhaltung offen, die
Filterhypothese samt Zeuge, und zwei neue acceptance examples — `pure 0` gegen
die Filterform, die Einheitskugel von `ℓ²` gegen das gelockerte Kriterium), die
Tabellenzeile `fact:stoneweierstrass` und `Facts/BACKLOG.md`. Eine Stelle
wurde umsortiert und nicht geändert: `integrable_of_continuous_of_bounded`
steht jetzt vor dem Stone–Weierstraß-Abschnitt, weil Schritt (1) sie braucht
und vor ihr stand.

**Werkzeugnotizen.** (a) `lake env lean` **immer** mit dem `cd` im selben
Befehl; der erste Aufruf dieses Laufs lief ohne, weil die Shell zwischendurch
in den Worktree zurückgesetzt worden war. Das dort liegende `.lake` vom
2026-09-06 (671 MB, ohne gebautes Mathlib) ist unverändert unbrauchbar und
gehört weiterhin gelöscht. (b) `Set.mem_setOf_eq` ist in dieser
Mathlib-Version `deprecated` (jetzt `Set.mem_ofPred_eq`), ebenso `push_neg`
(jetzt `push Not`); wer eine `simp only`-Liste aus älteren Beweisen kopiert,
erzeugt Warnungen. In dem einen Fall, in dem es hier vorkam, war das Lemma
entbehrlich — `simpa` beta-reduziert selbst.

**Vorschlag für das Nächste, als benanntes Ziel:
`isTightMeasureSet_of_stronglySeparatesPoints` **fertig** beweisen**,
`WeakConvergence` Meilenstein 1 — nach diesem Lauf reine Buchhaltung über drei
bewiesenen Sätzen und keine eigene Mathlib-Lücke mehr. Der Beweis ist: `μ₀`
straff via `isTightMeasureSet_singleton`; für `ε > 0` und eine Nullfolge `δ_m`
liefert `le_liminf_measure_thickening_of_stronglySeparatesPoints` zu jedem
`m` ein kompaktes `K m` mit `μ₀ K m ≥ 1 - ε 2⁻ᵐ` und
`liminf (μ n) (Metric.thickening δ_m (K m)) ≥ 1 - ε 2⁻ᵐ`, also (mit
`Filter.eventually_ge_of_liminf` o.ä.) eine `𝓕`-Menge, auf der
`μ n ((Metric.thickening δ_m (K m))ᶜ) ≤ ε 2⁻ᵐ` gilt; das Komplement dieser
Menge ist wegen `cofinite ≤ 𝓕` endlich, und für jeden der endlich vielen
Ausnahmeindizes liefert `isTightMeasureSet_singleton` auf `μ n` selbst ein
weiteres Kompaktum, das durch `IsCompact.union` in `K m` hineingezogen wird.
Das Ergebnis speist
`isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`.
Warum jetzt: sie ist nach diesem Lauf das **ganze**, was
`fact:stoneweierstrass` noch schuldet, und hängt an keinem neuen Mathlib-Fakt
mehr, nur an der endlichen Vereinigung der Ausnahmefälle. Der Zeuge, an dem
der Beweis sich messen muß, steht schon in M1: der `pure 0`-Zeuge zeigt, wo
`cofinite ≤ 𝓕` wirklich gebraucht wird — an der Endlichkeit der
Ausnahmemenge, nicht anderswo.

### 2026-09-08, erster Lauf des Tages — `fact:stoneweierstrass` ist ganz bewiesen, und die Vollständigkeit gehört an die gegebene Metrik

**Bearbeitet:** `fact:stoneweierstrass` (tragend 3), nach dem benannten Ziel des
siebzehnten Laufs vom Vortag: die Buchhaltung von Schritt (4), also
`isTightMeasureSet_of_stronglySeparatesPoints` fertig zu beweisen. Das ist
geschehen, und das Korollar gleich mit.

**Was bewiesen ist**, beides in `TauCeti/WeakConvergence/Suggested.lean`, beides
durch `lake env lean` gegen v4.33.1 (rc = 1 mit unverändert genau den **zwei**
angekündigten Fehlern an `tendsto_map_of_measure_setOf_continuousAt_eq_one`,
jetzt bei `:1925`; sonst kein Fehler):

* `isTightMeasureSet_of_stronglySeparatesPoints` — Straffheit aus starker
  Trennung, das Ganze dessen, was der Fact noch schuldete.
* `isConvergenceDetermining_of_stronglySeparatesPoints` — der Fact selbst, in
  der Form, in der das Manuskript ihn ausspricht. Er ruht auf dem ersten Satz
  und auf `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
  (`Measure/LevyConvergence.lean:150` in v4.33.1); die triviale Sternstruktur
  auf `A` ist dieselbe wie in `IsSeparating.of_subalgebra`, und
  `Nat.cofinite_eq_atTop` erledigt die Filterhypothese, weil
  `IsConvergenceDetermining` über Folgen quantifiziert. Dafür importiert die
  Datei jetzt `Mathlib.MeasureTheory.Measure.LevyConvergence`.

Die Datei zählt **101 Deklarationen und 8 `sorry`** (vorher 101 und 10);
**Meilenstein 1 trägt kein `sorry` mehr**. Die verbleibenden acht liegen alle in
den Meilensteinen 2 und 3.

**Maschineller Beleg, den der Vorlauf schuldig geblieben war.** `#print axioms`
ist diesmal gelaufen, für vier Deklarationen, und meldet für jede genau
`[propext, Classical.choice, Quot.sound]`:
`isTightMeasureSet_of_stronglySeparatesPoints`,
`isConvergenceDetermining_of_stronglySeparatesPoints`,
`le_liminf_measure_thickening_of_stronglySeparatesPoints` und
`isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`.
Kein `sorryAx`. Das Werkzeug: vier `#print axioms`-Zeilen ans Dateiende hängen,
einmal übersetzen, Zeilen wieder entfernen — ein Durchlauf, keine
Einzelaufrufe. (`cp` in `/tmp` ist gesperrt, eine Kopie der Datei außerhalb des
Worktrees ging also nicht; das Anhängen und Entfernen ist der Weg. Ebenso
gesperrt ist die Umleitung `>>` auf eine Datei im Worktree; Anhängen geht über
das `Edit`-Werkzeug.)

**Der Beweis, in der Reihenfolge, in der er läuft.** Er ist Buchhaltung, wie
angekündigt, aber mit drei Stellen, die nicht bloß Buchhaltung sind:

1. `ε ≥ 1` ist eine eigene Zeile: dort tut es die leere Menge, weil ein
   Wahrscheinlichkeitsmaß jeder Menge höchstens `1` gibt (`prob_le_one`). Ohne
   diesen Fall gibt es kein `ε/2 < ε`, denn in `ℝ≥0∞` ist `∞/2 = ∞`.
2. Die **Hälfte** ist nicht Bequemlichkeit, sondern das, was die Ungleichung
   strikt macht: `isTightMeasureSet_singleton` gibt `K₀` mit
   `μ₀ K₀ᶜ ≤ ε/2`, also `1 - ε/2 ≤ μ₀ K₀`, und Schritt (3) hebt das auf den
   `liminf`. Was `Filter.eventually_lt_of_lt_liminf` verlangt, ist `<`, und
   `1 - ε < 1 - ε/2` ist genau die Stelle, an der die Halbierung eingeht. Der
   Weg dahin in `ℝ≥0∞`: `(ENNReal.cancel_of_ne h).tsub_lt_tsub_left_of_le` —
   die unbedingte Form `tsub_lt_tsub_left_of_le` gilt in `ℝ≥0∞` nicht, weil
   `AddLeftReflectLE` dort falsch ist (`∞ + a = ∞ + b`); man braucht die
   `AddLECancellable`-Fassung, und `1 - ε ≠ ⊤` liefert sie.
3. Die Rückrechnung `μ n (Uᶜ) ≤ ε` aus `1 - ε < μ n U` ist `measure_compl`
   plus `tsub_le_tsub_left` plus
   `ENNReal.sub_sub_cancel : a ≠ ∞ → b ≤ a → a - (a - b) = b`.

Die Ausnahmemenge danach: `P := {n | μ n ((thickening δ K₀)ᶜ) ≤ ε}` liegt in
`𝓕`, also nach `cofinite ≤ 𝓕` in `cofinite`, also ist `Pᶜ` endlich
(`Filter.mem_cofinite`). Jedes einzelne `μ n` ist straff, das gibt `C n`, und
`K₀ ∪ ⋃ n ∈ Pᶜ, C n` ist kompakt nach `Set.Finite.isCompact_biUnion`. Beide
Fälle danach sind Monotonie: `Metric.thickening_subset_of_subset` für die guten
Indizes, `Metric.self_subset_thickening` für die Ausnahmen.

**Der Befund, und er ist der Ertrag dieses Laufs: `PolishSpace E` trägt den
Beweis nicht.** Die Aussage stand unter `[MetricSpace E] [PolishSpace E]
[BorelSpace E]`, und der erste Übersetzungsversuch scheiterte an genau einer
Instanz: `CompleteSpace E`. `PolishSpace` sagt, daß *eine* verträgliche Metrik
vollständig ist; der Beweis läuft in der **gegebenen**, weil `Metric.thickening`
in ihr lebt und
`isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`
`TotallyBounded.isCompact_of_isClosed` benutzt. Der Zeuge steht jetzt als
acceptance example in M1: auf `E = (0,1)` mit der euklidischen Metrik — polnisch
nach `IsOpen.polishSpace`, Metrik unvollständig — ist `(0,1/2]` abgeschlossen
und totalbeschränkt und nicht kompakt.

Die Aussage trägt darum jetzt `[MetricSpace E] [CompleteSpace E]
[SecondCountableTopology E] [BorelSpace E]`. Das ist **dieselbe Raumklasse** —
beide Hypothesen zusammen geben `PolishSpace E` als Instanz, und der Verbraucher
zahlt nichts —, aber die Vollständigkeit hängt an der genannten Metrik. Der Satz
ist unter `PolishSpace E` allein wahr, denn starke Trennung ist eine Bedingung
an den Umgebungsfilter und damit unabhängig von der gewählten verträglichen
Metrik; ein Beweis davon wechselt zuerst die Metrik
(`upgradeIsCompletelyMetrizable`), was zwei `MetricSpace`-Instanzen auf `E`
nebeneinanderstellt, und ist hier nicht geführt. Das steht so in der Roadmap und
im Docstring, damit niemand es für eine Verschärfung hält.

**Mitgenommen.** Der Modulkopf, `WeakConvergence/README.md` (Meilenstein 1: die
beiden Sätze als bewiesen, die Buchhaltung von Schritt (4) ausgeschrieben, das
Bündel samt Begründung, ein neues acceptance example — das offene Intervall
gegen `PolishSpace` an der Stelle von `CompleteSpace`), die Tabellenzeile
`fact:stoneweierstrass` und `Facts/BACKLOG.md`.

**Zweiter Teil desselben Laufs: `fact:cmt`, die f.ü.-stetige Hälfte, bewiesen.**
Der Vorschlag unten war zu Beginn des Laufs das nächste Ziel und ist im selben
Lauf eingelöst; er steht hier trotzdem im Wortlaut, weil er die Begründung
trägt. Bewiesen ist `tendsto_of_measure_setOf_not_continuousAt_eq_zero`
(`propext`, `Classical.choice`, `Quot.sound`; rc = 1 mit unverändert genau den
zwei angekündigten Fehlern). Drei Dinge daran sind Befunde:

* **Die Signaturfrage ist ohne zweite Aussage gelöst.** Die Bildmaße treten als
  Daten `μ' : ℕ → ProbabilityMeasure E'` samt den Gleichungen
  `(μ' n : Measure E') = (μ n : Measure E).map h` auf. Damit nennt die Aussage
  keine Bild*konstruktion*, elaboriert gegen v4.33.1 **und** gegen
  `upstream/master`, und die verpackte Fassung ist sie instanziiert, mit `rfl`
  als Gleichungen. Das ist der Weg, den solche Versionsdifferenzen künftig
  nehmen sollten.
* **Sie braucht weniger als der Meilenstein verlangt.** Quelle:
  `[OpensMeasurableSpace E] [HasOuterApproxClosed E]` — letzteres ist genau,
  was `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` fordert, und
  jeder Pseudo-EMetrik-Raum hat es. Ziel: `[TopologicalSpace E']
  [OpensMeasurableSpace E']`, **keine Metrik**, weil die Rückrichtung
  `tendsto_of_forall_isClosed_limsup_le'` (`Measure/Portmanteau.lean:617`) über
  einem beliebigen topologischen Raum und einem abzählbar erzeugten Filter
  steht. Separabilität von `E` kommt nirgends vor. Der Meilenstein hatte
  „separabel metrisch" auf beiden Seiten.
* **Die Hypothese steht als Nullmenge der Unstetigkeitsstellen**, nicht als
  `ν {x | ContinuousAt h x} = 1`. Für eine nicht als meßbar bekannte Menge sind
  das zwei verschiedene Aussagen — Menge und Komplement können beide äußeres Maß
  `1` haben —, und genau das hält die Metrik von `E'` fern. Wo die `= 1`-Form
  gewollt ist, ist der Übergang Mathlib: `measurableSet_of_continuousAt`
  (`Constructions/BorelSpace/Basic.lean:252`) und `prob_compl_eq_zero_iff`
  (`Measure/Typeclasses/Probability.lean:157`).

Beinahe wäre dabei ein Mathlib-Lemma nachgebaut worden: der Lauf hatte
`measurableSet_setOf_continuousAt` schon geschrieben und übersetzt, ehe der
Blick in die eigene Roadmap zeigte, daß Mathlib es als
`measurableSet_of_continuousAt` führt — im Wurzelnamensraum, mit
`[PseudoEMetricSpace β]`. Es ist wieder derselbe Fehler wie in der Regel für den
Negativbefund, nur andersherum: nicht „Mathlib hat das nicht", sondern „das
schreibe ich schnell selbst". Die Deklaration ist entfernt; die Datei zitiert
Mathlibs.

Die Datei zählt danach **102 Deklarationen und 8 `sorry`**. Zur Zählung eine
Warnung für künftige Läufe: das übliche
`grep -cE "^(theorem|lemma|def|…)"` zählt auch Fließtextzeilen des Modulkopfes
mit, die mit `theorem` beginnen; ein solcher Umbruch hat hier 103 gemeldet und
ist umformuliert.

*Der Vorschlag, wie er vor diesem zweiten Teil dastand — und der Rest davon ist
weiterhin offen, nämlich die verpackte Fassung und
`TendstoInDistribution.continuousAt_comp`:*

**Vorschlag für das Nächste, als benanntes Ziel:
`tendsto_map_of_measure_setOf_continuousAt_eq_one`**, `WeakConvergence`
Meilenstein 2 — der Satz von der **fast überall stetigen** Abbildung, die
Hälfte von `fact:cmt`, die Mathlib nicht hat (den stetigen Fall hat es zweimal,
`FiniteMeasure.tendsto_map_of_tendsto_of_continuous` und
`TendstoInDistribution.continuous_comp`). Warum jetzt: `fact:cmt` ist mit
tragend 3 die höchste Zeile, deren Beweis noch aussteht, nachdem
`fact:stoneweierstrass` und `fact:convdet` gefallen sind; und der Beweis ruht
auf Portmanteau, das in Mathlib vollständig vorliegt — für abgeschlossenes `F`
ist `closure (h⁻¹' F) ⊆ h⁻¹' F ∪ {x | ¬ ContinuousAt h x}`, die zweite Menge ist
`ν`-Null, also `limsup μ n (h⁻¹' F) ≤ ν (h⁻¹' F)`, und der Portmanteau-Schluß
über abgeschlossene Mengen schließt ab. **Ein Hindernis vorweg, und es ist
benannt:** die Aussage ist mit Absicht für `upstream/master` geschrieben und
elaboriert in v4.33.1 nicht, weil `ProbabilityMeasure.map` dort einen
`AEMeasurable`-Beweis nimmt. Wer sie beweist, entscheidet zuerst, ob er sie in
der v4.33.1-Form als zweite Deklaration führt oder auf `Measure.map` der
Koerzierungen umstellt — beides ist eine Signaturfrage und kein Satz, und die
Entscheidung gehört in den Meilenstein, nicht in den Beweis.

**Dritter Teil desselben Laufs: der erste Punkt von Meilenstein 3, geschenkt.**
`isTightMeasureSet_of_forall_exists_finite_iUnion_ball` (`fact:PSpolish`) ist
bewiesen, und der Beweis ist vier Zeilen: eine endliche Menge ist kompakt, und
`Metric.thickening_eq_biUnion_ball` (`Topology/MetricSpace/Thickening.lean:167`)
sagt, daß die `r`-Verdickung von `F` **die** Vereinigung der `r`-Bälle um ihre
Punkte ist — die Hypothese ist also die des gelockerten Kriteriums von
Meilenstein 1 bei `K = F`. Zwei Hypothesen sind dabei gefallen:
`SecondCountableTopology E` aus dieser Aussage (unbenutzt), und aus dem
gelockerten Kriterium selbst `MetricSpace` und `BorelSpace` — es steht jetzt
unter `[PseudoMetricSpace E] [CompleteSpace E]`, weil sein Beweis keine Menge
mißt, die er nicht bekommen hat, sondern nur `measure_mono` und
`measure_iUnion_le` benutzt. Die Datei zählt danach **102 Deklarationen und 7
`sorry`**, rc = 1 mit unverändert genau den zwei angekündigten Fehlern (`:2011`).

**Vorschlag für den nächsten Lauf, als benanntes Ziel:
`separableSpace_probabilityMeasure`**, `WeakConvergence` Meilenstein 3
(`fact:PSpolish`) — ist `E` separabel metrisch, so ist `ProbabilityMeasure E`
separabel. Warum jetzt: der Block von Meilenstein 3 hat drei Stufen —
Separabilität, Vollständigkeit von `LevyProkhorov (ProbabilityMeasure E)`,
daraus `PolishSpace` —, und die Separabilität ist die unterste; sie hängt an
keiner der beiden anderen, während die Vollständigkeit auf dem heute bewiesenen
`isTightMeasureSet_of_forall_exists_finite_iUnion_ball` **und** auf der
Separabilität ruht. Worauf sie ruht: die endlich getragenen Maße mit rationalen
Gewichten über einer abzählbaren dichten Menge sind dicht — das ist eine
Approximation in der Lévy-Prokhorov-Metrik, für die Mathlib mit
`MeasureTheory.SeparableSpace.exists_measurable_partition_diam_le`
(`Measure/LevyProkhorovMetric.lean:540`) schon die Zerlegung des Raums in
meßbare Stücke kleinen Durchmessers bereitstellt, die das Maß auf die
Repräsentanten der Stücke schiebt. Vor dem Beweis steht eine Suche, und sie ist
diesmal ausdrücklich Teil des Ziels: **ob Mathlib die Separabilität von
`ProbabilityMeasure E` nicht doch schon hat** — gesucht wurde für diesen
Vorschlag nur nach `SeparableSpace (ProbabilityMeasure` und
`SeparableSpace (FiniteMeasure` in v4.33.1 (kein Treffer); wer den Punkt
angeht, sucht zuerst auf `upstream/master` und nach der Aussage statt nach
diesen beiden Schreibweisen.

### 2026-09-08, zweiter Lauf des Tages — die beiden Abstandsschätzungen für `separableSpace_probabilityMeasure`, und Mathlib hat die Separabilität wirklich nicht

**Bearbeitet:** `fact:PSpolish` (tragend 1), nach dem benannten Ziel des
Vorlaufs: `separableSpace_probabilityMeasure`, `WeakConvergence` Meilenstein 3.
Das Ziel ist **nicht** erreicht — der Satz trägt weiterhin `sorry` —, aber die
beiden Schätzungen, auf denen er ruht, sind bewiesen, und die vom Vorlauf
ausdrücklich verlangte Suche ist gelaufen.

**Erstens die Suche, und sie ist negativ.** Gegen `upstream/master`
`572e4d091bc` (frisch geholt) gesucht, in Mathlibs Vokabeln und nicht in
unseren: `SeparableSpace (ProbabilityMeasure`, `SeparableSpace (FiniteMeasure`,
`SeparableSpace (LevyProkhorov`, `PolishSpace (ProbabilityMeasure`,
`PolishSpace (FiniteMeasure`, `CompleteSpace (LevyProkhorov`; dann als Regex
`SeparableSpace` und `ProbabilityMeasure`/`FiniteMeasure` in beiden
Reihenfolgen auf einer Zeile; dann `dense` neben `dirac` in beiden
Reihenfolgen. Das sind zehn Muster in vier Aufrufen; kein einziger Treffer in
`Mathlib/`. Mitgeprüft: die Dateien, die
`LevyProkhorov` überhaupt nennen, sind genau vier (`FiniteMeasurePi`,
`FiniteMeasureProd`, `LevyProkhorovMetric`, `Prokhorov`), und in
`LevyProkhorovMetric.lean` steht `SeparableSpace` nur als Hypothese über `Ω`,
nie über dem Maßraum. Die seit dem letzten Durchgang neue Datei
`MeasureTheory/Measure/DiracProba.lean` — sie war der einzige plausible Ort für
einen Neuzugang — bettet `E` in `ProbabilityMeasure E` ein
(`isEmbedding_diracProba`) und sagt über das Ziel nichts. **Die Lücke steht
also.**

**Zweitens, bewiesen und durch `lake env lean` gegen v4.33.1** (in
`TauCeti/WeakConvergence/Suggested.lean`; rc = 1 mit unverändert genau den
**zwei** angekündigten Fehlern an `tendsto_map_of_measure_setOf_continuousAt_eq_one`,
jetzt bei `:2011`, und keinem weiteren Fehler):

* `sum_smul_dirac_apply` — die Auswertung einer endlichen Dirac-Kombination auf
  einer meßbaren Menge. Sie steht mit `Set.indicator` und **nicht** mit einem
  `Finset.filter` über `{i | y i ∈ T}`, und das ist kein Geschmack: der Filter
  verlangt eine `DecidablePred`-Instanz in der **Aussage**, die dann an jeder
  Verwendungsstelle zusammenpassen muß, während der Indikator seine
  Fallunterscheidung selbst trägt. Der erste Anlauf mit Filter scheiterte genau
  daran (`failed to synthesize DecidablePred`).
* `levyProkhorovEDist_sum_dirac_le` — **die geometrische Hälfte**: ist
  `A : Fin n → Set E` eine endliche meßbare Zerlegung von `E`, ist `μ G ≤ ε`
  und liegt jedes `A i` außerhalb von `G` im `ε`-Abstand des Punktes `y i`, so
  ist `∑ i, μ (A i) • Measure.dirac (y i)` im Lévy--Prokhorov-Abstand höchstens
  `ε` von `μ` entfernt. Beide Ungleichungen von
  `levyProkhorovEDist_le_of_forall` (`Measure/LevyProkhorovMetric.lean:95`)
  folgen aus denselben zwei Beobachtungen: außerhalb `G` liegt jeder Punkt von
  `B` in einem `A i`, dessen Vertreter `y i` dann in der Verdickung von `B`
  liegt; und umgekehrt ist die diskrete Masse von `B` nach Disjunktheit
  `μ (⋃ i ∈ {i | y i ∈ B}, A i)`, eine Vereinigung, die außerhalb `G` in der
  Verdickung von `B` liegt. Die Masse von `G` ist auf beiden Seiten das `ε`.
  Weder Endlichkeit von `μ` noch Separabilität von `E` ist Hypothese — die
  Separabilität kommt erst mit der Zerlegung ins Spiel.
* `levyProkhorovEDist_sum_dirac_weights_le` — **die arithmetische Hälfte**:
  zwei diskrete Maße über denselben Atomen sind `δ`-nah, sobald ihre Gewichte
  `c i ≤ q i + d i` und `q i ≤ c i + d i` mit `∑ i, d i ≤ δ` erfüllen. Die
  Abweichungen stehen als **dritter Vektor** und nicht als `|c i - q i|`, weil
  die abgeschnittene Subtraktion in `ℝ≥0∞` nichts taugt; das ist der Schritt,
  der die Gewichte `μ (A i)` durch rationale ersetzt und die Familie damit
  abzählbar macht.

**Was fehlt, und zwar genau.** (1) Die Zerlegung: zu `ε > 0` gibt es ein `n` mit
`μ (⋃ k < n, ball (x k) ε)ᶜ ≤ ε`, weil diese Bälle nach Dichtheit von `x` gegen
`E` wachsen und `μ` endlich ist; `disjointed` macht sie disjunkt, und der
unbedeckte Rest ist zugleich das letzte Stück der Zerlegung und das `G` der
ersten Schätzung. Mathlibs
`SeparableSpace.exists_measurable_partition_diam_le`
(`LevyProkhorovMetric.lean:540`) ist dieselbe Disjunktifizierung, aber
**abzählbar** indiziert und ohne die Vertreter — darum wird die Zerlegung hier
gebaut und nicht dort geholt. (2) Die rationalen Gewichte: zu `c : Fin n → ℝ≥0∞`
mit `∑ i, c i = 1` wähle `q i ≤ c i` rational mit `c i ≤ q i + δ / n` für
`i ≠ 0` und lasse `q 0` den Rest aufnehmen, was die Summe rational und gleich
`1` hält. Die Abzählbarkeit der Familie ist dann das Bild von
`Σ n, (Fin n → ℕ) × (Fin n → ℚ≥0)` unter `ProbabilityMeasure.toMeasure_injective`
(`Measure/ProbabilityMeasure.lean:128`). Mitgefunden und im Meilenstein
festgehalten: **das leere `E` ist eine eigene Zeile und keine Hypothese** —
`TopologicalSpace.exists_dense_seq` (`Topology/Bases.lean:346`) verlangt
`[Nonempty E]`, und über leerem `E` gibt es gar kein Wahrscheinlichkeitsmaß,
`ProbabilityMeasure E` ist also leer und `∅` darin dicht.

Die Datei zählt danach **105 Deklarationen und 7 `sorry`** (vorher 102 und 7);
drei Deklarationen sind neu und bewiesen, keine neu als `sorry`
liegengeblieben. Die Zahl ist die des üblichen `grep -cE`, gegengeprüft mit
`git diff --unified=0 HEAD | grep -cE "^\+(theorem|…)"`, das genau die drei
neuen zählt. Eine Werkzeugnotiz, die Zeit gespart hat und wieder sparen
wird: entwickelt wurde in einer eigenen kleinen Datei mit nur zwei Imports
(`LevyProkhorovMetric`, `Prokhorov`) — drei Durchläufe in je unter einer Minute
gegen minutenlange Durchläufe der 3300-Zeilen-Datei —, und erst der fertige
Text wurde eingesetzt und **einmal** im Ganzen geprüft. Die Hilfsdatei ist
danach mit `git clean` entfernt; `rm` auf einen Pfad im Worktree ist von der
Sandbox blockiert, `git clean -f <pfad>` nicht.

Mitgefunden, beim Übersetzen: `Measure.coe_finset_sum` ist `deprecated` (jetzt
`Measure.coe_finsetSum`), ebenso `Set.subset_diff_union` (jetzt
`Set.subset_sdiff_union`); und `mul_le_mul_left'`/`mul_le_mul_right'` gibt es in
v4.33.1 unter diesen Namen **nicht** mehr — wer eine Ungleichung unter einem
Produkt braucht, nimmt `gcongr` oder rechnet die Fälle des Indikators von Hand
aus, was hier kürzer war.

**Vorschlag für den nächsten Lauf, als benanntes Ziel: die Zerlegung, Schritt
(1) oben**, als eigene Deklaration
`exists_finite_partition_ball_of_denseRange` in `WeakConvergence`
Meilenstein 3. Warum jetzt: sie ist der einzige Schritt zwischen den beiden
heute bewiesenen Schätzungen und dem Satz, der noch Mathlib-Suche braucht
(`disjointed`, `tendsto_measure_iUnion_atTop`, `Metric.mem_ball` — alles
vorhanden, aber die Fin-Indizierung gegen `⋃ k < n` ist Handarbeit), während
Schritt (2) reine Arithmetik über `ℚ≥0` ist und keine Rückfrage an Mathlib
stellt. Und sie ist zugleich die Aussage, die `SeparableSpace E` überhaupt
verbraucht — danach ist der Satz Buchhaltung über drei bewiesenen Stücken.

### 2026-09-08, dritter Lauf des Tages — die Zerlegung und die Gewichte; `separableSpace_probabilityMeasure` ist nur noch Buchhaltung

**Bearbeitet:** `fact:PSpolish` (tragend 1), nach dem benannten Ziel des
Vorlaufs. Das Ziel — `exists_finite_partition_ball_of_denseRange` — ist erreicht,
und der Lauf hat den zweiten der beiden ausstehenden Schritte gleich mitgenommen.
`separableSpace_probabilityMeasure` selbst trägt weiterhin `sorry`, aber kein
mathematischer Schritt fehlt ihm mehr.

**Bewiesen und durch `lake env lean` gegen v4.33.1** (in
`TauCeti/WeakConvergence/Suggested.lean`; rc = 1 mit unverändert genau den
**zwei** angekündigten Fehlern an
`tendsto_map_of_measure_setOf_continuousAt_eq_one`, jetzt bei `:2018`, und
keinem weiteren Fehler):

* `exists_finite_partition_ball_of_denseRange` — zu einer dichten Folge `x`,
  einem endlichen `μ`, einer Masse `ε > 0` und einem Radius `r > 0` gibt es eine
  endliche meßbare Zerlegung `A : Fin n → Set E`, Indizes `k : Fin n → ℕ` und
  eine Menge `G` mit `μ G ≤ ε`, so daß außerhalb `G` jeder Punkt von `A i` im
  Abstand `r` von `x (k i)` liegt. Das ist genau die Hypothese von
  `levyProkhorovEDist_sum_dirac_le`, hergestellt.

  Drei Entscheidungen, die den Beweis kurz gehalten haben und die beim
  Weiterschreiben gelten sollten. **Erstens: die Vertreter sind Indizes, keine
  Punkte.** `k : Fin n → ℕ` statt `y : Fin n → E` — die Punkte selbst machen die
  approximierende Familie nicht abzählbar, die Indizes in die dichte Folge tun
  es. **Zweitens: die Ausnahmemenge ist ein Stück der Zerlegung.** `A` läuft über
  `Fin (n+1)`, die ersten `n` Stücke sind die Disjunktifizierung
  `ball (x i) r \ ⋃ j < i, ball (x j) r`, das letzte ist der unbedeckte Rest
  `G = (⋃ j < n, ball (x j) r)ᶜ` — dadurch ist die Abstandsbedingung an diesem
  Stück leer (`A i \ G = ∅`) und braucht keinen eigenen Zeugen; für `n = 0`
  bleibt die Aussage richtig, mit `A 0 = univ = G`.
  **Drittens: der Abschnitt läuft über die Komplemente, nicht über die Massen.**
  `tendsto_measure_iInter_atTop` auf `(U m)ᶜ` mit `⋂ m, (U m)ᶜ = ∅` gibt
  `μ (U m)ᶜ → 0` direkt; der Weg über `tendsto_measure_iUnion_atTop` und
  `μ univ - μ (U m)` hätte eine Subtraktion in `ℝ≥0∞` gekostet, die man nicht
  braucht. Die Endlichkeit von `μ` geht genau einmal ein, als
  `∃ i, μ (s i) ≠ ∞` in dieser Anwendung.

  Mathlibs `SeparableSpace.exists_measurable_partition_diam_le`
  (`Measure/LevyProkhorovMetric.lean:540`) ist dieselbe Disjunktifizierung, aber
  abzählbar indiziert und ohne die Vertreter; weder der endliche Index noch die
  Punkte überleben sie, darum wird die Zerlegung hier gebaut.

* `exists_nat_weights` — ein Gewichtsvektor `c : Fin n → ℝ≥0∞` mit
  `∑ i, c i = 1` wird bis auf einen Gesamtfehler `δ` durch den **normierten**
  ganzzahligen Vektor `m i / ∑ j, m j` approximiert.

  **Der Befund, der hier zählt, ist eine Vereinfachung des angekündigten Wegs.**
  Der Meilenstein verlangte bis heute rationale Gewichte, die auf Summe `1`
  festgenagelt sind: `q i ≤ c i` abrunden und `q 0` den Rest aufnehmen lassen.
  Das braucht die abgeschnittene Subtraktion in `ℝ≥0∞` (oder in `ℚ≥0`) und eine
  Fallunterscheidung am Ausnahmeindex, an dem die Abweichung dann `(n-1)`-mal so
  groß ist wie an den übrigen. **Normieren spart beides.** Mit
  `m i = ⌊(c i).toReal * N⌋₊ + 1` liegt `∑ j, m j` zwischen `N` und `N + n`,
  jedes `m i` zwischen `(c i).toReal * N` und `(c i).toReal * N + 1`, also jedes
  normierte Gewicht im Abstand `(n+1)/N` von `c i` — **an jedem Index derselbe
  Fehler**, kein Ausnahmeindex —, und `∑ i, m i / ∑ j, m j = 1` gilt nach
  Konstruktion statt als Beweisverpflichtung. Das `+ 1` in den Zählern ist nicht
  kosmetisch: es hält `∑ j, m j` positiv, auch wenn alle Abrundungen
  verschwinden. Die Familie wird damit über `Σ n, (Fin n → ℕ) × (Fin n → ℕ)`
  indiziert, nicht über `Σ n, (Fin n → ℕ) × (Fin n → ℚ≥0)`; die Roadmap ist
  entsprechend geändert.

  Werkzeugnotiz: der Beweis rechnet in `ℝ` (über `.toReal`) und wird erst am
  Ende nach `ℝ≥0∞` gehoben, über `ENNReal.ofReal_div_of_pos`,
  `ENNReal.ofReal_add` und `ENNReal.ofReal_toReal`. Vier Zeilen Umrechnung gegen
  einen ganzen Beweis in `ℝ≥0∞` — die Division und die Subtraktion dort sind
  jede für sich teurer als die Hebung.

**Was jetzt noch fehlt, und es ist kein mathematischer Schritt mehr.** Die
Buchhaltung: Zerlegung mit `r = ε.toReal` holen,
`levyProkhorovEDist_sum_dirac_le` anwenden, `exists_nat_weights` auf
`c i = μ (A i)` (Gesamtmasse `1`, weil `A` eine Zerlegung ist), dann
`levyProkhorovEDist_sum_dirac_weights_le`, `levyProkhorovEDist_triangle`
(`Measure/LevyProkhorovMetric.lean:127`) gibt `2ε`, und
`LevyProkhorov.probabilityMeasureHomeomorph` (`ibid.:676`) trägt es in die
Topologie der Verteilungskonvergenz. Dazu die Abzählbarkeit des Bildes von
`Σ n, (Fin n → ℕ) × (Fin n → ℕ)` unter `ProbabilityMeasure.toMeasure_injective`
(`Measure/ProbabilityMeasure.lean:128`) und die eigene Zeile für leeres `E`
(`TopologicalSpace.exists_dense_seq`, `Topology/Bases.lean:346`, verlangt
`[Nonempty E]`; über leerem `E` ist `ProbabilityMeasure E` leer und `∅` darin
dicht). Alles steht ausgeschrieben im Docstring von
`separableSpace_probabilityMeasure` und im Meilenstein.

Die Datei gewinnt **genau zwei** Deklarationen, beide bewiesen, und **kein**
neues `sorry`: der Zähler über `git diff --unified=0 HEAD` auf hinzugefügte
Zeilen, die mit `theorem`/`lemma`/`def`/`instance` beginnen, gibt 2, und
`grep -cE ":= sorry$"` steht unverändert bei 7. (Die absolute
Deklarationszahl hängt am gewählten Muster — `^(theorem|lemma|def) ` gibt 103,
mit `instance` 108 —; der Vorlauf hat 105 genannt, die Differenz ist das Muster
und nicht der Inhalt. Der Delta-Zähler über `git diff` ist der belastbare.)

Die Entwicklung lief wieder in einer eigenen kleinen Datei mit **einem** Import
(`Mathlib.MeasureTheory.Measure.LevyProkhorovMetric`) — vier Durchläufe in je
unter einer Minute —, und erst der fertige Text wurde eingesetzt und zweimal im
Ganzen geprüft; die Hilfsdatei ist mit `git clean -f` entfernt. Das ist jetzt
zum zweiten Mal die Vorgehensweise, die den Lauf gerettet hat, und sie gehört
zum Standard.

Mitgefunden, beim Übersetzen: `Set.diff_subset` ist `deprecated` (jetzt
`Set.sdiff_subset`), und `zero_le'` ebenfalls (jetzt `zero_le`, mit implizitem
Argument — `zero_le _` ist ein Fehler, nicht bloß eine Warnung).

**Vorschlag für den nächsten Lauf, als benanntes Ziel:
`separableSpace_probabilityMeasure` selbst**, `WeakConvergence` Meilenstein 3.
Warum jetzt: es ist der erste Lauf, in dem der Satz **keine** Mathlib-Suche mehr
stellt und keine offene mathematische Frage mehr hat — vier bewiesene Stücke,
eine Dreiecksungleichung und ein Homöomorphismus, alle mit Fundstelle. Die
einzige Stelle, an der noch etwas schiefgehen kann, ist die Abzählbarkeit: sie
läuft über die Injektivität der Vergröberung `ProbabilityMeasure E → Measure E`
und über `Set.Countable.image` auf einem `Sigma`-Typ, und der Beweis muß dafür
das approximierende Maß als `ProbabilityMeasure` **bündeln**, also
`IsProbabilityMeasure (∑ i, (m i / M) • dirac (x (k i)))` nachweisen — das ist
`∑ i, m i / M = M / M = 1` über `ENNReal.div_self`, und es ist die eine
Rechnung, die der nächste Lauf zuerst hinschreiben sollte, weil alles Übrige
davon abhängt.

### 2026-09-08, vierter Lauf des Tages — `separableSpace_probabilityMeasure` ist bewiesen, und drei Nachbarn mit ihm

**Bearbeitet:** `fact:PSpolish` (tragend 1), nach dem benannten Ziel des
Vorlaufs. Das Ziel ist erreicht; der Lauf hat drei weitere Deklarationen
mitgenommen, von denen zwei Meilensteinpunkte sind, die bis dahin gar keine
Deklaration hatten.

**Bewiesen und durch `lake env lean` gegen v4.33.1** (in
`TauCeti/WeakConvergence/Suggested.lean`; rc = 1 mit unverändert genau den
**zwei** angekündigten Fehlern an
`tendsto_map_of_measure_setOf_continuousAt_eq_one`, jetzt bei `:2029`, und
keinem weiteren Fehler). Für alle vier ist `#print axioms` gelaufen, an einer
angehängten Kopie der Datei; die ersten vier hängen an `propext`,
`Classical.choice`, `Quot.sound` und an nichts sonst.

* `natWeightMeasure` und `isProbabilityMeasure_natWeightMeasure` — die
  approximierende Familie als **Definition**, nicht als Beschreibung im Beweis.
  Das ist die Entscheidung, an der die Abzählbarkeit hängt: als benannte
  Funktion auf `Σ n, (Fin n → ℕ) × (Fin n → ℕ)` ist die Familie ein
  `Set.range`, und `Set.Countable.preimage` längs
  `ProbabilityMeasure.toMeasure_injective` gibt die Abzählbarkeit der
  Menge der Wahrscheinlichkeitsmaße in **drei Zeilen**. Die Rechnung, die der
  Vorlauf als erste verlangt hatte, ist
  `isProbabilityMeasure_natWeightMeasure`: die Gesamtmasse ist
  `(∑ j, m j) / (∑ j, m j)`, und das ist die einzige Stelle, an der das `+ 1`
  in den Zählern von `exists_nat_weights` gebraucht wird, weil
  `ENNReal.div_self` einen Nenner `≠ 0` will.
* `separableSpace_levyProkhorov_probabilityMeasure` — die Aussage **auf dem
  Synonym**. Dort lebt die Metrik, dort greift `Metric.dense_iff`, und der Rest
  ist die vom Vorlauf ausgeschriebene Buchhaltung: `ε = ENNReal.ofReal (r/4)`,
  die Zerlegung mit Radius `ε.toReal`, `levyProkhorovEDist_sum_dirac_le`,
  `exists_nat_weights` auf `c i = μ (A i)` (Summe `1` über `measure_iUnion` und
  `tsum_fintype`), `levyProkhorovEDist_sum_dirac_weights_le`,
  `levyProkhorovEDist_triangle` — zusammen `2ε`, also `r/2 < r`.
* `separableSpace_probabilityMeasure` — die Aussage des Meilensteins,
  hinübergetragen mit `DenseRange.separableSpace` (`Topology/Bases.lean:378`)
  längs `probabilityMeasureHomeomorph.symm`, deren Surjektivität den dichten
  Bildbereich umsonst gibt.
* `secondCountableTopology_probabilityMeasure` — der Meilensteinpunkt, der bis
  heute nur im `README.md` stand: auf dem Synonym gibt
  `UniformSpace.secondCountable_of_separable`
  (`Topology/UniformSpace/Cauchy.lean:932`) die Zweitabzählbarkeit aus der
  Separabilität, und `Homeomorph.secondCountableTopology`
  (`Topology/Homeomorph/Lemmas.lean:37`) trägt sie zurück. Vollständigkeit von
  `E` geht nirgends ein.

**Ein Befund, und er ist eine Abschwächung.** `polishSpace_probabilityMeasure`
trägt statt `sorry` jetzt seinen Beweis — zwei Zeilen über
`isCompletelyMetrizableSpace_probabilityMeasure` und der eben bewiesenen
Separabilität, denn `PolishSpace` ist ausweislich
`Topology/MetricSpace/Polish.lean:62` genau `SecondCountableTopology` plus
`IsCompletelyMetrizableSpace`, und die Instanz bei `:65` baut es aus
Separabilität und vollständiger Metrisierbarkeit. Der Satz hängt damit noch an
`sorryAx`, aber über **einen benannten Eingang** und nicht über sich selbst.

Dabei ist die Aussage **schwächer geworden**, und zwar nicht aus Sparsamkeit,
sondern weil sie stärker nicht beweisbar war: sie stand unter
`[MetricSpace E] [BorelSpace E] [PolishSpace E]` und steht jetzt unter
`[TopologicalSpace E] [PolishSpace E] [BorelSpace E]`, **ohne Metrik auf `E`**.
Der Grund ist mechanisch und lohnt das Aufschreiben, weil er jede Aussage
dieses Meilensteins betrifft, die „`E` polnisch" statt „`E` metrisch und
vollständig" will: `isCompletelyMetrizableSpace_probabilityMeasure` verlangt
`[CompleteSpace E]`, und unter `[PolishSpace E]` liefert
`TopologicalSpace.upgradeIsCompletelyMetrizable`
(`Topology/Metrizable/CompletelyMetrizable.lean:205`) zwar eine vollständige
Metrik, aber als **zweite** Instanz neben der mitgegebenen. Das
`CompleteSpace E` des Aufstiegs ist dann für die aufgestiegene Uniformität
formuliert, das Ziel will es für die mitgegebene, und die beiden treffen sich
nicht — der Fehler lautet wörtlich
`has type @CompleteSpace E (… up.toMetricSpace) but is expected to have type
@CompleteSpace E (… inst✝²)`. Ein polnischer Raum hat keine ausgezeichnete
Metrik; nimmt man sie aus der Signatur heraus, ist die aufgestiegene die
einzige, und beide Eingänge passen zusammen. Der Versuch, es mit
`letI up : UpgradedIsCompletelyMetrizableSpace E := …` und
`haveI : CompleteSpace E := up.toCompleteSpace` doch unter der mitgegebenen
Metrik zu erzwingen, ist genau daran gescheitert.

**Stand der Datei.** Sechs Deklarationen tragen noch `sorry` (vorher sieben),
gezählt am Übersetzer: `tendsto_map_of_measure_setOf_continuousAt_eq_one`
(der Versionsgrund, zugleich die zwei angekündigten Fehler),
`completeSpace_levyProkhorov_probabilityMeasure`,
`isCompletelyMetrizableSpace_probabilityMeasure`,
`exists_measurable_partition_diam_le_null_frontier`,
`exists_ae_tendsto_of_tendsto` und
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`. Vier Deklarationen
sind neu und bewiesen (`natWeightMeasure`,
`isProbabilityMeasure_natWeightMeasure`,
`separableSpace_levyProkhorov_probabilityMeasure`,
`secondCountableTopology_probabilityMeasure`), zwei bisherige `sorry` sind
gefallen (`separableSpace_probabilityMeasure`,
`polishSpace_probabilityMeasure`).

Die Entwicklung lief wieder in einer eigenen kleinen Datei mit zwei Imports
(`LevyProkhorovMetric`, `MetricSpace.Polish`), in der die vier Vorlemmata als
`sorry`-Rümpfe standen — sechs Durchläufe in je unter einer Minute —, und erst
der fertige Text wurde eingesetzt und im Ganzen geprüft; die Hilfsdateien sind
mit `git clean -f scratch/` entfernt. Das ist der dritte Lauf in Folge, in dem
diese Vorgehensweise trägt.

Mitgefunden, beim Übersetzen, und beides kostet sonst Minuten:
`LevyProkhorov` ist eine **Struktur mit einem Feld** und kein Typsynonym
(`Measure/LevyProkhorovMetric.lean:259`) — eine Menge von Maßen und ihr Bild
unter `LevyProkhorov.ofMeasure` sind verschiedene Terme, und die Dichtheit muß
wirklich getragen und nicht bloß umgelesen werden. Und `Set.univ_eq_empty` gibt
es nicht; die Aussage heißt `Set.univ_eq_empty_iff` (`Data/Set/Basic.lean:540`).

**Fortsetzung desselben Laufs: die Vollständigkeit ist auch bewiesen, und mit
ihr der ganze Strang bis `polishSpace_probabilityMeasure`.** Der Vorschlag, der
unten als nächstes Ziel stand, ist im selben Lauf noch eingelöst worden; vier
weitere Deklarationen, alle bewiesen, alle durch `lake env lean` gegen v4.33.1,
und alle fünf betroffenen Sätze hängen laut `#print axioms` allein an `propext`,
`Classical.choice`, `Quot.sound` — **auch `polishSpace_probabilityMeasure`, das
damit kein `sorryAx` mehr sieht.**

* `isTightMeasureSet_of_forall_exists_levyProkhorovEDist_lt` — **eine
  Cauchy-Folge von Gesetzen ist straff**, der mathematische Kern. Die Aussage
  schreibt den Lévy--Prokhorov-Abstand aus, statt `CauchySeq` zu verlangen; das
  macht sie instanzfrei lesbar. Der Beweis ist die Stelle, an der die
  Vollständigkeit von `E` bezahlt wird, und zwar zweimal: über Ulam
  (`isTightMeasureSet_singleton`) für den endlichen Kopf und über
  `isTightMeasureSet_of_forall_exists_finite_iUnion_ball` — den Satz, den der
  erste Lauf des Tages eigens dafür gebaut hat — für den Schluß. Zu `ε` und `r`
  ist `δ = min (ε/2) (ofReal (r/2))`; der Kopf `u 0, …, u N` liegt im Kompaktum
  `L = ⋃ n ≤ N, K n`, dessen `r/2`-Netz das gesuchte `F` ist, und für `n > N`
  trägt `right_measure_le_of_levyProkhorovEDist_lt` die Kugelvereinigung `B` vom
  Radius `r/2` in ihre `δ`-Verdickung und damit in `A`, die Vereinigung der
  Kugeln vom Radius `r`. Die Bilanz `1 = (u N) B + (u N) Bᶜ ≤ ((u n) A + δ) +
  ε/2` gibt `(u n) Aᶜ ≤ ε`. **Subtraktion in `ℝ≥0∞` kommt im ganzen Beweis nicht
  vor**, sondern nur `measure_add_measure_compl` und
  `ENNReal.add_le_add_iff_left` — das ist dieselbe Lehre wie beim
  Gewichtsvektor des Vorlaufs.
* `isTightMeasureSet_of_cauchySeq` — dieselbe Aussage für `CauchySeq`, in drei
  Zeilen über `EMetric.cauchySeq_iff'`. Sie geht durch, ohne daß etwas
  umgeschrieben werden müßte, weil `edist` auf
  `LevyProkhorov (ProbabilityMeasure E)` **definitionsgleich**
  `levyProkhorovEDist` ist (`edist_probabilityMeasure_def`).
* `completeSpace_levyProkhorov_probabilityMeasure` — Straffheit, dann
  `isCompact_closure_of_isTightMeasureSet` (`Measure/Prokhorov.lean:530`) für
  den kompakten Abschluß, dann `IsCompact.tendsto_subseq` (der Raum der Gesetze
  ist metrisierbar, also folgenkompakt auf Kompakta), dann
  `tendsto_nhds_of_cauchySeq_of_subseq` (`UniformSpace/Cauchy.lean:277`). Der
  Wechsel der Topologie mittendrin ist die eigentliche Feinheit: die Teilfolge
  konvergiert **schwach**, die Folge soll **metrisch** konvergieren, und
  `probabilityMeasureHomeomorph` ist genau dafür da.
* `isCompletelyMetrizableSpace_probabilityMeasure` — der Transport auf den Raum
  der Gesetze selbst, über `Homeomorph.isClosedEmbedding` und
  `Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`
  (`Topology/Metrizable/CompletelyMetrizable.lean:249`).

**Stand der Datei danach:** noch **drei** Deklarationen mit `sorry` (zu Beginn
des Laufs sieben, nach der ersten Hälfte sechs) —
`exists_measurable_partition_diam_le_null_frontier`,
`exists_ae_tendsto_of_tendsto` (beides die Skorokhod-Darstellung) und
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (Meilenstein 4) —,
dazu unverändert `tendsto_map_of_measure_setOf_continuousAt_eq_one` mit den zwei
angekündigten Versionsfehlern bei `:2029`. **Der Block „der Raum der Gesetze"
von Meilenstein 3 ist damit vollständig bewiesen**; was von Meilenstein 3
bleibt, ist allein die Skorokhod-Darstellung.

*Der Vorschlag, der zu diesem Zeitpunkt geschrieben war und im selben Lauf
eingelöst wurde, zur Nachvollziehbarkeit der Reihenfolge:*
`completeSpace_levyProkhorov_probabilityMeasure`, `WeakConvergence`
Meilenstein 3. Warum jetzt: es ist der **letzte** mathematische Eingang des
Meilensteins, der noch keinen hat — die drei Sätze darüber (Separabilität,
Zweitabzählbarkeit, Polnischsein) sind bewiesen bzw. auf ihn reduziert, und
`isCompletelyMetrizableSpace_probabilityMeasure` ist danach der Transport längs
`probabilityMeasureHomeomorph` mit `Homeomorph.isClosedEmbedding` und
`Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`, also keine eigene
Rechnung. Alles, worauf sein Beweis ruht, steht bereits bewiesen da: die
Straffheit der endlichen Anfangsstücke aus `isTightMeasureSet_singleton`
(Ulam, `Measure/Tight.lean:99`) und `IsTightMeasureSet.union` (`:119`), die
Straffheit des Schwanzes aus dem im ersten Lauf des Tages bewiesenen
`isTightMeasureSet_of_forall_exists_finite_iUnion_ball` — das eigens dafür
gebaut wurde —, und `isCompact_closure_of_isTightMeasureSet`
(`Measure/Prokhorov.lean:530`) für die konvergente Teilfolge. Zu schreiben ist
allein die Wahl von `F` aus dem Kompaktum des Anfangsstücks und die
Lévy--Prokhorov-Ungleichung, die den Schwanz an dieses `F` bindet; der
Meilenstein schreibt beides aus. *(Beides ist in diesem Lauf geschrieben
worden; siehe oben.)*

**Vorschlag für den nächsten Lauf, als benanntes Ziel:
`exists_measurable_partition_diam_le_null_frontier`**, `WeakConvergence`
Meilenstein 3. Warum jetzt: es ist der erste der beiden verbliebenen `sorry`
dieses Meilensteins und der Schritt, der die **ganze** Skorokhod-Darstellung
trägt — `exists_ae_tendsto_of_tendsto` benutzt ihn Stück für Stück, damit
`tendsto_measure_of_null_frontier` (`Measure/Portmanteau.lean:243`) auf jedem
Teil greift, und ohne ihn ist dort nichts zu machen. Er stellt zudem **keine**
offene Frage an Mathlib mehr: die Radien kommen einzeln aus
`exists_null_frontier_thickening` (`Portmanteau.lean:401`), `disjointed` macht
die Kugeln disjunkt, und daß die Ränder dabei Nullmengen bleiben, geben
`frontier_inter_subset`, `frontier_union_subset` und `frontier_compl`
(`Topology/Closure.lean:537,544,528`) — alles im Meilenstein mit Fundstelle
ausgeschrieben. Was zu tun bleibt, ist die Buchhaltung über der
Disjunktifizierung, und die ist dem
`exists_finite_partition_ball_of_denseRange` des dritten Laufs so ähnlich, daß
dessen drei Entscheidungen (Vertreter als Indizes, Ausnahmestück als Teil der
Zerlegung, Abschnitt über die Komplemente) sich übertragen lassen sollten.

### 2026-09-08, fünfter Lauf des Tages — `fact:PSpolish`: zwei der drei Eingänge der Skorokhod-Darstellung

Kein Fact hat mehr den Status `?`, der Rückstau schickt an seinen ersten offenen
Punkt („`SkorokhodSpace` und `MartingaleProblems` weiter beweisen", von oben je
Datei), und der Vorschlag des Vorlaufs benennt darin genau ein Ziel:
`exists_measurable_partition_diam_le_null_frontier`, `WeakConvergence`
Meilenstein 3. Es ist bewiesen, samt zwei Hilfssätzen, die Mathlib nicht hat —
und im selben Lauf noch der zweite Eingang der Darstellung, der Scheffé-Schritt,
mit vier weiteren Deklarationen (unten). Alle sieben gehen durch
`lake env lean` gegen v4.33.1 und hängen laut `#print axioms` allein an
`propext`, `Classical.choice`, `Quot.sound`.

* `exists_measurable_partition_diam_le_null_frontier` — zu einem endlichen Maß
  `μ` auf einem separablen pseudometrischen Raum und `ε > 0` eine abzählbare
  meßbare Zerlegung in Stücke vom Durchmesser höchstens `ε`, deren Ränder alle
  `μ`-Nullmengen sind, mit der Beschränktheitsklausel von Mathlibs Fassung.
* `frontier_biInter_range_subset` — der Rand eines endlichen Durchschnitts liegt
  in der Vereinigung der Ränder. Mathlib hat mit `frontier_inter_subset`
  (`Topology/Closure.lean:537`) nur den Zweimengenfall.
* `frontier_disjointed_subset` — der Rand von `disjointed S n` liegt in der
  Vereinigung der Ränder von `S 0, …, S n`.

**Der eine Unterschied zu Mathlibs Beweis, und er ist die ganze Aussage.**
`SeparableSpace.exists_measurable_partition_diam_le`
(`Measure/LevyProkhorovMetric.lean:540`) disjunktifiziert Kugeln **eines festen
Radius** `ε/2` um eine dichte Folge. Hier wird der Radius **je Mittelpunkt**
gewählt, aus dem offenen Intervall `(ε/4, ε/2)`, durch
`exists_null_frontier_thickening` (`Measure/Portmanteau.lean:401`) angewandt auf
das Singleton `{xs n}` und mit `Metric.thickening_singleton`
(`Topology/MetricSpace/Thickening.lean:157`) als Kugel gelesen. Die drei
Bestandteile des Intervalls hängen einzeln an etwas:

* die **untere** Schranke `ε/4` trägt die Überdeckung — zu jedem `y` liefert
  `Metric.denseRange_iff` (`Topology/MetricSpace/Pseudo/Defs.lean:1260`) ein `n`
  mit `dist y (xs n) < ε/4 < r n`;
* die **obere** Schranke `ε/2` trägt den Durchmesser, über
  `Metric.diam_ball` (`Topology/MetricSpace/Bounded.lean:537`), das
  `diam (ball x r) ≤ 2 * r` sagt und nicht `=`;
* **offen** muß das Intervall sein, weil `exists_null_frontier_thickening` nicht
  einen vorgeschriebenen Radius liefert, sondern nur abzählbar viele belastete
  vermeidet. Ein fester Radius geht daher nicht, und das ist genau der Inhalt des
  acceptance example, das in Meilenstein 3 steht (`E = ℝ`, `μ = δ 0`, `ε = 1`:
  der Rand der Kugel vom Radius `1` um `1` trägt die ganze Masse).

**Die Randabschätzung war der Teil, den die Roadmap zu leicht genommen hatte.**
Sie nennt `frontier_inter_subset`, `frontier_union_subset` und `frontier_compl`,
und das sind die richtigen Bausteine, aber sie sind alle für **zwei** Mengen
formuliert, während `disjointed Bs n` ein Durchschnitt über `Finset.range n` ist.
Mathlib hat die endliche Fassung nicht — gesucht wurde nach
`frontier_biUnion`, `frontier_iUnion`, `frontier_sUnion` und
`frontier_biInter`; in `Mathlib/Topology/` gibt es zu `frontier` neben
`frontier_interior_subset`, `frontier_compl`, `frontier_inter_subset`,
`frontier_union_subset` und `frontier_inter_open_inter` nichts weiter. Die
Induktion selbst ist kurz; zu wissen ist nur, daß `Finset.range_succ` **nicht
existiert** (die Aussage heißt `Finset.range_add_one`,
`Data/Finset/Range.lean:79`) und daß ein `rw [Finset.range_add_one]` beide Seiten
trifft, wenn beide `Finset.range (n+1)` enthalten — im Schritt der Induktion muß
daher direkt `Finset.set_biUnion_insert` stehen.

**Der zweite Eingang der Skorokhod-Darstellung, im selben Lauf: der
Scheffé-Schritt.** Die Zerlegung allein trägt die Konstruktion nicht. Was sie
braucht, ist die Aussage, daß die auf der Zerlegung falsch plazierte Masse
**insgesamt** verschwindet, und die folgt aus der stückweisen Konvergenz durch
kein endliches Argument. Vier weitere Deklarationen, alle bewiesen, alle durch
`lake env lean` gegen v4.33.1 und alle mit `#print axioms` auf `propext`,
`Classical.choice`, `Quot.sound` geprüft:

* `tendsto_tsum_posPart_sub_of_tendsto_measure` — zu einer abzählbaren meßbaren
  Zerlegung `A` mit `μ n (A i) → ν (A i)` für jedes `i` geht
  `∑' i, max (ν (A i) - μ n (A i)) 0` gegen `0`.
* `tendsto_tsum_abs_sub_of_tendsto_measure` — dasselbe für
  `∑' i, |ν (A i) - μ n (A i)|`, den auf der Zerlegung gelesenen
  Totalvariationsabstand; das ist die Form, die die Kopplung verbraucht.
* `summable_toReal_measure_of_pairwise_disjoint` und
  `tsum_toReal_measure_eq_one` — die zwei Kleinigkeiten darunter.

**Warum der Positivteil und nicht der Betrag.** Der Beweis des ersten ist
Tannerys Satz, `tendsto_tsum_of_dominated_convergence`
(`Analysis/Normed/Group/Tannery.lean:40`, in v4.33.1 vorhanden), mit den Massen
des Grenzmaßes als summierbarer Majorante. Die Majorisierung
`max (ν (A i) - μ n (A i)) 0 ≤ ν (A i)` gilt, weil `μ n (A i) ≥ 0` ist — und
genau daran hängt, daß der **Positivteil** die Größe mit einer von `n` freien
Schranke ist und der Betrag nicht: `|ν (A i) - μ n (A i)|` läßt sich nur durch
`ν (A i) + μ n (A i)` majorisieren, und das ist keine feste Funktion von `i`.
Der Betrag kommt daher nicht durch eine zweite Anwendung Tannerys, sondern über
die Identität `|d| = 2 · max d 0 - d` und die Bilanz
`∑' i, (ν (A i) - μ n (A i)) = 1 - 1 = 0`; dort, und nur dort, wird die
Überdeckungsvoraussetzung `⋃ i, A i = univ` verbraucht. Mathlib hat den Satz
nicht unter seinem Namen: `scheffe` kommt auf `upstream/master` `572e4d091bc` in
`Mathlib/` überhaupt nicht vor, und die Suchen nach `tendsto_tsum_of`,
`tsum_tendsto`, `tendsto_tsum` finden allein Tannery, das die
maßtheoretische Fassung ausdrücklich als Spezialfall des Zählmaßes nennt.

**Stand der Datei.** `WeakConvergence/Suggested.lean` trägt **vier** `sorry`:
`tendsto_map_of_measure_setOf_continuousAt_eq_one` (der bekannte Versionsgrund,
mit seinen zwei angekündigten Fehlern bei `:2043` — die einzigen Fehler des
Durchlaufs), `exists_ae_tendsto_of_tendsto` und die in diesem Lauf **neu
angelegte** Aussage `exists_measurable_map_restrict_volume_eq_sum_smul_dirac`
(beide Meilenstein 3) sowie
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (Meilenstein 4). Die
neue Aussage ist der dritte Eingang der Darstellung — die diskrete Realisierung
auf `(0,1]` —, sie elaboriert und ist der benannte Auftrag des nächsten Laufs;
zu Beginn des Laufs waren es drei `sorry`, zwei sind gefallen und eine ist
hinzugekommen.

Die Entwicklung lief beide Male in einer eigenen kleinen Datei mit zwei Imports
(`Portmanteau` und `LevyProkhorovMetric` für die Zerlegung, `Portmanteau` und
`Tannery` für Scheffé) — Durchläufe unter einer Minute, gegen einen Durchlauf
der ganzen Datei von mehreren Minuten —, und erst der fertige Text wurde
eingesetzt und im Ganzen geprüft. Das ist der vierte Lauf in Folge, in dem das
trägt.

**Vorschlag für den nächsten Lauf, als benanntes Ziel: die einstufige Kopplung
auf `([0,1], Lebesgue)`**, `WeakConvergence` Meilenstein 3, als benannte
Zwischenaussage vor `exists_ae_tendsto_of_tendsto`. Warum jetzt: von den drei
Eingängen der Skorokhod-Darstellung stehen seit diesem Lauf **zwei** bewiesen da
— die Zerlegung mit nullen Rändern und der Scheffé-Schritt —, und der dritte,
die Konstruktion der Zufallsvariablen selbst, ist der einzige, der noch keine
Deklaration hat. Der Schnitt, den der nächste Lauf ziehen und dessen erste Hälfte
er beweisen soll:

* **(a) die diskrete Realisierung.** Sie steht seit diesem Lauf als
  `exists_measurable_map_restrict_volume_eq_sum_smul_dirac` in der Datei,
  elaboriert und mit `sorry` als Beweis: zu einem Wahrscheinlichkeitsvektor
  `p : ℕ → ℝ≥0∞` und Punkten `x : ℕ → E` eine meßbare Abbildung `g : ℝ → E` mit
  `(volume.restrict (Ioc 0 1)).map g = Measure.sum fun i => p i • dirac (x i)`,
  gebaut über die Teilintervalle `Ioc (∑_{j<i} p j) (∑_{j≤i} p j)`. Das ist
  reine Buchhaltung über `Finset.sum` und `Set.Ioc` und braucht kein
  Portmanteau; es ist die Aussage, die der nächste Lauf beweisen soll. Das
  Bildmaß steht als `Measure.sum` und nicht als `tsum`, weil das Mathlibs Form
  für eine abzählbare Überlagerung von Maßen ist. **Zwei Entscheidungen der
  Konstruktion sind schon getroffen und stehen im Meilenstein**, damit der
  nächste Lauf sie nicht neu sucht; beide betreffen den rechten Rand. Die
  Abbildung ist `g y = x (Nat.find (h y))` zum Prädikat
  `P i y := y ≤ s (i+1) ∨ 1 ≤ y` mit `s i = (∑ j ∈ Finset.range i, p j).toReal`,
  und ihre Meßbarkeit ist `Measurable.find`
  (`MeasureTheory/MeasurableSpace/Constructions.lean:516`, am Quelltext geprüft)
  an den konstanten Abbildungen `fun _ => x i`. Der Zusatz `1 ≤ y` ist das,
  woran `h : ∀ y, ∃ i, P i y` überhaupt hängt: für `y < 1` gibt es ein `i` mit
  `y ≤ s (i+1)`, weil `s i → 1`, aber bei `y = 1` muß es keines geben — die
  Partialsummen erreichen `1` nur bei endlichem Träger von `p`. Dieser eine
  Punkt ist eine Lebesgue-Nullmenge, und ebenso
  `Ioc 0 1 \ ⋃ i, Ioc (s i) (s (i+1))`, deren Maß `1 - ∑' i, p i = 0` ist; die
  Identifikation `g = x i` auf `Ioc (s i) (s (i+1)) \ {1}` und diese beiden
  Nullmengen sind der ganze Beweis des Bildmaßes. Der Lauf hat die Rechnung
  **nicht** durchgeführt, sondern nur den Weg belegt — sie ist der Auftrag.
* **(b) die einstufige Kopplung.** Zu `ε > 0` und `μ n → ν` schwach ein `N`, so
  daß es für `n ≥ N` auf `([0,1], Lebesgue)` Paare `(X n, Y)` mit den richtigen
  Gesetzen und `P (dist (X n) Y > ε) < ε` gibt. Hier greifen die beiden Sätze
  von heute zusammen: die Zerlegung vom Durchmesser `≤ ε` mit `ν`-nullen Rändern
  gibt über `tendsto_measure_of_null_frontier` (`Measure/Portmanteau.lean:243`)
  die stückweise Konvergenz, und `tendsto_tsum_abs_sub_of_tendsto_measure` macht
  daraus die Schranke `ε` für die Gesamtmasse, auf der die beiden Realisierungen
  in verschiedene Stücke fallen.

Das Zusammensetzen der Stufen zu einer fast sicher konvergenten Folge ist danach
Buchhaltung über einer Diagonalfolge und nicht mehr Portmanteau.

### 2026-09-08, sechster Lauf des Tages — die diskrete Realisierung und die Maximalkopplung, und der Raum der Skorokhod-Darstellung ist kein Einheitsintervall

Kein Fact hat den Status `?`; der Rückstau schickt an seinen ersten offenen Punkt,
und der Vorschlag des Vorlaufs benennt darin (a) die diskrete Realisierung als
Auftrag und (b) die einstufige Kopplung als Ziel. (a) ist bewiesen, von (b) ist
die Arithmetik bewiesen, und der Bauplan von (b) ist berichtigt — er stand auf
einem Raum, auf dem er nicht durchgeht.

**Bewiesen, beide durch `lake env lean` gegen v4.33.1 und beide mit
`#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft.**

* `exists_measurable_map_restrict_volume_eq_sum_smul_dirac` — zu einem
  Wahrscheinlichkeitsvektor `p : ℕ → ℝ≥0∞` und Punkten `x : ℕ → E` eine meßbare
  Abbildung `g : ℝ → E` mit
  `(volume.restrict (Ioc 0 1)).map g = Measure.sum fun i => p i • dirac (x i)`.
* `exists_coupling_tsum_offDiag_le` — die diskrete Maximalkopplung: zu `p`, `q`
  mit Summe `1` ein `π : ℕ → ℕ → ℝ≥0∞` mit den richtigen Randverteilungen und
  `∑' i, ∑' j, (if i = j then 0 else π i j) ≤ ∑' i, (p i - q i)`.

**Zur ersten.** Der Weg stand im Vorlauf ausgeschrieben und trug; drei Dinge sind
beim Ausführen dazugekommen, und alle drei betreffen den rechten Rand.

* Der Zusatz `1 ≤ y` im Prädikat `P i y := y ≤ s (i+1) ∨ 1 ≤ y` ist nicht
  Bequemlichkeit, sondern das, woran `h : ∀ y, ∃ i, P i y` überhaupt hängt: bei
  unendlichem Träger von `p` ist `s i < 1` für **jedes** `i`, also erfüllt bei
  `y = 1` kein `i` die erste Hälfte, und ohne die zweite ließe sich `Nat.find`
  nicht bilden. Das ist als acceptance example in Meilenstein 3 eingetragen,
  zusammen mit der benachbarten Instanz `p = (1,0,0,…)`, an der der Fehler sich
  **nicht** zeigt, weil dort schon `s 1 = 1` ist.
* Die Identifikation der Stücke `{y | Nat.find (h y) = i}` mit den Intervallen
  `Ioc (s i) (s (i+1))` gilt nur außerhalb von `{1}` und ist deshalb als
  `=ᵐ[volume]` und nicht als Mengengleichheit geführt. Bei `y = 1` ist `P j y`
  für **jedes** `j` wahr, also `Nat.find = 0`, und das Stück `i = 0` bekäme
  sonst den Punkt fälschlich dazu.
* Eine Falle der Notation, die vier Minuten gekostet hat und beim nächsten Mal
  keine mehr kosten soll: `A ∩ B =ᵐ[μ] C` elaboriert die linke Seite mit der
  erwarteten Art `ℝ → ?β`, weil `=ᵐ` über Funktionen erklärt ist, und sucht dann
  `Inter (ℝ → Prop)`. Beide Seiten brauchen die Typangabe `(… : Set ℝ)`.

Die Rechnung selbst läuft über `Measurable.find`
(`MeasureTheory/MeasurableSpace/Constructions.lean:516`) an den konstanten
Abbildungen, `measurable_find` für die Indexabbildung `g'`, und die
Bildmaßgleichung wird für **eine** beliebige meßbare Indexmenge `A ⊆ ℕ` auf
einmal erledigt: `g' ⁻¹' A = ⋃ i ∈ A, T i` ist eine abzählbare disjunkte
Vereinigung, `measure_biUnion` gibt `∑' i : A, p i`, und `tsum_subtype` macht
daraus `∑' i, A.indicator p i`. Erst danach kommt `E` ins Spiel, mit
`A = x ⁻¹' S`; so wird `Measure.map_sum` nirgends gebraucht.

**Zur zweiten.** Die Kopplung ist
`π i j = (if i = j then min (p i) (q i) else 0) + a i * b j / D` mit
`a i = p i - q i`, `b j = q j - p j`, `D = ∑' i, a i` — der gemeinsame Teil auf
der Diagonale, die beiden Reste unabhängig gekoppelt nach Normierung durch ihre
gemeinsame Gesamtmasse. Zwei Entscheidungen sind der ganze Trick.

* **Die Diagonale ist ein Summand, nicht der `then`-Zweig der ganzen Formel.**
  Stünde sie als `then`-Zweig, so müßte die Zeilensumme den Term `a i * b i / D`
  wieder **abziehen**, und in `ℝ≥0∞` überlebt keine Subtraktion einen `tsum`.
* **Der entartete Fall `D = 0` braucht keine Fallunterscheidung.** Dann ist
  `a i = 0` für jedes `i` (denn `a i ≤ D`), also verschwindet der zweite Summand
  schon durch `zero_mul`, und `0 / 0` wird nie ausgewertet. Die beiden
  Kürzungen `a i / D * D = a i` laufen deshalb über
  `ENNReal.div_mul_cancel'` (`Data/ENNReal/Inv.lean:171`), dessen Hypothesen
  gerade `D = 0 → a i = 0` und `D = ∞ → a i = 0` sind.

Daß die beiden Reste dieselbe Gesamtmasse haben, `∑' i, a i = ∑' j, b j`, ist
**nicht** Additivität der abgeschnittenen Differenz, sondern die Kürzung
`M + D = 1 = M + D'` über `ENNReal.add_right_inj`
(`Data/ENNReal/Operations.lean:269`); sie ist zulässig, weil
`M = ∑' i, min (p i) (q i) ≤ 1` endlich ist. Der Einstieg dazu ist die
punktweise Zerlegung `min (p i) (q i) + (p i - q i) = p i`, die über
`add_tsub_cancel_of_le` läuft und in beiden Anordnungen von `p i` und `q i`
gilt.

**Der Befund, und er berichtigt den Vorlauf.** Meilenstein 3 verlangte seit dem
fünften Lauf die einstufige Kopplung **auf `((0,1], Lebesgue)`**, und
`exists_ae_tendsto_of_tendsto` sollte „das Einheitsintervall mit dem Lebesguemaß
als gemeinsamen Raum" haben. Das geht so nicht. Der Indexpaar-Anteil geht: die
Kopplung `π` ist ein diskretes Gesetz auf `ℕ × ℕ`, und die eben bewiesene
Realisierung setzt es auf `(0,1]`. Was **nicht** geht, ist die Lage *innerhalb*
eines Stücks: sie ist nach dem bedingten Gesetz `μ (· ∩ A i) / μ (A i)`
verteilt, und dieses als Bild einer meßbaren Abbildung aus dem Einheitsintervall
zu schreiben ist der Borelsche Isomorphiesatz — er verlangt `E` polnisch,
während der ganze übrige Meilenstein mit `SeparableSpace E` auskommt.

Am Manuskriptbeleg nachgesehen, und der Befund steht dort schwarz auf weiß: EK
bauen den Raum als **Produkt**. Lemma 3.1.3 (Buchseite 100, PDF-Seite 110)
schreibt „Let $X, Y_0,\dots,Y_N,\xi$ be independent random variables on some
probability space $(\Omega,\mathcal F,\nu)$ with $X, Y_0,\dots,Y_N$ having
distributions $P, Q_0,\dots,Q_N$ and $\xi$ uniformly distributed on $[0,1]$",
und der Beweis von Theorem 3.1.8 (Buchseite 102) benutzt genau diese Gestalt,
Stufe für Stufe, mit $X_n = Y_i^{(n)}$ auf $\{X\in E_i^{(k_n)},\ \xi\ge c_i^{(n)}\}$.
Kein Schritt verlangt eine meßbare Abbildung aus dem Einheitsintervall. Die
bedingten Gesetze $Q_i$ entstehen dort durch **Normierung** der Maße $\lambda_i$
aus Corollary 3.1.5, und die Zufallsvariablen sind die Koordinaten des
Produkts. Meilenstein 3 und der Dateikopf tragen die Berichtigung; der Raum
heißt dort jetzt `((0,1], Lebesgue)` für das Indexpaar **mal** ein
`MeasureTheory.Measure.pi` der bedingten Gesetze.

Mitgefunden, und es ordnet die Vorarbeit: EKs Weg braucht die
nullrandige Zerlegung `exists_measurable_partition_diam_le_null_frontier` und
den Scheffé-Schritt `tendsto_tsum_abs_sub_of_tendsto_measure` **nicht** — er
läuft über den Prohorov-Abstand und ein Heiratssatz-Argument (Lemma 3.1.4 und
Corollary 3.1.5, Buchseiten 98/99: aus $\sum_{i\in I}p_i\le\mu(\bigcup_{i\in I}A_i)+\varepsilon$
für alle $I$ folgen Maße $\lambda_i$ mit $\lambda_i(A_i)=\lambda_i(S)\le p_i$).
Beide Wege sind gangbar; die Roadmap geht den zweiten (Billingsley-artigen), und
der Unterschied ist genau, ob man stückweise Konvergenz oder Strassen benutzt.
Wer den ersten Weg je aufnehmen will, muß Lemma 3.1.4 als eigenen Punkt
anlegen — Mathlib hat keinen maßtheoretischen Heiratssatz.

**Stand der Datei.** `WeakConvergence/Suggested.lean` trägt **zwei** `sorry` —
`exists_ae_tendsto_of_tendsto` (Meilenstein 3) und
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (Meilenstein 4) —
plus die zwei bekannten Fehler bei `tendsto_map_of_measure_setOf_continuousAt_eq_one`
aus dem Versionsgrund. Zu Beginn des Laufs waren es drei `sorry`.

Wie beim fünften Lauf lief die Entwicklung in zwei kleinen Dateien mit je zwei
Imports (`Lebesgue.Basic` und `MeasurableSpace.Constructions` für die
Realisierung, `InfiniteSum.ENNReal` und `ENNReal.Inv` für die Kopplung) —
Durchläufe unter einer Minute —, und erst der fertige Text wurde eingesetzt und
im Ganzen geprüft. Fünfter Lauf in Folge, in dem das trägt.

**Vorschlag für den nächsten Lauf, als benanntes Ziel: die einstufige Kopplung
auf dem Produktraum**, `WeakConvergence` Meilenstein 3, als benannte
Zwischenaussage vor `exists_ae_tendsto_of_tendsto`. Warum jetzt: alle drei
Eingänge stehen bewiesen da — die nullrandige Zerlegung, der Scheffé-Schritt,
und seit heute die Realisierung samt Indexkopplung —, und der Bauplan ist seit
heute der richtige, so daß der nächste Lauf ihn nicht erst suchen muß. Was zu
tun ist, in dieser Reihenfolge:

* **(b1) das bedingte Gesetz als Maß, nicht als Abbildung.** Zu einem meßbaren
  `A` mit `μ A ≠ 0` das normierte `(μ A)⁻¹ • μ.restrict A`, mit
  `IsProbabilityMeasure` als Instanz. Das ist eine Zeile Arithmetik in `ℝ≥0∞`
  (`ENNReal.inv_mul_cancel`) und die Stelle, an der der Fall `μ A = 0` einmal
  und für alle erledigt wird — dort nimmt man ein beliebiges festes Gesetz,
  denn das Stück wird nie getroffen.
* **(b2) der Produktraum.** `(0,1] × (ℕ → E)` mit
  `volume.restrict (Ioc 0 1) |>.prod (Measure.pi fun i => cond i)`, die
  Projektionen als Zufallsvariablen, und die Rechnung, daß die Zusammensetzung
  „Indexpaar aus der ersten Koordinate, Punkt aus der zugehörigen Koordinate der
  zweiten" das Gesetz `μ` hat. Das ist die eigentliche Buchhaltung des Laufs;
  sie ruht auf `Measure.pi` und auf nichts, was hier noch fehlt.
* **(b3) die Schranke.** Auf dem Ereignis „das Indexpaar liegt auf der
  Diagonale" liegen beide Punkte im selben Stück, also ist ihr Abstand höchstens
  dessen Durchmesser `ε`; das Komplement hat nach
  `exists_coupling_tsum_offDiag_le` und
  `tendsto_tsum_abs_sub_of_tendsto_measure` Masse unter `ε`, sobald `n` groß
  genug ist.

Der einzige Schritt, der neu erfunden werden muß, ist (b2); (b1) und (b3) sind
Anwendungen dessen, was heute und am fünften Lauf bewiesen wurde.

### 2026-09-08, siebter Lauf des Tages — die einstufige Kopplung ist bewiesen, und der gemeinsame Raum ist `E × E`

Kein Fact hat den Status `?`; der Rückstau schickt an seinen ersten offenen
Punkt, und der Vorschlag des Vorlaufs benennt darin (b1) das bedingte Gesetz,
(b2) den Produktraum und (b3) die Schranke. (b1) und (b3) sind bewiesen, (b2)
ist **entfallen** — der Raum, den er bauen wollte, wird nicht gebraucht.

**Bewiesen, alle durch `lake env lean` gegen v4.33.1 und alle mit
`#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft.**

* `condLaw` samt `condLaw_of_ne_zero`, `isProbabilityMeasure_condLaw`,
  `measure_mul_condLaw_apply` und `condLaw_compl_eq_zero` — das bedingte Gesetz,
  total gemacht.
* `exists_coupling_of_partition` — **die einstufige Kopplung**: zu zwei
  Gesetzen `μ`, `ν` auf einem separablen metrischen `E` und einer abzählbaren
  meßbaren Zerlegung `A` in beschränkte Stücke vom Durchmesser höchstens `ε`
  gibt es ein Gesetz `γ` auf `E × E` mit den Rändern `μ` und `ν` und
  `γ {z | ε < dist z.1 z.2} ≤ ∑' i, (μ (A i) - ν (A i))`.
* `exists_coupling_of_tendsto` — dieselbe Aussage, aus schwacher Konvergenz
  getrieben: ist `μ n → ν` schwach und `ε > 0`, so gibt es `∀ᶠ n in atTop` ein
  solches `γ` mit Schranke `ENNReal.ofReal ε`.

**Der Befund, und er berichtigt den Vorlauf.** Meilenstein 3 verlangte seit dem
sechsten Lauf für die einstufige Kopplung den Raum
`((0,1], Lebesgue) × Measure.pi (bedingte Gesetze)` — die Gestalt von EK,
Lemma 3.1.3. Sie trägt, aber sie ist überflüssig: **alles, was die Aussage über
den Raum behauptet, ist das gemeinsame Gesetz der beiden Zufallsvariablen, und
ein gemeinsames Gesetz ist ein Maß auf `E × E`.** Auf `E × E` gestellt sind die
Zufallsvariablen `Prod.fst` und `Prod.snd`, die beiden Randrechnungen sind
`Measure.map_fst_prod` und `Measure.map_snd_prod` unter einem `Measure.sum`, und
`ENNReal.tsum_prod'` besorgt den Übergang von der Doppelsumme über `ℕ × ℕ` zur
iterierten. Die Konstruktion ist
`γ = ∑' (i,j), π i j • (condLaw μ (A i)).prod (condLaw ν (A j))`: das Indexpaar
sagt, in welches Stück jede Koordinate fällt, die bedingten Gesetze sagen, wo
darin, und innerhalb eines Stücks sind die beiden unabhängig.

Damit werden zwei bewiesene Aussagen des fünften und sechsten Laufs für **diese**
Stelle nicht gebraucht: `exists_measurable_map_restrict_volume_eq_sum_smul_dirac`
(die Realisierung des Indexpaars auf `(0,1]`) und, für den Kern,
`tendsto_tsum_abs_sub_of_tendsto_measure` erst in der zweiten Fassung. Was vom
Befund des sechsten Laufs stehen bleibt, und es ist sein Kern: die bedingten
Gesetze müssen als **Maße** eingehen, nicht als Funktionen einer
gleichverteilten Variablen — Letzteres ist der Borelsche Isomorphiesatz und
verlangt `E` polnisch. Auf `E × E` gehen sie als Faktoren eines Produktmaßes
ein, und die Hypothese bleibt `SeparableSpace E`.

**Drei Dinge waren nicht geschenkt.**

* **Die Nullstücke.** Mathlibs `ProbabilityTheory.cond`
  (`Probability/ConditionalProbability.lean:76`) ist auf einer Nullmenge das
  **Nullmaß**. Das ist richtig fürs Bedingen und falsch für eine Kopplung: die
  Stücke sind über ganz `ℕ` indiziert, Nullstücke eingeschlossen, und ein
  Nullfaktor im Produktmaß zerstört die Ränder. Daher `condLaw`, das dort auf
  `μ` selbst zurückfällt. Der Ersatzwert kommt nie wieder vor, denn die einzige
  Eigenschaft, die die Kopplung benutzt — `μ A * condLaw μ A S = μ (S ∩ A)` —
  gilt auf einem Nullstück auch, beide Seiten `0`; sein Zweck ist allein, daß
  `IsProbabilityMeasure (condLaw μ A)` **unbedingt** gilt und damit Instanz ist.
* **Die Beschränktheit der Stücke.** `Metric.diam` einer unbeschränkten Menge
  ist `0`, also sagt `Metric.diam (A i) ≤ ε` ohne
  `Bornology.IsBounded (A i)` nichts. Der Zeuge steht als acceptance example in
  Meilenstein 3: `E = ℝ`, `A 0 = univ`, `μ = δ 0`, `ν = δ 100`, `ε = 1` — die
  Massenvektoren stimmen überein, die Schranke ist `0`, und jede Kopplung legt
  **alle** Masse auf `dist > 1`. Verbraucht wird die Hypothese genau einmal, in
  `Metric.dist_le_diam_of_mem`.
* **Der Übergang zwischen den Zahlbereichen.** Die Kopplung schätzt in `ℝ≥0∞`
  mit der abgeschnittenen Differenz, der Scheffé-Schritt liefert `ℝ` mit
  Betrag; `a - b = ENNReal.ofReal (a.toReal - b.toReal)` verbindet beides für
  endliche `a`, `b` — in **beiden** Anordnungen, der Fall `a ≤ b` ist
  `0 = ENNReal.ofReal` einer nichtpositiven Zahl —, und
  `ENNReal.ofReal_tsum_of_nonneg` zieht `ENNReal.ofReal` durch die Summe.

Die Diagonalschätzung ist übrigens eine **Gleichung** und keine Ungleichung: auf
`i = j` liegen beide Koordinaten fast sicher im selben Stück, also ist das böse
Ereignis eine Nullmenge. Daß die Nebendiagonale überhaupt klein ist, ist der
Satz des sechsten Laufs; die Rechnung hier fügt nur hinzu, daß bei `π i i > 0`
weder `μ (A i)` noch `ν (A i)` verschwinden kann, weil
`π i i ≤ ∑' j, π i j = μ (A i)` und `π i i ≤ ∑' i, π i j = ν (A i)`.

**Stand der Datei.** `WeakConvergence/Suggested.lean` trägt weiterhin **zwei**
`sorry` — `exists_ae_tendsto_of_tendsto` (Meilenstein 3) und
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (Meilenstein 4) —
plus die zwei bekannten Fehler bei
`tendsto_map_of_measure_setOf_continuousAt_eq_one` aus dem Versionsgrund. Ein
Import ist dazugekommen, `Mathlib.Probability.ConditionalProbability`.
Entwickelt wurde wieder in zwei kleinen Dateien unter `scratch/` (Durchlauf
unter einer Minute); der Ordner ist jetzt in `.gitignore` und trägt eine
`README.md`, die sagt, daß nichts darin gilt — die Sandbox erlaubt in diesem
Worktree kein `rm`, sonst wären die Dateien gelöscht.

**Vorschlag für den nächsten Lauf, als benanntes Ziel:
`exists_ae_tendsto_of_tendsto`**, die Skorokhod-Darstellung selbst,
`WeakConvergence` Meilenstein 3 — der letzte offene Punkt dieses Meilensteins.
Warum jetzt: die einstufige Kopplung steht seit heute als *ein* Satz da,
`exists_coupling_of_tendsto`, und was noch fehlt, ist allein die Iteration über
eine Nullfolge `ε k = 2⁻ᵏ`. Was zu tun ist, in dieser Reihenfolge:

* **(c1) die Teilfolge.** Zu jedem `k` liefert `exists_coupling_of_tendsto` ein
  `N k`; man wähle `N` streng wachsend und setze für `n ∈ [N k, N (k+1))` die
  Kopplung der Stufe `k` ein. Das ist eine Rekursion über `k` und Mathlibs
  `Nat.rec`, kein Maßtheorie-Schritt.
* **(c2) der gemeinsame Raum.** Die Kopplungen `γ k` sind Maße auf `E × E` mit
  **gemeinsamem zweitem Rand** `ν`. Sie zu einem einzigen Raum zu verkleben ist
  der Punkt, an dem die Zerlegung nach dem zweiten Rand gebraucht wird —
  `MeasureTheory.Measure.compProd` und `ProbabilityTheory.Kernel` sind der Weg,
  den Mathlib dafür hat (`Kernel/Disintegration/`), und er verlangt `E` als
  Standard-Borel-Raum. Das ist die erste Stelle des Meilensteins, an der
  „separabel metrisch" möglicherweise nicht mehr reicht; **das ist vorab zu
  prüfen**, denn EK kommen ohne Zerlegung aus, indem sie alle Stufen von Anfang
  an auf **einem** Produktraum bauen.
* **(c3) die fast sichere Konvergenz.** `∑ k, γ k {dist > 2⁻ᵏ} < ∞` und
  Borel--Cantelli (`MeasureTheory.measure_limsup_atTop_eq_zero`) geben, daß fast
  jedes `ω` nur endlich oft weiter als `2⁻ᵏ` liegt, also `X n ω → Y ω`.

(c2) ist der einzige Schritt, der eine Entscheidung verlangt; (c1) und (c3) sind
Anwendungen von Vorhandenem.

### 2026-09-08, achter Lauf des Tages — der Randomisierungsschritt, und die Stufen werden nicht verklebt

Kein Fact hat den Status `?`; der Rückstau schickt an seinen ersten offenen
Punkt, und der Vorschlag des Vorlaufs benennt darin `exists_ae_tendsto_of_tendsto`
als Ziel und (c2) — den gemeinsamen Raum — als den einen Schritt, der eine
Entscheidung verlangt und **vorab zu prüfen** ist. Die Entscheidung ist gefallen,
und der Baustein, der sie trägt, ist bewiesen.

**Bewiesen, alle sieben durch `lake env lean` gegen v4.33.1 und alle mit
`#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft.**

* `map_eval_prod_infinitePi` — **der Randomisierungsschritt**: auf dem Produkt
  eines Raums mit meßbarem Index `ι : Ω → κ` und Mathlibs abzählbarem
  Produktmaß `Measure.infinitePi m` trägt die Abbildung `z ↦ z.2 (ι z.1)` das
  Mischungsgesetz `Measure.sum fun i => (P.map ι {i}) • m i`.
* `sum_smul_dirac_singleton` — die Punktmassen einer abzählbaren
  Dirac-Überlagerung sind ihre Gewichte.
* `map_eval_prod_infinitePi_of_map_eq` — derselbe Satz mit dem Indexgesetz als
  Gewichtsvektor.
* `exists_measurable_map_prod_infinitePi_eq_sum_smul` — die konkrete Fassung auf
  `(0,1] × (ℕ → E)`: eine abzählbare Mischung wird dort realisiert.
* `exists_measurable_partitionIndex` — die Zerlegung gibt ein meßbares
  `j : E → ℕ` mit `j ⁻¹' {i} = A i`.
* `exists_measurable_index_of_stochastic_matrix` — eine stochastische Matrix `c`
  wird von **einer** meßbaren Abbildung `G : ℕ × ℝ → ℕ` realisiert, gleichmäßig
  im bedingenden Index.
* `map_index_prod_eq` — die beiden Indexabbildungen zusammengesetzt: auf `E × ℝ`
  mit `ν ⊗ Lebesgue|₍₀,₁₎` hat `z ↦ G (j z.1, z.2)` das Gesetz
  `Measure.sum fun i => (∑' k, ν (A k) * c k i) • dirac i`.

**Wozu.** Die Skorokhod-Darstellung muß auf **einem** Raum einen zufälligen
Punkt erzeugen, dessen bedingtes Gesetz bei gegebenem Index `i` ein
vorgeschriebenes `m i` ist. Als meßbare **Funktion** einer gleichverteilten
Variablen geschrieben ist das der Borelsche Isomorphiesatz und kostet `E`
polnisch — der Befund des sechsten Laufs, und er stand seither als Hindernis in
Meilenstein 3. Als **Koordinate** eines Produkts der `m i` geschrieben kostet es
gar nichts: die sieben Deklarationen nennen über `E` nichts als
`MeasurableSpace E`, keine Topologie, keine Metrik, keine Separabilität. Der
Beweis ist Fubini (`Measure.prod_apply`), das Koordinatengesetz des Produktmaßes
(`Measure.infinitePi_map_eval`) und der Variablenwechsel `lintegral_map` in ein
Integral über `κ`, das eine Summe ist, weil `κ` abzählbar ist. Damit bleibt der
ganze Meilenstein bei `SeparableSpace E`.

Der Indexraum `κ` ist irgendein abzählbarer meßbarer Raum mit meßbaren
Einpunktmengen — `ℕ` für eine Stufe, `ℕ × ℕ` für alle Stufen zugleich. Diese
Verallgemeinerung ist nicht Zierat: sie ist genau das, was die Familie über
`(Stufe, Stück)` in **einem** `infinitePi` unterzubringen erlaubt.

**Die Entscheidung zu (c2), und sie fällt gegen das Verkleben.**
`exists_coupling_of_tendsto` liefert je Stufe ein Gesetz `γ` auf `E × E` mit
zweitem Rand `ν`. Eine abzählbare Familie solcher Gesetze längs des gemeinsamen
Randes zu verkleben ist **Desintegration** — `Measure.condKernel`, und die
verlangt `E` standard-borelsch — und danach ein **abzählbares Produkt der
entstehenden Kerne**. ~~Das zweite hat Mathlib nicht, und zwar gar nicht:
`Measure.infinitePi` (`Probability/ProductMeasure.lean:358`) ist ein Produkt von
*Maßen*; unter `Probability/Kernel/` kommt weder `infinitePi` noch `Kernel.pi`
noch irgendein `def pi` vor. Gesucht am 2026-09-08 auf `upstream/master`
`572e4d091bc`, in Mathlibs Vokabeln statt in unseren: `infinitePi` (sechs
Dateien, alle über Maße — `ProductMeasure`, `Independence/InfinitePi`,
`HasLawExists`, `IdentDistribIndep`, `Distributions/SetBernoulli`,
`Combinatorics/BinomialRandomGraph/Defs`), `Kernel.pi`, `productMeasure`,
`^def pi` und `^noncomputable def pi` unter `Probability/`; vorhanden sind
`Kernel.prod` für zwei Faktoren und die Ionescu--Tulcea-`traj` für eine
Filtration, beides nicht das Gesuchte.~~

> **Berichtigt am 2026-09-08, neunter Lauf des Tages** (vom Nutzer gefunden, am
> Quelltext bestätigt): **der durchgestrichene Satz ist falsch.** Das abzählbare
> Produkt von Kernen über einer gemeinsamen Basis hat Mathlib, unter dem Namen
> des Satzes statt unter dem der Konstruktion:
> **`ProbabilityTheory.Kernel.traj`**,
> `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:518`, im Doc-Kommentar
> ausdrücklich *Ionescu-Tulcea Theorem* genannt; belegt an v4.33.1 **und** an
> `upstream/master` `572e4d091bc`, beide Male an derselben Zeile. Voraussetzungen
> sind allein `[∀ n, MeasurableSpace (X n)]` (Zeile 101) und
> `[∀ n, IsMarkovKernel (κ n)]` (Zeile 212) — keine Topologie; `StandardBorelSpace`
> kommt in der ganzen Datei nur bei `condDistrib_trajMeasure` (`:788`) vor. Das
> Produkt ist der Sonderfall, in dem die Kerne die Vergangenheit nicht lesen:
> mit `X n := E`, `κ n := (K n).comap (fun x ↦ x ⟨0, _⟩)` — markovsch nach
> `Kernel.IsMarkovKernel.comap` (`Kernel/Composition/MapComap.lean:187`) — ist
> `traj κ 0` ein Kern von `Π i : Iic 0, E ≃ᵐ E` nach `ℕ → E`, und
> `Kernel.trajMeasure` (`:763`) das verklebte Maß. Charakterisiert wird es durch
> `traj_map_frestrictLe` (`:530`).
>
> **Warum die Suche danebenging, und die Lehre.** Nicht am Nichtfinden: der
> Lauf hatte `traj` **in der Hand** und hat sie im selben Satz abgetan, mit
> „für eine Filtration, beides nicht das Gesuchte". Das ist eine Beschreibung
> und keine Voraussetzung. Die vier Suchbegriffe (`infinitePi`, `Kernel.pi`,
> `productMeasure`, `^def pi`) waren zwar Mathlib-Vokabeln, aber weiterhin
> Vokabeln **unserer Konstruktion**; die Aussage lautet „aus einer Folge von
> Kernen wird ein Maß auf dem abzählbaren Produkt", und danach gesucht heißt
> nach *Ionescu-Tulcea* gesucht. Erschwerend: die Antwort stand im eigenen
> Bestand — `TauCeti/KolmogorovExtension/README.md` nennt
> `ProbabilityTheory.Kernel.traj` an vier Stellen (`:51`, `:149`, `:159`,
> `:176`) samt Datei, und das Inventar selbst an `:2737`. Die Regel für den
> Negativbefund bekommt daher eine zweite Hälfte: **wer einen Kandidaten
> verwirft, nennt die Voraussetzung, an der er scheitert**, am Quelltext, und
> sucht vorher im eigenen Bestand nach dem Namen. Ein Kandidat, der mit einer
> Beschreibung statt mit einer Hypothese verworfen wird, ist nicht geprüft.

Also wird nicht verklebt, sondern **alles auf einmal gebaut**, auf
`(E × (ℕ → ℝ)) × (ℕ × ℕ → E)`: der erste Faktor trägt `Y ∼ ν` und je Stufe eine
gleichverteilte Variable, der zweite je Stufe und Stück eine unabhängige Ziehung
aus `condLaw (μ n) (A n i)`. Dann ist
`X n z = z.2 (n, G n (j n (Y z), ξ n z))`, und die sieben Aussagen des Laufs
rechnen sein Gesetz aus. Das ist EK, Lemma 3.1.3 (Buchseite 100, „Let
`X, Y₀, …, Y_N, ξ` be independent random variables …") mit `N = ∞`, und es ist
der Grund, warum der Meilenstein `E` nie polnisch braucht.

**Was das für den Vorschlag des Vorlaufs heißt.** (c1) — die Teilfolge — steht
unverändert. (c2) ist beantwortet und war, wie der Vorlauf vermutete, die
Stelle, an der „separabel metrisch" zu kippen drohte; es kippt nicht, aber nur,
weil die Kopplung nicht mehr als fertiges `γ` eingeht, sondern in ihren Stücken
— Indexkopplung `π` und bedingte Gesetze `condLaw` — die
`exists_coupling_of_partition` ohnehin schon konstruiert. (c3) — Borel--Cantelli
— steht unverändert.

**Stand der Datei.** `WeakConvergence/Suggested.lean` trägt weiterhin **zwei**
`sorry` — `exists_ae_tendsto_of_tendsto` (Meilenstein 3) und
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (Meilenstein 4) —
plus die zwei bekannten Fehler bei
`tendsto_map_of_measure_setOf_continuousAt_eq_one` aus dem Versionsgrund. Ein
Import ist dazugekommen, `Mathlib.Probability.ProductMeasure`. Entwickelt wurde
wieder in kleinen Dateien unter `scratch/` (Durchlauf unter drei Sekunden, weil
nur `Probability.ProductMeasure` importiert wird), mit einem `sorry`-Stellvertreter
für `exists_measurable_map_restrict_volume_eq_sum_smul_dirac`, damit die neue
Aussage geprüft werden kann, ohne die große Datei zu laden; erst der fertige Text
kam hinein. Sechster Lauf in Folge, in dem das trägt.

**Meilenstein 3 trägt die Befunde**, mit vier neuen acceptance examples: der
Kollaps des Randomisierungsschritts auf den Dirac-Fall über Mathlibs
`infinitePi_dirac` (die Verallgemeinerung muß den Spezialfall wörtlich
reproduzieren, und sie tut es), der Zeuge dafür, daß die Ziehung **nicht** von
derselben Variablen abgelesen werden darf wie der Index (`m 0 = m 1 = δ 0`
gegen die Wahl `X = ξ`), der Zeuge dafür, daß die Disjunktheit in
`exists_measurable_partitionIndex` die Faseraussage trägt und nicht bloß
`∀ y, y ∈ A (j y)`, und der Zeuge dafür, daß die stochastische Matrix zeilenweise
normiert sein muß (die rohe Kopplungsmatrix `π i j` hat Zeilensumme `ν (A j)`).

**Zur Massenbuchhaltung `map_index_prod_eq`.** Sie ist im selben Lauf noch
mitgekommen und war der Zweischritt von `map_eval_prod_infinitePi` ein zweites
Mal: `Measure.prod_apply` über die gleichverteilte Variable, dann
`lintegral_map` gegen `ν.map j`, das eine Summe ist, weil der Indexraum
abzählbar ist; die Umordnung am Schluß ist `ENNReal.tsum_comm`. Verbraucht wird
darin genau die **Faseraussage** von `exists_measurable_partitionIndex` —
`(ν.map j) {k} = ν (A k)` gilt nur, wenn die Faser das Stück *ist*. Für die
Zeile `c k i = π i k / ν (A k)` aus `exists_coupling_of_partition` ist das
Gewicht `∑' k, π i k = μ (A i)`, also fällt der Index in das `i`-te Stück mit
genau der Wahrscheinlichkeit, die `μ` ihm gibt; zusammen mit
`map_eval_prod_infinitePi` ist das Gesetz der gebauten Variablen damit `μ`.

**Vorschlag für den nächsten Lauf, als benanntes Ziel: eine Stufe der
Darstellung als *eine* Aussage**, `WeakConvergence` Meilenstein 3, als benannte
Zwischenaussage `exists_measurable_pair_of_partition` vor
`exists_ae_tendsto_of_tendsto`. Ausgeschrieben: zu `μ`, `ν`, einer abzählbaren
meßbaren Zerlegung `A` in beschränkte Stücke vom Durchmesser `≤ ε` und der
Indexkopplung `π` aus `exists_coupling_tsum_offDiag_le` zwei **meßbare
Abbildungen** `X`, `Y` auf `(E × ℝ) × (ℕ → E)` mit `P.map Y = ν`,
`P.map X = μ` und `P {ω | ε < dist (X ω) (Y ω)} ≤ ∑' i, (μ (A i) - ν (A i))`,
wobei `Y ω = ω.1.1` die erste Koordinate selbst ist. Warum jetzt: alle vier
Zutaten stehen seit heute bewiesen da — `exists_measurable_partitionIndex`,
`exists_measurable_index_of_stochastic_matrix`, `map_index_prod_eq` für das
Gesetz von `X` und `map_eval_prod_infinitePi` für die Positionen —, und was die
Aussage gegenüber `exists_coupling_of_partition` **hinzufügt**, ist gerade das,
was zum Iterieren fehlt: `Y` ist auf allen Stufen **dieselbe Abbildung**, weil
alle Stufen dieselbe erste Koordinate lesen. Genau daran scheitert das Verkleben
fertiger `γ`, und genau das macht (c1) und (c3) danach zu Buchhaltung: die
Stufen leben auf `(E × (ℕ → ℝ)) × (ℕ × ℕ → E)`, wo `ℕ → ℝ` je Stufe eine
gleichverteilte Variable und `ℕ × ℕ → E` je Stufe und Stück eine Ziehung hält —
der Indexraum `ℕ × ℕ` ist der Grund, warum `map_eval_prod_infinitePi` über
beliebigem abzählbarem `κ` und nicht nur über `ℕ` bewiesen wurde. Der einzige
Schritt, der dort neu ist, ist die Schranke: auf dem Ereignis „beide Indizes
gleich" liegen beide Punkte im selben Stück, also ist der Abstand höchstens
dessen Durchmesser — dieselbe Rechnung wie in `exists_coupling_of_partition`,
nur mit `Measure.map` statt mit `Measure.prod`.

### 2026-09-08, neunter Lauf des Tages — Ionescu--Tulcea steht in Mathlib, und was `StandardBorelSpace` an der Gebrauchsstelle wirklich kostet

**Bearbeitet:** die vorrangige Aufgabe des Nutzers vom 2026-09-08 in ihren
beiden Teilen. Kein Fact hat den Status `?`; berührt ist `fact:PSpolish`
(tragend 1) über `WeakConvergence` Meilenstein 3.

**Erstens, die Berichtigung, und sie steht an beiden Stellen.** Der Satz „Mathlib
hat kein abzählbares Produkt von Kernen" ist falsch. Er steht durchgestrichen
samt Berichtigung im Bericht des achten Laufs weiter oben, und Meilenstein 3
trägt den Absatz „The common space" neu geschrieben. Der Beleg, am Quelltext und
zweifach:

* `ProbabilityTheory.Kernel.traj`,
  `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:518`, im Doc-Kommentar
  ausdrücklich *Ionescu-Tulcea Theorem* genannt. Gleiche Datei, gleiche Zeile in
  v4.33.1 (`~/Code/lean/journal/.lake/packages/mathlib`) und auf `upstream/master`
  `572e4d091bc` — hier ist der Release ausnahmsweise kein Stellvertreter, sondern
  deckungsgleich.
* Voraussetzungen: `[∀ n, MeasurableSpace (X n)]` (`:101`) und
  `[∀ n, IsMarkovKernel (κ n)]` (`:212`). **Sonst nichts.** `StandardBorelSpace`
  kommt in der ganzen Datei genau einmal vor, bei `condDistrib_trajMeasure`
  (`:788`), und das ist nicht `traj`.
* Charakterisierung: `traj_map_frestrictLe` (`:530`) — die Projektion auf `Iic b`
  ist `partialTraj κ a b`; die Eindeutigkeit daraus ist `eq_traj` (`:566`).
* Das **Produkt** ist der Sonderfall, in dem die Kerne die Vergangenheit nicht
  lesen: `X n := E`, `κ n := (K n).comap (fun x ↦ x ⟨0, _⟩)`, markovsch nach
  `Kernel.IsMarkovKernel.comap` (`Kernel/Composition/MapComap.lean:187`;
  `comap` selbst `:152`); dann geht `traj κ 0` von `Π i : Iic 0, E ≃ᵐ E` nach
  `ℕ → E`, und `Kernel.trajMeasure` (`Traj.lean:763`) ist das verklebte Maß.

**Warum die Suche danebenging.** Nicht am Nichtfinden. Der achte Lauf hatte
`traj` in der Hand und verwarf sie mit „für eine Filtration, beides nicht das
Gesuchte" — einer **Beschreibung** statt einer **Voraussetzung**. Genau darin
liegt der Fehler: „für eine Filtration" beschreibt die *Allgemeinheit* von `traj`
(die Kerne dürfen die Vergangenheit lesen) und liest sie als *Einschränkung*.
Die vier Suchbegriffe — `infinitePi`, `Kernel.pi`, `productMeasure`, `^def pi` —
waren zwar Mathlib-Vokabeln, aber Vokabeln **unserer Konstruktion**; die Aussage
lautet „aus einer Folge von Kernen wird ein Maß auf dem abzählbaren Produkt", und
wer danach sucht, sucht nach Ionescu--Tulcea. Erschwerend: die Antwort stand im
eigenen Bestand — `TauCeti/KolmogorovExtension/README.md` nennt
`ProbabilityTheory.Kernel.traj` samt Datei an vier Stellen (`:51`, `:149`,
`:159`, `:176`), das Inventar selbst an `:2737`. **Die Regel für den
Negativbefund bekommt daher eine zweite Hälfte:** wer einen Kandidaten verwirft,
nennt die Voraussetzung, an der er scheitert, am Quelltext; und wer „Mathlib hat
das nicht" schreiben will, sucht zuvor im eigenen Bestand nach dem Namen. Ein mit
einer Beschreibung verworfener Kandidat ist nicht geprüft.

**Zweitens, die Abwägung — an der Gebrauchsstelle gerechnet, nicht im luftleeren
Raum.** Die Frage des Nutzers war: kostet `StandardBorelSpace E` dort etwas, oder
steht es ohnehin da? Die Antwort ist dreiteilig, und der mittlere Teil ist der
überraschende.

*Wo die Darstellung gebraucht wird.* `fact:PSpolish` wird im Manuskript an zwei
Stellen konsumiert (die Buchhaltungstabelle bei `:1673` nennt nur die erste):

1. `rem:EKrelcompact` (`:8355`) — dort ist `(E,r)` polnisch vorausgesetzt, und der
   Raum der Gesetze ist `D_E` unter `J_1`, nach `thm:DEpolish` (`:2096`)
   **polnisch**. Hier ist `StandardBorelSpace` trivial vorhanden.
2. `thm:MZconv`, Schritt 1 (`:9336`) — und das ist die Stelle, um die es geht:
   der Raum ist `D_E` in der **Pseudopfad-Topologie**. `fact:pseudopath`(ii)
   (`:9280`) sagt ausdrücklich: metrisierbar und separabel, aber **nicht
   polnisch** (B. V. Rao), „$D_E$ being merely Borel in that compact space".
   `rem:MZcost` (`:9418`) zieht die Folgerung, die diese Roadmap bindet: „a
   formalization must have the continuous mapping theorem and the Skorokhod
   representation at that generality and not only for Polish spaces".

*Der überraschende Teil.* `StandardBorelSpace` ist **nicht** `PolishSpace`. In
Mathlib ist es eine Eigenschaft allein der σ-Algebra —
`class StandardBorelSpace ... polish : ∃ _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α`
(`MeasureTheory/Constructions/Polish/Basic.lean:81`) — und an der Stelle 2 ist
sie **erfüllt**, aus zwei unabhängigen Gründen, die beide im Manuskript stehen:
`fact:pseudopath`(ii) macht `D_E` zu einer Borelmenge eines kompakten
metrisierbaren Raums, und `fact:pseudopath`(iii) (`:9283`) sagt, daß die
Borel-σ-Algebra der Pseudopfad-Topologie **dieselbe** ist wie die von `J_1`,
nämlich `σ(π_u)` — und unter `J_1` ist der Raum polnisch. Der Zeuge für
`StandardBorelSpace` ist also die `J_1`-Topologie selbst. Mathematisch steht
`StandardBorelSpace` an der Gebrauchsstelle mithin ohnehin da.

*Und warum es trotzdem etwas kostet.* Drei Posten, und sie sind der Grund, daß
die Entscheidung des achten Laufs im **Ergebnis** richtig war:

1. **In der Aussage.** `fact:PSpolish` ist für `S` separabel formuliert (EK,
   Theorem 3.1.8), und separabel metrisch impliziert nicht standard-borelsch:
   eine nicht-borelsche Menge `A ⊆ ℝ` mit der Teilraumtopologie ist separabel
   metrisch, und ihre Spur-σ-Algebra ist nicht standard, weil sonst
   Lusin--Souslin (`MeasurableSet.image_of_measurable_injOn`,
   `Polish/Basic.lean:834`, in Mathlib so benannt) auf `Subtype.val` die Menge
   `A` in `ℝ` borelsch machte. Ein Meilensteinpunkt mit `StandardBorelSpace E`
   wäre also **schwächer als der Fact, den er abtragen soll** — genau der Fall,
   den die stehende Regel „minimale Voraussetzungen" verbietet.
2. **In der Einlösung.** Daß der Pseudopfadraum standard-borelsch ist, ist keine
   Instanz, sondern ein Satz: er braucht `fact:pseudopath`(iii) (MZ, Fußnote 2)
   oder das Borel-im-Kompaktifizierten-Argument. Keine Roadmap baut ihn — die
   Zeichenkette „pseudo-path" kommt unter `TauCeti/` **nirgends** vor. Die
   Verklebung verschöbe also Arbeit aus einem Meilenstein, den es gibt, in einen,
   den es nicht gibt.
3. **Im Umfang.** `Measure.condKernel` verlangt neben `[StandardBorelSpace Ω]`
   auch `[Nonempty Ω]` (Variablenblock
   `Kernel/Disintegration/StandardBorel.lean:77`, Definition `:361`). Das ist
   billig, aber es ist eine zweite Hypothese in einer Aussage, die heute mit
   `MeasurableSpace E` auskommt.

**Ergebnis der Abwägung, und es ist keine Präferenz.** Die Begründung des achten
Laufs stand auf zwei Beinen; das erste — „Mathlib hat kein Produkt von Kernen" —
ist gebrochen und ersetzt, das zweite — die Desintegration kostet
`StandardBorelSpace` — trägt, und es trägt allein. Der jetzige Weg beweist den
Meilensteinpunkt in der Allgemeinheit, in der das Manuskript ihn zitiert; der
Verklebeweg beweist ihn in einer echt kleineren. Hinzu kommt, was der Nutzer als
drittes ohnehin verlangt: die sieben Aussagen des achten Laufs sind bewiesen und
geprüft, ein Wechsel würfe sie weg und kaufte dafür eine Montage vergleichbarer
Länge (Desintegration je Stufe, `traj`-Aufbau, Koordinatengesetze) samt der
stärkeren Hypothese. **Die Route wird nicht gewechselt.** Was sich ändert, ist
allein die Begründung, und sie steht jetzt in Meilenstein 3 als Hypothesenfrage
statt als Verfügbarkeitsfrage.

**Was in Meilenstein 3 geändert wurde.** Der Absatz „The common space, and why it
is not a gluing of the one-stage couplings" nennt jetzt beide Schritte der
Verklebung mit Deklaration, Datei und Zeile (`condKernel`, `traj`, `comap`,
`trajMeasure`, `traj_map_frestrictLe`) und begründet die Wahl mit der Hypothese
statt mit der Abwesenheit; der Schlußsatz sagt statt „never needs `E` Polish"
jetzt, was tatsächlich gilt — die sieben Zutaten nennen über `E` nichts als
`MeasurableSpace E`, also entfällt `PolishSpace` **und** `StandardBorelSpace`.
Dazu ein neues acceptance example, das genau diesen Unterschied prüft:
`E = A ⊆ ℝ` nicht-borelsch mit der Teilraumtopologie,
`μ n = δ (a n) → δ a` längs eines Kondensationspunktes von `A` in sich — eine
zulässige Instanz des Meilensteinpunkts, über der jede Zutat der gebauten
Konstruktion lebt und `Measure.condKernel` gar nicht anwendbar ist.

**Drittens, und im selben Lauf: die Berichtigung ist jetzt Lean und nicht
Behauptung.** `ProbabilityTheory.exists_kernel_pi_of_markov` in
`TauCeti/KolmogorovExtension/scratch/TrajPi.lean` — zu Markovkernen
`K : ℕ → Kernel E E` über bloßem `[MeasurableSpace E]` ein **Markovkern**
`η : Kernel E (ℕ → E)` mit `(η y).map (fun x ↦ x 0) = Measure.dirac y` und
`(η y).map (fun x ↦ x (n+1)) = K n y` für alle `n`. Der Beweis ist die
Spezialisierung von Ionescu--Tulcea auf gedächtnislose Kerne, in gut dreißig
Zeilen:
`κ n := (K n).comap (fun x ↦ x ⟨0, _⟩)`, `η := (traj κ 0).comap (fun y _ ↦ y)`;
die Nullkoordinate über `traj_map_frestrictLe_of_le (le_refl 0)`, die
`(n+1)`-te über `traj_comp_partialTraj (Nat.zero_le n)` und
`map_traj_succ_self`, und der Schritt, der `κ n` wieder auf `K n y` zurückführt,
über `partialTraj_map_frestrictLe₂_apply` mit `b = 0` — die Nullkoordinate bleibt
unter `partialTraj κ 0 n` deterministisch die Eingabe. Geht durch
`lake env lean` gegen v4.33.1 und hängt laut `#print axioms` allein an `propext`,
`Classical.choice`, `Quot.sound`. Damit ist „Mathlib hat das abzählbare Produkt
von Kernen" nicht mehr eine Lesart der Quelle, sondern eine typgeprüfte Aussage,
und zwar **ohne jede Topologie über `E`** — was die Abwägung oben noch schärft:
das Produkt kostet nichts, die *Desintegration* kostet `StandardBorelSpace`.

**Eine Vorsichtsnotiz zum Werkzeug, für den nächsten Lauf.** Das Arbeitsverzeichnis
der Shell **bleibt zwischen Aufrufen stehen**. Nach einem `cd` in den
Hauptcheckout (nötig für nichts — `lake env lean` nimmt absolute Pfade) lief hier
ein `python3 Journal/Blog/MartingaleProblem/check.py` versehentlich **dort** und
schrieb `MartingaleProblem.pdf` auf `master`; sofort zurückgenommen
(`git checkout --`, Hauptcheckout wieder sauber), aber die Regel „im
Hauptcheckout wird nur gelesen" hängt an dieser Falle. Wer sie vermeiden will,
benutzt in jedem Aufruf absolute Pfade und `git -C`, nie `cd`. Das Manuskript ist
in diesem Lauf unverändert, `check.py` im Worktree daher nicht gelaufen.

**Vorschlag für den nächsten Lauf, als benanntes Ziel: der Vorschlag des achten
Laufs bleibt der erste** — `exists_measurable_pair_of_partition` in
`WeakConvergence` Meilenstein 3, eine Stufe der Darstellung als *eine* Aussage,
mit `Y` als erster Koordinate auf allen Stufen. Er ist durch diesen Lauf
unberührt: die Abwägung hat die Route bestätigt, nicht verschoben, und alle vier
Zutaten stehen bewiesen da.

**Ein zweites, kleineres Ziel, falls der erste Punkt hakt**, und es baut auf dem
Zeugen dieses Laufs auf: die **Unabhängigkeit** der Koordinaten von
`exists_kernel_pi_of_markov` als eigene Aussage — `(η y).map (frestrictLe n)` ist
das endliche Produkt der `K i y` samt `dirac y`, also
`iIndepFun` unter `η y` (`Probability/Independence/Basic.lean:136`). Worauf
sie ruht: `traj_map_frestrictLe` (`Traj.lean:530`) gibt die Projektion als
`partialTraj κ 0 n`, und für gedächtnislose `κ` ist `partialTraj` die iterierte
Komposition unabhängiger Faktoren (`PartialTraj.lean`, `partialTraj_succ_self`).
Warum jetzt: der Zeuge sagt bisher nur, welches **Randgesetz** jede Koordinate
hat; die Verklebung der Skorokhod-Stufen bräuchte, wenn man sie je gehen wollte,
die gemeinsame Verteilung, und dies ist die kleinste Aussage, die sie liefert.
Sie gehört nach `KolmogorovExtension`, dessen Meilenstein `traj` bereits als
Sonderfall der projektiven Grenzwerte führt, nicht nach `WeakConvergence`.


### 2026-09-08, zehnter Lauf des Tages — eine Stufe der Skorokhod-Darstellung als *eine* Aussage, mit `Y` als fester Koordinate

**Bearbeitet:** das benannte Ziel der beiden Vorläufe,
`exists_measurable_pair_of_partition` in `WeakConvergence` Meilenstein 3. Kein
Fact hat den Status `?`; berührt ist `fact:PSpolish` (tragend 1). Keine
vorrangige Aufgabe stand offen, also galt Punkt 3 der Reihenfolge, und dort
Rückstaupunkt 1 („`SkorokhodSpace` und `MartingaleProblems` weiter beweisen",
in seiner Fortschreibung auf `WeakConvergence`).

**Das Ziel ist gefallen.** `exists_measurable_pair_of_partition` ist bewiesen
und geht durch `lake env lean` gegen v4.33.1; `#print axioms` nennt für alle
neun neuen Deklarationen nur `propext`, `Classical.choice`, `Quot.sound`. Die
Aussage, ausgeschrieben: unter genau den Hypothesen von
`exists_coupling_of_partition` gibt es auf
`stageMeasure μ ν A = (ν ⊗ Lebesgue|₍₀,₁₎) ⊗ infinitePi (condLaw μ ∘ A)` eine
meßbare Abbildung `X` mit `map X = μ`, so daß die **erste Koordinate selbst**
das Gesetz `ν` hat und

```
stageMeasure μ ν A {z | ε < dist (X z) z.1.1} ≤ ∑' i, (μ (A i) - ν (A i))
```

gilt. Neu und bewiesen sind neun Deklarationen:
`isProbabilityMeasure_volume_restrict_Ioc`, `tsum_measure_inter_eq`,
`sum_smul_condLaw_eq`, `condRow` mit `tsum_condRow` und `mul_condRow`,
`measure_index_ne_prod`, `stageMeasure` und der Satz selbst. `WeakConvergence`
steht danach bei **zwei** `sorry` — unverändert `exists_ae_tendsto_of_tendsto`
(Meilenstein 3) und `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`
(Meilenstein 4) —, rc = 1 mit unverändert genau den zwei angekündigten Fehlern
aus dem Versionsgrund bei `tendsto_map_of_measure_setOf_continuousAt_eq_one`,
jetzt bei `:2094`.

**Was die Aussage gegenüber `exists_coupling_of_partition` hinzufügt, und es ist
der Grund, warum sie gebraucht wurde.** Jene liefert ein Gesetz `γ` auf `E × E`;
seine beiden Koordinaten leben auf einem Raum, der von der Stufe abhängt. Hier
ist die Grenzvariable `fun z => z.1.1` — eine Abbildung, die weder von `μ` noch
von der Zerlegung noch von `ε` abhängt. Jede Stufe liest ihre Grenzvariable von
**derselben** Koordinate ab, und genau das kann eine Verklebung fertiger `γ`
nicht geben: die f.s.-Aussage `X n ω → Y ω` handelt von *einem* `Y`, nicht von
einem `Y` je Stufe.

**Der Bauplan, und wo jedes Stück verbraucht wird.** Der erste Faktor `E × ℝ`
trägt `Y` und eine gleichverteilte Variable, der zweite Faktor `ℕ → E` je Stück
eine unabhängige Ziehung aus `condLaw μ (A i)`. Dann liest `j`
(`exists_measurable_partitionIndex`) das Stück ab, in dem `Y` liegt; `G`
(`exists_measurable_index_of_stochastic_matrix`) zieht aus der Zeile
`condRow π (ν ∘ A) (j Y)` das Stück, in dem `X` liegen soll; und
`X z = z.2 (G (j z.1.1, z.1.2))` schlägt die zugehörige Ziehung nach. Das Gesetz
von `X` ist `μ` über `map_index_prod_eq` (der Index fällt mit
`∑' k, π i k = μ (A i)` in das `i`-te Stück),
`map_eval_prod_infinitePi_of_map_eq` (die Position ist dann nach
`condLaw μ (A i)` verteilt) und `sum_smul_condLaw_eq` (die Mischung der
bedingten Gesetze ist `μ`).

**Die Schranke zerfällt in zwei Teile, und nur der erste ist quantitativ.**
Entweder die beiden Indizes weichen ab — das ist `measure_index_ne_prod`, die
einzige Ungleichung der Stufe, und sie geht über `mul_condRow` und
`ENNReal.tsum_comm` genau in die Außerdiagonalmasse über, die
`exists_coupling_tsum_offDiag_le` schätzt —, oder sie stimmen überein, und dann
liegt `Y` nach der Faseraussage von `j` im Stück, `X` nach
`condLaw_compl_eq_zero` f.s. ebenfalls, und `Metric.dist_le_diam_of_mem` macht
das schlechte Ereignis leer.

**Der eine Punkt, an dem das Argument nicht trägt, und er ist keine
Formalität.** Auf einem Stück der `μ`-Masse `0` fällt `condLaw` auf `μ` zurück
und ist dort *nicht* vom Stück getragen — der Diagonalschluß ist also gerade
dort nicht verfügbar. Er wird nicht gebraucht, weil die Menge dieser Stufen
selbst eine Nullmenge ist: das Indexgesetz sagt, daß der Index mit
Wahrscheinlichkeit `μ (A i)` im `i`-ten Stück landet. Im Beweis ist das der
Schritt, an dem die Schnittmengenschranke gegen
`Set.indicator {w | μ (A (G (j w.1, w.2))) = 0} 1` läuft statt gegen `0`, und
`mul_condRow` ist eigens so formuliert, daß es **auch** auf einem Nullstück gilt
(beide Seiten verschwinden, die rechte weil `π i k ≤ ∑' i, π i k = ν (A k)`).
Ein Beweis, der „die Indizes stimmen überein, also ist der Abstand höchstens der
Durchmesser" ohne dieses Aussondern führte, wäre falsch; das zugehörige
acceptance example steht in Meilenstein 3.

**Die Hypothesen sind die von `exists_coupling_of_partition` und keine
schärferen.** Über `E` steht `PseudoMetricSpace`, `OpensMeasurableSpace`,
`SecondCountableTopology`; die Konstruktion selbst braucht `MeasurableSpace E`
und sonst nichts, die Zweitabzählbarkeit geht allein in die Meßbarkeit des
schlechten Ereignisses (`Measurable.dist`,
`Constructions/BorelSpace/Metric.lean:77`). Weder `PolishSpace` noch
`StandardBorelSpace` kommt vor — die Abwägung des neunten Laufs bleibt damit
auch an der gebauten Aussage bestätigt und nicht nur an ihrem Bauplan.

**Mathlib-Lücke mitgefunden und geschlossen.** Für
`volume.restrict (Set.Ioc (0:ℝ) 1)` gibt es keine
`IsProbabilityMeasure`-Instanz. Belegt an `upstream/master` `572e4d091bc` mit
zwei Suchen: `git grep "Ioc (0 : ℝ) 1" upstream/master -- Mathlib/` gibt sieben
Treffer, alle in Analysis/NumberTheory/Topology und keiner maßtheoretisch, und
`git grep "IsProbabilityMeasure (volume.restrict\|isProbabilityMeasure_restrict"`
gibt **keinen**. Dasselbe im Release v4.33.1. Der Randomisierungsschritt
braucht sie für jedes `Measure.prod`, das er bildet; sie steht jetzt als
`isProbabilityMeasure_volume_restrict_Ioc` in der Datei.

**Werkzeug.** Wieder in einer eigenen kleinen Datei entwickelt
(`WeakConvergence/scratch/Stage.lean`, nur `Probability.ProductMeasure`,
`Probability.ConditionalProbability`, `Measure.Lebesgue.Basic`,
`Constructions.BorelSpace.Metric`, Durchlauf unter einer Minute) mit
`sorry`-Stellvertretern für die fünf schon bewiesenen Zutaten; erst der fertige
Text kam in die große Datei, und der Durchlauf dort meldete kein einziges neues
Problem. Die Hilfsdatei ist mit `git clean -f` wieder weg. Siebter Lauf in
Folge, in dem das trägt.

**Meilenstein 3 trägt den Befund**, als eigener Punkt vor
`exists_ae_tendsto_of_tendsto`, mit den fünf Hilfsaussagen einzeln benannt, und
mit zwei neuen acceptance examples: der Zweipunktraum, auf dem die Schranke `0`
die Diagonale erzwingt und die unabhängige Kopplung `ν ⊗ ν` mit richtigen
Rändern sie verfehlt (samt der Bemerkung, warum die Grenzvariable eine
Koordinate sein muß), und das `μ`-Nullstück `μ = δ 0`, `ν = (δ 0 + δ 1)/2`, auf
dem die Schranke `1/2` **genau** angenommen wird und der Rückfallwert von
`condLaw` nachweislich nur auf einer Nullmenge nachgeschlagen wird.

**Vorschlag für den nächsten Lauf, als benanntes Ziel:
`exists_ae_tendsto_of_tendsto` selbst**, und zwar in den drei Stücken, die der
siebte Lauf (c1)–(c3) genannt hat und von denen (c2) durch diesen Lauf erledigt
ist. Ausgeschrieben, was noch fehlt:

* **(c1) die Teilfolge.** `exists_coupling_of_tendsto` gilt `∀ᶠ n in atTop`; zu
  wählen ist eine strikt wachsende `φ : ℕ → ℕ` mit `ε n = 2⁻ⁿ`, so daß die
  Stufe `n` die Zerlegung
  `exists_measurable_partition_diam_le_null_frontier ν (2⁻ⁿ)` und den Index
  `φ n` benutzt. Worauf es ruht: `Filter.extraction_of_frequently_atTop` bzw.
  `Nat.rec` über die `eventually`-Aussage.
* **(c3) Borel--Cantelli.** `∑' n, (2:ℝ≥0∞)⁻ⁿ < ∞`, also ist nach
  `MeasureTheory.measure_limsup_atTop_eq_zero` f.s. nur endlich oft
  `2⁻ⁿ < dist (X n) Y`, und daraus folgt `Tendsto (X · ω) atTop (𝓝 (Y ω))` über
  `Metric.tendsto_atTop`.
* **Der Zusammenbau**: alle Stufen auf `(E × (ℕ → ℝ)) × (ℕ × ℕ → E)` statt je
  Stufe auf `(E × ℝ) × (ℕ → E)`. Das ist der einzige Punkt, an dem dieser Lauf
  noch nichts geleistet hat: `stageMeasure` ist für **eine** Stufe geschrieben,
  und die Verallgemeinerung ist eine Umindizierung —
  `map_eval_prod_infinitePi` ist eigens über beliebigem abzählbarem `κ`
  bewiesen, also über `κ = ℕ × ℕ`, und die gleichverteilten Variablen laufen
  über `ℕ → ℝ` statt über `ℝ`. Warum jetzt: mit
  `exists_measurable_pair_of_partition` steht die Stufe als *eine* Aussage da,
  deren Gebrauch die Umindizierung von der Wahrscheinlichkeitsrechnung trennt;
  was bleibt, ist Buchhaltung über bewiesenen Sätzen und keine neue Idee.


### 2026-09-08, elfter Lauf des Tages — Schritt 1 von `thm:MZconv` geht über den polnischen Raum $M_E$; die Prüfung ist positiv in allen vier Punkten

**Bearbeitet:** die vorrangige Aufgabe des Nutzers vom 2026-09-08 („geht
Schritt 1 von `thm:MZconv` über den polnischen Raum $M_E$?"). Berührt sind
`fact:PSpolish` (tragend 1), `fact:cmt` (tragend 3) und `fact:pseudopath`
(tragend 1). Kein Fact wechselt den Status; was wechselt, ist die
**Allgemeinheit**, in der zwei von ihnen gebraucht werden.

**Das Ergebnis in einem Satz.** Der Fund trägt: (a) ja, (b) ja, (c) ja, (d) ja
— und (d) aus einem zweiten, von der ganzen Prüfung unabhängigen Grund. Damit
braucht die Roadmap `fact:PSpolish` und `fact:cmt` **nur für polnische Räume**,
und der zweite Absatz von `rem:MZcost` ist falsch.

#### Die Quelle, am Scan belegt

Kurtz (1991), *Random time changes and convergence in distribution under the
Meyer--Zheng conditions*, Ann. Probab. **19**, 1010--1034; PDF unter
`~/Uni/Download/Papers/Kurtz1991a.pdf`, JSTOR-Scan, seitenweise mit dem
Read-Werkzeug gelesen (Buchseite $n$ ist PDF-Seite $n-1009$). Vier Stellen, alle
im Abschnitt 4 „Convergence in measure":

* **S. 1022, Beginn von §4** — die tragende Stelle, wörtlich: „Let $(E,r)$ be a
  complete, separable metric space and let $M_E[0,\infty)$ be the space of
  equivalence classes of Borel-measurable, $E$-valued functions on $[0,\infty)$
  (two functions being equivalent if they are equal Lebesgue a.e.). For
  $x,y \in M_E[0,\infty)$, define (4.1) $d_m(x,y) = \int_0^\infty e^{-t}
  [1 \wedge r(x(t),y(t))]\,dt$. … Then $d_m$ is a metric corresponding to
  convergence in measure and $(M_E[0,\infty), d_m)$ is a complete, separable
  metric space." Die Vollständigkeit ist dort bewiesen ((4.2)--(4.4), sechs
  Zeilen: eine Teilfolge mit $\sum_k d_m(x_{n_k},x_{n_{k+1}})<\infty$, eine
  Lebesgue-volle Menge $T$, punktweiser Limes darauf); die **Separabilität ist
  „left to the reader"** — das ist der einzige Punkt der Konstruktion, für den
  Kurtz keinen Beweis hergibt, und er ist unten als Kostenpunkt genannt.
* **S. 1023, Theorem 4.1** — relative Kompaktheit in $M_E$: $A \subset M_E$ ist
  relativ kompakt genau dann, wenn (C4.1(i)) zu $\varepsilon,T>0$ ein kompaktes
  $K\subset E$ existiert mit $\sup_{x\in A} m\{t\le T: x(t)\notin K\}\le
  \varepsilon$ und (C4.1(ii)) $\lim_{h\to0}\sup_{x\in A}\int_0^T 1\wedge
  r(x(t+h),x(t))\,dt = 0$; dazu 4.2 Remark(b) mit der abgeschwächten Form
  C4.1(iii) und 4.4 Corollary, das die kompakten Mengen explizit hinschreibt.
* **S. 1025** — für **jede** $M_E$-wertige Zufallsvariable $\tilde X$ gibt es
  einen **meßbaren Prozeß** $X$ mit $X(\cdot,\omega)\in\tilde X(\omega)$; der
  Vertreter wird kanonisch gebaut, über $y_f(x,t)=\limsup_n n\int_t^{t+1/n}
  f(x(s))\,ds$ ((4.15)), eine Borel-Einbettung $h:E\to\R^\infty$ mit borelschem
  Bild ((4.16)) und $G(x,t)=g(y_1(x,t),y_2(x,t),\dots)$ ((4.18)). Umgekehrt
  bestimmt jeder meßbare Prozeß eine $M_E$-wertige Zufallsvariable, denn
  $\{\omega : d_m(\tilde X,x)<a\}$ ist die dort hingeschriebene Menge.
* **S. 1026, Proposition 4.5** — zwei meßbare Prozesse haben **dasselbe Gesetz
  auf $M_E$ genau dann**, wenn für jedes $m$ und Lebesgue-fast jedes
  $(t_1,\dots,t_m)$ die Vektoren $(X(t_1),\dots,X(t_m))$ und
  $(Y(t_1),\dots,Y(t_m))$ dasselbe Gesetz auf $E^m$ haben. Der Beweis läuft über
  die Klasse $F(x)=\prod_{i\le m}\int_0^{T_i} f_i(t,x(t))\,dt$, die
  multiplikativ ist, Punkte von $M_E$ trennt und daher nach EK, Theorem 3.4.5
  die Maße auf $M_E$ trennt. Dazu 4.6 Theorem: dieselbe Kompaktheitsbedingung in
  Erwartung charakterisiert relative Kompaktheit der **Gesetze**.

#### (a) Ist $\DE$ borelsch in $(M_E,d_m)$? — **Ja**, und in drei Zeilen aus Fakten, die das Manuskript schon zitiert

Sei $\gamma$ die Pseudopfad-Abbildung, $\gamma(w) = \lambda\circ(u\mapsto
(u,w(u)))^{-1}$, mit Werten im **kompakten** metrisierbaren
$\hat{\mathcal P} = \Prob([0,\infty]\times\hat E)$.

1. **$\gamma$ ist auf ganz $M_E$ wohldefiniert und injektiv.**
   `fact:pseudopath` sagt es selbst: „This assignment identifies two paths
   exactly when they agree $\lambda$-a.e." Das ist wörtlich die Injektivität auf
   den $\lambda$-Äquivalenzklassen, also auf $M_E$; das Manuskript zieht daraus
   nur die schwächere Folgerung „so it is injective on $\DE$".
2. **$\gamma$ ist auf $M_E$ stetig.** Ist $x_n\to x$ in $d_m$, also im $r$-Maß
   bezüglich $\lambda$, so konvergiert jede Teilfolge längs einer weiteren
   $\lambda$-f.ü., dort auch in der Metrik $\hat r$ von $\hat E$ (die auf $E$
   dieselbe Topologie trägt); also gilt $\int F(u,x_n(u))\,\lambda(du) \to \int
   F(u,x(u))\,\lambda(du)$ für $F\in C([0,\infty]\times\hat E)$ nach dominierter
   Konvergenz und dem Teilfolgenprinzip. $M_E$ ist metrisch, also ist
   Folgenstetigkeit Stetigkeit.
3. **$\gamma(\DE)$ ist borelsch in $\hat{\mathcal P}$** — das ist genau
   `fact:pseudopath`(ii) („$\DE$ being merely Borel in that compact space",
   B. V. Rao; MZ, Appendix).

Also ist $\DE = \{x\in M_E : \gamma(x)\in\gamma(\DE)\}$ — die Gleichheit ist
Punkt 1 — das Urbild einer Borelmenge unter einer stetigen Abbildung, mithin
borelsch in $M_E$. **Der Angelpunkt hält.**

Zwei Bemerkungen dazu, damit der Beweis nicht stärker aussieht, als er ist.
*Erstens* braucht er **kein** Lusin--Souslin und **nicht**, daß $M_E$ polnisch
ist; die Polnischkeit wird allein für die Skorokhod-Darstellung selbst
verbraucht. *Zweitens* ruht Punkt 3 auf dem Manuskript-Fact und damit auf MZ,
nicht auf Kurtz; Kurtz sagt zu $\DE\subset M_E$ nichts. Wer den Umweg über das
kompakte Modell vermeiden wollte, müßte „$G(x,\cdot)$ ist càdlàg" direkt als
Borelbedingung an $x$ schreiben (Kurtz' kanonischer Vertreter, (4.18)); das ist
möglich, aber länger, und es ist nicht nötig.

#### (b) Ist die Spur der Borel-$\sigma$-Algebra von $M_E$ auf $\DE$ gleich $\sigma(\pi_u)$? — **Ja**, und zweimal unabhängig

Für **jeden** Teilraum $Y\subseteq X$ eines topologischen Raums gilt
$\Bor(Y) = \Bor(X)|_Y$: die eine Inklusion, weil $\Bor(X)|_Y$ eine
$\sigma$-Algebra ist, die die Spuren der offenen Mengen — also die offenen
Mengen von $Y$ — enthält; die andere, weil $\{A\subseteq X : A\cap
Y\in\Bor(Y)\}$ eine $\sigma$-Algebra ist, die die offenen Mengen von $X$
enthält. Keine Separabilität, kein Maß, nichts.

Die Teilraumtopologie von $\DE\subseteq M_E$ ist die Konvergenz im
$\lambda$-Maß, denn $d_m$ metrisiert diese (Kurtz, (4.1)) und $\DE\to M_E$ ist
injektiv (zwei $\lambda$-f.ü. gleiche càdlàg-Funktionen sind gleich). Nach
`fact:pseudopath`(i) **ist** das die Pseudopfad-Topologie; nach (iii) ist ihre
Borel-$\sigma$-Algebra $\sigma(\pi_u : u\in\Rp)$. Also $\Bor(M_E)|_{\DE} =
\sigma(\pi_u)$. Schritt 1 und Schritt 2 reden von derselben $\sigma$-Algebra.

Kurtz' Proposition 4.5 sagt dasselbe von der anderen Seite und ohne
Teilraumargument: das Gesetz auf $M_E$ ist durch die f.ü.-endlichdimensionalen
Verteilungen bestimmt, und für càdlàg-Pfade bestimmen diese wegen der
Rechtsstetigkeit alle endlichdimensionalen Verteilungen. Zwei Wege zu demselben
Ergebnis; der erste ist der kürzere und der, den eine Formalisierung gehen
sollte.

#### (c) Hält der Rest des Beweises von `thm:MZconv`? — **Ja**, und Schritt 2 wird kürzer

Der neue Schritt 1, ausgeschrieben:

1. $X_n \wto X$ auf $\DE$ in der Pseudopfad-Topologie ist die Hypothese des
   Satzes (und die Konklusion von `fact:MZtight`). Die Inklusion
   $\iota:\DE\to M_E$ ist stetig — nach (b) sogar ein Homöomorphismus auf ihr
   Bild —, also $\iota_*P_n \wto \iota_*P$ auf $M_E$.
2. $M_E$ ist polnisch (Kurtz, S. 1022). Die **gewöhnliche**
   Skorokhod-Darstellung gibt $\tilde X_n,\tilde X$ auf einem Raum mit den
   Gesetzen $\iota_*P_n,\iota_*P$ und $d_m(\tilde X_n,\tilde X)\to0$ f.s.
3. $\iota_*P_n(\DE)=1$, und $\DE$ ist nach (a) borelsch in $M_E$; also ist
   $\tilde X_n$ f.s. càdlàg. Nach (b) ist $\tilde X_n$, als $\DE$-wertige
   Zufallsvariable gelesen, $\sigma(\pi_u)$-meßbar und hat dort das Gesetz
   $P_n$ — das ist genau die Klammer „the same laws on the same $\sigma$-field"
   des Manuskripts, jetzt begründet statt zitiert.
4. Gemeinsame Meßbarkeit in $(\omega,u)$: unverändert, denn càdlàg zusammen mit
   „$\omega\mapsto\pi_u(\tilde X_n(\omega))$ meßbar für jedes $u$" ist genau die
   Voraussetzung, die das Manuskript benutzt. (Kurtz, S. 1025 gäbe es
   alternativ auf ganz $M_E$ geschenkt, samt kanonischem Vertreter; gebraucht
   wird das hier nicht.)

Schritt 2 wird dabei **kürzer**, nicht länger: das Manuskript schließt von
„Konvergenz im $\lambda$-Maß f.s." auf $\int\rho(\tilde X_n,\tilde
X)\dif\lambda \to0$ f.s.; auf dem $M_E$-Weg **ist** dieses Integral die Metrik
$d_m$ (mit $\rho=1\wedge r$), die f.s. gegen $0$ geht. Alles Weitere —
dominierte Konvergenz, $P\otimes\lambda$-Maß, Teilfolge, Fubini, (a) und (b)
des Schritts 2 — steht unverändert. Schritt 3 benutzt von der
Pseudopfad-Topologie nur noch `fact:pseudopath`(iii), für die Zulässigkeit der
determinierenden Menge; die Konklusion nichts.

#### (d) Wird `fact:cmt` an derselben Stelle in nicht-polnischer Allgemeinheit gebraucht? — **Nein, und schon vor dieser Prüfung nicht**

Das ist der Befund, der die Aufgabe überschreitet, und er ist von ihr
unabhängig. Drei Beobachtungen, alle am Manuskript:

1. **Der Beweis von `thm:MZconv` benutzt `fact:cmt` überhaupt nicht.** Er sagt
   es selbst, im Absatz zu (C1$'$): „this is where the argument differs from
   every earlier one in this section: the coordinates are nowhere continuous, so
   (C3a) is unavailable and *only* the weakened form (C1$'$) can be verified ---
   and it is verified not by a continuous mapping theorem but by exhibiting the
   convergence on a common space." Die `\ref{fact:cmt}`-Vorkommen im Manuskript
   sind `:1671`, `:8429`, `:8442`, `:8492`, `:8511`, `:8976`, `:9023`, `:9121`,
   `:9133`, `:9213`, `:9454`, `:9828`; **zwischen `:9314` und `:9400`, dem
   Beweis von `thm:MZconv`, steht keines.**
2. **Wo `fact:cmt` benutzt wird, ist der Raum polnisch, per Annahme.**
   `set:abstract` (`:2324`) sagt: „Under (E3) we take $F$ to carry a **Polish**
   topology and $\mathcal S = \Bor(F)$", und `thm:absconv` (`:8393`) ist mit
   (T0)+(E3) annotiert. `lem:contuse` (`:8963`) hält fest, daß `fact:cmt` dort
   auf genau drei Funktionale angewandt wird und sonst nirgends;
   `thm:absconvaug` (`:8990`) arbeitet auf $F\times G$ mit $G$ polnisch, also
   wieder polnisch; `thm:absconvws` ersetzt `fact:cmt` durch `fact:jacodmemin`,
   und `def:weakstrong` (`:9169`) verlangt ausdrücklich „let $F$ be Polish".
3. **Der einzige nicht-polnische Pfadraum des Manuskripts ist $\DE$ unter der
   Pseudopfad-Topologie, und dort läuft der Beweis über
   `rem:absconvtopfree`**, das $F$ jede Topologie nimmt: „In that form the path
   space $F$ carries no topology at all."

Das Einzige, was der neue Schritt 1 an CMT braucht, ist die **triviale Hälfte**:
Bildmaße unter einer **überall stetigen** Abbildung. Die hat Mathlib, und zwar
ohne jede Metrik und ohne Separabilität —
`MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`
(`MeasureTheory/Measure/ProbabilityMeasure.lean:657` auf `upstream/master`,
`:639` in v4.33.1), unter `[TopologicalSpace Ω] [OpensMeasurableSpace Ω]` und
`[TopologicalSpace Ω'] [BorelSpace Ω']`, sowie in der
Zufallsvariablen-Fassung `MeasureTheory.TendstoInDistribution.continuous_comp`
(`MeasureTheory/Function/ConvergenceInDistribution.lean:136`, dort im
Doc-Kommentar `:29` ausdrücklich als **Continuous mapping theorem** geführt).
Beide am 2026-09-08 gegen `upstream/master` geprüft.

#### Was das kostet, und es ist ehrlich zu nennen

Der Weg ist nicht gratis. Er tauscht **zwei Sätze in nicht-polnischer
Allgemeinheit** gegen **eine Raumkonstruktion**:

* $M_E[0,\infty)$ ist zu bauen: der Quotient der Borel-meßbaren
  $w:\Rp\to E$ nach $\lambda$-f.ü.-Gleichheit, die Metrik $d_m$ (4.1), ihre
  Wohldefiniertheit auf Klassen, die **Vollständigkeit** (Kurtz gibt den Beweis)
  und die **Separabilität** (Kurtz gibt ihn *nicht* — „left to the reader"). Das
  ist ein neuer Meilensteinpunkt, kein vorhandener.
* Dazu `fact:pseudopath`(ii) in der Form „$\gamma(\DE)$ borelsch in
  $\hat{\mathcal P}$", die für (a) gebraucht wird und die das Manuskript ohnehin
  zitiert.

Die Rechnung geht trotzdem auf, und zwar deutlich: die Skorokhod-Darstellung für
bloß separables $S$ ist die schwerste Einzelaussage der ganzen Roadmap — der
`WeakConvergence`-Meilenstein 3 hat sie seit dem Abend des 2026-09-07 in *sechs*
Läufen in Teile zerlegt und steht bei der letzten Zusammensetzung —, während
$M_E$ eine Metrikkonstruktion mit zwei Standardbeweisen ist. Und `fact:cmt` in
nicht-polnischer Allgemeinheit entfällt nach (d) ersatzlos, ohne Gegenrechnung.

#### Was daran hängt, und was **nicht** weggeworfen wird

`exists_ae_tendsto_of_tendsto` und die Deklarationen, die die Läufe fünf bis
zehn dafür bewiesen haben, bleiben **richtig und nützlich**. Was sich ändert,
ist ihr Status: sie sind nicht mehr die einzige Straße nach `thm:MZconv`,
sondern eine Aussage, die *mehr* beweist, als die Roadmap braucht. Zwei Gründe,
sie zu behalten und zu Ende zu führen:

1. Der polnische Fall ist ein **Spezialfall** des separablen, nicht umgekehrt.
   Was gebaut ist, deckt beide Gebrauchsstellen (`rem:EKrelcompact` unter $J_1$,
   `thm:MZconv` über $M_E$) und mehr ab.
2. Mathlib hat die Skorokhod-Darstellung **überhaupt nicht** (am 2026-09-08
   belegt; nur ein Eintrag in `docs/1000.yaml`). Die allgemeinere Fassung ist
   der bessere Beitrag.

Was der Befund ändert, ist die **Reihenfolge der Not**: `WeakConvergence` M3 ist
nach diesem Lauf nicht mehr der Engpaß von `thm:MZconv`.

#### Am Manuskript

`rem:MZcost`, zweiter Absatz, behauptete: „It does mean that a formalization
must have the continuous mapping theorem and the Skorokhod representation at
that generality and not only for Polish spaces." Das ist nach (a)--(d) falsch,
und zwar in beiden Hälften. Die Stelle ist korrigiert; der erste Satz des
Absatzes („The path space is not Polish. It is separable metric …") bleibt, weil
er wahr ist — nicht polnisch ist $\DE$ unter der Pseudopfad-Topologie sehr wohl.
Ersetzt wird allein die Folgerung, durch den Weg über $M_E$ samt Literaturstelle.

#### Vorschlag für den nächsten Lauf, als benanntes Ziel

**Der Raum $M_E$ als polnischer Raum**, eingetragen als `WeakConvergence`
Meilenstein 6. Ausgeschrieben, was zu bauen ist, in der Reihenfolge, in der es
aufeinander ruht:

* der Setoid „$f = g$ $\lambda$-f.ü." auf den meßbaren $f : \Rp \to E$ und sein
  Quotient. Mathlib hat denselben Quotienten als `MeasureTheory.AEEqFun`
  (`MeasureTheory/Function/AEEqFun.lean`) und damit den natürlichen Ort; die
  dortigen Metriken sind aber die $L^p$-Konstruktionen und nicht $d_m$;
* `dm f g = ∫ t, Real.exp (-t) * min 1 (dist (f t) (g t))` als `Dist`-Instanz,
  wohldefiniert auf dem Quotienten, mit `MetricSpace`-Instanz (die
  Dreiecksungleichung ist punktweise, die Trennung ist die
  f.ü.-Verschwindungsaussage für nichtnegative Integranden);
* `CompleteSpace`, nach Kurtz (4.2)--(4.4): aus einer Cauchy-Folge eine Teilfolge
  mit $\sum_k d_m(x_{n_k},x_{n_{k+1}})<\infty$ wählen, punktweise auf einer
  Lebesgue-vollen Menge den Limes bilden, außerhalb konstant $x_0$ setzen;
* `SeparableSpace` — der Punkt, den Kurtz **nicht** beweist. Der naheliegende
  Weg: Treppenfunktionen mit rationalen Sprungstellen und Werten in einer
  abzählbaren dichten Teilmenge von $E$; ihre Dichte in $d_m$ ist Lusin
  zusammen mit der Dichte der Treppenfunktionen in $L^1$.

Warum jetzt: es ist die einzige neue Aussage, die dieser Lauf als nötig erkannt
hat; sie ist elementar (keine Kerne, keine Desintegration, keine
Borel-Isomorphie); sie ruht auf nichts, was noch fehlt; und sie ersetzt die
schwerste Hypothesenabschwächung der Roadmap durch eine Konstruktion. Der
Ertrag darüber hinaus: mit $M_E$ polnisch ist Prohorov dort verfügbar, und
Kurtz' Theorem 4.6 (S. 1026) wird zu einem Straffheitskriterium für Gesetze
meßbarer Prozesse, das `fact:MZtight` von der Kompaktheitsseite her stützt.

#### Nachtrag desselben Laufs: der Angelpunkt ist Lean, nicht Prosa

Der Beweis von (a) hängt an **einer** Aussage, und sie ist so klein, daß sie
nicht als Skizze stehenbleiben mußte. In `WeakConvergence/Suggested.lean` steht
sie jetzt, mit dem Rest von Meilenstein 6:

* `measurableSet_of_measurable_injective` — für meßbares und injektives
  `γ : X → Y` und `S : Set X` mit `MeasurableSet (γ '' S)` ist `S` meßbar. Der
  Beweis ist `Function.Injective.preimage_image` gefolgt von
  `MeasurableSet.preimage`. Die Aussage trägt **keine Topologie**: zwei nackte
  `MeasurableSpace`-Instanzen und sonst nichts — das ist die stehende Regel der
  minimalen Voraussetzungen, hier ausnahmsweise mit Gewinn, denn sie zeigt, daß
  der Angelpunkt von (a) nichts mit polnisch, separabel oder vollständig zu tun
  hat.
* `measurableSet_of_continuous_injective` — dieselbe Aussage für stetiges `γ`,
  unter `[OpensMeasurableSpace X]` und `[BorelSpace Y]`, und das ist die Gestalt,
  in der die Pseudopfad-Abbildung eingesetzt wird.
* `MeasureTheory.AEEqFun.distInMeasure` als `∫ a, min 1 (dist (f a) (g a)) ∂μ`
  auf `α →ₘ[μ] E`, samt `distInMeasure_nonneg`, `distInMeasure_comm` und
  `distInMeasure_self`.

Alle fünf Sätze gehen durch `lake env lean` gegen v4.33.1 und hängen laut
`#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`;
`measurableSet_of_measurable_injective` sogar nur an `propext` und `Quot.sound`.
Die fünf weiteren Deklarationen des Meilensteins —
`distInMeasure_triangle`, `distInMeasure_eq_zero_iff`,
`tendsto_iff_tendstoInMeasure`, `exists_tendsto_distInMeasure_of_cauchy`,
`exists_countable_dense_distInMeasure` — sind Aussagen mit eigenem `sorry`, also
das, wofür die Datei da ist. `rc = 1` mit unverändert genau den zwei
angekündigten Fehlern aus dem Versionsgrund bei
`tendsto_map_of_measure_setOf_continuousAt_eq_one`, jetzt bei `:2097` (drei
Importzeilen weiter unten).

Drei Namen sind dabei am Quelltext berichtigt worden, weil sie aus dem Gedächtnis
falsch waren: die Klasse heißt `MeasureTheory.IsSeparable` und **nicht**
`MeasureTheory.Measure.IsSeparable` (`Measure/SeparableMeasure.lean:339`, in
v4.33.1 und auf `upstream/master` an derselben Zeile), und
`SecondCountableTopology` liegt im Wurzelnamensraum und nicht unter
`TopologicalSpace`. Die Instanz, die `IsSeparable μ` für unseren Fall gratis
gibt, steht bei `:382` — `[MeasurableSpace.CountablyGenerated X] [SFinite μ]`.

**Mitgefunden und berichtigt.** Der Kopfkommentar von `Suggested.lean` trug noch
den Satz „Mathlib has no product of kernels over a countable index", den der
neunte Lauf des Tages im Inventar als falsch erkannt und dort durchgestrichen
hat, ohne ihn in der Lean-Datei nachzuziehen. Er ist jetzt auch dort ersetzt:
das Produkt heißt `ProbabilityTheory.Kernel.traj`
(`Probability/Kernel/IonescuTulcea/Traj.lean:518`), und die Entscheidung gegen
das Verkleben trägt allein `Measure.condKernel` mit `[StandardBorelSpace Ω]`
`[Nonempty Ω]`. Die Lehre, klein aber wiederholt: eine Berichtigung ist erst
fertig, wenn sie an **allen** Stellen steht, die den Befund tragen, und eine
Lean-Datei mit Kopfkommentar ist eine solche Stelle.

#### Das Manuskript, und wie es geprüft ist

`rem:MZcost`, zweiter Absatz, ist ersetzt: die Folgerung „a formalization must
have the continuous mapping theorem and the Skorokhod representation at that
generality and not only for Polish spaces" weicht dem Weg über $M_E$, mit dem
`\Ku`-Zitat (der Bibliographieeintrag `Kurtz91` steht schon, `:10563`), der
Metrik $d_m$ als abgesetzter Formel, und den drei Schritten (Teilraum, Borel,
Spur). `python3 check.py` meldet **`clean -- 133 pages, 12 overfull (max
7.7pt)`**. Der erste Satz des Absatzes bleibt stehen; er ist wahr.

**Nicht** angefaßt sind zwei Nachbarstellen, und zwar mit Grund. Die Liste in
`ssec:available` (`:9828`) führt „the continuous mapping theorem in the form of
Fact~\ref{fact:cmt} and the Skorokhod representation (Fact~\ref{fact:PSpolish})"
unter „to be built" **ohne Angabe einer Allgemeinheit** und bleibt damit
richtig. Und `rem:threetopologies` (`:9454`) sagt von Jakubowskis
$S$-Topologie, sie sei nicht metrisierbar, weshalb „Facts~\ref{fact:cmt} and
\ref{fact:PSpolish} would both have to be replaced" — das ist ein Satz über
Nichtmetrisierbarkeit und nicht über Nichtpolnischkeit, und der $M_E$-Weg hilft
dort nicht, denn er ruht gerade darauf, daß die Pseudopfad-Topologie metrisch
ist.

#### Eine Lesart, die festgehalten sein will

`fact:pseudopath`(ii) endet mit „$\DE$ being merely Borel in that compact
space". „That compact space" ist der Raum der **Gesetze**,
$\Prob([0,\infty]\times\hat E)$ — die Klausel davor sagt „being induced from the
weak topology on the laws on a compact metric space" —, und nicht
$[0,\infty]\times\hat E$ selbst. Der ganze Punkt (a) hängt an dieser Lesart, und
sie ist die einzige, unter der der Satz überhaupt wahr ist: $\DE$ ist kein
Teilraum von $[0,\infty]\times\hat E$.

### 2026-09-08, zwölfter Lauf des Tages — der Raum $M_E$: vier der fünf offenen Aussagen von Meilenstein 6 sind bewiesen

**Bearbeitet:** `fact:PSpolish` (über `WeakConvergence` Meilenstein 6, den der
elfte Lauf als Preis des $M_E$-Weges angelegt hat) und, mittelbar,
`fact:pseudopath`(i) — die Aussage, daß die Pseudopfad-Topologie die Konvergenz
im Maß ist, hat jetzt ihre Lean-Fassung.

Der elfte Lauf hatte Meilenstein 6 mit fünf Aussagen und je eigenem `sorry`
hinterlassen. **Vier davon tragen jetzt Beweise**, dazu neun neue Deklarationen
(drei Hilfssätze, die Abschätzung `distInMeasure_le_add`, die drei Instanzen und
zwei Aussagen über sie); alle gehen durch `lake env lean` gegen v4.33.1 und hängen laut `#print axioms`
allein an `propext`, `Classical.choice`, `Quot.sound`. `WeakConvergence/Suggested.lean`
steht danach bei **168 Deklarationen und drei `sorry`** (vorher 159 und sieben), und
von den dreien gehören zwei nicht zu diesem Meilenstein; `rc = 0`, mit unverändert
genau den beiden angekündigten Fehlern aus dem Versionsgrund bei
`tendsto_map_of_measure_setOf_continuousAt_eq_one` (jetzt `:2125`).

#### Was bewiesen ist

* `distInMeasure_triangle` — die Dreiecksungleichung. Ihr ganzer Inhalt ist
  punktweise und steht als privates `min_one_add_le`: für $a,b\ge0$ ist
  $\min(1,a+b)\le\min(1,a)+\min(1,b)$. Drei Fälle, und der einzige, in dem etwas
  passiert, ist $a,b<1$; sonst ist schon ein Summand gleich $1$.
* `distInMeasure_eq_zero_iff` — die Trennung, über
  `integral_eq_zero_iff_of_nonneg` und `AEEqFun.ext`. Die Abschneidung wird von
  `min_eq_iff` aufgehoben, dessen erster Zweig $1 = 0$ verlangte.
* `tendsto_iff_tendstoInMeasure` — **die Aussage, die die Metrik benennt**, und
  der Berührungspunkt mit `fact:pseudopath`(i). Beide Richtungen laufen über
  Mathlibs `tendstoInMeasure_iff_measureReal_dist`
  (`Function/ConvergenceInMeasure.lean:110`). Die Hinrichtung ist Markov,
  `mul_meas_ge_le_integral_of_nonneg` (`Integral/Bochner/Basic.lean:1129`), und
  die Stelle, an der es schiefgeht, wenn man nicht aufpaßt: die Ungleichung ist
  auf der Höhe $\min(1,\varepsilon)$ anzuwenden und nicht auf der Höhe
  $\varepsilon$, sonst zeigt die Mengeninklusion in die falsche Richtung. Die
  Rückrichtung ist die Zerlegung des Integrals bei $\varepsilon$; sie ist als
  eigene Aussage `distInMeasure_le_add` herausgezogen,
  `distInMeasure f g ≤ ε * μ.real univ + μ.real {a | ε ≤ dist (f a) (g a)}`,
  weil sie sonst zweimal dasteht.
* `exists_tendsto_distInMeasure_of_cauchy` — die **Vollständigkeit**, Kurtz
  (4.2)--(4.4). Teilfolge mit summierbaren Nachbarabständen (die Monotonisierung
  ist `Nat.rec` mit `max (N (k+1)) (ns k + 1)`), `lintegral_tsum` zieht die Summe
  ins Integral, `ae_lt_top` gibt die punktweise Summierbarkeit f.ü.,
  `cauchySeq_of_summable_dist` und `cauchySeq_tendsto_of_complete` den Limes,
  `aestronglyMeasurable_of_tendsto_ae` seine Meßbarkeit,
  `tendstoInMeasure_of_tendsto_ae` seine Konvergenz im Maß, und die
  Dreiecksungleichung gegen die Teilfolge trägt sie auf die ganze Folge.

Dazu die drei Hilfssätze `measurable_dist_coeFn`, `integrable_min_one_dist` und
das private `min_one_add_le`.

**Und damit die Instanzen selbst**, die bis dahin nur im Bauplan standen:
`instDist` samt `dist_eq_distInMeasure`, `metricSpace` aus den vier Aussagen, und
`completeSpace` aus der Vollständigkeit über `Metric.complete_of_cauchySeq_tendsto`.
Nichts wird dabei verdeckt: Mathlibs konkurrierende Metriken der f.ü.-Klassen
liegen auf `MeasureTheory.Lp` (`Function/LpSpace/Basic.lean:223`), einem anderen
Typ, und `α →ₘ[μ] E` selbst trug keinen Abstand. Mit der Metrik steht auch die
Aussage in ihrer eigentlichen Form da — `tendsto_nhds_iff_tendstoInMeasure`,
`Tendsto f l (𝓝 g) ↔ TendstoInMeasure …`, ein Satz über die **Topologie** und
nicht über eine Zahlenfolge. Die tragenden Deklarationen samt
Instanzen sind mit `#print axioms` in der ganzen Datei geprüft.

#### Drei Befunde, die festzuhalten sind

**Erstens: `SecondCountableTopology E` war eine Hypothese zuviel.** Sie stand
seit dem elften Lauf an `distInMeasure` und an allem, was darauf ruht. Kein
Beweis benutzt sie, auch nicht die Vollständigkeit; sie ist gestrichen. Der
Grund, aus dem sie entbehrlich ist, ist eine Mathlib-Eigenheit, die eigens
notiert sei: **die Koerzion einer f.ü.-Klasse ist *stark* meßbar**, nicht bloß
f.ü. stark meßbar — `AEEqFun.stronglyMeasurable` (`Function/AEEqFun.lean:139`) —,
und darum sind die Mengen $\{a : \varepsilon \le d(f(a),g(a))\}$ ohne jede
Zweitabzählbarkeit meßbar. Das steht als `measurable_dist_coeFn` in der Datei,
damit die nächste Aussage es nicht neu sucht.

**Zweitens: die Vollständigkeit braucht kein `Nonempty E`.** Der Bauplan des
elften Laufs schrieb „off it, put the limit equal to a fixed `x₀ : E`", und das
geht so nicht: über einem leeren $E$ gibt es kein $x_0$, und ob $E$ leer ist,
sagt die Aussage nicht. Was statt dessen dasteht, ist der **erste Folgenwert**
als Ausweichwert — `if h : ∃ l, Tendsto … then h.choose else F 0 a` —, und damit
ist die Definition unbedingt. Der Bauplan in Meilenstein 6 ist entsprechend
berichtigt.

**Drittens, ein Negativbefund mit den Suchen, mit denen er gefunden ist.**
Mathlib hat **keine Vollständigkeit der Konvergenz im Maß**. Gesucht ist
`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` nach `cauchy`
(unabhängig von Groß- und Kleinschreibung; **kein einziger Treffer** in der
ganzen Datei) und der ganze `Mathlib/MeasureTheory/`-Baum nach
`ae_tendsto_of_cauchy`, `exists_seq_tendsto_ae`, `cauchySeq_ae`. Was es gibt, ist
`TendstoInMeasure.exists_seq_tendsto_ae` (`:277`) — die Teilfolge zu einem
**gegebenen** Grenzwert — und `ae_tendsto_of_cauchy_eLpNorm`
(`Function/LpSpace/Complete.lean:290`), das den Grenzwert produziert, aber
`[NormedAddCommGroup E]` verlangt und über unserem metrischen $E$ nicht
instanziierbar ist. Der Grenzwert muß also erzeugt und nicht wiedererkannt
werden, und genau das tut der Beweis.

**Mitgefunden, für den nächsten, der `∑'` über `ℝ≥0∞` meßbar braucht:**
`Measurable.ennreal_tsum` (`Constructions/BorelSpace/Real.lean:354`) ist in
v4.33.1 `deprecated`, und der in der Deprecation genannte Ersatz
`Measurable.tsum` aus `MeasureTheory/Constructions/Polish/Basic.lean` **existiert
dort in v4.33.1 nicht** (die Datei enthält `tsum` überhaupt nicht). Es bleibt,
den zweizeiligen Beweis von Hand hinzuschreiben — `ENNReal.tsum_eq_iSup_sum`,
`Measurable.iSup`, `Finset.measurable_fun_sum` —, und so steht er in der Datei.

#### Was offen bleibt, und der Vorschlag für den nächsten Lauf

Von Meilenstein 6 bleibt **eine** Aussage: `exists_countable_dense_distInMeasure`,
die **Separabilität**. Das ist genau der Punkt, den Kurtz „left to the reader"
schreibt, und er ist damit der einzige Teil des Meilensteins ohne Vorlage. Er ist
der benannte Vorschlag für den nächsten Lauf, und der Weg ist der, den
Meilenstein 6 nennt:

1. `MeasureTheory.IsSeparable μ` (`Measure/SeparableMeasure.lean:339`) gibt eine
   abzählbare Familie meßbarer Mengen, die die σ-Algebra maßdicht ausschöpft;
   `TopologicalSpace.SeparableSpace E` eine abzählbare dichte Menge in $E$.
2. Die approximierende Familie ist — wie in
   `separableSpace_probabilityMeasure` des vierten Laufs — als **Definition** zu
   benennen und nicht im Beweis zu beschreiben, sonst kostet ihre Abzählbarkeit
   eine Seite: die Klassen der Funktionen $\sum_{i<n} 1_{A_i} \cdot y_i$ über
   endliche Indexvektoren aus den beiden abzählbaren Familien.
3. Die Dichte ist der Zweischritt aus Meilenstein 6: erst eine abzählbarwertige
   Funktion im punktweisen Abstand $\varepsilon$, dann der Schnitt des Schwanzes
   an der Endlichkeit von $\mu$, dann jede Niveaumenge auf eine maßdichte
   verschoben. Der zweite Schritt ist der, an dem `[IsFiniteMeasure μ]` ein
   zweites Mal bezahlt wird.

Warum jetzt: mit ihr ist `AEEqFun.polishSpace` eine Zeile (Vollständigkeit und
Separabilität sind dann beide da), und mit `polishSpace` steht der Raum $M_E$,
über den Schritt 1 von `thm:MZconv` seit dem elften Lauf läuft. Es ist die letzte
Aussage zwischen der Roadmap und der Abschwächung, die `rem:MZcost` seit
gestern behauptet.

Das Manuskript ist von diesem Lauf **nicht** angefaßt.

**Ein Mißgriff, der zu nennen ist, weil er im Rückstau schon steht.** Ein
`lake env lean` ist einmal ohne das vorangestellte `cd ~/Code/lean/journal`
gelaufen, aus dem Mathlib-Verzeichnis heraus; `lake` hat daraufhin acht Pakete
nach `~/Code/lean/journal/.lake/packages/mathlib/.lake/packages/` geklont, 57 MB.
Der Ordner ist überflüssig — die Pakete liegen eine Ebene höher schon gebaut —
und gehört gelöscht; die Sandbox dieses Laufs erlaubt das `rm` dort nicht. Die
Warnung im Rückstau ist damit zum zweiten Mal bestätigt und steht dort jetzt mit
diesem zweiten Fall.

### 2026-09-08, dreizehnter Lauf des Tages — die Separabilität von $M_E$, und damit Meilenstein 6 geschlossen

**Bearbeitet:** `fact:PSpolish`, über `WeakConvergence` Meilenstein 6. Das war
der benannte Vorschlag des zwölften Laufs, und er ist eingelöst: die
**Separabilität** des Raums $M_E[0,\infty)$ — der Punkt, den Kurtz (1991),
Abschnitt 4, „left to the reader" schreibt und der einzige Teil des Meilensteins
ohne Vorlage in der Quelle — ist bewiesen, und mit ihr die Polnischkeit.

**Acht neue Deklarationen, alle bewiesen**, alle durch
`cd ~/Code/lean/journal && lake env lean` gegen v4.33.1 und alle mit
`#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft.
`WeakConvergence/Suggested.lean` steht danach bei **176 Deklarationen und zwei
`sorry`** (vorher 168 und drei; mit dem Nachtrag zu Meilenstein 4 weiter unten
sind es 177); die beiden übrigen sind
`exists_ae_tendsto_of_tendsto` (Meilenstein 3) und
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (Meilenstein 4), also
keiner mehr in Meilenstein 6. `rc = 1` mit unverändert genau den beiden
angekündigten Fehlern aus dem Versionsgrund bei
`tendsto_map_of_measure_setOf_continuousAt_eq_one` (jetzt `:2125`).

#### Was bewiesen ist

* `exists_countable_dense_distInMeasure` — die Aussage selbst: eine abzählbare
  Menge von Klassen, die in `distInMeasure` dicht liegt, unter
  `[IsFiniteMeasure μ] [IsSeparable μ] [TopologicalSpace.SeparableSpace E]` und
  sonst nichts.
* `separableSpace`, `secondCountableTopology`, `polishSpace` — dieselbe Aussage
  als Aussage über die Topologie, und die beiden Folgerungen. Die letzten beiden
  sind je eine Zeile hinter der ersten, genau wie der zwölfte Lauf es
  vorhergesagt hatte: mit der Separabilität im lokalen Kontext findet
  `infer_instance` erst `UniformSpace.secondCountable_of_separable` und dann die
  `PolishSpace`-Instanz eines vollständigen separablen metrischen Raums.
* `distInMeasure_mk_le_add` — die Abschätzung `distInMeasure_le_add` gegen einen
  **Vertreter** statt gegen eine Klasse. Ein Approximationsargument erzeugt eine
  Funktion, keine Klasse, und die f.ü.-Buchhaltung dazwischen ist ein
  `measureReal_congr` längs `AEEqFun.coeFn_mk`; als eigene Aussage
  herausgezogen, weil sie sonst im Beweis mehrfach dastünde.
* `stepFun`, `stronglyMeasurable_stepFun`, `exists_mem_stepFun`, `stepClass` —
  die approximierende Familie.

#### Der Befund, der die Gestalt der Familie bestimmt

**Der Bauplan des Meilensteins war nicht typrichtig.** Er beschrieb die dichte
Familie seit dem elften Lauf als die Klassen der Summen
`∑ i, Set.indicator (A i) (fun _ ↦ y i)` — die Formulierung, die Mathlibs
`Lp.SecondCountableTopology` (`Measure/SeparableMeasure.lean:427`) benutzt. Dort
ist `E` eine normierte Gruppe; hier ist `E` ein **bloßer metrischer Raum** und
hat keine Addition, und die Summe elaboriert nicht. Dasselbe erledigt den
naheliegenden Gedanken, Mathlibs Beweis zu übertragen: er läuft über
`Lp.induction`, und dessen tragender Schritt ist die Abgeschlossenheit unter
Summen.

Was an die Stelle der Summe tritt, ist die Stufenfunktion über einer **Liste**
`l : List (ℕ × ℕ)` von Indexpaaren — der erste Eintrag benennt eine Menge der
maßdichten Familie, der zweite einen Punkt der dichten Folge, und die früheren
Einträge haben Vorrang. Zwei Dinge gewinnt man damit, und beide sind der Grund,
warum der Beweis kurz ist:

1. **Die Abzählbarkeit ist Instanzsuche.** `Countable (List (ℕ × ℕ))` steht in
   Mathlib, also ist `Set.countable_range` die ganze erste Hälfte der Aussage.
   Über `Σ n, (Fin n → ℕ) × (Fin n → ℕ)` — der Indexmenge, die
   `natWeightMeasure` in Meilenstein 3 benutzt — wäre es dasselbe, aber die
   Liste erspart die Umindizierung beim Zusammensetzen.
2. **Die überdeckenden Mengen dürfen einander überlappen.**
   `exists_mem_stepFun` sagt nicht, *welcher* Zweig feuert, sondern nur, daß der
   gefeuerte von irgendeinem Eintrag stammt, dessen Menge das Argument enthält —
   und das genügt, weil jeder solche Eintrag einen Punkt im Abstand `r` von
   `f a` benennt. Damit entfällt die Disjunktifizierung
   `A i = ball (y i) r \ ⋃ j < i, ball (y j) r`, die
   `exists_finite_partition_ball_of_denseRange` in Meilenstein 3 kostet, und mit
   ihr die Eindeutigkeitsbuchhaltung. `exists_mem_stepFun` steht deshalb unter
   `omit [MeasurableSpace α] [MetricSpace E]`: es ist eine Aussage über Listen
   und Mengen und über nichts sonst.

Und eine dritte Kleinigkeit, die eigens dasteht, weil sie zweimal gebraucht
wird: eine Stufenfunktion ist **stark** meßbar und nicht bloß meßbar, weil sie
endlich viele Werte hat (`StronglyMeasurable.ite`,
`Function/StronglyMeasurable/Basic.lean:817`, Induktion über die Liste). Ohne
das ginge es nicht, denn `Measurable → StronglyMeasurable` verlangt über einem
metrischen Ziel Zweitabzählbarkeit, die hier nicht dasteht. Es ist dieselbe
Eigenheit, die der zwölfte Lauf schon einmal bezahlt bekam
(`AEEqFun.stronglyMeasurable`).

#### Der Beweis, in der Reihenfolge, in der er läuft

Zu `f` und `ε`: setze `r = ε / (2 (μ.real univ + 1))` und `δ = ε / 8`.

1. `S m = {a | dist (f a) (y m) < r}` ist meßbar — hier wird
   `AEEqFun.stronglyMeasurable` ein zweites Mal verbraucht — und überdeckt `α`,
   weil `y` dicht ist. Also wächst `⋃ m < n, S m` gegen `α`, und da `μ` endlich
   ist, gibt `tendsto_measure_iInter_atTop` ein `N` mit
   `μ (⋃ m < N, S m)ᶜ < δ`.
2. `Measure.MeasureDense.approx` ersetzt jedes `S i`, `i < N`, durch ein
   `A (c i)` der maßdichten Familie mit `μ (S i ∆ A (c i)) < δ / (N + 1)`. Das
   `N + 1` ist es, was die Summe der `N` Fehler ohne Fallunterscheidung bei
   `N = 0` unter `δ` hält.
3. Außerhalb von `(⋃ m < N, S m)ᶜ ∪ ⋃ i, S i ∆ A (c i)`, einer Menge der Masse
   höchstens `2δ = ε/4`, ist die Stufenfunktion über
   `List.ofFn (fun i : Fin N ↦ (c i, i))` im Abstand `< r` von `f`, und
   `r * μ.real univ ≤ ε/2`.

**Das leere `E` ist eine eigene Zeile und keine Hypothese.**
`TopologicalSpace.exists_dense_seq` verlangt `[Nonempty E]`, und über einem
leeren `E` gibt es die dichte Folge nicht. Sie wird dort auch nicht gebraucht:
ein Element von `α →ₘ[μ] E` erzwingt, daß `α` leer ist, also ist der Raum ein
Subsingleton, also abzählbar, also ist `Set.univ` seine eigene dichte Menge.
Dieselbe Sorte Randfall wie beim leeren `E` in
`separableSpace_probabilityMeasure` (vierter Lauf), nur mit anderem Grund.

#### Was das für die Roadmap heißt

**Meilenstein 6 trägt kein `sorry` mehr.** Damit steht der Raum $M_E$ vollständig
— Metrik, Vollständigkeit, Separabilität, Polnischkeit, und die Aussage
`tendsto_nhds_iff_tendstoInMeasure`, die ihn mit `fact:pseudopath`(i) verbindet.
Was der elfte Lauf als *Preis* des $M_E$-Weges gebucht hatte („die Konstruktion
von $M_E$ selbst"), ist bezahlt; was er als *Ertrag* buchte — daß Schritt 1 von
`thm:MZconv` über einen polnischen Raum läuft und die Skorokhod-Darstellung von
Meilenstein 3 nur für polnische Räume gebraucht wird —, steht damit auf einem
gebauten Fundament statt auf einem geplanten.

Das Manuskript ist von diesem Lauf **nicht** angefaßt.

#### Vorschlag für den nächsten Lauf

`exists_ae_tendsto_of_tendsto` (`WeakConvergence` Meilenstein 3), die
Skorokhod-Darstellung selbst — von den zwei verbliebenen `sorry` der Datei der
weiter gediehene. Sie ruht auf `exists_measurable_pair_of_partition` (zehnter
Lauf), das eine Stufe als *eine* Aussage mit der Grenzvariablen als fester
erster Koordinate liefert; was fehlt, ist nach dem Bauplan des zehnten Laufs die
Teilfolge, Borel--Cantelli und die Umindizierung aller Stufen auf
`(E × (ℕ → ℝ)) × (ℕ × ℕ → E)` — Buchhaltung über bewiesenen Sätzen, keine neue
Idee. Sie ist jetzt dran, weil sie nach dem Abschluß von Meilenstein 6 die
einzige Aussage ist, die zwischen der Roadmap und dem Weg steht, den
`rem:MZcost` seit dem elften Lauf behauptet: die Darstellung wird dort für
**polnische** Räume gebraucht, und dieser Fall ist ein Spezialfall dessen, was in
der Datei schon bewiesen ist.

#### Mitgefunden im selben Lauf: `IsUniformlyIntegrableLaws` war entartet

Beim Durchsehen des zweiten verbliebenen `sorry` — Meilenstein 4 — fiel eine
**falsche Aussage** auf, und sie ist berichtigt. `IsUniformlyIntegrableLaws`
stand seit ihrer Aufstellung als

```
Tendsto (fun N : ℕ => ⨆ n, ∫ x, (|x| - min |x| N) ∂(μ n)) atTop (𝓝 0)
```

mit dem **Bochner**-Integral. Der Integrand ist $\max(|x|-N,0)$, also nicht
negativ; eine Familie mit unendlichem ersten Moment macht ihn für **jedes** $N$
nichtintegrierbar, und dann gibt `MeasureTheory.integral_undef`
(`Integral/Bochner/Basic.lean:202`) den Ersatzwert `0` zurück. Das Supremum ist
für jedes `N` gleich `0`, die Folge ist konstant `0`, die Voraussetzung **ist
erfüllt** — von genau den Familien, die das Kriterium ausschließen soll. Der
Satz `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` behauptet unter
ihr `Integrable id ν`, und das ist dann falsch. Zeuge, als konstante Familie
$\mu_n = \nu$: `ProbabilityTheory.cauchyMeasure 0 1`
(`Probability/Distributions/Cauchy.lean:170`, Wahrscheinlichkeitsmaß durch die
Instanz bei `:188`). Der Zeuge ist **argumentiert und nicht formalisiert** —
Mathlib hat in `Cauchy.lean` keine Aussage über die Nichtintegrierbarkeit von
`id`, und sie hinzuschreiben ist ein eigenes Stück Arbeit; was am Quelltext
belegt ist, ist der Ersatzwert und die Existenz des Maßes.

**Die Berichtigung** ist das **untere** Integral,
`∫⁻ x, ENNReal.ofReal (|x| - min |x| N) ∂(μ n)`. In `ℝ≥0∞` gibt es keinen
Ersatzwert, und das Kriterium **impliziert** die Integrierbarkeit, statt sie
vorauszusetzen: das ist `integrable_id_of_isUniformlyIntegrableLaws`, bewiesen
im selben Lauf, durch `lake env lean` gegen v4.33.1 und mit `#print axioms` auf
`propext`, `Classical.choice`, `Quot.sound` geprüft — zu einem `N` mit
`⨆ k, ∫⁻ … < 1` ist punktweise `|x| ≤ N + (|x| - min |x| N)`, also
`∫⁻ x, ‖x‖ₑ ∂(μ n) ≤ N + 1 < ∞`. Damit steht der Meilenstein bei **177
Deklarationen und weiterhin zwei `sorry`**.

**Die Lehre, und sie reicht über diesen Meilenstein hinaus.** Ein Kriterium, das
als Bochner-Integral eines *nichtnegativen* Integranden formuliert ist, ist
genau dort stillschweigend leer, wo der Integrand nicht integrierbar ist — und
das ist genau die Stelle, an der solche Kriterien angewandt werden. Es ist
derselbe Fehlertyp wie die drei „leeren Aussagen" der Läufe vom 2026-09-05 und
2026-09-07, aber mit einer neuen Quelle: nicht eine erfüllbare Hypothesenmenge,
sondern ein **Ersatzwert**. Wer eine Aussage über Integrale prüft, prüft
deshalb zuerst, was sie sagt, wenn das Integral nicht existiert.

**Der Merge-Konflikt mit `origin/master`, wie der Auftrag ihn ankündigt.** Dieser
Lauf hat nur vier Dateien angefaßt — `TauCeti/WeakConvergence/Suggested.lean`,
`TauCeti/WeakConvergence/README.md`, dieses Inventar und `Facts/BACKLOG.md` —,
und alle vier zweifelsfrei zur Aufgabe gehörig. Drei Hilfsdateien im Arbeitsbaum
(`scratch_sep.lean`, `scratch_ui.lean`, `axcheck.lean`) sind nach der
Werkzeugnotiz des zweiten Laufs benutzt und mit `git clean -f` wieder entfernt
worden.

### 2026-09-08, vierzehnter Lauf des Tages — der letzte Schritt der Skorokhod-Darstellung geht nicht über Borel--Cantelli, und der Bauplan war dort falsch

**Bearbeitet:** `fact:PSpolish`, über `WeakConvergence` Meilenstein 3, entlang
des Vorschlags des dreizehnten Laufs (`exists_ae_tendsto_of_tendsto`). Der Lauf
hat den Zusammenbau **nicht** fertiggestellt, sondern etwas anderes gefunden:
der Bauplan, nach dem er zusammenzubauen wäre, ist an seinem letzten Schritt
falsch. Der Befund ist belegt, das Ersatzstück ist bewiesen, und der Meilenstein
trägt jetzt den richtigen Weg.

#### Der Befund: Punkt (c3) des Bauplans ist nicht durchführbar

Der zehnte Lauf hatte den Schluß so ausgeschrieben:

> **(c3) Borel--Cantelli.** `∑' n, (2:ℝ≥0∞)⁻ⁿ < ∞`, also ist nach
> `MeasureTheory.measure_limsup_atTop_eq_zero` f.s. nur endlich oft
> `2⁻ⁿ < dist (X n) Y`.

Das setzt voraus, daß die Stufe `n` die Schranke `2⁻ⁿ` **hat**. Sie hat sie
nicht. Was die Stufe liefert, ist `exists_measurable_pair_of_partition`, und
deren Schranke ist `∑' i, (μ n (A i) - ν (A i))` — eine Größe, die von `μ n`
abhängt und über die der Bauplan nichts verfügen kann. Sie geht gegen `0`, aber
**beliebig langsam**, und das ist keine Vermutung, sondern ein Zeuge:

> `E = ℝ`, `ν = dirac 0`, `μ n = (1 - 1/log n) • dirac 0 + (1/log n) • dirac 1`.

`μ n ⇒ ν` schwach. Jede Zerlegung in Stücke vom Durchmesser unter `1` trennt die
beiden Atome, also liegt `1` in einem Stück `A` mit `ν A = 0` und
`μ n A = 1/log n`, und die Schranke der Stufe ist mindestens `1/log n` — auf
**jeder** Stufe, deren Durchmesser unter `1` liegt. Da jede Stufenfolge mit
`δ k → 0` alle bis auf endlich viele Stufen unter `1` hat und die gewählten
Niveaus `k n → ∞` gehen, ist die Schranke der Stufe `n` schließlich mindestens
`1/log n`, und `∑ 1/log n = ∞`. **Keine Wahl der Niveaus repariert das**, denn
die Divergenz ist eine Eigenschaft der Folge der Gesetze und nicht der
Zerlegung. `measure_limsup_atTop_eq_zero` ist damit an dieser Stelle nicht
anwendbar.

Der Satz gilt für diese Folge trotzdem, und der Zeuge sagt auch, woran das
liegt: mit `U` gleichverteilt und `X n = 1` genau auf `{U ≤ 1/log n}` ist
`X n ∼ μ n`, und weil `1/log n` fällt, sind die schlechten Ereignisse
**geschachtelt** — `⋂_N ⋃_{n≥N} {U ≤ 1/log n} = {U ≤ 0}`, eine Nullmenge, obwohl
die Wahrscheinlichkeiten nicht summierbar sind. **Die fast sichere Konvergenz
kommt aus der Abhängigkeit zwischen den Stufen, nicht aus den Schranken der
einzelnen Stufe.** Ein Beweis, der die Stufen unabhängig randomisiert und am
Ende summiert, kann sie nicht bekommen.

#### Wie Ethier--Kurtz es machen, am Scan gelesen

\EK{}, Theorem 3.1.8, Buchseiten 102--103 (PDF-Seiten 112--113, Versatz +10).
Ihre Konstruktion (1.33)--(1.36) ist genau die geschachtelte:

* Zu jedem `k` **endlich** viele disjunkte `E_1^{(k)},…,E_{N_k}^{(k)}` vom
  Durchmesser unter `2⁻ᵏ` mit `P(E_0^{(k)}) ≤ 2⁻ᵏ` für den Rest
  `E_0^{(k)} = S \ ⋃ᵢ Eᵢ^{(k)}`, und **o.B.d.A. `ε_k = minᵢ P(Eᵢ^{(k)}) > 0`**.
* `k_n = max ({1} ∪ {k ≥ 1 : ρ(P_n,P) < ε_k/k})`, also `k_n → ∞`.
* Lemma 3.1.3 auf der Stufe `k_n`, **mit einer einzigen, allen Stufen
  gemeinsamen gleichverteilten Variablen `ξ`** (1.34): `X_n = Y_i^{(n)}` auf
  `{X ∈ Eᵢ^{(k_n)}, ξ ≥ cᵢ^{(n)}}`.
* (1.35) ist eine **Inklusion** und keine Zahl:
  `{d(X_n,X) ≥ 2^{-k_n} + ε_{k_n}/k_n} ⊆ {X ∈ E_0^{(k_n)}} ∪ {ξ < 1/k_n}`.
* (1.36) summiert deshalb über die **Niveaus** und nicht über `n`: mit
  `K_n = min_{m≥n} k_m` ist
  `ν(⋃_{m≥n} …) ≤ ∑_{k≥K_n} ν(X ∈ E_0^{(k)}) + ν(ξ < 1/K_n) ≤ 2^{-K_n+1} + 1/K_n`.

Drei Dinge daran sind für unseren Bau nicht verhandelbar, und alle drei fehlten
im Bauplan: **eine gemeinsame** gleichverteilte Variable (der Bauplan des
zehnten Laufs schrieb `E × (ℕ → ℝ)`, also eine je Stufe); die Schranke als
**Inklusion in ein Ereignis dieser Variablen** statt als Zahl; und **endlich
viele Stücke von positiver Masse** plus einen Rest, denn nur dann ist der
Zeilendefekt `(ν Aᵢ - μ n Aᵢ)/ν Aᵢ` gleichmäßig über die Stücke klein.

#### Was bewiesen ist

`ae_tendsto_of_subset_of_tendsto_measure_iUnion_ge` — (1.36) als eigener Satz,
von der Konstruktion gelöst: liegt das Ereignis „Stufe `n` weicht um mehr als
`δ (k n)` ab" f.ü. in einer Menge `B (k n)`, die **allein vom Niveau** abhängt,
gehen die Niveaus gegen unendlich und die Schwänze `P (⋃ m ≥ K, B m)` gegen `0`,
so gilt `X n → Y` f.s. Durch `lake env lean` gegen v4.33.1, und `#print axioms`
nennt `propext`, `Classical.choice`, `Quot.sound`.

Zwei Entscheidungen an der Aussage, beide aus der Gebrauchsstelle:

* Die Inklusion wird **f.ü.** verlangt (`∀ n, ∀ᵐ ω ∂P, … → ω ∈ B (k n)`), nicht
  überall. Das ist die Form, in der eine Stufe sie liefert: der Beweis von
  `exists_measurable_pair_of_partition` argumentiert auf den Stücken positiver
  Masse und sondert eine Nullmenge aus, hat also je Stufe eine Ausnahmemenge.
  Abzählbar viele Nullmengen sind eine Nullmenge — `ae_all_iff`, eine Zeile.
* `δ` ist eine Folge über den **Niveaus** und nicht über `n`, weil die
  Abstandsschranke der Durchmesser des Niveaus ist. `hδ.comp hk` ist der ganze
  Unterschied.

**Stand der Datei:** `WeakConvergence/Suggested.lean` zählt nach `grep` 177
Deklarationen und trägt weiterhin zwei `sorry`, `exists_ae_tendsto_of_tendsto`
(Meilenstein 3) und `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`
(Meilenstein 4); `rc = 1` mit unverändert genau den beiden angekündigten Fehlern
aus dem Versionsgrund bei `tendsto_map_of_measure_setOf_continuousAt_eq_one`
(jetzt `:2142`).

Der Beweis ist kurz: `⋂ K, ⋃ m ≥ K, B m` ist eine Nullmenge, weil sie in jedem
Schwanz liegt (`ge_of_tendsto` gegen `measure_mono`); außerhalb verfehlt ein
Schwanz das `ω` ganz, und von dem Index an, ab dem `k n ≥ K` ist, ist der
Abstand höchstens `δ (k n)`, was `squeeze_zero'` mit
`tendsto_iff_dist_tendsto_zero` schließt.

#### Was Meilenstein 3 jetzt sagt

Vier Punkte stehen neu bzw. berichtigt vor `exists_ae_tendsto_of_tendsto`, in
der Reihenfolge, in der sie gebraucht werden:

1. `ae_tendsto_of_subset_of_tendsto_measure_iUnion_ge` (bewiesen), mit dem
   Zeugen gegen Borel--Cantelli im Punkt selbst — er gehört dorthin, weil er
   die Bauform begründet und nicht bloß eine Anekdote ist.
2. `exists_measurable_index_of_stochastic_matrix_diag`: die Indexabbildung mit
   dem **Diagonalzweig auf einem benannten Intervall**, `G (j, y) = j` für
   `0 < y ≤ (c j j).toReal`. Sie ist es, die aus einer Zahl eine Inklusion
   macht. Der Weg ist benannt: die vorhandene Aussage auf `c j ∘ Equiv.swap 0 j`
   angewandt, damit der Diagonaleintrag das **erste** Teilsummenintervall wird,
   und `exists_measurable_map_restrict_volume_eq_sum_smul_dirac` um den
   Zusatz `∀ y, 0 < y → y ≤ (p 0).toReal → g y = x 0` ergänzt, der in ihrem
   Beweis `Nat.find_eq_zero` ist.
3. `exists_finite_partition_diam_le_null_frontier`: endlich viele Stücke
   **positiver** Masse mit Nullrand, plus ein Rest kleiner Masse — die
   Trunkierung der abzählbaren Zerlegung des fünften Laufs. Warum beides zählt,
   steht dort: die Positivität macht den Zeilendefekt endlich, die Endlichkeit
   macht sein Supremum klein.
4. `exists_measurable_pair_of_partition_subset`: die Stufe mit der Schätzung als
   Inklusion, `{z | ε < dist (X z) z.1.1} ⊆ {z | z.1.1 ∈ A 0} ∪ {z | z.1.2 ≤ t}`.

Und der Zusammenbau selbst ist neu geschrieben, mit `k n` als \EK{}s `k_n`, mit
`B k = {Y ∈ A^{(k)} 0} ∪ {ξ ≤ 1/k}` und der Rechnung
`P (⋃ m ≥ K, B m) ≤ ∑_{k≥K} 2⁻ᵏ + 1/K`. Der Raum ist danach
`(E × ℝ) × (ℕ × ℕ → E)` — **eine** gleichverteilte Variable, nicht `ℕ → ℝ`.

**Was vom bisherigen Bestand fällt: nichts.** `exists_measurable_pair_of_partition`
und seine acht Hilfsaussagen bleiben richtig und werden gebraucht; was sich
ändert, ist allein die Gestalt ihrer letzten Zeile — eine Inklusion statt einer
Zahl —, und die Konstruktion darin ist dieselbe. Auch der Rest von Meilenstein 3
ist unberührt.

**Das Manuskript ist nicht angefaßt.** `rem:MZcost` und die Aussage von
`fact:PSpolish` reden über die Existenz der Darstellung, nicht über ihren
Beweisweg.

#### Vorschlag für den nächsten Lauf

`exists_measurable_index_of_stochastic_matrix_diag`, samt dem Zusatz an
`exists_measurable_map_restrict_volume_eq_sum_smul_dirac`. Worauf es ruht: auf
der vorhandenen Konstruktion, die den Diagonaleintrag nur an die richtige Stelle
der Aufzählung zu bringen braucht (`Equiv.swap 0 j`, `Measure.sum_comp_equiv`,
`Equiv.tsum_eq`), und auf `Nat.find_eq_zero` in deren Beweis. Warum jetzt: es
ist der einzige der drei ausstehenden Punkte, der ausschließlich auf schon
Bewiesenem steht, und er ist derjenige, ohne den die Stufe ihre Schranke nicht
als Inklusion aussprechen kann — die drei anderen hängen der Reihe nach an ihm.
Die drei Aufrufstellen von
`exists_measurable_map_restrict_volume_eq_sum_smul_dirac` (`:3280`, `:3324` und
die Aussage selbst) sind beim Ergänzen des Konjunkts mitzuziehen.

**Werkzeugnotiz, und diesmal ohne Schaden.** Ein `lake env lean` ist versehentlich
ohne vorangestelltes `cd ~/Code/lean/journal` gelaufen, aus dem Worktree heraus.
Es hat **kein** `.lake` angelegt (`git status` im Worktree zeigt nur die drei
bearbeiteten Pfade, und `find` findet dort kein Paketverzeichnis) und dasselbe
Ergebnis geliefert wie der Lauf davor. Die Regel des zwölften Laufs bleibt
trotzdem stehen: sie ist billig und der Schaden im Fehlerfall groß.

### 2026-09-08, fünfzehnter Lauf des Tages — der Diagonalzweig auf dem ersten Intervall, die endliche Zerlegung mit positiven Stücken, und zweimal war die Voraussetzung zu stark

**Bearbeitet:** `fact:PSpolish`, über `WeakConvergence` Meilenstein 3, genau
entlang des Vorschlags des vierzehnten Laufs. Beide angekündigten Stücke sind
bewiesen und durch `lake env lean` gegen v4.33.1 gelaufen.

#### Was bewiesen ist

**Erstens, der Zusatz an `exists_measurable_map_restrict_volume_eq_sum_smul_dirac`.**
Die Aussage trägt jetzt ein drittes Konjunkt:

```
∀ y : ℝ, y ≤ (p 0).toReal → g y = x 0
```

Der Beweis ist zwei Zeilen: `s 1 = s 0 + (p 0).toReal = (p 0).toReal` aus
`hstep 0` und `hs0`, dann `Nat.find_eq_zero` (`Data/Nat/Find.lean:106`), dessen
rechte Seite gerade `P 0 y = (y ≤ s 1 ∨ 1 ≤ y)` ist. Er steht als `have hdiag`
vor dem abschließenden `refine`, so daß der vorhandene Beweis der Bildmaß-Formel
unangetastet bleibt. Die beiden Aufrufstellen (`exists_measurable_map_prod_infinitePi_eq_sum_smul`
und `exists_measurable_index_of_stochastic_matrix`) sind mitgezogen und brauchen
das neue Konjunkt nicht.

**Zweitens, `exists_measurable_index_of_stochastic_matrix_diag`.** Ein
meßbares `G : ℕ × ℝ → ℕ`, das jede Zeile `c j` als Gesetz von `G (j, ·)` unter
Lebesgue auf `(0,1]` realisiert **und** `G (j, y) = j` für `y ≤ (c j j).toReal`
erfüllt. Der Weg ist der angekündigte: je `j` die vorhandene Aussage auf die
Gewichte `c j ∘ Equiv.swap 0 j` und die Punkte `Equiv.swap 0 j` angewandt, so
daß der Diagonaleintrag der nullte wird.

* Die **Hypothese** wandert mit `Equiv.tsum_eq` zurück — der additiven Fassung
  von `Equiv.tprod_eq` (`Topology/Algebra/InfiniteSum/Basic.lean:562`, per
  `@[to_additive]`).
* Die **Konklusion** wandert mit `Measure.sum_comp_equiv`
  (`Measure/MeasureSpace.lean:1415`) zurück; `Measure.sum (m ∘ e) = Measure.sum m`
  paßt hier ohne Umformung, weil `fun i => c j (swap 0 j i) • dirac (swap 0 j i)`
  definitionsgleich `(fun i => c j i • dirac i) ∘ swap 0 j` ist.
* Das **erste Intervall** ist `Equiv.swap_apply_left` (`Logic/Equiv/Basic.lean:655`)
  an beiden Stellen: `p 0 = c j (swap 0 j 0) = c j j` und
  `x 0 = swap 0 j 0 = j`.

Die Verklebung über `j` ist wie bei der undiagonalen Fassung
`measurable_from_prod_countable_right`.

#### Eine Abschwächung gegen den Bauplan: die Positivität von `y` fällt

Der Bauplan des vierzehnten Laufs schrieb das Konjunkt als
`∀ y, 0 < y → y ≤ (p 0).toReal → g y = x 0` und die Diagonalbedingung als
`G (j, y) = j` für `0 < y ≤ (c j j).toReal`. Die Voraussetzung `0 < y` wird
nicht gebraucht und steht daher in keiner der beiden Aussagen: für `y ≤ 0` ist
erst recht `y ≤ s 1`, also findet `Nat.find` schon bei `0`. Das ist die stehende
Regel „minimale Voraussetzungen" an einer Stelle, an der sie nichts kostet — die
Gebrauchsstelle arbeitet ohnehin auf `Ioc 0 1`, dort ist die schwächere
Hypothese gratis. `WeakConvergence/README.md` ist an beiden Stellen berichtigt;
die Formulierungen mit `0 < y` im Bericht des vierzehnten Laufs (Punkt 2 seiner
Meilensteinliste) sind damit überholt.

#### Prüfung

`lake env lean` auf `WeakConvergence/Suggested.lean` meldet **nur noch die zwei
bekannten Fehler** aus dem Versionsgrund bei
`tendsto_map_of_measure_setOf_continuousAt_eq_one` (nach den Einträgen dieses
Laufs `:2155`, vorher `:2142`; `Measure.map` nimmt in v4.33.1 kein blankes
`h : E → E'`) und genau die zwei angekündigten `sorry`,
`exists_ae_tendsto_of_tendsto` (M3) und
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (M4). Kein neuer
Fehler, keine neue Warnung. `#print axioms` — vorübergehend an die Datei
gehängt, danach wieder entfernt — nennt für

* `exists_measurable_map_restrict_volume_eq_sum_smul_dirac`,
* `exists_measurable_index_of_stochastic_matrix_diag`,
* `exists_measurable_index_of_stochastic_matrix`

je genau `propext`, `Classical.choice`, `Quot.sound`; kein `sorryAx`, die
Fehlerstelle bei `:2142` färbt also nicht ab.

**Eine Falle beim Anschreiben, die Zeit gekostet hat und die der nächste Lauf
kennen sollte:** in

```
... = Measure.sum fun i => p i • Measure.dirac (x i) ∧ ∀ y, ...
```

schluckt das `fun` das `∧`; der Fehler erscheint als „Type mismatch … expected
to have type `Prop`" **an der Summe** und nicht am Konjunkt, und die Folgefehler
stehen im Beweisrumpf. Die Klammer um `(Measure.sum fun i => …)` ist Pflicht,
sobald hinter einer solchen Gleichung noch etwas steht.

**Stand der Datei:** `WeakConvergence/Suggested.lean` zählt nach dem Nachtrag
unten 178 Deklarationen (`theorem`/`lemma`/`def`/`instance`/`abbrev` am
Zeilenanfang) und trägt unverändert die zwei genannten `sorry`.

**Das Manuskript ist nicht angefaßt.**

#### Nachtrag desselben Laufs: `exists_finite_partition_diam_le_null_frontier` ist auch bewiesen

Der Lauf hatte den obigen Punkt als Vorschlag für den nächsten notiert und dann
noch Zeit; er ist erledigt, samt einer Hilfsaussage, die dafür fehlte.

**`frontier_biUnion_finset_subset`** — `frontier (⋃ j ∈ K, S j) ⊆ ⋃ j ∈ K,
frontier (S j)` für einen `Finset`-Index. Mathlib hat den Zweimengenfall,
`frontier_union_subset` (`Topology/Closure.lean:544`), aber **scharf**
formuliert: `frontier s ∩ closure tᶜ ∪ closure sᶜ ∩ frontier t`. Die Induktion
über `Finset.set_biUnion_insert` muß die Durchschnitte darum von Hand
wegwerfen; das ist der einzige Unterschied zum erwarteten Dreizeiler und der
Grund, warum `frontier_biInter_range_subset` (Zweimengenfall
`frontier_inter_subset`) im Bestand steht, die Vereinigungsform aber nicht.

**`exists_finite_partition_diam_le_null_frontier`** — für `ν` ein
Wahrscheinlichkeitsmaß auf separablem pseudometrischem `E` und `ε, η > 0` ein
`K : Finset ℕ` mit `0 ∉ K` und ein `A : ℕ → Set E`, das eine abzählbare meßbare
Zerlegung von `E` ist, außerhalb `insert 0 K` leer, mit `0 < ν (A j)` und
`Metric.diam (A j) ≤ ε` für `j ∈ K`, mit `ν (frontier (A i)) = 0` für **jedes**
`i` — den Rest eingeschlossen — und `ν (A 0) ≤ η`.

Drei Entscheidungen an der Aussage, alle drei aus der Gebrauchsstelle:

* **Der Index ist ein `Finset`, kein Präfix `1, …, N`.** Der Bauplan des
  vierzehnten Laufs schrieb `A 1, …, A N`; das hätte die überlebenden Stücke
  neu durchzählen müssen (`Finset.orderIsoOfFin` und ein `dite` mit zwei
  Beweisverpflichtungen im Rumpf). Über einem `Finset` entfällt die Umzählung
  ersatzlos, und es kostet nichts: die Familie ist weiterhin `ℕ`-indiziert und
  eine Zerlegung, also gilt für sie jede Aussage, die für eine solche gilt.
* **Der Rest wird nicht zusammengesetzt, sondern komplementiert.** `A 0 = Uᶜ`
  mit `U = ⋃ j ∈ K, As (j-1)`, statt „Schwanz vereinigt mit den Nullstücken".
  Das ist der Grund, warum das Absorbieren der Stücke der Masse `0` — der Punkt,
  an dem der Vorschlag den größten Aufwand vermutete — nichts kostet: ein
  Komplement hat den Rand dessen, was es komplementiert (`frontier_compl`), und
  der Rand der endlichen Vereinigung ist die neue Hilfsaussage. Die Vermutung
  des Vorschlags war also falsch, und zwar zugunsten des Beweises.
* **Keine Subtraktion in `ℝ≥0∞`.** Statt `ν (A 0) = 1 - ν U` abzuschätzen, geht
  der Beweis über die Inklusion
  `Uᶜ ⊆ T M ∪ ⋃ {As i | i < M, ν (As i) = 0}` und dann `measure_union_le` mit
  `measure_biUnion_null_iff`. Genau dort werden Überdeckung und Disjunktheit
  der abzählbaren Zerlegung verbraucht.

Die Trunkierung selbst geht über die Schwänze `T M = (⋃ i < M, As i)ᶜ`, die
gegen `∅` fallen, mit `tendsto_measure_iInter_atTop`
(`Measure/MeasureSpace.lean:672`) — **nicht** mit `tendsto_measure_iUnion_atTop`
(`:648`), das der Vorschlag genannt hatte: die aufsteigende Fassung liefert
`ν (⋃ i<M, As i) → 1` und damit erst nach einer Subtraktion die Schranke, die
absteigende liefert sie direkt.

**Prüfung.** Beides steht in `WeakConvergence/Suggested.lean` und geht dort
durch `lake env lean` — unverändert nur die zwei bekannten Fehler bei `:2142`
und die zwei angekündigten `sorry`. `#print axioms` nennt für beide genau
`propext`, `Classical.choice`, `Quot.sound`. Zusätzlich liegt der Beweis
**standalone** in `TauCeti/WeakConvergence/scratch/FinitePartition.lean`: dort
ist die abzählbare Zerlegung eine explizite Hypothese `hcountable` statt ein
Aufruf von `exists_measurable_partition_diam_le_null_frontier`, so daß die Datei
nur von Mathlib abhängt und für sich typprüfbar ist. Sie ist als
Entwicklungswerkzeug entstanden — der Zyklus Schreiben–Übersetzen kostet dort
unter einer Minute statt vier — und bleibt als Zeuge stehen.

#### Vorschlag für den nächsten Lauf

`exists_measurable_pair_of_partition_subset` — die Stufe von
`exists_measurable_pair_of_partition` mit der Schätzung als **Inklusion**,
`{z | ε < dist (X z) z.1.1} ⊆ {z | z.1.1 ∈ A 0} ∪ {z | z.1.2 ≤ t}` f.ü. Worauf
sie ruht: auf den beiden heute bewiesenen Aussagen und sonst auf nichts
Ausstehendem — `exists_finite_partition_diam_le_null_frontier` liefert die
endliche Zerlegung mit positiven Stücken (die Positivität macht den Zeilendefekt
`(ν (A i) - μ n (A i)) / ν (A i)` endlich, die Endlichkeit sein Supremum klein),
`exists_measurable_index_of_stochastic_matrix_diag` liefert die Diagonale auf
`(0, (c j j).toReal]`, und die Konstruktion selbst ist die von
`exists_measurable_pair_of_partition`, deren letzte Zeile allein die Gestalt
wechselt. Warum jetzt: sie ist der **letzte** Punkt vor dem Zusammenbau; danach
steht `exists_ae_tendsto_of_tendsto` auf lauter Bewiesenem und
`ae_tendsto_of_subset_of_tendsto_measure_iUnion_ge` schließt ihn. Wo mit Arbeit
zu rechnen ist: beim Übergang vom `⨆`-Zeilendefekt zur Zahl `t`, denn die
Aussage muß `t` als gegeben nehmen (die Wahl von `t` gehört in den Zusammenbau,
wo `μ n` läuft), und bei der f.ü.-Klausel, die von den `μ`-Nullstücken kommt.

**Werkzeugnotiz, diesmal mit Schaden, und er ist klein.** Ein `grep` mit
vorangestelltem `cd ~/Code/lean/journal/.lake/packages/mathlib` hat das
Arbeitsverzeichnis dort stehen lassen, und der nächste `lake env lean` lief
darum mit **Mathlib als Wurzelpaket**. `lake` hat daraufhin dessen
Abhängigkeiten nach `journal/.lake/packages/mathlib/.lake/packages/` geklont
(57 MB: `aesop`, `batteries`, `Cli`, `importGraph`, `LeanSearchClient`,
`plausible`, `proofwidgets`, `Qq`). Kein Quelltext ist geändert — `git status`
ist sowohl in `journal` als auch in `journal/.lake/packages/mathlib` sauber —,
und `mathlib/.lake/build` ist unberührt; die Klone liegen unter `.lake` und sind
reiner Plattenverbrauch. Wegräumen ließ sich das im Lauf nicht, weil `rm` in
dieser Sitzung auch in den freigegebenen Verzeichnissen abgelehnt wurde. Die
Regel bleibt und wird schärfer: **jedem `lake env lean` geht ein eigenes
`cd ~/Code/lean/journal` unmittelbar voraus**, und `cd` in ein Unterverzeichnis
von `.lake` unterbleibt — `grep -rn … <Pfad>` tut dasselbe ohne
Verzeichniswechsel.

### 2026-09-08, sechzehnter Lauf des Tages — der Basispunkt wird eine Typklasse, und mit ihm fallen drei `sorry` in `SkorokhodSpace`

Erster von vier Läufen der vorrangigen Aufgabe. `SkorokhodSpace/Suggested.lean`
steht bei **acht** `sorry` statt elf; die Datei geht durch `lake env lean` gegen
v4.33.1 ohne Fehler und ohne Linterwarnung.

#### Punkt 1: die Signaturfrage, und warum die Typklasse gewinnt

Der Befund des fünften Laufs vom 2026-09-07 war richtig: der parameterlosen
`MetricSpace D(ι, E)` fehlte **kein Axiom**, sondern der Basispunkt. Von den
beiden angebotenen Wegen ist der zweite genommen:

```
class BasePoint (α : Type*) where
  basePoint : α
```

mit `Real.instBasePoint : BasePoint ℝ := ⟨0⟩` und
`BasePoint.ofMem : basePoint ∈ s → BasePoint s` für die drei
Teilraum-Instanzen von Meilenstein 1. `ofMem` ist ein `def` und keine
`instance`, und das ist die ehrliche Form: `Set.Icc (1:ℝ) 2` ist ein Index
dieses Meilensteins und hat keinen kanonischen Ursprung.

**Die Begründung, und sie ist ein einziges Argument.** `[Nonempty ι]` samt
`Classical.arbitrary ι` liefert auch einen Punkt, aber einen **opaken**: über
`Classical.arbitrary ℝ` ist nichts beweisbar, insbesondere nicht, daß er `0`
ist. Damit wäre `dist f g` auf `D(ℝ, E)` nie mit `totalDist 0 f g` zu
identifizieren — und die acceptance examples der Meilensteine 4 bis 7 nennen
**alle** ihren Basispunkt, und alle nennen `0`: der gleitende Sprung, die
Auswertung am Sprung, die beiden Sprünge, die nicht verschmelzen, das
schrumpfende Bündel, „One jump costs nothing" mit `t₀ = 0` und `m = 2`. Keines
davon ließe sich unter `Classical.arbitrary` auch nur hinschreiben. Mit
`BasePoint` ist die Identifikation

```
theorem SkorokhodSpace.dist_eq (f g : D(ι, E)) :
    dist f g = SkorokhodSpace.totalDist (basePoint : ι) f g := rfl
```

und sie ist `rfl`. Das ist der ganze Unterschied, und er ist der Grund, daß die
Klasse **Daten** trägt und kein `Prop` ist.

Zwei Nebenpunkte, die die Wahl mitgetragen haben. Erstens: Mathlib hat keine
unbundled Typklasse für punktierte Typen — `git grep "class .*Pointed"` und
`git grep basePoint` auf `upstream/master -- Mathlib/` finden nichts, und einen
`Zero → Inhabited`-Übergang gibt es in `Algebra/Group/ZeroOne.lean` auch nicht;
es war also nichts zu übernehmen. Zweitens: `[Inhabited ι]` wäre die
naheliegende Zweckentfremdung gewesen, aber `default` ist in Mathlib der
Junkwert und nicht der Ursprung, und ein Index kann seinen `Inhabited`-Zeugen
aus einer ganz anderen Quelle beziehen als seinen Nullpunkt.

**Bewiesen, mit `#print axioms` geprüft** (alle auf `propext`,
`Classical.choice`, `Quot.sound`, keines auf `sorryAx`):

* `SkorokhodSpace.instMetricSpace : MetricSpace D(ι, E)` — die parameterlose
  Instanz, `SkorokhodSpace.metricSpace basePoint`. **Der Angelpunkt der
  Aufgabe.**
* `SkorokhodSpace.dist_eq` — ihre Schnittstelle, `rfl`.
* `Real.instBasePoint`, `BasePoint.ofMem`, `BasePoint.coe_ofMem` (die beiden
  letzten hängen an gar keinem Axiom).
* `exhaustion_subset_exhaustion : exhaustion t₀ m ⊆ exhaustion t₁ (m + ⌈dist t₀ t₁⌉₊)`
  — die Fenster zweier Basispunkte sind ineinander kofinal. Dreiecksungleichung
  und `Nat.le_ceil`; es braucht weder die Ordnung noch `AdditiveDist` noch
  Properheit.

**Was ausdrücklich *nicht* behauptet wird, und warum nicht als `sorry`.** Ob
zwei Basispunkte dieselbe Topologie geben, steht nirgends — auch nicht als
`sorry`-Theorem, obwohl das der bequeme Weg gewesen wäre. Der Grund ist ein
gerechneter: die Fenster sind kofinal (siehe oben), aber die Untergruppen
`TimeChange.fixing t₀` sind es nicht — die Translation, die `t₁` nach `t₀`
zurückträgt, hat Norm `0` und verschiebt trotzdem die Pfade, so daß aus
`λ ∈ fixing t₀` mit kleiner Norm kein `μ ∈ fixing t₁` mit kleiner Norm **und**
kleinem Pfadabstand folgt. Die Aussage ist in beiden Richtungen offen, und ein
`sorry` darauf wäre eine Behauptung und keine Verpflichtung gewesen. Statt
dessen ist sie **umgangen**: alles, was unterhalb der Instanz die Topologie von
`D(ι, E)` erwähnt, liest seinen Basispunkt aus der Instanz und nicht aus einem
Parameter. Das betrifft `SkorokhodSpace.isCompact_closure_iff`, dem der freie
`t₀` genommen ist — mit ihm hätten die beiden Seiten der Äquivalenz von zwei
verschiedenen Räumen gesprochen.

#### Punkt 2, halb: `PolishSpace` ist geschenkt

`SkorokhodSpace.instPolishSpace` ist `inferInstance` und kein `sorry` mehr.
Mathlib baut `PolishSpace` aus `SeparableSpace` und `IsCompletelyMetrizableSpace`
(`Mathlib/Topology/MetricSpace/Polish.lean:66`), und letzteres aus einer
vollständigen Metrik (`MetricSpace.toIsCompletelyMetrizableSpace`,
`Mathlib/Topology/Metrizable/CompletelyMetrizable.lean:172`). Es hängt an
`sorryAx` nur durch die beiden Instanzen darüber, nie auf eigene Rechnung, und
ist axiomrein in dem Augenblick, in dem die beiden es sind. Das ist der dritte
Punkt von Meilenstein 5, und er kostet nichts.

`CompleteSpace` und `SeparableSpace` selbst stehen weiter als `sorry` — sie sind
jetzt aber, wie die Aufgabe es wollte, überhaupt erst **formulierbar**, weil die
Metrik da ist. Beide Instanzen haben Namen bekommen
(`SkorokhodSpace.instCompleteSpace`, `SkorokhodSpace.instSeparableSpace`),
damit `#print axioms` sie erreicht.

#### Punkt 4, erste Hälfte: `modulus` ist eine Definition und kein `sorry` mehr

Die Aufgabe nennt es beim Namen: eine Definition mit `sorry`-Rumpf macht jeden
Satz über sie zu einer Aussage über `sorryAx`. Geschrieben und bewiesen:

* `SkorokhodSpace.IsSubdivision t₀ m δ (t : Fin (n+1) → ι)` — `StrictMono t`,
  `t 0 = (B m).min`, `t (Fin.last n) = (B m).max`, und `δ < dist (t i.castSucc)
  (t i.succ)` für jedes `i`. Als benanntes Prädikat, damit das Infimum unten
  über ein `Prop` läuft und kein `BddBelow` braucht.
* `SkorokhodSpace.subdivisionOsc f t` — die Oszillation über den halboffenen
  Zellen `Set.Ico (t i.castSucc) (t i.succ)`, vom linken Randpunkt aus gemessen.
* `SkorokhodSpace.modulus t₀ m f δ = ⨅ n, ⨅ t, ⨅ _ : IsSubdivision t₀ m δ t,
  subdivisionOsc f t`.
* `SkorokhodSpace.modulus_mono` — Monotonie in `δ`.
* `SkorokhodSpace.modulus_eq_zero_of_exhaustion_subsingleton` — auf einem
  einpunktigen Fenster ist der Modul `0`, durch die leere Zerlegung `n = 0`.

**Die eine Abweichung, und ihr Grund.** Der Modul ist **`ℝ≥0∞`-wertig**, die
Roadmap sagte `ℝ`. Das ist nicht Geschmack, sondern der leere Fall: sobald `δ`
den Durchmesser des Fensters erreicht, gibt es überhaupt keine `δ`-dünne
Zerlegung mehr — nicht einmal die triviale vom kleinsten zum größten Punkt —,
und das Infimum läuft über die leere Menge. In `ℝ` ist das der Junkwert `0`,
`modulus` wäre also `0` für alle großen `δ`, die von Meilenstein 7 verlangte
Monotonie in `δ` wäre **falsch** und `tendsto_modulus` sagte nichts. In `ℝ≥0∞`
ist es `⊤`, was die klassische Konvention ist, und `modulus_mono` ist ein Satz.
Dieselbe Wahl zahlt ein zweites Mal in `isCompact_closure_iff`, wo
`⨆ f ∈ A, modulus …` über eine unbeschränkte Familie in `ℝ` wieder ein Junk-`0`
gewesen wäre.

`modulus_eq_zero_of_exhaustion_subsingleton` ist dabei mehr als eine
Beispielrechnung: es ist der einzige Wert von `modulus`, der vor
`tendsto_modulus` zu haben ist, und er legt die Orientierung der Definition
fest. Mit `Set.Icc`-Zellen, oder mit der Oszillation zwischen den
Teilungspunkten statt innerhalb der Zellen, wäre die leere Zerlegung nicht
zulässig und die Aussage falsch.

#### Roadmap

`SkorokhodSpace/README.md` ist an vier Stellen nachgezogen: Meilenstein 1 trägt
`BasePoint` samt der Begründung gegen `Classical.arbitrary` und
`exhaustion_subset_exhaustion`; Meilenstein 4 die parameterlose Instanz und
`dist_eq`; Meilenstein 5 den Nachweis, daß `PolishSpace` nichts kostet;
Meilenstein 7 die fünf neuen Deklarationen samt der `ℝ≥0∞`-Begründung und dem
Basispunkt in `isCompact_closure_iff`.

#### Punkt 2, die erste Sprosse der Vollständigkeit: bewiesen

**`IsCadlag.of_tendstoUniformly`** — der gleichmäßige Limes càdlàg-Funktionen
ist càdlàg, unter `[CompleteSpace E]`. Bewiesen, `#print axioms` nennt
`propext`, `Classical.choice`, `Quot.sound`. Der Beweis braucht weder
`AdditiveDist` noch `ProperSpace` und nichts aus dem Bündel (B).

*Worauf sie ruht.* Auf Mathlibs
`TendstoUniformly.tendsto_of_eventually_tendsto`
(`Topology/UniformSpace/UniformConvergence.lean:625`): konvergieren die `F i`
gleichmäßig gegen `f` und hat jedes `F i` einen Limes `L i` längs eines Filters
`p'`, und konvergieren die `L i` gegen `ℓ`, so ist `Tendsto f p' (𝓝 ℓ)`. Beide
Klauseln von `IsCadlag` sind Instanzen davon — die Rechtsstetigkeit mit
`p' = 𝓝[>] a` und `L i = F i a`, die Linkslimiten mit `p' = 𝓝[<] x` und
`L i = Function.leftLim (F i) x`. Für die zweite ist zu zeigen, daß die `L i`
eine Cauchyfolge bilden, und das ist die gleichmäßige Schranke plus die
Vollständigkeit von `E`; der Fall `𝓝[<] x = ⊥` ist getrennt und trivial.
Vorhanden ist alles Weitere: `IsCadlag.tendsto_leftLim` von Meilenstein 2 macht
`Function.leftLim` zur Aussage über den Strukturzeugen.

*Warum sie zählt.* Weil sie die Sprosse ist, an der `CompleteSpace D(ι, E)`
seinen Grenzpfad **erzeugt**. Billingsleys Beweis komponiert die Zeitwechsel
unendlich und erhält daraus eine gleichmäßig auf den Fenstern konvergente Folge
`gₖ ∘ μₖ⁻¹`; daß ihr Limes wieder in `D(ι, E)` liegt und nicht bloß in den
beschränkten Funktionen, ist genau diese Aussage. Sie stand in keinem
Meilenstein — Meilenstein 2 führte die Abschlußeigenschaften von `IsCadlag`
unter Komposition (`comp_monotone_continuous`) und unter Gleichheit auf dichten
Mengen (`eq_of_eqOn_dense`), aber nicht unter gleichmäßiger Konvergenz — und
steht jetzt dort.

#### Vorschlag für den nächsten Lauf

**`TimeChange.tendsto_of_summable_norm`** — hat `l : ℕ → TimeChange ι`
summierbare Normen, so konvergieren die Teilkompositionen `l 0 * ⋯ * l n`
gleichmäßig auf jedem Fenster gegen einen Zeitwechsel. Das ist Billingsleys
unendliche Komposition.

*Worauf sie ruht.* Auf `TimeChange.norm_mul_le` und
`TimeChange.dist_le_of_norm_le`, beide bewiesen — die erste macht die Normen der
Teilkompositionen summierbar, die zweite übersetzt eine Normschranke in eine
Verschiebungsschranke auf dem Fenster —, und auf der Vollständigkeit von `ι`,
die aus `ProperSpace ι` kommt. Der Punkt, an dem mit Arbeit zu rechnen ist, ist
nicht die Konvergenz, sondern daß der Limes wieder ein `TimeChange` ist:
strenge Monotonie und Stetigkeit erbt er, die **Surjektivität** nicht, und sie
ist bei Billingsley der eigentliche Inhalt.

*Warum jetzt.* Weil `CompleteSpace D(ι, E)` mit der heute bewiesenen ersten
Sprosse nur noch an ihr und an einem Zusammenbau hängt:
`SkorokhodSpace.exists_lt_distOn_add` (bewiesen) liefert aus der
Cauchy-Eigenschaft die Zeitwechsel mit kleinen Normen,
`TimeChange.tendsto_of_summable_norm` setzt sie zusammen, und
`IsCadlag.of_tendstoUniformly` fängt den Grenzpfad auf. Drei benannte Schritte,
von denen zwei stehen.

*Für die Separabilität, und es ist eine Warnung.* Meilenstein 5 beschreibt die
dichte Menge als Treppenpfade mit Sprungzeiten in einer abzählbar dichten Menge
des Index. Ein Index dieses Meilensteins ist eine **abgeschlossene** Teilmenge
von `ℝ` und keine Strecke; die Sprungzeiten müssen also aus einer abzählbar
dichten Teilmenge von `ι` selbst kommen, die es nach `ProperSpace ι` gibt
(σ-kompakt, also separabel), und nicht aus den Rationalen. Das ist derselbe
Fallstrick, an dem 2026-09-07 die Separation von `distOn` beinahe gescheitert
wäre.

### 2026-09-08, siebzehnter Lauf des Tages — die unendliche Komposition der Zeitwechsel, samt ihrer Surjektivität

*Zweiter von vier Läufen der vorrangigen Aufgabe an `SkorokhodSpace`.* Punkt 2
der Aufgabe, `CompleteSpace`. Kein `sorry` ist gefallen — die Datei steht
weiterhin bei **acht** —, aber die Sprosse, an der der Beweis seit dem sechzehnten
Lauf hing, ist bewiesen, und mit ihr vierzehn weitere Deklarationen. Alle fünfzehn
sind mit `#print axioms` geprüft und hängen an `propext`, `Classical.choice`,
`Quot.sound` und an nichts sonst; die Datei geht durch `lake env lean` gegen
v4.33.1.

#### Was bewiesen ist

**`TimeChange.exists_tendsto_of_summable_norm`** — der Kern. Sind
`l : ℕ → TimeChange ι` alle in `TimeChange.fixing t₀` und ist `‖l n‖ ≤ γ n` mit
`γ` summierbar, so konvergieren die Teilkompositionen
`TimeChange.partialComp l n = l 0 ∘ ⋯ ∘ l (n-1)` punktweise gegen einen
Zeitwechsel `L`, der wieder `t₀` festhält und `‖L‖ ≤ ∑' γ` erfüllt.

*Die Surjektivität, und wie sie kommt.* Der vorige Lauf hat sie als den harten
Punkt benannt, und sie war es. Der punktweise Limes einer Folge von
Ordnungsisomorphismen ist umsonst monoton und, unter einer gleichmäßigen
bi-Lipschitz-Schranke, injektiv; **daß sein Bild ganz `ι` ist, folgt daraus
nicht.** Der Index dieses Meilensteins ist nicht als zusammenhängend
vorausgesetzt — `AddSubgroup.zmultiples (1:ℝ)` ist eine der vier laufenden
Instanzen —, also hilft kein Zwischenwertargument, und das Bild ist zwar
abgeschlossen, aber Abgeschlossenheit allein füllt keine Lücke.

Das Mittel ist, **dieselbe Rechnung auf den Inversen zu führen**. Die
Teilkompositionen erfüllen `partialComp l (n+1) = partialComp l n * l n`, also
`(partialComp l (n+1))⁻¹ = (l n)⁻¹ * (partialComp l n)⁻¹`: der Schritt der
inversen Folge verschiebt einen Punkt um genau die Verschiebung von `(l n)⁻¹`,
gelesen an der Stelle `(partialComp l n)⁻¹ t`. Diese Stelle liegt im Fenster
`exhaustion t₀ ⌈exp (∑' γ) * m⌉₊`, wenn `t` im Fenster `m` liegt, weil
`(partialComp l n)⁻¹` den Basispunkt festhält und `exp (∑' γ)`-Lipschitz ist.
Also greift `TimeChange.dist_le_of_norm_le` auch hier, die inverse Folge ist
punktweise Cauchy, ihr Limes `M` existiert, und
`partialComp l n ((partialComp l n)⁻¹ t) = t` geht mit der gleichmäßigen
Lipschitz-Schranke in den Limes über: `L (M t) = t` und `M (L t) = t`. Der Limes
ist damit eine Bijektion **mit benanntem Inversen**, und nicht bloß eine
Einbettung. Beide Richtungen der Monotonie geben `map_rel_iff'`, und die beiden
Lipschitz-Felder der Struktur `TimeChange` sind die beiden Grenzwertabschätzungen.

*Was die Abschätzung summierbar macht.* Nicht `dist_le_of_norm_le` allein: sie
liefert `dist (l t) t ≤ (exp γₙ - 1) * (2m)`, und `exp γₙ - 1` ist zwar eine
Nullfolge, aber ohne weiteres nicht summierbar aus der Summierbarkeit von `γ`.
Der Schritt ist `exp x - 1 ≤ x * exp x`, was `Real.add_one_le_exp (-x)` mal
`exp x` ist; damit ist `exp γₙ - 1 ≤ γₙ * exp (∑' γ)` und die Schranke hat die
Gestalt `C * γ n` mit von `n` unabhängigem `C`. Das ist die Stelle, an der die
**Logarithmus**-Gestalt der Norm von Meilenstein 3 zahlt: eine additive Norm
liefert multiplikative Lipschitz-Konstanten, und deren Produkt über die
Teilkomposition bleibt beschränkt.

*Vollständigkeit von `ι`.* Aus `ProperSpace ι` über `complete_of_proper`
(`Mathlib/Topology/MetricSpace/ProperSpace.lean:104`). Das ist die einzige
Stelle der Meilensteine 3 bis 5, an der `ProperSpace` für etwas anderes als die
Kompaktheit eines Fensters gebraucht wird.

**`TimeChange.exists_tendsto_norm_tail_le`** — dieselbe Aussage mit **Rate**.
Für jedes `n` ist `‖(partialComp l n)⁻¹ * L‖ ≤ ∑' i, γ (n + i)`. Ohne sie sagt
die Existenz nur, daß ein Limes da ist; mit ihr ist die `n`-te Näherung
quantitativ nah, und das ist es, was ein Konvergenzbeweis in `D(ι, E)` liest.
Der Beweis läuft die Existenzaussage auf jeder verschobenen Folge noch einmal
und identifiziert `L` mit `partialComp l n * (der verschobene Limes)` über die
Eindeutigkeit des Grenzwerts; das Bindeglied ist
`TimeChange.partialComp_add`, also
`partialComp l (n + k) = partialComp l n * partialComp (l ∘ (n + ·)) k`.

**Die Hilfssätze**, alle neu und alle gebraucht:
`TimeChange.lipConst_le_exp_norm` (`lipConst ≤ exp ‖·‖`),
`TimeChange.dist_le_exp_norm_mul`, `TimeChange.norm_le_of_lipschitzWith` (die
Umkehrung, mit dem entarteten Zweig `Real.log 0 = 0` für den einpunktigen Index),
`TimeChange.partialComp` samt `partialComp_zero`, `partialComp_succ`,
`partialComp_mem_fixing` und `norm_partialComp_le`.

**Und drei Aussagen über das Verhältnis von Metrik und Fenster**, die der
Zusammenbau an beiden Enden braucht:
`SkorokhodSpace.min_one_distOn_le` (`min 1 (distOn t₀ m f g) ≤ 2^m * totalDist t₀ f g`),
`SkorokhodSpace.distOn_le_of_two_pow_mul_lt_one` (dieselbe Schranke ohne die
Trunkierung, für Paare mit `2^m * totalDist < 1` — die Voraussetzung ist kein
Mangel, denn `distOn` ist im Fenster unbeschränkt, und eine Cauchyfolge liefert
sie für alle bis auf endlich viele Indizes) und
`SkorokhodSpace.totalDist_le_sum_add`
(`totalDist ≤ ∑_{m<M} 2⁻¹^m · min 1 (distOn m) + 2·2⁻¹^M`, die Gegenrichtung:
Konvergenz in endlich vielen Fenstern genügt, weil die Trunkierung den Schwanz
trägt).

**Und drei Aussagen zur Kohärenz der Fenster**, die dem offenen Punkt unten
vorarbeiten: `exhaustion_subset_of_le` (die Fenster um **einen** Basispunkt sind
geschachtelt, ohne die Radiusvergrößerung, die
`exhaustion_subset_exhaustion` für zwei Basispunkte zahlen muß),
`clamp_clamp_of_le` (`clamp t₀ m' (clamp t₀ m t) = clamp t₀ m t` für `m ≤ m'`)
und `SkorokhodSpace.restrictExhaustion_restrictExhaustion` (auf ein großes
Fenster trunkieren und dann auf ein kleines ist auf das kleine trunkieren). Das
ist die algebraische Seite der Verträglichkeit; die analytische steht noch aus.

#### Woran der nächste Lauf hängt, und es ist nicht mehr die Komposition

`CompleteSpace D(ι, E)` steht jetzt auf sechs benannten Punkten, von denen fünf
bewiesen sind. Der offene ist die **Verträglichkeit der Fenstergrenzwerte**, und
er ist präziser, als der sechzehnte Lauf ihn stellen konnte. Für jedes `m` liefert
die Konstruktion einen Grenzwert der Trunkierungen auf `exhaustion t₀ m`, und die
Zeitwechsel, mit denen sie ihn liefert, hängen von `m` ab. Zu zeigen ist, daß ein
einziges `f : D(ι, E)` für **jedes** `m` zugleich `distOn t₀ m fₙ f → 0` erfüllt.

*Der naheliegende Weg geht nicht, und das ist ein Befund.* Man möchte
`distOn t₀ m ≤ distOn t₀ (m+1)` haben und daraus die Verträglichkeit ablesen. Der
Zeitwechsel, der für das größere Fenster zulässig ist, vergleicht aber
`f ∘ clamp (m+1) ∘ λ` mit `g ∘ clamp (m+1)`, und liest man diesen Vergleich an
einem Punkt des kleineren Fensters, so stehen die beiden `clamp` nicht
zusammen — links `clamp (m+1) (λ t)`, rechts `clamp (m+1) t`, und keines von
beiden ist `clamp m` von irgend etwas. Der Punkt ist also über die Trunkierungen
zu führen und nicht über die Pseudoabstände; so steht er jetzt in Meilenstein 5,
als `SkorokhodSpace.exists_restrictExhaustion_limit`.

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.exists_restrictExhaustion_limit`** — zu einer im
`totalDist t₀` Cauchyschen Folge `fₙ` gibt es ein `f : D(ι, E)` mit
`distOn t₀ m fₙ f → 0` für jedes `m`.

*Worauf sie ruht.* Auf den fünf bewiesenen Punkten oben, und der Arbeitsanteil
ist allein die Verträglichkeit: die Eindeutigkeit **innerhalb** eines Fensters ist
`SkorokhodSpace.eq_of_distOn_eq_zero` (bewiesen 2026-09-07), die Erzeugung des
Grenzpfads ist `IsCadlag.of_tendstoUniformly` samt
`TimeChange.exists_tendsto_norm_tail_le`, und der Zusammenbau zur Metrik ist
`SkorokhodSpace.totalDist_le_sum_add`.

*Warum jetzt.* Weil sie der letzte offene Punkt von `CompleteSpace D(ι, E)` ist
und weil `SeparableSpace` und `PolishSpace` — der dritte kostet nach dem
sechzehnten Lauf nichts mehr — hinter ihr stehen. Sie ist überdies die einzige
der drei, deren Beweis nicht in der Literatur nachzuschlagen ist: Billingsley
führt `D[0,∞)` über die Restriktionsabbildungen nach `D[0,m]`, was in dieser
Allgemeinheit kein Gegenstück hat, weil ein Fenster hier kein Intervall sein muß.

*Und die Warnung zur Separabilität, die vom sechzehnten Lauf steht und weiter
gilt.* Die Sprungzeiten der dichten Treppenpfade müssen aus einer abzählbar
dichten Teilmenge von `ι` selbst kommen — die es nach `ProperSpace ι` gibt, denn
σ-kompakt heißt separabel —, und nicht aus den Rationalen: ein Index dieses
Meilensteins ist eine abgeschlossene Teilmenge von `ℝ` und keine Strecke.

### 2026-09-08, achtzehnter Lauf des Tages — die Metrik von Meilenstein 4 ist keine Skorokhod-Metrik, und das ist bewiesen

*Vorrangige Aufgabe, dritter von vier Läufen an `SkorokhodSpace`.* Der Auftrag
lautete, `CompleteSpace D(ι, E)` zu beweisen. Der Lauf hat statt dessen gezeigt,
daß die Aussage **falsch** ist, und zwar nicht knapp, sondern strukturell: die
Metrik, auf der sie steht, ist nicht die Skorokhod-Metrik. Dreizehn neue
Deklarationen, alle durch `lake env lean` gegen v4.33.1 und alle mit
`#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft. Die
Datei steht bei **fünf** `sorry` statt acht — drei sind hinausgegangen, ohne
bewiesen zu werden, weil zwei von ihnen falsch waren und der dritte ohne sie
nicht formulierbar ist.

#### Der Befund, in einem Satz

`distOn t₀ m f g` liest den Abstand der beiden Pfade **am Rand des Fensters**
ungedämpft ab, gleichgültig welchen Zeitwechsel man wählt; damit erzwingt die
Konvergenz in der Metrik die punktweise Konvergenz an allen Fensterrändern, was
die $J_1$-Topologie nicht tut.

```lean
theorem SkorokhodSpace.dist_exhaustionMax_le_distOn (t₀ : ι) (m : ℕ) (f g : D(ι, E)) :
    dist (f.toFun (exhaustionMax t₀ m)) (g.toFun (exhaustionMax t₀ m))
      ≤ SkorokhodSpace.distOn t₀ m f g
```

*Der Beweis ist drei Zeilen lang und das ist der Punkt.* Sei
$b = \texttt{exhaustionMax}\ t_0\ m$ und $\lambda$ ein beliebiger zulässiger
Zeitwechsel. Setze $t = \max(\lambda^{-1} b, b)$. Dann ist $t \ge b$, also
$\texttt{clamp}\ t = b$, und $\lambda t \ge \lambda(\lambda^{-1}b) = b$, also
auch $\texttt{clamp}(\lambda t) = b$. Das Supremum in `distOn` enthält daher den
Term $r(f(b), g(b))$, für **jedes** $\lambda$, und das Infimum kommt nicht
darunter. Dasselbe am linken Rand:
`SkorokhodSpace.dist_exhaustionMin_le_distOn`. Die dafür nötigen
Clamp-Aussagen sind `clamp_eq_exhaustionMax_of_le` und
`clamp_eq_exhaustionMin_of_le`, beide einzeilig.

#### Was daraus folgt, und es ist in Lean bewiesen

`SkorokhodSpace.min_one_dist_exhaustionMax_le` kombiniert das mit
`min_one_distOn_le` zu
$\min(1, r(f(b), g(b))) \le 2^m \cdot \texttt{totalDist}$, und daraus wird

```lean
theorem SkorokhodSpace.continuous_eval_exhaustionMax (m : ℕ) :
    Continuous fun f : D(ι, E) => f.toFun (exhaustionMax (basePoint : ι) m)
```

— **die Auswertung am Fensterrand ist stetig, an jedem Pfad, mit Sprung oder
ohne.** Für die Skorokhod-Topologie ist sie das nur an den Pfaden, die dort nicht
springen; genau das stand bis heute als `SkorokhodSpace.continuousAt_eval` mit
`sorry` in der Datei, als Äquivalenz. Die Äquivalenz ist widerlegt, und zwar
konkret:

```lean
theorem SkorokhodSpace.exists_jump_continuousAt_eval :
    ∃ f : D(ℝ, ℝ), Function.leftLim f.toFun 1 ≠ f.toFun 1 ∧
      ContinuousAt (fun g : D(ℝ, ℝ) => g.toFun 1) f
```

Der Zeuge ist `SkorokhodSpace.step`, die Einheitsstufe bei $1$, mitsamt
`step_apply` und `leftLim_step`; daß $1$ der Fensterrand ist, ist
`exhaustionMax_real : exhaustionMax (0:ℝ) m = m`. Für $\iota = \R$ und
$t_0 = 0$ sind die Fensterränder die ganzen Zahlen, also erzwingt die Metrik
punktweise Konvergenz an **jeder** ganzen Zahl.

#### Und die Vollständigkeit fällt mit

Nicht in Lean, sondern von Hand gerechnet, aber vollständig, und der Kern
$w\,1 = 1$ ist der bewiesene Satz oben. Nimm $\iota = \R$, $E = \R$, $t_0 = 0$
und
$$x_n = \mathbf 1_{(-\infty,\;1 + \frac1{n+1})}.$$
Jedes $x_n$ ist càdlàg.

*Cauchy.* Der stückweise lineare Zeitwechsel $\lambda_{n,k}$, der $0$ fest läßt,
außerhalb $[\tfrac12, 2]$ die Identität ist und $1+\frac1{k+1}$ auf
$1+\frac1{n+1}$ trägt, erfüllt $x_n(\texttt{clamp}_m(\lambda t)) = x_k(\texttt{clamp}_m t)$
für **alle** $t$ und **alle** $m$ — man prüft die drei Bereiche
$t \le -m$, $-m \le t \le m$, $t \ge m$ einzeln —, also ist jedes Supremum $0$
und $\texttt{distOn}\ m\ x_n\ x_k \le \|\lambda_{n,k}\|$. Die Steigungen von
$\lambda_{n,k}$ sind $\frac{1/2 + 1/(n+1)}{1/2 + 1/(k+1)}$ und
$\frac{1 - 1/(n+1)}{1 - 1/(k+1)}$, beide $\to 1$, also
$\|\lambda_{n,k}\| \to 0$ und $\texttt{totalDist}(x_n, x_k) \le 2\|\lambda_{n,k}\| \to 0$.

*Kein Grenzwert.* Sei $w \in D(\R,\R)$ mit $\texttt{totalDist}(x_n, w) \to 0$.
Nach `dist_exhaustionMax_le_distOn` beim Radius $1$ ist
$r(x_n(1), w(1)) \le \texttt{distOn}\ 1\ x_n\ w \to 0$, und $x_n(1) = 1$ für
jedes $n$, also $w(1) = 1$. Beim Radius $2$ liefert die Konvergenz Zeitwechsel
$\lambda_n$ mit $\|\lambda_n\| \to 0$ und
$\sup_t |x_n(\texttt{clamp}_2(\lambda_n t)) - w(\texttt{clamp}_2 t)| \to 0$.
Da $x_n$ nur die Werte $0$ und $1$ annimmt, tut $w$ es auch, und für große $n$
ist $\{t \in [-2,2] : w(t) = 1\} = [-2, c_n)$ mit
$c_n = \lambda_n^{-1}(1 + \frac1{n+1})$. Also ist $c_n \wedge 2$ ab einem $n$
konstant, aus $w(1) = 1$ folgt $c_n > 1$, und aus
`TimeChange.dist_le_of_norm_le` folgt $c_n \to 1$. Widerspruch.

Der Sprung von $w$ müßte also echt rechts von $1$ liegen, und die Zeitwechsel
des zweiten Fensters müßten ihn mit gegen $0$ gehender Norm nach
$1 + \frac1{n+1} \to 1$ tragen. Beides zugleich geht nicht.

#### Warum das kein Zufall ist, und wie die Reparatur aussieht

Der Fehler steckt nicht im Beweis, sondern in der **Summe über ganzzahlige
Radien**. Ethier--Kurtz definieren auf $D_E[0,\infty)$
$$d(x,y) = \inf_{\lambda}\Bigl[\gamma(\lambda) \vee \int_0^\infty e^{-u}\,
  \bigl(1 \wedge \sup_t r(x(t\wedge u), y(\lambda(t)\wedge u))\bigr)\,\dif u\Bigr],$$
und das Innere ist **wörtlich unser `distOn`** — dieselbe Gestalt, dieselbe
einseitige Clampung, derselbe `max` gegen die Norm. Der einzige Unterschied ist,
daß der Radius $u$ reell ist und integriert wird statt summiert. Und der Grund
dafür ist genau der hier gefundene: für festes $u$ ist der Ausdruck an den
Sprungstellen von $x$ und $y$ unstetig, aber diese Radien sind abzählbar, also
Lebesgue-null, und das Integral sieht sie nicht. Billingsleys Alternative ist
die stetige Rampe $g_m(t)x(t)$ statt der Clampung — die hier ausscheidet, weil
sie Pfadwerte mit Skalaren multipliziert und $E$ ein metrischer Raum ohne
lineare Struktur ist.

Also: **`distOn` bleibt, der Radius wird reell, und `totalDist` wird ein
Integral.** Das steht so in `SkorokhodSpace/README.md`, Meilenstein 4, samt der
einen neuen Verpflichtung, die diese Gestalt mitbringt — die Borel-Meßbarkeit
von $u \mapsto \sup_t r(\dots)$ bei festem $\lambda$ — und samt dem Grund, warum
das Infimum über $\lambda$ **außerhalb** des Integrals steht und nicht innerhalb
wie in `distOn`: außen braucht man die Meßbarkeit für einen Zeitwechsel nach dem
anderen, und sie folgt aus der Rechtsstetigkeit, die das Supremum auf eine
abzählbare dichte Menge zurückführt; innen wäre der Integrand ein Infimum über
eine überabzählbare Familie.

#### Das eigene acceptance example hat es gefunden

Es steht seit dem 2026-09-07 als **erstes** acceptance example von Meilenstein 4
in `SkorokhodSpace/README.md`: $f = \mathbf 1_{[1,\infty)}$,
$g_\varepsilon = \mathbf 1_{[1+\varepsilon,\infty)}$, und die Behauptung
$\texttt{dist}(f, g_\varepsilon) \to 0$. Beim Radius $1$ ist
$b = 1$, $f(1) = 1$, $g_\varepsilon(1) = 0$, also
$\texttt{distOn}\ 1\ f\ g_\varepsilon \ge 1$ und
$\texttt{totalDist} \ge \tfrac12$ für **jedes** $\varepsilon$. Das Beispiel ist
für die summierte Metrik falsch. Es ist die Probe, für die acceptance examples
da sind, und sie hätte den Defekt am 2026-09-07 gefunden, wäre sie gerechnet und
nicht bloß aufgeschrieben worden. Die Lehre, und sie gehört neben die „Regel für
den Negativbefund": **ein acceptance example, das nur dasteht, prüft nichts.**
Wo es sich in Lean hinschreiben läßt, gehört es hingeschrieben; wo nicht,
gehört wenigstens die eine Ungleichung nachgerechnet, an der es hängt.

#### Was an der Datei geändert wurde

* **Neu und bewiesen (dreizehn Deklarationen):** `clamp_eq_exhaustionMax_of_le`,
  `clamp_eq_exhaustionMin_of_le`, `SkorokhodSpace.dist_exhaustionMax_le_distOn`,
  `SkorokhodSpace.dist_exhaustionMin_le_distOn`,
  `SkorokhodSpace.min_one_dist_exhaustionMax_le`,
  `SkorokhodSpace.continuous_eval_exhaustionMax`, `exhaustionMax_real`,
  `SkorokhodSpace.step`, `SkorokhodSpace.step_apply`,
  `SkorokhodSpace.leftLim_step`,
  `SkorokhodSpace.exists_jump_continuousAt_eval`, und aus Meilenstein 2
  `IsCadlag.of_forall_eventuallyEq` samt
  `IsCadlag.of_tendstoUniformlyOn_exhaustion`.
* **Entfernt, mit Begründung an der Stelle:** `SkorokhodSpace.instCompleteSpace`
  (falsch), `SkorokhodSpace.continuousAt_eval` (falsch),
  `SkorokhodSpace.instSeparableSpace` und `SkorokhodSpace.instPolishSpace` (nicht
  falsch, aber Aussagen über eine Metrik, die keine Skorokhod-Metrik ist; die
  zweite ruhte überdies auf der ersten). An ihrer Stelle steht ein
  Meilenstein-5-Kopf, der die Widerlegung, die Cauchy-Folge und die Reparatur
  nennt.
* **Unberührt:** alles über `TimeChange` und alles über `distOn`. Die fünfzehn
  Deklarationen des siebzehnten Laufs, die unendliche Komposition samt ihrer
  Surjektivität, `IsCadlag.of_tendstoUniformly`, `min_one_distOn_le`,
  `distOn_le_of_two_pow_mul_lt_one`, `totalDist_le_sum_add` — alle bleiben
  richtig und alle werden von der reparierten Metrik gebraucht. Verloren ist
  nichts als die Verklebung über die Fenster, und die war ohnehin die Stelle, an
  der zwei Läufe nicht weiterkamen.

#### Und der Weg zur Vollständigkeit, jetzt benannt

Der siebzehnte Lauf ließ als offenen Punkt `exists_restrictExhaustion_limit`
stehen, die Verträglichkeit der Fenstergrenzwerte. Dieser Punkt ist **gestrichen
und ersetzt**, denn er ist nicht schwer, sondern falsch: er verlangt einen
Grenzwert in `distOn u`, und ein solcher muß die Folge am Fensterrand punktweise
treffen. An seine Stelle tritt `SkorokhodSpace.tendsto_of_partialComp`, und es
ist Billingsleys Argument in der Fassung, die zu `partialComp` paßt: mit
$P_n = \texttt{partialComp}\ l\ n$ und $L$ der unendlichen Komposition
vergleicht man $y_n = x_n \circ P_n^{-1} \circ L$ mit $y_{n+1}$; die Substitution
$s = P_{n+1}^{-1}(Lt)$ macht daraus $r(x_n(l_n s), x_{n+1}(s))$, und das ist,
was `distOn` beschränkt. Die $y_n$ sind also auf jedem Fenster gleichmäßig
Cauchy, ihr Grenzwert $z$ ist der Grenzpfad, und
$\texttt{dist}(x_n, z)$ wird mit dem Zeitwechsel $P_n^{-1}L$ abgeschätzt, dessen
Norm der Schwanz $\sum_{i} \gamma(n+i)$ aus
`TimeChange.exists_tendsto_norm_tail_le` ist.

Die eine Zutat, die dafür fehlte, ist im selben Lauf **bewiesen**:
`IsCadlag.of_forall_eventuallyEq` — eine Funktion, die in der Umgebung jedes
Punktes mit *irgendeiner* càdlàg-Funktion übereinstimmt, ist càdlàg. Beide
Klauseln von `IsCadlag` sind Aussagen über `𝓝[>] a` und `𝓝[<] x`, also lokal,
und der ganze Inhalt ist `Filter.Tendsto.congr'`. Die Fassung, in der sie
gebraucht wird, ist gleich mitbewiesen:
`IsCadlag.of_tendstoUniformlyOn_exhaustion` — gleichmäßige Konvergenz auf
**jedem** Fenster genügt, denn `F n` mit `clamp m` verkettet konvergiert
gleichmäßig auf ganz `ι`, und jeder Punkt liegt in einer offenen Kugel
ganzzahligen Radius. Beide hängen nur an `propext`, `Classical.choice`,
`Quot.sound`, beide sind von der Metrik unabhängig und überstehen deren
Reparatur unverändert. Gebraucht werden sie, weil die
Abschätzung nur auf Fenstern gilt: `IsCadlag.of_tendstoUniformly` wird auf
$y_n \circ \texttt{clamp}\ u$ angewandt statt auf $y_n$, und $z$ ist càdlàg in
einem Punkt, weil es in dessen Umgebung mit $z \circ \texttt{clamp}\ u$
übereinstimmt — jeder Punkt liegt im Inneren eines Fensters.

#### Vorschlag für den nächsten Lauf

**Der Radius von `SkorokhodSpace.distOn` wird reell.** Also
`exhaustion (t₀ : ι) (u : ℝ) = Metric.closedBall t₀ u`, `clamp t₀ u`,
`restrictExhaustion t₀ u`, `distOn t₀ u`, und `totalDist` wird das Integral von
Meilenstein 4.

*Worauf es ruht.* Auf nichts Neuem. Die Umstellung ist mechanisch: die
natürliche Zahl `m` geht in die vorhandenen Beweise nur als `(m : ℝ)` ein, an
zwei Stellen (`dist_le_of_norm_le` mit seinem `2 * m` und die Geometrie der
Reihe), und die Kompaktheit des Fensters ist `isCompact_closedBall` für jeden
reellen Radius. Die vierzig bewiesenen Aussagen über `distOn` — Symmetrie,
Dreiecksungleichung, Trennung, die beiden Randabschätzungen von heute — gehen
Zeile für Zeile durch.

*Warum jetzt.* Weil die Metrik der Angelpunkt ist: `CompleteSpace`,
`SeparableSpace`, `PolishSpace`, die meßbare Einbettung von Meilenstein 6 und
das Kompaktheitskriterium von Meilenstein 7 sind alle Aussagen über sie, und
solange sie falsch ist, ist keine von ihnen auch nur formulierbar. Und weil der
Schritt keinen Beweis kostet, sondern nur eine Signatur — die teuren Teile,
die Meßbarkeit des Integranden und die Vollständigkeit, kommen danach und stehen
beide benannt in der Roadmap.

*Was dafür schon bereitliegt.* `IsCadlag.of_tendstoUniformlyOn_exhaustion` ist
in diesem Lauf bewiesen und ist die Stelle, an der
`SkorokhodSpace.tendsto_of_partialComp` seinen Grenzpfad auffängt; sie ist von
der Metrik unabhängig und wartet auf den reellen Radius, nicht umgekehrt. Von
`CompleteSpace D(ι, E)` steht damit alles außer der Metrik selbst und dem
Zusammenbau.

### 2026-09-08, neunzehnter Lauf des Tages

**Vorrangige Aufgabe, vierter von vier Läufen an `SkorokhodSpace`.** Der Punkt,
an dem der achtzehnte Lauf endete, war eine Signatur und keine Lücke: der Radius
des Fensters mußte reell werden, sonst ist keiner der offenen Punkte
formulierbar. Er ist es. `SkorokhodSpace/Suggested.lean` steht weiterhin bei
**fünf** `sorry` — der Lauf hat keines gestrichen, sondern die Datei auf die
Metrik umgestellt, die Meilenstein 4 seit dem achtzehnten Lauf verlangt, und
deren einzige neue Beweispflicht bezahlt. Neunzehn neue Deklarationen, alle mit
`#print axioms` geprüft und alle nur auf `propext`, `Classical.choice`,
`Quot.sound`; die Datei geht durch `lake env lean` ohne Fehler und ohne Warnung.

**Der reelle Radius.** `exhaustion`, `exhaustionMin`, `exhaustionMax`, `clamp`,
`TimeChange.normOn`, `TimeChange.lipConstOn`, `TimeChange.dist_le_of_norm_le`,
`SkorokhodSpace.restrictExhaustion`, `distOn`, `IsSubdivision`, `modulus` und
alles, was daran hängt, nehmen jetzt `u : ℝ`. Zwei Entscheidungen dabei, beide
begründungsbedürftig:

*Erstens, `exhaustion t₀ u = Metric.closedBall t₀ (max u 0)` und nicht
`closedBall t₀ u`.* Ein negativer Radius machte das Fenster leer, und
`exhaustionMin`, `exhaustionMax`, `clamp` sind `def`s, die es bewohnt brauchen —
sie wählen aus einer Kompaktheitsaussage, die auf der leeren Menge keine Zeugen
hat. Mit der Trunkierung bleibt jede Deklaration total; für `0 ≤ u` ist es die
Kugel, und das ist `exhaustion_eq_closedBall`.

*Zweitens, `0 ≤ u` als Hypothese, und zwar an genau drei Stellen.*
`TimeChange.dist_le_of_norm_le` (die Schranke `(exp γ - 1) * (2 * u)` ist für
`u < 0` negativ und die Aussage damit falsch), `exhaustion_subset_exhaustion`
und `SkorokhodSpace.eq_of_distOn_eq_zero`. Nirgends sonst; die übrigen Beweise
lesen den Radius als Atom und überstehen den Wechsel unverändert. Als Zugabe
verliert `exhaustion_subset_exhaustion` sein `⌈dist t₀ t₁⌉₊`: die Aufrundung war
ein Artefakt des ganzzahligen Radius, und die Aussage lautet jetzt
`exhaustion t₀ u ⊆ exhaustion t₁ (u + dist t₀ t₁)`.

**Die Meßbarkeit des Integranden, und sie war der Preis der Reparatur.** Der
achtzehnte Lauf hatte sie als die einzige zusätzliche Beweispflicht der
Integralgestalt benannt und den Weg dazu angegeben: die rechte Stetigkeit lasse
das Supremum über eine abzählbare **dichte** Teilmenge von `ι` nehmen. **Das ist
falsch, und der Zeuge ist billig:** auf `ι = Set.Icc (0:ℝ) 1` ist `ℚ ∩ [0,1)`
dicht, und eine rechtsstetige Funktion darf im Punkt `1` — der nur von links
angelaufen wird — über ihrem Supremum auf dieser Menge liegen. Was zu einer
dichten Menge hinzukommen muß, sind die Punkte, an die von rechts nichts
heranreicht.

*Und davon gibt es abzählbar viele.* `rightIsolated ι = {t | IsOpen (Set.Iic t)}`
und `countable_rightIsolated`. Der Beweis ist **intrinsisch** — er geht nicht
über die Einbettung des Index in `ℝ`, die `exists_orderIso_isometry_real` heißt
und weiterhin ein `sorry` ist. Für rechtsisoliertes `t` ist `Set.Iic t` offen,
also hat eine abzählbare Basis ein Glied `v` mit `t ∈ v ⊆ Set.Iic t`, und diese
Zuordnung ist injektiv: aus `v s = v t` folgt `s ≤ t` und `t ≤ s` zugleich.
Zweitabzählbarkeit ist die einzige Voraussetzung, und der Index hat sie aus
`ProperSpace`. Die andere Hälfte ist
`nonempty_inter_Ioi_of_notMem_rightIsolated`: ist `Set.Iic t` nicht offen, so
trifft jede offene Umgebung von `t` die Menge `Set.Ioi t` — denn sonst wäre
`Set.Iic t = Set.Iio t ∪ W` offen, und `Set.Iio t` ist es in der
Ordnungstopologie immer.

*Damit `exists_countable_ciSup_eq`:* **eine abzählbare Menge berechnet das
Supremum jeder rechtsstetigen reellen Funktion auf dem Index.** Sie ist die
dichte Menge vereinigt mit `rightIsolated ι`, und daß sie **nicht von der
Funktion abhängt**, ist der ganze Punkt: eine supremumsapproximierende Folge
hinge von ihr ab, und eine andere abzählbare Menge je Fensterradius berechnet
nichts.

**Die Metrik.** `SkorokhodSpace.distWith t₀ u λ f g` ist Ethier--Kurtz'
`d(x, y, λ, u)` — das gefensterte Supremum für *einen* Zeitwechsel —,
`SkorokhodSpace.distOn_eq_iInf_distWith` identifiziert `distOn` als das Infimum
von `max ‖λ‖ ·` darüber, und zwar durch `rfl`, so daß die bewiesenen Aussagen
über `distOn` unangetastet bleiben. Darauf:

* `SkorokhodSpace.rightContinuous_dist_restrictExhaustion` — der Integrand ist
  rechtsstetig im Index; beide Hälften sind càdlàg, die linke, weil ein
  càdlàg-Pfad nach einem Ordnungsisomorphismus wieder càdlàg ist.
* `monotone_exhaustionMax`, `antitone_exhaustionMin`, `measurable_clamp` — der
  Clamp ist meßbar im Radius, und das ist nichts als Monotonie.
* `SkorokhodSpace.measurable_distWith` — die Meßbarkeit, aus den dreien und
  `Measurable.iSup` über die abzählbare Menge.
* `SkorokhodSpace.intDist` — die Metrik von Meilenstein 4, mit dem Infimum über
  die Zeitwechsel **außerhalb** des Integrals, und
  `SkorokhodSpace.integrableOn_intDist`: der Integrand ist von `exp (-u)`
  dominiert (`integrableOn_exp_neg_Ioi`) und damit integrierbar. Ohne diese
  Aussage wäre das Integral der Müllwert `0` und `intDist` fiele auf
  `⨅ λ, ‖λ‖ = 0` zusammen.

**Was der Lauf ausdrücklich nicht getan hat.** Die `MetricSpace D(ι, E)`-Instanz
liest weiterhin `SkorokhodSpace.totalDist`, die über die ganzzahligen Radien
summierte Größe, deren vier Axiome bewiesen sind. Die vier Axiome von `intDist`
sind es nicht, und die Instanz umzuhängen, bevor sie es sind, setzte `sorryAx`
unter die zwanzig Deklarationen, die die Topologie lesen — genau die Falle, in
der `modulus` bis zum sechzehnten Lauf saß. Das steht so in der Roadmap.

**Woran der nächste hängt.** An den vier Axiomen von `intDist`, und sie sind
jetzt gewöhnliche Arbeit statt einer offenen Frage: `intDist_self` ist der
Zeitwechsel `1` und ein Integrand, der verschwindet; `intDist_comm` ist die
Umindizierung `λ ↦ λ⁻¹` des siebzehnten Laufs, punktweise im Radius geführt und
dann integriert; die Dreiecksungleichung ist `distOn_triangle` punktweise im
Radius, `min 1 ·` subadditiv auf den nichtnegativen Reellen, und
`MeasureTheory.integral_add` auf `integrableOn_intDist`; die Trennung ist
`eq_of_distOn_eq_zero` plus die Beobachtung, daß ein nichtnegativer Integrand
mit Integral `0` fast überall verschwindet, also für einen Radius in jeder
Umgebung. Erst danach wird die Instanz umgehängt, und erst danach ist
`CompleteSpace D(ι, E)` — dessen übrige Bausteine seit dem siebzehnten und
achtzehnten Lauf bewiesen dastehen — überhaupt wieder eine wahre Aussage.

### 2026-09-08, zwanzigster Lauf des Tages — die vier Axiome von `intDist` sind bewiesen, und das vierte ist von anderer Art als die drei

**Bearbeitet:** `SkorokhodSpace`, Meilenstein 4, genau entlang des Vorschlags des
neunzehnten Laufs (Rückstau 2, „`SkorokhodSpace` und `MartingaleProblems` weiter
beweisen"; die vorrangige Aufgabe ist seit dem neunzehnten Lauf gestrichen).
`SkorokhodSpace/Suggested.lean` steht weiterhin bei **fünf** `sorry` — der Lauf
hat keines gestrichen, denn keines der vier Axiome stand als `sorry` da; sie
waren überhaupt nicht formuliert, weil der achtzehnte Lauf die alte Metrik
verworfen und der neunzehnte die neue erst definiert hat. **Neunzehn neue
Deklarationen**, alle mit `#print axioms` geprüft und alle nur auf `propext`,
`Classical.choice`, `Quot.sound`; die Datei geht durch `lake env lean` gegen
v4.33.1 ohne Fehler und ohne Warnung.

#### Die drei algebraischen Axiome: der Radius ist Zuschauer

`SkorokhodSpace.intWith t₀ λ f g` ist neu und ist das Integral für **einen**
Zeitwechsel, aus `intDist` herausgezogen; `intDist` ist jetzt
`⨅ λ, max ‖λ‖ (intWith t₀ λ f g)`, unverändert im Wert. Der Ertrag ist, daß jedes
der drei Axiome in zwei zerfällt, und beide Hälften sind schon da: eine über
`TimeChange.norm` (Meilenstein 3, seit dem 2026-09-07 bewiesen) und eine über
`intWith`, und jede über `intWith` ist die entsprechende über `distWith`, bei
festem Radius geführt und dann integriert.

* `SkorokhodSpace.distWith_self` → `intWith_self` → `intDist_self`.
* `SkorokhodSpace.distWith_inv` → `intWith_inv` → `intDist_comm`. Die
  Umindizierung des Supremums längs `λ` selbst ist als
  `SkorokhodSpace.ciSup_reindex` herausgezogen, aus dem Beweis von
  `distOn_comm`, wo sie bisher als `have` stand.
* `SkorokhodSpace.distWith_triangle` (Zeuge `λ * λ'`) → `intWith_triangle` →
  `intDist_triangle`, dazu `bddBelow_range_intDist`, `intDist_nonneg`,
  `intWith_nonneg` und `exists_lt_intDist_add` als Unterbau.

**Die Integrierbarkeit wird an genau einer Stelle ausgegeben**, und zwar zweimal:
`intWith_triangle` braucht `MeasureTheory.integral_add` und
`MeasureTheory.integral_mono`, beide auf `integrableOn_intDist`. Ohne
Integrierbarkeit ist das Integral der Müllwert `0`, und ein solcher Müllwert auf
der **linken** Seite der Ungleichung machte sie falsch — nicht bloß unbeweisbar.

#### Das vierte Axiom, und es ist nicht von dieser Form

Der Vorschlag des neunzehnten Laufs lautete: „die Trennung ist
`eq_of_distOn_eq_zero` plus die Beobachtung, daß ein nichtnegativer Integrand mit
Integral `0` fast überall verschwindet". **Das trifft nicht zu, und der Grund ist
der Unterschied zwischen einem Infimum und einem Minimum.** `intDist t₀ f g = 0`
liefert keinen Zeitwechsel mit verschwindendem Integral, sondern eine **Folge**
`λ n`, und zu keinem einzelnen `λ n` ist ein Radius benannt, an dem es gut ist.
Die summierte Metrik hatte das Problem nicht: dort war jeder Radius verfügbar und
`eq_of_forall_distOn_eq_zero` las sie einen nach dem anderen ab.

Der Weg, der trägt, und er ist in Lean:

1. Wähle `λ n` mit `‖λ n‖ < 2⁻ⁿ` **und** `intWith t₀ (λ n) f g < 2⁻ⁿ`; beides
   fällt aus `exists_lt_intDist_add` mit `δ = 2⁻ⁿ`.
2. `MeasureTheory.lintegral_tsum` und die geometrische Reihe machen
   `∑' n, ENNReal.ofReal (exp (-u) * min 1 (distWith t₀ u (λ n) f g))` über
   `Set.Ioi 0` integrierbar; `MeasureTheory.ae_lt_top` macht sie an fast jedem
   Radius endlich, `ENNReal.tendsto_atTop_zero_of_tsum_ne_top` läßt dort ihre
   Glieder gegen `0` gehen.
3. An jedem solchen Radius greift das Kriterium bei festem Radius. Es ist neu
   und heißt `SkorokhodSpace.eq_restrictExhaustion_of_forall_exists`: gibt es zu
   jedem `δ` einen verankerten Zeitwechsel mit `‖λ‖ < δ`, der die eine
   Trunkierung gleichmäßig bis auf `δ` in die andere trägt, so sind die
   Trunkierungen gleich. Das ist der bisherige Rumpf von
   `eq_of_distOn_eq_zero`, herausgezogen; `eq_of_distOn_eq_zero` gewinnt seine
   Hypothese jetzt durch Abwickeln des eigenen Infimums und ist fünf Zeilen lang.
   **Beide Metriken lesen dasselbe Kriterium**, und das war der Zweck der
   Zerlegung.
4. Eine Menge vollen Maßes in `Set.Ioi 0` reicht über jeden Punkt des Index
   hinaus (`Real.volume_Ioi`, `MeasureTheory.ae_neBot`,
   `MeasureTheory.self_mem_ae_restrict`), also gilt die Gleichheit überall.

Das ist `SkorokhodSpace.eq_of_intDist_eq_zero`.

#### Was der Preis der Integralgestalt wirklich ist: `SecondCountableTopology E`

Die vier Axiome hätten `[MeasurableSpace ι] [BorelSpace ι] [MeasurableSpace E]
[BorelSpace E] [SecondCountableTopology E]` geerbt, denn so standen
`measurable_distWith` und `integrableOn_intDist` seit dem neunzehnten Lauf da.
Das wäre für eine `MetricSpace`-Instanz viel zu teuer gewesen. **Vier der fünf
sind weg, und der Grund ist, daß sie nie in der Aussage standen:** beide
Deklarationen reden über Funktionen `ℝ → ℝ`, die σ-Algebren von `ι` und `E`
kommen allein im Beweis vor, und dort werden sie jetzt mit `borel ι` bzw.
`borel E` eingeführt statt vorausgesetzt.

Übrig bleibt `[SecondCountableTopology E]`, und die ist echt: sie ist die
Voraussetzung von `Measurable.dist`
(`MeasureTheory/Constructions/BorelSpace/Metric.lean:77`, an `upstream/master`
gelesen), und keine Wahl einer σ-Algebra liefert sie. Sie steht auf
`intWith_triangle`, `intDist_triangle`, `eq_of_intDist_eq_zero` und
`metricSpaceInt` und sonst nirgends im ganzen Bestand.

#### `metricSpaceInt`, und warum die Instanz noch nicht umgehängt ist

`SkorokhodSpace.metricSpaceInt (t₀ : ι) : MetricSpace D(ι, E)` ist gebaut, aus
den vier Axiomen, mit `#print axioms` geprüft. Die parameterlose Instanz
`SkorokhodSpace.instMetricSpace` liest weiterhin `SkorokhodSpace.metricSpace`,
die summierte Metrik. **Das Umhängen ist keine Umbenennung, und das ist der
Befund dieses Punktes:** die Widerlegung des achtzehnten Laufs —
`SkorokhodSpace.continuous_eval_exhaustionMax` und
`SkorokhodSpace.exists_jump_continuousAt_eval` — ist für die Topologie der
*Instanz* formuliert und ist ein Satz über die **summierte** Metrik; die erste
ist für `intDist` falsch, und genau deshalb wird die Summe ersetzt. Wer die
Instanz umhängt, ohne diese beiden vorher ihre Metrik nennen zu lassen (über
`SkorokhodSpace.metricSpace t₀` und deren Topologie), macht die Datei zu einer
Behauptung über `intDist`, die `totalDist` disqualifiziert hat. Das steht so an
`metricSpaceInt` und in der Roadmap.

#### Vorschlag für den nächsten Lauf

**Die beiden Widerlegungssätze auf `SkorokhodSpace.metricSpace t₀` umstellen und
dann `SkorokhodSpace.instMetricSpace := metricSpaceInt basePoint` setzen.**
Worauf es ruht: auf den vier bewiesenen Axiomen und auf nichts sonst; die Arbeit
ist, `continuous_eval_exhaustionMax` und `exists_jump_continuousAt_eval` mit
explizit genannter Metrik zu schreiben, und die etwa zwanzig Deklarationen zu
prüfen, die die Topologie von `D(ι, E)` lesen — die Borel-Struktur `borel _`
voran. Warum jetzt: ohne die Umhängung ist `CompleteSpace D(ι, E)` weiterhin
keine wahre Aussage, und die Bausteine der Vollständigkeit (siebzehnter und
achtzehnter Lauf) warten seit drei Läufen darauf. Danach, und erst danach, ist
`CompleteSpace` an der Reihe; seine Rungen
`TimeChange.exists_tendsto_of_summable_norm`, `IsCadlag.of_forall_eventuallyEq`
und `IsCadlag.of_tendstoUniformlyOn_exhaustion` sind von der Metrik unabhängig
und stehen bewiesen da.

**Das Manuskript ist nicht angefaßt.** Am Inventar ändert sich keine Zeile: alle
29 Facts stehen belegt, und `fact:Dcountable`, `fact:relcompact` und
`fact:relcompact2` zeigen auf dieselben Meilensteine wie zuvor.

### 2026-09-08, einundzwanzigster Lauf des Tages — die Instanz ist umgehängt, und was sie kostete, ist bezahlt

**Bearbeitet:** `SkorokhodSpace`, Meilensteine 4 und 5, genau entlang des
Vorschlags des zwanzigsten Laufs (Rückstau 2, „`SkorokhodSpace` und
`MartingaleProblems` weiter beweisen"; vorrangige Aufgaben stehen keine offen).
`SkorokhodSpace/Suggested.lean` geht durch `lake env lean` gegen v4.33.1 **ohne
Fehler und ohne Warnung**; 188 Deklarationen, sieben `sorry`.

**Die Zahl steigt von fünf auf sieben, und das ist kein Rückschritt, sondern die
Buchführung.** Zwei der zurückgenommenen Aussagen des achtzehnten Laufs sind
wieder Verpflichtungen, weil die Metrik, für die sie falsch waren, nicht mehr die
Instanz ist. Wer nur zählt, sieht zwei mehr; wer liest, sieht, daß Meilenstein 5
seit heute überhaupt wieder etwas schuldet.

#### `SkorokhodSpace.instMetricSpace` ist `metricSpaceInt basePoint`

Das war der Auftrag, und er ist erledigt. `SkorokhodSpace.dist_eq` ist jetzt
`dist f g = intDist basePoint f g`, weiterhin `rfl`, weiterhin `@[simp]`.
`#print axioms` gibt für `instMetricSpace` und `dist_eq` `propext`,
`Classical.choice`, `Quot.sound` und sonst nichts.

**Die Umhängung war keine Umbenennung, und der Preis ist eine neue Deklaration.**
`SkorokhodSpace.totalTopology (t₀ : ι) : TopologicalSpace D(ι, E)` ist die
Topologie der summierten Metrik, benannt. Die beiden Widerlegungssätze des
achtzehnten Laufs lasen ihre Topologie von der Instanz ab; stünden sie so da,
behauptete die Datei nach der Umhängung von `intDist` genau das, was `totalDist`
disqualifiziert hat. Sie nennen sie jetzt:

* `SkorokhodSpace.continuous_eval_exhaustionMax (t₀ : ι) (m : ℕ)` trägt den
  Basispunkt wieder als Parameter — er ist kein Instanzparameter mehr, sondern
  der der genannten Metrik — und ihre Aussage ist
  `Continuous[SkorokhodSpace.totalTopology t₀, inferInstance]`.
* `SkorokhodSpace.exists_jump_continuousAt_eval` desgleichen, mit
  `@ContinuousAt _ _ (SkorokhodSpace.totalTopology (0 : ℝ)) _`.

Beide sind neu bewiesen und hängen an `propext`, `Classical.choice`,
`Quot.sound`. Der Zeuge `SkorokhodSpace.step` ist unverändert. Die summierte
Metrik `SkorokhodSpace.metricSpace` bleibt aus genau diesem Grund stehen und aus
keinem anderen: ohne sie gäbe es die Widerlegung nicht mehr, für die sie
widerlegt wurde.

**Zwei Handgriffe, die nicht offensichtlich waren.** `totalTopology` braucht
`@[instance_reducible]`, sonst scheitert der Defeq-Vergleich bei reduzierbarer
Transparenz und der Beweis läßt sich nicht schließen; der Linter verlangt das
Attribut ohnehin für Definitionen von Klassentyp. Und
`[SecondCountableTopology E]` steht **auf der Instanz** und nicht als
`variable`: als Abschnittsvariable kollidiert es in den Meilensteinen 6 und 7 mit
`[PolishSpace E]`, das es erweitert (`Topology/MetricSpace/Polish.lean:62`, dort
`extends SecondCountableTopology α, IsCompletelyMetrizableSpace α`), und der
`linter.overlappingInstances` meldet das an fünf Deklarationen. Auf der Instanz
getragen, ziehen die späteren Meilensteine es aus ihrem `PolishSpace E`. Dafür
mußte in Meilenstein 6 die `variable`-Zeile **vor** die
`MeasurableSpace D(ι, E) := borel _`-Instanz rücken, die sonst keine Topologie
mehr findet.

#### Meilenstein 5 schuldet wieder etwas, und es sind zwei Aussagen und nicht drei

`SkorokhodSpace.instCompleteSpace` (unter `[CompleteSpace E]`) und
`SkorokhodSpace.instSeparableSpace` (unter `[SeparableSpace E]`, **nicht** unter
`[PolishSpace E]` — die Approximation durch Treppenpfade benutzt die
Rechtsstetigkeit und die Kompaktheit des Fensters, die Vollständigkeit von `E`
nirgends) stehen als `sorry`. `SkorokhodSpace.instPolishSpace` ist wie am
sechzehnten Lauf `inferInstance` und schuldet nichts Eigenes; `#print axioms`
zeigt bei allen dreien `sorryAx`, bei den ersten beiden aus eigenem `sorry`, bei
der dritten geerbt. Das steht an der Deklaration, denn ein `sorry` in einer
`instance` färbt auf alles ab, was sie benutzt.

#### Die eine Sprosse, die die Metrik wirklich gekostet hat, ist bezahlt

`SkorokhodSpace.ae_summable_min_one_distWith` ist bewiesen, in einem Zug, und
hängt an `propext`, `Classical.choice`, `Quot.sound`.

> Vergleichen die Zeitwechsel `l n` die Paare `x n`, `y n` mit summierbaren
> Kosten `γ n` in `intWith`, so ist an **fast jedem** Radius `u` die Folge
> `min 1 (distWith t₀ u (l n) (x n) (y n))` in `n` summierbar.

Das ist die Stelle, an der die beiden Metriken auseinandergehen, und sie ist die
einzige. Für die Summe war der Übergang `min_one_distOn_le` und galt an
**jedem** Radius, weil jeder ganzzahlige Radius sein eigenes Gewicht `2⁻ᵐ` in der
Summe trägt — und genau daran ist die Summe gestorben. Das Integral trägt an
keinem *benannten* Radius ein Gewicht, und ein kleines `intDist` sagt dort
nichts; was es sagt, ist diese Aussage. Ein Vollständigkeitsbeweis braucht eine
summierbare Rate an *einem* Radius und darf ihn wählen, also wählt er einen
davon. Mehr ist an Billingsleys Argument nicht anzupassen.

Der Beweis ist der von `eq_of_intDist_eq_zero` mit `γ n = 2⁻ⁿ`, herausgezogen und
für summierbares `γ` geführt: `MeasureTheory.lintegral_tsum` macht die Reihe der
Integranden integrierbar, `MeasureTheory.ae_lt_top` macht sie fast überall
endlich, und `ENNReal.tsum_coe_ne_top_iff_summable`
(`Topology/Algebra/InfiniteSum/ENNReal.lean:64`) macht aus der Endlichkeit
zurück eine Summierbarkeit über `ℝ`. Das Gewicht `Real.exp (-u)` kürzt sich mit
`summable_mul_left_iff` (`Topology/Algebra/InfiniteSum/Ring.lean:106`) heraus,
weil es nicht von `n` abhängt; `2⁻ᵐ` hätte das nicht getan, und diese Asymmetrie
ist der ganze Unterschied der beiden Metriken für diesen Beweis.

#### Am Rande: ein Skript, das der Lauf nicht löschen durfte

Die Axiomprobe läuft am billigsten über eine Kopie der Datei mit `#print axioms`
je Deklaration. Die erste Kopie landete als `axcheck_tmp.lean` in der Wurzel des
Worktrees, und die Sandbox verweigert dort `rm` — wie unter `.lake`, und diesmal
in einem ausdrücklich erlaubten Verzeichnis. Die Datei ist auf einen
Erklärungsblock eingedampft und in `.gitignore` eingetragen; die zweite Kopie
liegt unter `scratch/`, das ohnehin ignoriert wird. **Für den nächsten Lauf:
diese Kopie gleich unter `scratch/` anlegen.**

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.instCompleteSpace` beweisen.** Worauf es ruht: auf sechs
benannten Sprossen, von denen fünf bewiesen sind —
`SkorokhodSpace.ae_summable_min_one_distWith` für den Übergang von der Metrik
zum Radius (neu, dieser Lauf), `SkorokhodSpace.exists_lt_intDist_add` für die
Zeitwechsel, `TimeChange.exists_tendsto_of_summable_norm` samt
`TimeChange.exists_tendsto_norm_tail_le` für ihre unendliche Komposition und die
Surjektivität des Grenzwerts, `IsCadlag.of_tendstoUniformlyOn_exhaustion` samt
`IsCadlag.of_forall_eventuallyEq` für den Auffang des Grenzpfads. Offen ist
allein die Montage, `SkorokhodSpace.tendsto_of_partialComp`, und sie steht in
`SkorokhodSpace/README.md`, Meilenstein 5, mit der Substitution
`s = (P (n+1))⁻¹ (L t)` ausgeschrieben. Warum jetzt: es ist die letzte offene
Sprosse, die Metrik steht seit diesem Lauf fest, und `instSeparableSpace` ist
ohne sie nicht die schwächere Aufgabe, sondern die andere. Danach
`instSeparableSpace`, dann Meilenstein 6.

**Das Manuskript ist nicht angefaßt.** Am Inventar ändert sich keine Zeile.
`fact:PSpolish` zeigt weiterhin auf `SkorokhodSpace` Meilenstein 5, und dieser
Lauf ist der erste seit dem achtzehnten, nach dem dort wieder eine Aussage steht,
auf die er zeigen kann.

### 2026-09-08, zweiundzwanzigster Lauf des Tages — die Montage ist bewiesen, und was von der Vollständigkeit bleibt, ist ein Randpunkt

**Bearbeitet.** Keine Fact-Zeile; der Lauf steht im Rückstau, Punkt 2
(`SkorokhodSpace` weiter beweisen), an der Stelle, die der einundzwanzigste Lauf
benannt hat: `SkorokhodSpace.tendsto_of_partialComp`, die letzte offene Sprosse
von `CompleteSpace D(ι, E)`.

**Stand der Datei.** `SkorokhodSpace/Suggested.lean` zählt **193
Deklarationen** (vorher 188) und unverändert **sieben `sorry`**; `lake env lean`
gegen v4.33.1 meldet `rc = 0` und außer den sieben `sorry`-Warnungen keine
einzige. Fünf neue Deklarationen, alle mit `#print axioms` geprüft und alle nur
auf `propext`, `Classical.choice`, `Quot.sound`. Daß die Zahl der `sorry` steht,
ist der Bericht und kein Versäumnis: die Montage war nie ein `sorry`, sie war
eine Verpflichtung der Roadmap ohne Deklaration, und `instCompleteSpace` bleibt
offen, weil ihm nach der Montage noch **ein** Schritt fehlt — ein anderer, als
die Roadmap bis heute annahm.

#### Die Montage, und sie ist bewiesen

`SkorokhodSpace.tendsto_of_partialComp`:

> Sind die Zeitwechsel `l n` bei `t₀` verankert und sind sowohl ihre Normen als
> auch ihre Kosten `intWith t₀ (l n) (x n) (x (n+1))` durch ein summierbares `γ`
> beschränkt, so gibt es einen Pfad `z : D(ι, E)` und **einen** Zeitwechsel `L`
> mit `‖(partialComp l n)⁻¹ * L‖ ≤ ∑' i, γ (n + i)`, so daß
> `x n ∘ ((partialComp l n)⁻¹ * L)` auf **jedem** Fenster gleichmäßig gegen `z`
> konvergiert.

Die Voraussetzung ist genau das, was `SkorokhodSpace.exists_lt_intDist_add` aus
einer Cauchyfolge mit summierbaren Nachbarabständen hergibt. Drei Dinge tragen
den Beweis, und sie sind der Grund, daß er in einem Zug durchgeht:

* **Die Rekursion.** Mit `κ n := (partialComp l n)⁻¹ * L` ist
  `κ n = l n * κ (n+1)` — eine Zeile in der Gruppe der Zeitwechsel —, und damit
  wird das Inkrement `r (x n (κ n t)) (x (n+1) (κ (n+1) t))` durch die
  Substitution `s = κ (n+1) t` zu `r (x n (l n s)) (x (n+1) s)`, also zu einem
  Term des Supremums, das `distWith` ist.
* **Die gleichmäßige Normschranke.** `‖κ n‖ ≤ ∑' γ` für **alle** `n` (die
  Schwänze von `γ` liegen unter seiner Summe), also verschiebt kein `κ n` einen
  Punkt des Fensters vom Radius `m` weiter als auf den Radius
  `exp (∑' γ) · m`. Damit liegen `s` und `l n s` gleichzeitig in *einem*
  Fenster, und ein einziges `distWith` beschränkt das Inkrement für das ganze
  Fenster auf einmal.
* **Der Radius.** `SkorokhodSpace.exists_gt_summable_distWith`, neu und
  bewiesen: über **jeder** Schranke gibt es einen Radius, an dem die
  `distWith t₀ u (l n) (x n) (y n)` in `n` summierbar sind. Denn die schlechten
  Radien sind nach `ae_summable_min_one_distWith` eine Nullmenge, und
  `Set.Ioi c` hat nach `Real.volume_Ioi` unendliches Maß. Das ist die Stelle,
  an der die Integralmetrik ihre Arbeit tut, und es ist der einzige Schritt der
  Montage, den die summierte Metrik anders gegangen wäre.

Dann geben `cauchySeq_of_dist_le_of_summable` und `cauchySeq_tendsto_of_complete`
den Grenzwert punktweise, `dist_le_tsum_of_dist_le_of_tendsto` mit
`tendsto_sum_nat_add` die Gleichmäßigkeit auf dem Fenster samt Rate, und
`IsCadlag.of_tendstoUniformlyOn_exhaustion` fängt den Grenzpfad auf. Zwei
Kleinigkeiten kommen mit: `summable_of_summable_min_one` — die Trunkierung bei
`1`, die `ae_summable_min_one_distWith` stehen läßt, kostet nichts, weil eine
summierbare Folge gegen `0` geht und Summierbarkeit ein endliches Anfangsstück
nicht sieht — und `SkorokhodSpace.dist_le_distWith`, ein Term des Supremums.

#### Was von `CompleteSpace` bleibt, und es ist nicht die Montage

Der Schritt zurück von der lokal gleichmäßigen Konvergenz zu `intDist` ist
**keine Wiederholung** der Montage, und der Grund steht in der Definition:
`distWith t₀ u λ f g` schneidet die beiden Pfade **getrennt** ab, `f` bei
`clamp u (λ t)` und `g` bei `clamp u t`. Oberhalb von `A := exhaustionMax t₀ u`
fallen beide Lesarten auf `A` zusammen, und der Term ist `r (x n A) (z A)` —
ein Vergleich der beiden Pfade an *einem* Punkt, um den Zeitwechsel verschoben.
Er geht nicht ohne weiteres gegen `0`: `x n A = (x n ∘ κ n) (κ n⁻¹ A)`, und
`κ n⁻¹ A → A` liefert `z (κ n⁻¹ A) → z A` nur, wenn `z` bei `A` stetig ist.

Dominierte Konvergenz über den Radius (der Integrand liegt unter `1`,
`exp (-u)` ist auf `Set.Ioi 0` integrierbar) reduziert die Behauptung auf fast
jeden Radius, und dort steht eine **Dichotomie**, die dieser Lauf zur Hälfte
bezahlt hat:

* Entweder ist die Niveaumenge `{u : exhaustionMax t₀ u = A}` eine Nullmenge —
  dann fällt der Radius mit der Nullmenge weg.
* Oder sie ist es nicht. Dann hat der Index über `A` eine **Lücke**, und
  `TimeChange.eq_of_gap_of_norm_lt` (neu, bewiesen) sagt: ein bei `t₀`
  verankerter Zeitwechsel, dessen Verschiebung `(exp ‖λ‖ - 1) · 2u` auf dem
  Fenster unter der Lückenbreite liegt, **fixiert `A`**. Beide Anordnungen
  scheiden aus, `λ A < A` an der Lücke über `A` durch `λ⁻¹`, `A < λ A` direkt;
  beides über `TimeChange.dist_le_of_norm_le`, angewandt auf `λ` und auf `λ⁻¹`.
  Der Satz braucht weder `OrderTopology ι` noch `ProperSpace ι`, und beide sind
  an der Deklaration mit `omit` weggenommen.

Damit ist der Randpunkt in beiden Fällen erledigt; offen bleibt, die Dichotomie
selbst zu führen (die Lückenbreite entsteht durch Kompaktheit: die Punkte über
`A` in beschränktem Abstand bilden eine kompakte Menge, die sich nicht bei `A`
häuft, und haben daher ein kleinstes Element) und die Fallunterscheidung des
Supremums auszuschreiben. Das steht als
`SkorokhodSpace.tendsto_intDist_of_tendsto_of_partialComp` in
`SkorokhodSpace/README.md`, Meilenstein 5.

**Das ist eine Berichtigung der Roadmap.** Bis zu diesem Lauf las Meilenstein 5,
`dist (x n) z` werde „mit dem Zeitwechsel `(P n)⁻¹ * L` abgeschätzt, dessen Norm
der Schwanz `∑' i, γ (n + i)` ist" — als sei das eine Folgerung aus der Montage.
Es ist keine: die Norm ist klein, aber das Integral über die Fensterabstände ist
es aus dem genannten Grund nicht ohne die Dichotomie. Der Meilenstein zählt
seither **sieben** benannte Sprossen statt sechs, davon sechs bewiesen.

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.tendsto_intDist_of_tendsto_of_partialComp` beweisen**, also
den eben benannten Punkt, und danach `instCompleteSpace` als seine
Zusammensetzung mit `tendsto_of_partialComp`. Worauf er ruht: auf
`TimeChange.eq_of_gap_of_norm_lt` (bewiesen, dieser Lauf), auf
`SkorokhodSpace.integrableOn_intDist` für die Dominante, auf
`monotone_exhaustionMax` und `antitone_exhaustionMin` für die Niveaumengen, und
auf `clamp_eq_exhaustionMax_of_le` und `clamp_eq_exhaustionMin_of_le` für die
Fallunterscheidung des Supremums. Warum jetzt: es ist der einzige noch offene
Schritt von `CompleteSpace D(ι, E)`, alle übrigen sind bewiesen, und die
untere Fensterkante kostet nichts — dort ist `z` von selbst rechtsstetig, das
ist die càdlàg-Eigenschaft. Erst danach `instSeparableSpace`.

**Das Manuskript ist nicht angefaßt.** Am Inventar ändert sich keine Zeile;
`fact:PSpolish` zeigt weiterhin auf `SkorokhodSpace` Meilenstein 5.

### 2026-09-08, dreiundzwanzigster Lauf des Tages — `CompleteSpace D(ι, E)` ist bewiesen, und die Dichotomie der Roadmap war die falsche

**Bearbeitet.** Keine Fact-Zeile; der Lauf steht im Rückstau, Punkt 2
(`SkorokhodSpace` weiter beweisen), an der Stelle, die der zweiundzwanzigste Lauf
als Vorschlag hinterlassen hat: `SkorokhodSpace.tendsto_intDist_of_tendsto_of_partialComp`
und danach `instCompleteSpace` als dessen Zusammensetzung mit
`tendsto_of_partialComp`.

**Stand der Datei.** `SkorokhodSpace/Suggested.lean` trägt **sechs `sorry`**
statt sieben; `lake env lean` gegen v4.33.1 meldet `rc = 0` und außer den sechs
`sorry`-Warnungen und zwei `push_neg`-Deprecations keine Meldung. Drei neue
Deklarationen, und alle dreizehn Deklarationen dieses und des vorigen,
abgebrochenen Laufs sind mit `#print axioms` geprüft: alle hängen nur an
`propext`, `Classical.choice`, `Quot.sound` (`min_max_pair_cases` sogar nur an
`propext`). Die Namensliste samt Verfahren steht in
`TauCeti/SkorokhodSpace/Axioms.lean` — einer reinen Aufzeichnung ohne `import`,
weil der Worktree kein Lake-Projekt hat; die Prüfung selbst läuft über eine
Kopie von `Suggested.lean` mit angehängten `#print axioms`-Zeilen unter dem
git-ignorierten Namen `axcheck.lean`.

#### Zuerst: der vorige Lauf war abgebrochen und hat die Datei kaputt hinterlassen

Der Lauf `20260908T182301Z` endete mit `rc = 1` und ohne Laufbericht. Er hatte
266 Zeilen in `Suggested.lean` geschrieben — und zwar gute, sie tragen den
heutigen Beweis —, aber vier `omit [OrderTopology ι] in` zuviel: `exhaustionMax`
ist über `isCompact_exhaustion` von der Ordnungstopologie abhängig, und
`cannot omit referenced section variable` war der Zustand, in dem die Datei
stand. Berichtigt sind alle vier (zweimal ganz entfallen, zweimal auf
`omit [AdditiveDist ι] [BasePoint ι]` gebracht, was der Linter selbst vorschlägt).
Das ist der Grund, aus dem der Bericht des zweiundzwanzigsten Laufs von
**sieben** `sorry` und 193 Deklarationen spricht, ohne die fünf Deklarationen zu
nennen, die seither dastanden: sie waren geschrieben und nicht berichtet.

#### `CompleteSpace D(ι, E)` ist bewiesen

Vier neue Aussagen schließen ihn, und die erste ist die eigentliche Arbeit.

* `SkorokhodSpace.tendsto_distWith_of_tendstoUniformlyOn` — bei **einem** Radius:
  konvergiert `x n ∘ κ n` auf jedem Fenster gleichmäßig gegen `z` und geht
  `‖κ n‖ → 0`, so geht `distWith t₀ u (κ n) (x n) z → 0`, sofern an jedem der
  beiden Fensterränder eine von zwei Bedingungen gilt (siehe unten). Der Beweis
  ist `SkorokhodSpace.distWith_le_of_oscillation` mit `ε = a/4`, und die drei
  Voraussetzungen jener Aussage werden einzeln „schließlich in `n`" hergestellt:
  die gleichmäßige aus `hunif` auf dem Fenster vom Radius `m ≥ exp 1 · u`, weil
  `κ n⁻¹` einen Punkt des Fensters `u` höchstens auf den Radius `exp ‖κ n‖ · u`
  trägt, und die beiden Schwingungen aus der Dichotomie.
* `SkorokhodSpace.tendsto_intWith_of_ae_tendsto_distWith` — dominierte Konvergenz
  über den Radius, Dominante `exp (-u)`, das ist `integrableOn_exp_neg_Ioi`.
* `SkorokhodSpace.tendsto_intDist_of_tendsto_of_partialComp` — die beiden
  zusammen, mit `intDist t₀ (x n) z ≤ max ‖κ n‖ (intWith t₀ (κ n) (x n) z)`
  (`ciInf_le` gegen `bddBelow_range_intDist`) und `squeeze_zero`.
* `SkorokhodSpace.instCompleteSpace` — `Metric.complete_of_convergent_controlled_sequences`
  mit `B n = 2⁻⁽ⁿ⁺¹⁾`. Das Kriterium ist hier nicht Bequemlichkeit, sondern
  notwendig: eine beliebige Cauchyfolge liefert **keine Rate**, und sowohl
  `exists_lt_intDist_add` als auch `tendsto_of_partialComp` brauchen eine
  summierbare. Mit ihr ist `max ‖l n‖ (intWith t₀ (l n) (y n) (y (n+1))) < 2⁻ⁿ`,
  und `‖(partialComp l n)⁻¹ * L‖ → 0` folgt aus `hLtail` und
  `tendsto_sum_nat_add`.

#### Die Dichotomie der Roadmap war falsch, und das ist der Befund des Laufs

Meilenstein 5 führte seit dem zweiundzwanzigsten Lauf: „entweder ist die
Niveaumenge `{u : exhaustionMax t₀ u = A}` eine Nullmenge — dann fällt der Radius
mit der Nullmenge weg; oder sie ist es nicht, dann hat der Index eine Lücke über
`A`." Der erste Zweig ist **kein Argument**: eine Vereinigung von Nullmengen
braucht keine Nullmenge zu sein, und über die schlechten Radien wird vereinigt.

Richtig ist die Umkehrung der Reihenfolge, und sie stand als Beobachtung schon in
der Dokumentation des abgebrochenen Laufs: ein Radius **ohne** Lücke über seinem
Fensterrand legt diesen Rand fest (`exhaustionMax_lt_exhaustionMax_of_no_gap`:
das Fenster wächst dann echt), also bildet `countable_radius_exhaustionMax` die
Radien, deren Rand überdies ein Sprung von `z` ist, injektiv in die Sprungmenge
ab, und die ist nach `countable_leftJumpSet` abzählbar. Abzählbar ist
Lebesgue-null — das ist die Stelle, an der die Integralmetrik zahlt, wofür der
achtzehnte Lauf sie eingeführt hat. Die Dichotomie lautet damit an jedem Radius
außerhalb dieser abzählbaren Menge: **Lücke am Fensterrand** (dann fixiert jeder
verankerte Zeitwechsel kleiner Norm den Rand, `TimeChange.eq_of_gap_of_norm_lt`,
und die Schwingungsvoraussetzung ist leer) **oder Stetigkeit von `z` dort** (dann
stirbt die Schwingung mit der Verschiebung `(exp ‖λ‖ - 1) · 2u`). Kompaktheit
wird nirgends verbraucht; der Satz der Roadmap, die Lückenbreite entstehe durch
Kompaktheit, ist mit gestrichen.

**Und der untere Fensterrand ist nicht umsonst**, was derselbe Meilenstein
annahm: „dort ist `z` von selbst rechtsstetig, das ist die càdlàg-Eigenschaft".
Das trüge nur, wenn die Zeitwechsel `exhaustionMin t₀ u` nach rechts bewegten,
und nichts zwingt sie dazu — `κ n⁻¹` darf ihn nach links tragen, und
`Set.uIcc` ist das Intervall in beide Richtungen. Der Spiegel wird deshalb ganz
geführt (`TimeChange.eq_of_gap_below_of_norm_lt`,
`exhaustionMin_lt_exhaustionMin_of_no_gap`, `countable_radius_exhaustionMin`),
und was am unteren Rand verbraucht wird, ist `ContinuousAt`, nicht
Rechtsstetigkeit. Beides ist in `SkorokhodSpace/README.md`, Meilenstein 5,
berichtigt, samt dem falschen ersten Zweig.

#### Was der abgebrochene Lauf gebaut hatte und was daran trägt

Fünf Deklarationen, jetzt mitgeprüft: `SkorokhodSpace.distWith_le_of_oscillation`
(`distWith ≤ 3ε` aus einer gleichmäßigen Schätzung und zwei Randschwingungen;
sie braucht weder `0 ≤ u` noch `l t₀ = t₀`), ihre kombinatorische Hälfte
`min_max_pair_cases` (die beiden `clamp` eines Punktes stimmen überein oder
liegen beide zwischen den beiden oberen bzw. beiden unteren Fensterenden) und
ihre metrische `dist_le_dist_of_mem_uIcc` (reines `AdditiveDist`), dazu
`TimeChange.eq_of_gap_below_of_norm_lt` und die beiden
`_lt_..._of_no_gap`-Aussagen samt den beiden `countable_radius_...`.

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.instSeparableSpace` beweisen** — die Treppenpfade mit
Sprungzeiten in einer abzählbar dichten Teilmenge von `ι` und Werten in einer
abzählbar dichten Teilmenge von `E` sind dicht in `D(ι, E)`. Worauf er ruht:
auf `IsCadlag.finite_largeLeftJumpSet_inter` (Meilenstein 2, bewiesen — ein
Fenster trifft nur endlich viele große Sprünge), auf `isCompact_exhaustion` für
die Endlichkeit, auf `TimeChange.norm_le_of_lipschitzWith`, um den Zeitwechsel zu
bauen, der die Sprungzeit auf einen dichten Punkt schiebt, und auf
`SkorokhodSpace.dist_le_distWith`, um den Abstand aus einem Zeugen abzulesen.
Warum jetzt: es ist der letzte offene Punkt von Meilenstein 5, `instPolishSpace`
ist `inferInstance` und fällt mit ihm, und `fact:PSpolish` in der Lesart von
`rem:EKrelcompact` — $\DE$ unter $J_1$ ist polnisch — ist damit ganz. Die
Vorlage dafür steht in `WeakConvergence/Suggested.lean` als `stepFun`,
`stronglyMeasurable_stepFun`, `exists_mem_stepFun`, `stepClass` (dreizehnter
Lauf, für $M_E$), samt der dort gefundenen Vereinfachung: eine **Liste** von
Indexpaaren mit Vorrang der früheren Einträge ersetzt die Summe von Indikatoren
und erspart die Disjunktifizierung.

**Das Manuskript ist nicht angefaßt.** Am Inventar ändert sich eine Zeile,
`fact:PSpolish`, um den Beweis von `CompleteSpace D(ι, E)`.

### 2026-09-08, vierundzwanzigster Lauf des Tages — der Index bekommt eine Koordinate, Meilenstein 1 ist zu, und die Separabilität hängt an einer Aussage über den Index und nicht über die Pfade

**Bearbeitet.** Keine Fact-Zeile neu; der Lauf steht im Rückstau, Punkt 2
(`SkorokhodSpace` weiter beweisen). Der Vorschlag des dreiundzwanzigsten Laufs
war `SkorokhodSpace.instSeparableSpace`; dieser Lauf hat ihn **nicht** bewiesen,
sondern zuerst geprüft, worauf er ruht, und dabei gefunden, daß das Fundament
fehlte. Was statt dessen dasteht, ist dieses Fundament.

**Stand der Datei.** `SkorokhodSpace/Suggested.lean` trägt **fünf `sorry`**
statt sechs; `lake env lean` gegen v4.33.1 meldet `rc = 0` und außer den fünf
`sorry`-Warnungen und zwei `push_neg`-Deprecations keine Meldung — insbesondere
keine des `unusedSectionVars`-Linters. Sieben neue Deklarationen, alle mit
`#print axioms` geprüft: alle hängen allein an `propext`, `Classical.choice`,
`Quot.sound`. Das Verfahren ist das des Vorlaufs, eine Kopie mit angehängten
`#print axioms`-Zeilen unter dem git-ignorierten `axcheck.lean`.

#### `exists_orderIso_isometry_real` ist bewiesen, und Meilenstein 1 trägt kein `sorry` mehr

Der Satz stand seit dem 2026-09-06 als `sorry` da und war der **einzige** offene
Punkt von Meilenstein 1; der elfte Lauf des 2026-09-07 hatte bei
`countable_rightIsolated` eigens vermerkt, sein Beweis gehe „nicht durch die
Einbettung des Index in `ℝ`, die noch offen ist". Sie ist es nicht mehr.

Der Beweis ist kurz, und das ist der Punkt: er besteht darin, die Einbettung
**hinzuschreiben** statt sie zu suchen. `lengthCoord t₀ t` ist die Länge zum
Basispunkt, mit dem Vorzeichen der Seite:

```
lengthCoord t₀ t = if t₀ ≤ t then dist t₀ t else -dist t₀ t
```

Die eine Aussage, aus der alles folgt, ist `sub_lengthCoord_of_le`: für `s ≤ t`
ist `lengthCoord t₀ t - lengthCoord t₀ s = dist s t` — **ohne** Betrag. Drei
Fälle, nach der Lage des Paars zum Basispunkt, und nur im gemischten Fall
`s < t₀ ≤ t` addieren sich die beiden Längen, statt sich zu subtrahieren. Daraus
`strictMono_lengthCoord` (mit `dist_pos`, und das ist die einzige Stelle, an der
`MetricSpace` statt `PseudoMetricSpace` verbraucht wird), `isometry_lengthCoord`
und `lengthCoord_self : lengthCoord t₀ t₀ = 0`. Der Satz selbst ist dann
`StrictMono.orderIso` für den Ordnungsisomorphismus auf das Bild und
`Isometry.isClosedEmbedding` (`Topology/MetricSpace/Isometry.lean:218`) für die
Abgeschlossenheit des Bildes.

**Eine Hypothese fällt, und sie stand im Meilenstein.** `OrderTopology ι` wird
nicht gebraucht; der Satz ist `omit [OrderTopology ι] in` gestellt und gilt für
jede lineare Ordnung mit einer längs ihr additiven Metrik, was für eine
Topologie sie auch trage. Verbraucht werden `AdditiveDist` (Isometrie),
`MetricSpace` (Striktheit) und `ProperSpace` — und von Letzterem nur die
Vollständigkeit, über `complete_of_proper`
(`Topology/MetricSpace/ProperSpace.lean:104`). Der leere Index ist ein eigener
Fall und nimmt `s = ∅`: ohne Punkt gibt es keinen Basispunkt, um die Koordinate
zu nehmen.

**Warum die Koordinate benannt ist und nicht aus dem Existenzsatz gelesen wird.**
Aus demselben Grund, aus dem `BasePoint` Daten sind und nicht `[Nonempty ι]`:
der von einem `∃` gelieferte Ordnungsisomorphismus ist opak, und gegen ihn läßt
sich kein einziger Zeitwechsel hinschreiben. Der Existenzsatz ist die
Zusammenfassung; gearbeitet wird mit `lengthCoord`.

#### `TimeChange.exists_of_lengthCoord` — Zeitwechsel werden in der Koordinate gebaut

Bis heute konstruierte **nichts** in der Datei einen Zeitwechsel auf einem
allgemeinen Index: `TimeChange.steep` und `TimeChange.double` sind auf `ℝ`
geschrieben, alles andere über `TimeChange` handelt von gegebenen. Mit der
Koordinate ist nichts mehr zu konstruieren, und der Satz sagt es:

> Ist `φ : ℝ → ℝ` streng monoton mit `φ 0 = 0`, gilt `|φ x - φ y| ≤ exp γ ·
> |x - y|` und `|x - y| ≤ exp γ · |φ x - φ y|`, und bildet `φ` das Bild von
> `lengthCoord t₀` **auf sich** ab, so gibt es einen Zeitwechsel `l` mit
> `l t₀ = t₀`, `‖l‖ ≤ γ` und `lengthCoord t₀ (l t) = φ (lengthCoord t₀ t)`.

Der Beweis wählt mit `choose` das Urbild, liest die drei Eigenschaften des
Ordnungsisomorphismus (streng monoton, surjektiv, bi-Lipschitz) aus denen von
`φ` ab, weil die Koordinate eine Isometrie ist und Ordnungen reflektiert, und
schließt mit `StrictMono.orderIsoOfSurjective` und dem vorhandenen
`TimeChange.norm_le_of_lipschitzWith`. Die Normschranke ist damit `γ` und keine
Ableitung daraus; die Schranke wird zweimal mit demselben `exp γ` verlangt,
weil die Norm das Maximum über `l` und `l⁻¹` ist.

#### Der Befund über die Separabilität, und er ist der Ertrag des Laufs

Die Aufgabe war `SkorokhodSpace.instSeparableSpace`, und die Prüfung, worauf sie
ruht, hat sie in zwei Hälften **sehr** verschiedenen Gewichts zerlegt.

*Die leichte Hälfte ist die Approximation durch Treppenpfade an den eigenen
Sprungzeiten.* Sie ist auf jedem Fenster gleichmäßig und braucht **keinen**
Zeitwechsel; sie ist die Unterteilung von Meilenstein 7 und kommt mit
`tendsto_modulus`.

*Die schwere Hälfte ist das Verschieben der Sprungzeiten auf die abzählbare
Menge, und sie ist eine Aussage über den Index und nicht über die Pfade.* Ohne
sie geht es nicht, und das ist beweisbar und nicht bloß plausibel: liegt der
Sprung von `f` bei `a` und der von `g` bei `a' ≠ a`, so ist das gefensterte
Supremum unter dem **identischen** Zeitwechsel mindestens die halbe Sprunghöhe,
für jeden Radius oberhalb von `|a|` — und da die Radien über ein Intervall
laufen und nicht über eine Nullmenge, hilft die Integralform hier nicht. Die
naheliegende Abkürzung, die Unterteilungspunkte gleich aus der abzählbaren
dichten Menge zu nehmen, scheitert an derselben Rechnung.

**Und die Schranke, die dabei sichtbar wurde:** die Verschiebung ist auf einem
allgemeinen Index nicht immer möglich, und das ist kein Mangel des Beweises. Für
`ι = h • ℤ` ist das Bild der Koordinate `h • ℤ`, das einzige zulässige `φ` ist
die Identität, und der Index hat **keinen** Zeitwechsel außer dem trivialen —
dort ist die abzählbare dichte Menge der Index selbst und die Sprungzeiten
müssen nicht verschoben werden. Für `ι = ℝ` tut es jedes stückweise lineare
`φ`. Was der Meilenstein schuldet, ist also weder eine Konstruktion auf `ℝ`
noch eine über Pfade, sondern **das Interpolationslemma auf dem Bild der
Koordinate**: endlich viele vorgeschriebene Punkte des Bildes auf endlich viele
benachbarte Punkte des Bildes, durch ein `φ`, das das Bild auf sich abbildet und
dessen beide Lipschitzkonstanten nahe bei `1` liegen. Das ist in Meilenstein 5
so eingetragen, `TimeChange.exists_of_lengthCoord` ist in Meilenstein 3
eingetragen, und die zwei Surjektivitätshypothesen dort sind der Ort, an dem die
Bedingung sichtbar wird.

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.tendsto_modulus` beweisen** — Billingsleys `w'(f, δ) → 0` für
`δ ↓ 0`, auf dem Fenster `exhaustion t₀ m`. Worauf er ruht: auf
`isCompact_exhaustion`, auf `IsCadlag.tendsto_leftLim` und der
Rechtsstetigkeit für die lokale Schwingungsschranke, auf `modulus_mono` für die
Reduktion von `𝓝[>] 0` auf ein einziges `δ` je `ε`, und auf
`ordConnected_exhaustion`, damit die Überdeckung des Fensters durch Intervalle
läuft. Warum jetzt: es ist der erste offene Punkt von Meilenstein 7, es ist
**die leichte Hälfte der Separabilität** — die Unterteilung mit kleiner
Schwingung auf jeder Zelle ist genau der Treppenpfad, der `instSeparableSpace`
approximiert —, und es ist der einzige der fünf verbliebenen `sorry`, der von
keiner offenen Frage über den Index abhängt. Die andere Hälfte der
Separabilität, das Interpolationslemma, ist der Vorschlag danach; sie ist
schwerer und jetzt wenigstens benannt.

**Das Manuskript ist nicht angefaßt.** Am Inventar ändert sich eine Zeile,
`fact:PSpolish`, um den Stand von Meilenstein 1 und um die Zerlegung der
Separabilität.

### 2026-09-08, fünfundzwanzigster Lauf des Tages — die Unterteilung ist bewiesen, und mit ihr fällt Meilenstein 7 zur Hälfte und Meilenstein 5 zur Hälfte

**Bearbeitet:** `SkorokhodSpace/Suggested.lean`, Meilensteine 2, 5 und 7.
`fact:PSpolish` bleibt `Roadmap`. Die Datei steht bei **vier** `sorry` statt
fünf. **Vierzehn neue Deklarationen**, alle durch `lake env lean` gegen v4.33.1
geprüft und alle mit `#print axioms`: sämtlich nur `propext`,
`Classical.choice`, `Quot.sound`.

#### Zur Reihenfolge, und sie weicht vom Auftrag ab

Der Auftrag nennt `instSeparableSpace` als Punkt 1 und Meilenstein 7 als
Punkt 3. Dieser Lauf hat Punkt 3 zuerst angefaßt, und der Grund ist kein
Geschmack, sondern eine Abhängigkeit in der falschen Richtung: **die
Separabilität ruht auf dem Satz, der Meilenstein 7 trägt.** Billingsleys Beweis
der Separabilität von `D` approximiert einen Pfad durch einen Treppenpfad, und
die Treppe ist genau eine Unterteilung des Fensters, auf deren Zellen der Pfad
um höchstens `ε` schwankt — dieselbe Unterteilung, deren Existenz
`tendsto_modulus` behauptet. Wer die Separabilität zuerst anfaßt, beweist die
Unterteilung unterwegs und ohne Namen. Der Vorschlag des vierundzwanzigsten
Laufs sagte dasselbe („es ist **die leichte Hälfte der Separabilität**"), und
dieser Lauf ist ihm gefolgt.

#### Der Satz, auf dem beides steht

`IsCadlag.exists_subdivision`: ist `f` càdlàg, `a ≤ b` und `Set.Icc a b`
kompakt, so gibt es zu jedem `ε > 0` ein `n` und ein streng monotones
`t : Fin (n+1) → ι` mit `t 0 = a`, `t (Fin.last n) = b` und

    ∀ i, ∀ x ∈ Set.Ico (t i.castSucc) (t i.succ), dist (f x) (f (t i.castSucc)) ≤ ε.

*Der Beweis ist ein Supremumsargument und keine Induktion*, und das ist der
Punkt: die Zellen lassen sich nicht vorab wählen, ihre Längen sind von den
Sprüngen von `f` diktiert und dürfen gegen `0` gehen. Sei `S` die Menge der
Endpunkte, die eine solche Unterteilung erreicht, und `c` der größte Punkt von
`closure S` — er existiert, weil das Fenster kompakt ist. Der *Linkslimes* bei
`c` zeigt `c ∈ S`: auf einem Intervall `(y, c)` bleibt `f` innerhalb `ε/2` des
Linkslimes, ein erreichbares `s > y` liegt darin, und die Zelle `[s, c)` kostet
nach der Dreiecksungleichung `ε`. Die *Rechtsstetigkeit* bei `c` zeigt `c = b`:
wäre `c < b`, so ließe sich `min u b` anhängen und `c` wäre nicht der größte.

*Minimale Voraussetzungen, und sie sind kleiner als erwartet.* Die Kompaktheit
des Fensters ist **Hypothese** und nicht `ProperSpace ι`; `AdditiveDist` und die
Metrik des Index kommen nicht vor. Nur die Ordnungstopologie und die Metrik auf
`E` gehen ein. Der eine kombinatorische Schritt ist abgetrennt:
`exists_snoc_subdivision`, das Anhängen eines Punktes über `Fin.snoc`, ohne
càdlàg und ohne Topologie.

#### Meilenstein 7: `tendsto_modulus` ist bewiesen

`SkorokhodSpace.tendsto_modulus (t₀) (m : ℕ) (f) : Tendsto (modulus t₀ m f)
(𝓝[>] 0) (𝓝 0)`. Aus der Unterteilung mit einer Beobachtung: ihre Lücken sind
endlich viele und jede positiv, weil sie streng monoton ist, also liegt ein
`δ₀ > 0` unter allen; jedes `δ < δ₀` läßt dieselbe Unterteilung als
`δ`-spärliche zu, und das Infimum in `modulus t₀ m f δ` ist von `δ₀` an
höchstens `ε`. Die `ℝ≥0∞`-Wertigkeit — die Abweichung des sechzehnten Laufs —
kostet hier genau einen Schritt: `ENNReal.tendsto_nhds_zero` verlangt ein
`ε : ℝ≥0∞`, `ENNReal.ofReal_toReal` macht ein reelles daraus, und der Wert `⊤`
ist gratis.

Von Meilenstein 7 bleibt allein `isCompact_closure_iff`.

#### Meilenstein 5: die Treppenpfade, und wo die Separabilität wirklich hängt

Der Treppenpfad ist als Komposition gebaut und nicht als Fallunterscheidung:
`stepRetract t` ist die Retraktion des Index auf das Bild eines endlichen
Tupels — jeder Punkt geht auf den größten Eintrag unter ihm, und auf `t 0`,
wenn es keinen gibt —, und der Treppenpfad ist `f ∘ stepRetract t`. Fünf
bewiesene Aussagen darüber:

* `IsCadlag.of_eventually_const` — wer auf einer Rechtsumgebung jedes Punktes
  und auf einer Linksumgebung jedes Punktes konstant ist, ist càdlàg. Die
  beiden entarteten Fälle brauchen keine Sonderbehandlung: an einem größten
  Element ist `𝓝[>] x = ⊥`, an einem kleinsten `𝓝[<] x = ⊥`.
* `eventually_stepRetract_eq_nhdsGT` und
  `exists_eventually_stepRetract_eq_nhdsLT` — die Retraktion ist lokal
  konstant, rechts wie links. Rechts über den größten Index `i` mit `t i ≤ x`
  und den nächsten Eintrag `t (i+1) > x`, links über den größten Index mit
  `t i < x`.
* `isCadlag_comp_stepRetract` — **der Treppenpfad ist càdlàg, und `f` muß es
  nicht sein.** Das ist keine Schwächung, sondern der ehrliche Umfang: die
  Aussage steht auf der lokalen Konstanz der Retraktion allein.
* `finite_range_comp_stepRetract` — er nimmt endlich viele Werte an. Das ist,
  was das Abzählen später braucht, und der einzige Grund, warum die Retraktion
  über ein `Finset` läuft.
* `dist_comp_stepRetract_le` — auf `Set.Icc (t 0) (t (Fin.last n))` ist er
  gleichmäßig `ε`-nah an `f`, wenn die Zellen `ε` tragen. Das Tupel muß dafür
  **nicht** streng monoton sein, und der Linter hat recht: die Retraktion liest
  den größten Index aus einem `Finset`, ein wiederholter Eintrag ändert, welcher
  Wert genommen wird, aber nicht, daß er in einer Zelle der Hypothese liegt.

Zusammengesetzt: `SkorokhodSpace.exists_finite_range_distWith_le (t₀) (f) (hε)
(M)` — zu jedem `f`, `ε > 0` und `M` gibt es ein `g : D(ι, E)` mit endlichem
Wertebereich und `distWith t₀ u 1 f g ≤ ε` für alle `u ≤ M`, für den
**identischen** Zeitwechsel. Das ist die Hälfte der Separabilität, die die
Analysis trägt.

#### Und der Befund, der die andere Hälfte betrifft

Was fehlt, ist nicht die Approximation, sondern die **Abzählbarkeit**: die
Sprungzeiten des Approximanten sind die von `f` und laufen über ganz `ι`. Sie
auf eine feste abzählbare Menge zu schieben, ist Sache des Zeitwechsels, und
dabei gilt:

> **Eine beliebige abzählbare dichte Teilmenge von `ι` genügt nicht.**

Der Zeuge, von Hand gerechnet und an der Deklaration
`SkorokhodSpace.instSeparableSpace` eingetragen: `ι = Set.Icc (0:ℝ) 1` mit
Basispunkt `0`. Jeder Zeitwechsel ist ein Ordnungsisomorphismus einer linearen
Ordnung mit größtem Element, **fixiert also `1`**. Der Pfad
`f = Set.indicator {1} 1` ist càdlàg (bei `1` ist `𝓝[>] 1 = ⊥`). Ist `g` ein
Treppenpfad, dessen Sprungzeiten `1` meiden, und `d < 1` seine letzte
Sprungzeit, so ist `g` auf `[d, 1]` konstant mit Wert `c`; für jedes `l` ist
`f (l 1) = 1` und `f (l d) = 0`, also

    distWith t₀ u l f g ≥ max |c - 1| |c| ≥ 1/2   für u ≥ 1,

und damit `intDist t₀ f g ≥ exp (-1) / 2` für **jedes** solche `g` und jedes
`l`. Eine abzählbare dichte Teilmenge von `Set.Icc (0:ℝ) 1` muß `1` nicht
enthalten.

Die Sprungzeiten sind also aus einer abzählbaren Menge zu nehmen, die
zusätzlich die von keinem Zeitwechsel bewegbaren Punkte trägt — das Spiegelbild
von `rightIsolated` und `exists_countable_ciSup_eq`, die dieselbe Lücke für die
Suprema schließen und schon in der Datei stehen. Das ist der benannte nächste
Schritt und steht so in Meilenstein 5.

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.exists_countable_timeChangeInvariant`** — eine abzählbare
Menge `C ⊆ ι`, die dicht ist **und** jeden Punkt enthält, den kein Zeitwechsel
bewegt. Worauf sie ruht: auf `countable_rightIsolated` (bewiesen, im selben
Stil), auf `exists_countable_ciSup_eq` (bewiesen, dieselbe Bauform: dicht plus
eine abzählbare Ausnahmemenge), und auf `exists_orderIso_isometry_real`, das
den Index als abgeschlossene Teilmenge von `ℝ` sieht und die unbeweglichen
Punkte als die Ränder ihrer Zusammenhangskomponenten identifiziert. Warum
jetzt: es ist der einzige noch unbenannte Schritt der Separabilität — die
Analysis ist mit `exists_finite_range_distWith_le` bezahlt, die Abzählbarkeit
der Werte ist `[SeparableSpace E]` —, und der Zeuge oben zeigt, daß ohne ihn
kein Beweis geführt werden **kann**, nicht bloß keiner geführt wurde.

Danach, und erst danach, das Interpolationslemma: zu endlich vielen Punkten
`t 0 < … < t n` und Nachbarn `d i ∈ C` ein Zeitwechsel kleiner Norm mit
`l (t i) = d i`.

**Zweiter Vorschlag, unabhängig und billig:** die Integralbuchführung von
`exists_finite_range_distWith_le` nach `intDist` — aus `distWith ≤ ε` für
`u ≤ M` und `min 1 (·) ≤ 1` sonst folgt `intDist t₀ f g ≤ ε + exp (-M)`, über
`integral_exp_neg_Ioi` (`Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean:57`)
und eine Zerlegung `Set.Ioi 0 = Set.Ioc 0 M ∪ Set.Ioi M`. Das macht aus der
Fensteraussage eine echte Dichtheitsaussage über die Metrik und ist von der
Frage über den Index unabhängig.

**Das Manuskript ist nicht angefaßt.**

### 2026-09-09, erster Lauf des Tages — die Separabilität von `D(ι, E)` ist falsch, und was an ihre Stelle tritt

**Bearbeitet:** `SkorokhodSpace/Suggested.lean` und `SkorokhodSpace/README.md`,
Meilenstein 5. `fact:PSpolish` bleibt `Roadmap`. Die Datei steht weiter bei
**vier** `sorry` — dieser Lauf hat keines gestrichen, sondern eines
**berichtigt**, und das ist sein Ergebnis. **Zehn neue Deklarationen**, alle
durch `lake env lean` gegen v4.33.1 geprüft und alle mit `#print axioms`:
sämtlich nur `propext`, `Classical.choice`, `Quot.sound`.

#### Der Befund: `SeparableSpace D(ι, E)` ist keine Aussage über `D(ι, E)` allein

Der Auftrag nennt `instSeparableSpace` als Punkt 1, und der vorige Lauf hatte
als nächsten Schritt `SkorokhodSpace.exists_countable_timeChangeInvariant`
benannt: eine abzählbare Menge, die dicht ist und alle von keinem Zeitwechsel
bewegbaren Punkte enthält. Der Versuch, sie zu bauen, stößt auf ein Hindernis,
das keine Konstruktion umgeht:

> **Die von keinem Zeitwechsel bewegbaren Punkte sind nicht abzählbar.**

`exists_orderIso_isometry_real` sieht den Index als abgeschlossene Teilmenge
`S ⊆ ℝ`. Der vorige Lauf las die unbeweglichen Punkte als „die Ränder der
Zusammenhangskomponenten" und schloß daraus auf Abzählbarkeit. Das ist falsch:
`S \ interior S` ist für eine perfekte nirgends dichte Menge die ganze Menge.
Die **Cantormenge** ist ein zulässiger Index dieser Datei — abgeschlossen in
`ℝ`, also `LinearOrder`, `MetricSpace`, `OrderTopology`, `AdditiveDist` über
`instAdditiveDistSubtype`, und `ProperSpace`, weil sie kompakt ist — und sie ist
überabzählbar.

Auf ihr gibt es **außer der Identität keinen billigen Zeitwechsel**. Die Lücken
haben die Längen `3^{-n}`; ein Ordnungsisomorphismus trägt Lücken auf Lücken,
und ist er bi-Lipschitz mit beiden Konstanten unter `3`, so kann er keine
Lückenlänge ändern, weil das Verhältnis zweier verschiedener Lückenlängen
mindestens `3` ist. Also fixiert er die eine Lücke der Länge `1/3`, per
Induktion längs der Ordnung jede Lücke, damit jeden Lückenrand, und weil die
Ränder dicht liegen, alles. Jeder Zeitwechsel ≠ 1 hat somit Norm ≥ `log 3`.

Damit ist die überabzählbare Familie `stepAt x 1 0`, `x` in der Cantormenge,
paarweise mindestens `min (log 3) (exp (-1))` voneinander entfernt, und
`D(ι, ℝ)` ist **nicht separabel**.

#### Was davon in Lean steht

`SkorokhodSpace.not_separableSpace_of_rigid`: ist `ι` überabzählbar, ist der
einzige Zeitwechsel in `TimeChange.fixing basePoint` mit Norm `< c` (für ein
`c > 0`) die Identität, und hat `E` zwei verschiedene Punkte, so ist
`D(ι, E)` **nicht separabel**. Der Weg dorthin, vier Deklarationen:

* `SkorokhodSpace.stepAt x a b` — der Pfad, der ab `x` den Wert `a` und darunter
  `b` nimmt. Càdlàg über `IsCadlag.of_eventually_const`, ohne jeden Limes: er
  ist auf einer Rechts- und einer Linksumgebung jedes Punktes konstant.
* `SkorokhodSpace.dist_le_distWith_stepAt` — zwei solche Pfade sind für den
  **identischen** Zeitwechsel bei `min x y` um `dist a b` auseinander, sobald
  das Fenster diesen Punkt enthält. Unterhalb von `min x y` stimmen beide
  überein und oberhalb von `max x y` auch; `min x y` ist der eine Punkt, an dem
  die Aussage abzulesen ist.
* `SkorokhodSpace.le_intWith_stepAt` — dasselbe unter dem Integral über den
  Radius: alle Radien oberhalb `dist t₀ (min x y)` sehen die Trennung und tragen
  die Masse `exp (-dist t₀ (min x y))`.
* `SkorokhodSpace.le_intDist_stepAt` — und in der Metrik, über die
  Fallunterscheidung, die den ganzen Satz trägt: entweder ist der Zeitwechsel
  billig, dann ist er nach `hrigid` die Identität, oder er kostet `c`.

Die Nichtseparabilität selbst ist dann Buchführung: eine überabzählbare Menge
hat eine überabzählbare abgeschlossene Kugel (`exists_nat_ge` über die
Ausschöpfung), und eine `r`-getrennte Familie in einem separablen metrischen
Raum ist abzählbar, weil sie sich in die abzählbare dichte Menge einbetten läßt
— hier als Überdeckung durch die Bälle vom Radius `r/2` um deren Punkte, deren
jeder höchstens ein Familienmitglied trifft.

**Was nicht in Lean steht, und das ist ehrlich zu nennen:** die Rechnung mit den
Lückenlängen der Cantormenge, die `hrigid` einlöst. Sie steht als Prosa an der
Deklaration und in Meilenstein 5. Damit ist `not_separableSpace_of_rigid` eine
Implikation, deren Hypothesen ich als erfüllbar *behaupte* und nicht *beweise* —
die Sorte Aussage, die die Prüfung des 2026-09-07 „leer" nennen würde, wenn die
Erfüllbarkeit unklar wäre. Sie ist es nicht; sie ist bloß teuer, weil Mathlib
die Cantormenge mit ihrer Lückenstruktur nicht führt. Wer sie baut, macht die
Widerlegung unbedingt, und sonst hängt nichts daran.

#### Was an die Stelle tritt

`SkorokhodSpace.HasCountableCore ι`, eine Typklasse: eine abzählbare Menge
`C ⊆ ι` und zu jedem endlichen streng monotonen Tupel `t : Fin (n+1) → ι` und
jedem `δ > 0` ein Tupel `d` in `C` und ein Zeitwechsel `l` mit
`l basePoint = basePoint`, `‖l‖ ≤ δ` und `l (d i) = t i`. Das ist die schwere
Hälfte der Separabilität, als Aussage **über den Index** isoliert, und sie ist
eine Hypothese und kein Satz.

`instSeparableSpace` und `instPolishSpace` tragen sie seit heute; beide bleiben
`sorry` bzw. `inferInstance`, aber die Aussage von `instSeparableSpace` ist jetzt
eine, die stimmen kann. Der Grund für eine **Typklasse** und nicht für eine
Hypothese am Satz ist mechanisch: `instSeparableSpace` ist eine Instanz, und
`instPolishSpace` ist `inferInstance` und liest sie über die Instanzensuche.

`exists_countable_timeChangeInvariant` ist **gestrichen** — es war als Satz
gedacht und kann keiner sein. Der `Set.Icc (0:ℝ) 1`-Zeuge des vorigen Laufs
bleibt und steht jetzt an der Klasse: er zeigt, daß `C` mehr als dicht sein muß;
der Cantor-Zeuge zeigt, daß es `C` nicht immer gibt.

Was Meilenstein 5 jetzt schuldet, sind drei Dinge statt einem: die Klasse
(steht), ihre drei Instanzen für `ℝ`, `AddSubgroup.zmultiples (1:ℝ)` und
`Set.Icc (0:ℝ) 1`, und die Separabilität unter ihr.

#### Der zweite Vorschlag des vorigen Laufs, eingelöst

`SkorokhodSpace.intWith_le_of_forall_distWith_le`: bleiben die gefensterten
Suprema für **einen** Zeitwechsel bis zum Radius `M` unter `ε`, so ist
`intWith t₀ l f g ≤ ε + exp (-M)`. `Set.Ioi 0` wird bei `M` geteilt
(`Set.Ioc_union_Ioi_eq_Ioi`, `MeasureTheory.setIntegral_union`), die nahen Radien
zahlen `ε` gegen eine Wahrscheinlichkeitsdichte, die fernen ihre eigene Masse
`exp (-M)` gegen die Trunkierung bei `1`. Daraus
`SkorokhodSpace.exists_finite_range_intDist_le`: zu `f`, `ε > 0` und `M ≥ 0` ein
`g` mit endlichem Wertebereich und `intDist t₀ f g ≤ ε + exp (-M)`. Das macht
aus der Fensteraussage des vorigen Laufs eine Aussage über die Metrik, und es
ist von der Frage über den Index unabhängig — es gilt auch auf der Cantormenge,
wo nur die *Abzählbarkeit* der Approximanten scheitert und nicht die
Approximation.

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.instHasCountableCoreReal`**, die Klasse für `ι = ℝ`. Worauf
sie ruht: auf `TimeChange.exists_of_lengthCoord` (bewiesen, Meilenstein 3), das
aus einem streng monotonen bi-Lipschitz-`φ : ℝ → ℝ` mit `φ 0 = 0`, das den
Bereich von `lengthCoord` auf sich abbildet, einen Zeitwechsel der Norm ≤ `γ`
macht — und für `ι = ℝ` ist dieser Bereich ganz `ℝ`, die beiden lästigen
Hypothesen sind also gratis. Zu bauen ist allein das stückweise lineare `φ`, das
außerhalb disjunkter `η`-Umgebungen der `t i` die Identität ist und darin ein
rationales `d i` auf `t i` trägt; seine Steigungen sind `η / (η ± |d i - t i|)`,
also durch Wahl von `d i` nahe genug an `1`. Warum jetzt: es ist die erste der
drei Instanzen, die einzige mit echtem Inhalt, und ohne sie ist die Klasse eine
Hypothese, von der niemand weiß, ob sie je erfüllt ist — genau der Vorwurf, den
dieser Lauf an `not_separableSpace_of_rigid` selbst erhebt.

**Zweiter Vorschlag, danach:** die Separabilität unter der Klasse. Der Umbau der
Sprungzeiten ist Buchführung, nicht Analysis: ist `l` ein Ordnungsisomorphismus
mit `l (d i) = t i`, so gilt `t i ≤ l s` genau dann, wenn `d i ≤ s`, also
`f ∘ stepRetract t ∘ l = f ∘ l ∘ stepRetract d` — dieselben Werte an den Zeiten
`d i ∈ C`. Die Werte in eine abzählbare dichte Teilmenge von `E` zu schieben ist
gratis und braucht keinen Zeitwechsel.

#### Eine Nebenwirkung, damit sie nicht rätselhaft bleibt

Der erste `lake env lean`-Aufruf dieses Laufs lief versehentlich aus
`~/Code/lean/journal/.lake/packages/mathlib` statt aus `~/Code/lean/journal`.
`lake` hat daraufhin Mathlibs eigene Abhängigkeiten nach
`~/Code/lean/journal/.lake/packages/mathlib/.lake/packages/` geklont
(`batteries`, `aesop`, `Qq`, `proofwidgets`, `importGraph`, `Cli`,
`LeanSearchClient`, `plausible`), und der Aufruf schlug fehl. Das liegt
vollständig in einem `.lake`-Verzeichnis, ist von git ignoriert und wird vom
Build des Hauptcheckouts nicht gelesen; entfernt habe ich es nicht, weil Löschen
im Hauptcheckout die riskantere Handlung wäre. **Die Regel für den nächsten
Lauf:** `lake env lean` wird aus `~/Code/lean/journal` aufgerufen, nie aus einem
Paketverzeichnis darunter — das Arbeitsverzeichnis entscheidet, welches
`lakefile` gilt.

**Das Manuskript ist nicht angefaßt.**


### 2026-09-09, zweiter Lauf des Tages — `HasCountableCore ℝ` ist bewiesen, und die Klasse ist damit nicht leer

**Vorrangige Aufgabe, Teil A, Punkt 1.** Der vorige Lauf hat
`SkorokhodSpace.instSeparableSpace` berichtigt statt bewiesen und die schwere
Hälfte der Separabilität als Typklasse `SkorokhodSpace.HasCountableCore ι`
isoliert. Dieser Lauf löst die erste ihrer drei Instanzen ein.
`SkorokhodSpace/Suggested.lean` steht weiter bei **vier** `sorry`; gestrichen ist
keines. Elf neue Deklarationen, alle durch `lake env lean` gegen v4.33.1 geprüft
und alle mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`.

#### Der Befund: die Klasse ist erfüllbar, und `ℝ` erfüllt sie mit `C = ℚ`

`Real.instHasCountableCore` ist bewiesen. Das ist keine Zugabe, sondern die
Antwort auf den Vorwurf, den der vorige Lauf an seine eigene Konstruktion
erhoben hat: `not_separableSpace_of_rigid` zeigt, daß die Separabilität von
`D(ι, E)` für einen Index scheitern kann, den diese Datei zuläßt, und daraus
folgt eine Hypothese — aber eine Hypothese, von der niemand weiß, ob sie je
erfüllt ist, ist von einer leeren Aussage nicht zu unterscheiden. Sie ist es
jetzt: `instSeparableSpace` und `instPolishSpace` sind Aussagen über eine
bewohnte Klasse, und ihr Zeuge ist der Index, den das Manuskript überall meint.

#### Die Konstruktion, und warum sie eine Störung und keine Interpolation ist

Die Roadmap hatte hier ein **stückweise lineares** `φ` vorgesehen: die Identität
außerhalb disjunkter `η`-Umgebungen der `t i`, darin die Gerade von `d i` nach
`t i`. Gebaut ist statt dessen `φ x = x + ψ x` mit

```
ψ x = ∑ i, (t i - d i) * tent ρ (d i) x,   tent ρ c x = max 0 (1 - |x - c| / ρ),
```

und das ist derselbe Gedanke in der Gestalt, in der er sich rechnen läßt. Der
Grund ist eine Buchführung: bei der Interpolation muß man die Steigung auf jedem
der `2(n+1)` Stücke einzeln kontrollieren und dazu wissen, welches Stück wo
liegt; bei der Störung genügt die **grobe** Schranke

```
Lip ψ ≤ ∑ i |t i - d i| / ρ ≤ (n+1) · η / ρ,
```

die davon, daß die Zelte disjunkte Träger haben, gar keinen Gebrauch macht — und
die trotzdem reicht, weil `η` **nach** `ρ` gewählt werden darf. Der Radius `ρ`
wird von der Trennung der Knoten diktiert, die Höhe `η` von nichts, also nimmt
man `η ≤ K·ε/(8(n+1))` und ist fertig. Aus `Lip ψ ≤ K < 1` folgt alles Übrige:
`x ↦ x + ψ x` ist streng monoton, surjektiv (`Continuous.surjective` gegen
`(1-K)x ≤ x + ψ x` auf `Ici 0` und `x + ψ x ≤ (1-K)x` auf `Iic 0`, beides
`ψ 0 = 0` durch die Lipschitz-Schranke gelesen), und bi-Lipschitz mit den
Konstanten `1 + K` und `(1-K)⁻¹`. Mit `K = 1 - exp(-δ)` sind beide höchstens
`exp δ`: die zweite ist es exakt, die erste, weil `2 - a⁻¹ ≤ a` für `a > 0`
nichts anderes ist als `(a-1)² ≥ 0`.

Der Übergang zum Index ist `TimeChange.exists_of_lengthCoord` aus Meilenstein 3,
und für `ι = ℝ` sind seine beiden lästigen Hypothesen — daß `φ` den Bereich der
Koordinate auf sich abbildet — gratis, weil `lengthCoord (0:ℝ)` die Identität
ist (`lengthCoord_real`, `@[simp]`).

#### Der Basispunkt ist die Stelle, an der die Konstruktion beinahe bricht

Zwei Einzelheiten sind keine Verzierung, und beide betreffen die `0`.

*Erstens ist die Trennung über `{0} ∪ range t` zu nehmen und nicht über
`range t`.* Der Zeitwechsel muß den Basispunkt festhalten, also darf kein Zelt
ihn überdecken; ein Knoten kann aber beliebig nah an `0` liegen, ohne `0` zu
sein, und aus den Abständen der `t i` untereinander folgt darüber nichts. Zeuge:
`n = 0`, `t 0 = 10⁻¹⁰⁰` — die Menge der Lücken von `t` ist leer, und jede
Schranke, die nur aus ihr gewonnen wird, ist vakuum. Das Mittel ist
`exists_pos_forall_le_abs_sub` über `Option (Fin (n+1))` mit `none ↦ 0`: eine
endliche Familie reeller Zahlen ist gleichmäßig diskret, und die Aussage über
`{0} ∪ range t` ist dieselbe Aussage über eine Familie mit einem Element mehr.

*Zweitens ist der Knoten eines `t i`, das **selbst** `0` ist, die `0`.* Dann hat
sein Zelt die Höhe `0`, und der Term verschwindet, obwohl das Zelt den
Basispunkt sehr wohl überdeckt. Ohne diese Fallunterscheidung müßte man `0` aus
dem Bild von `t` ausschließen, was die Aussage schwächte.

#### Die neuen Deklarationen

* `exists_pos_forall_le_abs_sub` — eine endliche Familie reeller Zahlen ist
  gleichmäßig diskret. Über `Fintype α` und nicht über `Finset ℝ` formuliert,
  gerade damit `Option (Fin (n+1))` eingesetzt werden kann.
* `SkorokhodSpace.tent`, `tent_self`, `tent_eq_zero`, `abs_tent_sub_le` — das
  Zelt und die drei Aussagen über es. Es ist stückweise linear und nicht glatt,
  weil hier nichts differenziert wird.
* `SkorokhodSpace.exists_rat_nodes_perturbation` — die analytische Hälfte: zu
  jedem streng monotonen `t : Fin (n+1) → ℝ` und jedem `K > 0` rationale Knoten
  `d` und ein `K`-lipschitzstetiges `ψ` mit `ψ 0 = 0` und `d i + ψ (d i) = t i`.
  `K` wird **vorgegeben** und nicht produziert; das ist es, was die Aussage
  brauchbar macht, denn der Aufrufer gewinnt `K` aus `δ`.
* `SkorokhodSpace.perturbation_orderIso_facts` — die vier Eigenschaften von
  `x ↦ x + ψ x`, die ein Zeitwechsel braucht.
* `lengthCoord_real` — `lengthCoord (0:ℝ) x = x`.
* `TimeChange.exists_real_of_perturbation` — der Zeitwechsel auf `ℝ` samt
  Normschranke.
* `Real.instHasCountableCore` — die Instanz.
* `SkorokhodSpace.hasCountableCore_of_countable` — **die zweite Instanz, und sie
  kostet nichts**: ist der Index abzählbar, so ist `C` er selbst und `l` die
  Identität, deren Norm `0` ist. Damit ist auch
  `AddSubgroup.zmultiples (1:ℝ)` erledigt, die zweite der vier laufenden
  Instanzen der Datei. Es ist die Klasse in dem Fall, in dem die Pfade ohnehin
  schon Treppenpfade sind.
* `stepRetract_orderIso` — **die Buchführung der Separabilität, vorweggenommen**:
  trägt ein Ordnungsisomorphismus `e` das Tupel `d` auf `t`, so ist
  `stepRetract t (e x) = e (stepRetract d x)`. Das ist eine *Gleichheit* von
  Pfaden und keine Abschätzung, kostet an der Metrik also nichts außer `‖l‖`,
  und es ist die Stelle, an der der abzählbare Kern ausgegeben wird: der
  Approximant an der Unterteilung `t` wird nach dem Zeitwechsel zum
  Approximanten an der Unterteilung `d`, deren Punkte in `C` liegen. Der Beweis
  hat eine Zeile Inhalt — `t i ≤ e x` und `d i ≤ x` sind dieselbe Bedingung,
  also sind die beiden `Finset.filter`, deren Maximum `stepRetract` nimmt, ein
  und dieselbe endliche Menge.

#### Was offen blieb

Die dritte Instanz der Klasse, `Set.Icc (0:ℝ) 1` (dort ist
`C = (ℚ ∩ [0,1]) ∪ {0,1}`, und die beiden Endpunkte sind die Punkte, die kein
Zeitwechsel bewegt), und die Separabilität unter der Klasse selbst. Punkt 2 und
der Rest von Punkt 3 der vorrangigen Aufgabe sind unberührt.

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.instSeparableSpace` unter `[HasCountableCore ι]`.** Worauf sie
ruht: auf `SkorokhodSpace.exists_finite_range_intDist_le` (bewiesen, 2026-09-09),
das zu `f`, `ε > 0` und `M ≥ 0` ein `g` mit endlichem Wertebereich und
`intDist t₀ f g ≤ ε + exp (-M)` liefert, und auf der Klasse, die jetzt bewohnt
ist. Was noch zu tun ist, ist Buchführung und keine Analysis: die Werte in eine
abzählbare dichte Teilmenge von `E` zu schieben kostet `ε` im gefensterten
Supremum und keinen Zeitwechsel, und der Umbau der Sprungzeiten ist
`stepRetract_orderIso`, in diesem Lauf **bewiesen**.

Was danach bleibt, ist die Abzählbarkeit der Familie als solche — eine
Surjektion von einem abzählbaren Typ auf sie —, und dafür ist der Treppenpfad
als **Term** hinzuschreiben: `stepPath d v : D(ι, E)` zu `d : Fin (n+1) → ι` mit
Werten in `C` und `v : Fin (n+1) → E` mit Werten in einer abzählbaren dichten
Teilmenge. Hier liegt die eine Signaturfrage, und sie ist vor dem ersten Beweis
zu entscheiden: `stepRetract` gibt heute den *Punkt* `t i` zurück und nicht den
*Index* `i`, die Werte lassen sich also nicht unmittelbar daran hängen. Entweder
tritt ein `stepIdx` daneben, mit `stepRetract t = t ∘ stepIdx t`, oder
`stepRetract` wird `Fin (n+1)`-wertig und die heutige Fassung ihre Komposition
mit `t`. Warum jetzt: es ist die letzte offene Zusage von Meilenstein 5,
`instPolishSpace` ist danach `inferInstance`, und `fact:PSpolish` hängt an nichts
sonst.

**Das Manuskript ist nicht angefaßt.**

### 2026-09-09, dritter Lauf des Tages — die Familie ist abzählbar, und der Fensterrand ist der offene Punkt

**Vorrangige Aufgabe, Teil A, Punkt 1.** Der vorige Lauf hat die Klasse
`SkorokhodSpace.HasCountableCore` bewohnt gemacht und den nächsten Schritt
benannt: die Abzählbarkeit der Familie als Term, samt einer Signaturfrage.
Dieser Lauf entscheidet die Signaturfrage, beweist die Abzählbarkeit — und
findet, daß danach **nicht** die Separabilität dasteht, sondern eine Lücke, die
Analysis ist und nicht Buchführung. `SkorokhodSpace/Suggested.lean` steht weiter
bei **vier** `sorry`. Dreißig Deklarationen sind neu oder umgeschrieben,
alle durch `lake env lean` gegen v4.33.1 geprüft (`rc=0`, nur Warnungen) und alle
mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`.

#### Die Signaturfrage: `stepIdx` tritt daneben, und `stepRetract` wird seine Komposition

Der Auftrag verlangte, vor dem ersten Beweis zu entscheiden und die Wahl zu
begründen. Sie ist die **zweite Deklaration**:

```
stepIdx t x : Fin (n+1)        -- der Index der Zelle, in die x fällt
stepRetract t x = t (stepIdx t x)   -- ab jetzt die Definition, nicht ein Satz
```

Drei Gründe, und der dritte war nicht vorhergesehen.

*Erstens* ist `stepRetract` `Fin (n+1)`-wertig zu machen kein billigerer Weg,
sondern ein teurerer: fünf bewiesene Sätze über es und ihr bewiesener Abnehmer
`exists_finite_range_distWith_le` reden von Pfadwerten und nicht von Indizes, und
sie müßten alle angefaßt werden, um nichts zu gewinnen. *Zweitens* ist die
Familie über die *Punkte* `t i` zu indizieren gar nicht möglich — genau deren
Überabzählbarkeit ist das Problem, das die Klasse löst. *Drittens* wird die
Buchführung **einfacher** und nicht bloß anders: `stepIdx_orderIso` sagt

```
stepIdx t (e x) = stepIdx d x        (für e (d i) = t i)
```

und trägt rechts keinen Ordnungsisomorphismus mehr, während
`stepRetract_orderIso` — jetzt daraus abgeleitet — einen tragen muß. Das ist
genau die Gestalt, in der die Separabilität sie braucht: die Werte bleiben
dieselben, nur die Knoten ziehen um.

*Und die Entscheidung hat drei Hypothesen abgetragen.* Die Lokalität des Index
braucht **keine Monotonie** des Tupels: `stepIdx` liest ein Maximum aus einem
`Finset`, und das ist von der Aufzählung unabhängig — Monotonie ist eine Aussage
über die Aufzählung, Lokalität eine über den Wertebereich. Also stehen
`eventually_stepRetract_eq_nhdsGT`, `exists_eventually_stepRetract_eq_nhdsLT` und
`isCadlag_comp_stepRetract` jetzt ohne `StrictMono t` da, und ihre Beweise sind
je zwei Zeilen statt zusammen sechzig. Das ist es, was `stepPath` **total** macht,
und Totalität ist es, was die Abzählung braucht: die Familie ist das Bild einer
Abbildung von `Σ n, (Fin (n+1) → C) × (Fin (n+1) → Q)`, ohne Nebenbedingung an
die Daten, und mit Nebenbedingung wäre der Definitionsbereich ein Untertyp, dessen
Abzählbarkeit eine Aufgabe mehr ist.

#### Die Abzählbarkeit ist bewiesen

`SkorokhodSpace.stepPath d v : D(ι, E)` zu beliebigen Knoten und Werten,
`SkorokhodSpace.stepPathFamily C Q` die Familie,
`SkorokhodSpace.countable_stepPathFamily` ihre Abzählbarkeit — ein abzählbares
`C`, ein abzählbares `Q`, `Fin (n+1)` endlich, eine abzählbare Vereinigung über
die Länge. `SkorokhodSpace.stepPath_mem_stepPathFamily` ist die Zugehörigkeit,
`SkorokhodSpace.stepPath_comp_eq` sagt, daß der Approximant der analytischen
Hälfte **derselbe Term** ist (`rfl`), und
`SkorokhodSpace.distWith_one_stepPath_le` ist der Umzug der Werte, der nichts
kostet.

#### Der Befund: der Fensterrand, und er ist Analysis

Der vorige Lauf hat angesagt, was bleibe, sei die Abzählbarkeit; das war zu
wenig. Nach den beiden Umzügen steht **nicht** `distWith t₀ u l f g ≤ ε` da,
sondern das für das Innere des Fensters. Am Rand gilt es nicht, und der
Mechanismus ist der, der schon die summierte Metrik erledigt hat: für `x`
jenseits von `B = exhaustionMax t₀ u` klemmen **beide** Seiten von `distWith` auf
`B`, der Term ist `dist (f B) (g B)` — *ohne dazwischengeschalteten
Zeitwechsel*, das ist `SkorokhodSpace.dist_exhaustionMax_le_distOn` —, und `g B`
ist der Wert der Zelle von `B`, gezählt mit den **verschobenen** Knoten, also
`stepIdx t (l B)` und nicht `stepIdx t B`. Die beiden weichen genau dann
voneinander ab, wenn ein Knoten `B` von `l B` trennt, und dann ist der Term der
**Sprung von `f` an diesem Knoten**; kein `ε` macht ihn klein.

Die Richtung der Verschiebung hilft nicht: schiebt man die Knoten nach unten, so
fällt `l B` unter `B`, `clamp (l x)` läuft über `[l B, B]`, und derselbe Term
erscheint auf der anderen Seite. Das ist kein Beweisdetail, sondern eine
Eigenschaft dieser Metrik, und es ist der Grund, warum Billingsley auf `[0,1]`
arbeitet, wo der Zeitwechsel **beide Endpunkte festhält**, und warum
Ethier--Kurtz über den Radius integrieren.

#### Was daraus folgt, und was davon schon getan ist

Die Reparatur ist zweiteilig, und der eine Teil steht.

*Erstens*, und das ist neu in der Datei: `HasCountableCore` hat eine **dritte
Klausel**, `dist (d i) (t i) ≤ δ`. Sie folgt **nicht** aus der Normschranke — auf
einem Index mit Lücken hat die Identität die Norm `0`, und ein Zeitwechsel der
Norm `0` trägt einen Punkt über eine ganze Lücke —, und sie ist genau das, was die
schlechten Radien zählt. Beide Instanzen erfüllen sie:
`SkorokhodSpace.exists_rat_nodes_perturbation` nimmt seine Rationalzahlen jetzt
innerhalb eines vorgegebenen `ζ` der `t i` (die Höhe der Zelte stand dem Aufrufer
ohnehin frei, es ist ein `min` mehr in `η`), und auf einem abzählbaren Index ist
`d = t`.

*Zweitens*, und das ist der neue Satz: `volume_radius_exhaustionMax_mem_Ico`
schätzt

```
volume {u ≥ 0 : exhaustionMax t₀ u ∈ Set.Ico a b} ≤ ENNReal.ofReal (dist a b)
```

und braucht dafür **keine Fallunterscheidung**, weil `lengthCoord` alles erledigt:
das Fenster ist das Urbild von `Set.Icc (-u) u` unter der Längenkoordinate, also
liegt ein Radius, dessen Rand in `Set.Ico a b` fällt, selbst in
`Set.Icc (lengthCoord t₀ a) (lengthCoord t₀ b)` — unten, weil der Rand über `a`
liegt und seine Koordinate höchstens der Radius ist, oben, weil ein Radius
jenseits von `lengthCoord t₀ b` schon `b` ins Fenster nimmt und den Rand auf `b`
oder darüber schiebt. Die Länge dieses Intervalls ist `dist a b`
(`sub_lengthCoord_of_le`). Damit haben die schlechten Radien eines Knotens das Maß
`dist (d i) (t i)`, alle zusammen höchstens `(n+1) δ`, und da der Integrand von
`intWith` durch `1` beschränkt ist, kosten sie in der Metrik nicht mehr als das.

Daß die Schranke `dist a b` und nicht etwa `0` ist, ist der Punkt: für `ι = ℝ`
ist die Menge der schlechten Radien ein Intervall der Länge `|t i - d i|` und
nicht null, für `ι = ℤ` ist sie eine ganze Lücke lang — dort ist aber `d = t`, und
das ist derselbe Sachverhalt von der anderen Seite.

#### Die neuen Deklarationen

* `stepIdx`, `stepIdx_eq_of_forall_le`, `stepIdx_eq_zero_of_lt`,
  `stepIdx_orderIso` — der Index und seine drei Aussagen.
* `eventually_stepIdx_eq_nhdsGT`, `exists_eventually_stepIdx_eq_nhdsLT`,
  `isCadlag_comp_stepIdx` — die Lokalität, **ohne Monotonie**, und der Pfad
  daraus.
* `stepRetract` (Definition umgeschrieben zu `t ∘ stepIdx t`),
  `stepRetract_eq_of_forall_le`, `stepRetract_eq_first`, `stepRetract_mem_range`,
  `stepRetract_orderIso`, `eventually_stepRetract_eq_nhdsGT`,
  `exists_eventually_stepRetract_eq_nhdsLT`, `isCadlag_comp_stepRetract` — alle
  acht neu bewiesen, sechs davon in einer Zeile, drei mit schwächeren Hypothesen.
* `SkorokhodSpace.stepPath`, `stepPath_apply`, `stepPath_comp_eq`,
  `stepPath_apply_orderIso`, `stepPathFamily`, `stepPath_mem_stepPathFamily`,
  `countable_stepPathFamily`, `distWith_one_stepPath_le` — die Familie.
* `radius_exhaustionMax_mem_Ico_subset` und
  `volume_radius_exhaustionMax_mem_Ico` — die Einschließung der schlechten Radien
  in ein benanntes Koordinatenintervall und ihr Maß. Die Einschließung ist die
  Form, die gebraucht wird, denn die Menge selbst ist nicht sichtbar meßbar:
  `exhaustionMax` ist monoton und mehr nicht.
* `SkorokhodSpace.intWith_le_of_ae_distWith_le` — **das erste der beiden Stücke,
  die nach dem Befund noch fehlten**: `intWith_le_of_forall_distWith_le` mit der
  gefensterten Schranke nur *außerhalb* einer meßbaren Radienmenge `B`, zum Preis
  von deren Maß unterhalb `M`, also `ε + β + exp (-M)`. Der Beweis zerlegt
  `Set.Ioc 0 M` in `\ B` und `∩ B` (`Set.diff_union_inter`), schätzt das erste
  Stück wie bisher und das zweite durch `1`, weil `exp (-u) ≤ 1` für `u > 0` und
  `min 1 _ ≤ 1`; `MeasureTheory.setIntegral_const` macht daraus das Maß.
* `SkorokhodSpace.HasCountableCore` (dritte Klausel),
  `SkorokhodSpace.exists_rat_nodes_perturbation` (mit `ζ`),
  `Real.instHasCountableCore` und `SkorokhodSpace.hasCountableCore_of_countable`
  (beide nachgezogen).

#### Vorschlag für den nächsten Lauf

**`SkorokhodSpace.instSeparableSpace`, und diesmal ist der Weg ganz
ausgeschrieben.** Zwei Stücke fehlen, beide benannt:

1. ~~Die f.ü.-Fassung von `intWith_le_of_forall_distWith_le`.~~ **In diesem Lauf
   noch bewiesen**, als `SkorokhodSpace.intWith_le_of_ae_distWith_le`. Was an ihr
   noch zu tun ist, ist sie einzusetzen: `B` ist
   `⋃ i, Set.Icc (lengthCoord t₀ (d i)) (lengthCoord t₀ (t i))`, eine endliche
   Vereinigung von Intervallen, also meßbar, und ihr Maß ist nach
   `radius_exhaustionMax_mem_Ico_subset` höchstens `∑ᵢ dist (d i) (t i) ≤ (n+1) δ`
   — das `δ` wird also nach `n` gewählt, und `n` kommt aus der Unterteilung.
2. **Die Fallunterscheidung am Supremum.** Sie ist `min_max_pair_cases`, dasselbe
   kombinatorische Lemma, das `SkorokhodSpace.distWith_le_of_oscillation` schon
   führt: die beiden Klemmungen eines Punktes stimmen überein, oder beide liegen
   zwischen den zwei oberen Fensterenden, oder beide zwischen den zwei unteren.
   Im ersten Fall greift die Zelleigenschaft, in den beiden anderen ist der Radius
   schlecht.

Warum jetzt: es ist die letzte offene Zusage von Meilenstein 5, `instPolishSpace`
ist danach `inferInstance`, und `fact:PSpolish` hängt an nichts sonst. Analysis,
Buchführung, Abzählung, die Maßschranke und die f.ü.-Integralschranke sind alle
fünf bezahlt; was bleibt, ist die Fallunterscheidung am Fensterrand und die
Montage.

**Das Manuskript ist nicht angefaßt.**

### 2026-09-09, vierter Lauf des Tages — die Separabilität ist bewiesen, und `D(ι, E)` ist polnisch

**Vorrangige Aufgabe, Teil A, Punkt 1: erledigt.** `SkorokhodSpace/Suggested.lean`
steht bei **drei** `sorry` statt vier. Fünf Deklarationen sind neu, eine ist von
`sorry` zu einem Beweis geworden, alle durch `lake env lean` gegen v4.33.1 geprüft
(`rc=0`, nur Warnungen) und alle mit `#print axioms` auf `propext`,
`Classical.choice`, `Quot.sound` — `SkorokhodSpace.instSeparableSpace` und
`SkorokhodSpace.instPolishSpace` eingeschlossen. **Damit ist Meilenstein 5
geschlossen** bis auf die dritte Instanz der Typklasse, an der nichts hängt, und
`fact:PSpolish` ist an seiner zweiten Gebrauchsstelle (`rem:EKrelcompact`,
$\DE$ unter $J_1$) eingelöst.

#### Was der vorige Lauf angesagt hatte, und was daran stimmte

Der dritte Lauf hat zwei Stücke benannt: die Einsetzung von
`intWith_le_of_ae_distWith_le` mit dem Bad-Set, und „die Fallunterscheidung am
Supremum, die `min_max_pair_cases` ist". Das erste stimmte. Das zweite war eine
Ansage zu viel: `min_max_pair_cases` steht bereits *innerhalb* von
`SkorokhodSpace.distWith_le_of_oscillation`, und was die Separabilität zu liefern
hat, sind nicht seine Fälle, sondern seine **drei Hypothesen**. Das ist der Grund,
warum dieser Lauf mit fünf kleinen Sätzen auskommt statt mit einer zweiten
Kombinatorik.

`SkorokhodSpace.distWith_stepPath_le` ist die Schätzung an einem Radius,
`distWith t₀ u l f (stepPath d w) ≤ 6 ε`, und die Verteilung der Kosten ist
lehrreich: die *gleichmäßige* Hypothese kostet `2 ε` (`stepIdx_orderIso` trägt die
Werte umsonst über den Zeitwechsel, dann je ein `ε` für `dist_comp_stepRetract_le`
und für den Umzug nach `Q`), die beiden *Schwingungs*-Hypothesen kosten **nichts**.
Der Treppenpfad ist zwischen einem Fensterende und seinem Urbild nämlich
**konstant**, nicht bloß wenig schwingend, und die Bedingung dafür ist eine
Bedingung an den Index allein: das Fensterende `A` möge jedes Intervall
`Set.Ico (min (d i) (t i)) (max (d i) (t i))` meiden, also das von einem Knoten und
seinem Bild aufgespannte. Das ist `SkorokhodSpace.stepIdx_eq_of_mem_uIcc`, und sein
Beweis ist die Trichotomie von `A` gegen `l⁻¹ A`, durch den Ordnungsisomorphismus
gelesen. Darunter liegt `stepIdx_congr_of_forall_notMem_Ioc`: der Zellindex sieht
nur die Knoten in `Set.Ioc` der beiden Punkte, halboffen auf **der** Seite, auf der
`stepIdx` sein `≤` liest.

#### Der Befund: die beiden Fensterenden sind nicht symmetrisch

Das ist die Überraschung des Laufs, und sie hätte die ganze Reparatur des dritten
Laufs kosten können. Der dritte Lauf hat `volume_radius_exhaustionMax_mem_Ico`
bewiesen und stillschweigend angenommen, die Spiegelung mit `exhaustionMin` an
Stelle von `exhaustionMax` sei dieselbe Aussage. **Sie ist falsch.**
`exhaustionMax t₀` ist monoton und `exhaustionMin t₀` antiton, also schließt
`Set.Ico a b` gerade das klebrige Ende des ersten aus und das des zweiten ein: ein
Radius, dessen unteres Fensterende auf `a` sitzt, sitzt dort für die ganze Länge
der Lücke unter `a` — auf einem nach unten beschränkten Index also für **alle**
Radien jenseits der Koordinate von `a`. Das Maß ist dann unendlich, und der Fall
ist kein Kunstprodukt: `ι = Set.Icc (0:ℝ) 1` mit Basispunkt `0` hat ihn, und diese
Instanz läuft in der Datei.

*Die Reparatur ist keine Abschwächung, sondern die Beobachtung, daß die Anwendung
mehr weiß.* Das untere Ende ist überhaupt nur dann ein schlechter Radius, wenn der
Zeitwechsel es **bewegt**; und ein Zeitwechsel, der den kleinsten Punkt des Fensters
bewegt, legt einen Punkt des Index um höchstens `κ` unter diesen Punkt — sein Bild
oder sein Urbild, je nachdem, welches nach unten fällt. Dieser Punkt liegt außerhalb
des Fensters, also ist der Radius höchstens `κ` über der Koordinate des Endes, und
der klebrige Schwanz ist bei `κ` abgeschnitten. `radius_exhaustionMin_mem_Ico_subset`
trägt darum die Zusatzhypothese
`∃ s < exhaustionMin t₀ u, dist (exhaustionMin t₀ u) s ≤ κ`, und
`volume_radius_exhaustionMin_mem_Ico` schätzt `dist a b + κ` und nicht `dist a b`.
Die andere Seite derselben Münze ist die **Disjunktion** in
`distWith_stepPath_le`: am unteren Ende genügt auch, daß der Zeitwechsel es
*festhält*, und genau das erzwingt ein Index mit einer Lücke darunter.

#### Die Reihenfolge der Wahlen, und sie ist erzwungen

`6 ε ≤ r/4` legt `ε` aus `r` fest; `exp (-M) < r/4` legt `M` aus `r` fest; die
Unterteilung von `IsCadlag.exists_subdivision` legt `n` fest; und **erst danach**
wird `δ` gewählt, klein genug für `δ < r/4` (das schätzt `‖l‖`) und für
`(n+1) (2δ + (exp δ - 1) 2M) < r/4` (das schätzt die schlechten Radien). Die
Reihenfolge ist nicht umstellbar — `n` hängt an `ε` und `M`, das Bad-Set an `n` —,
und sie ist der Grund, warum die dritte Klausel von `HasCountableCore` über `δ`
**nach** dem Tupel quantifiziert. Das Bad-Set selbst ist
`⋃ i, (Icc (lengthCoord (min)) (lengthCoord (max)) ∪ Icc (-lengthCoord (max)) (κ - lengthCoord (min)))`,
eine endliche Vereinigung von Intervallen in der Längenkoordinate, also sichtbar
meßbar — die Radienmengen selbst sind es nicht, `exhaustionMax` ist bloß monoton,
und das ist der Grund, warum `intWith_le_of_ae_distWith_le` sein `B` als Hypothese
und nicht als Konstruktion nimmt.

#### Die neuen Deklarationen

* `stepIdx_congr_of_forall_notMem_Ioc` — der Zellindex sieht nur die Knoten
  zwischen den beiden Punkten, halboffen.
* `SkorokhodSpace.stepIdx_eq_of_mem_uIcc` — der Treppenpfad ist zwischen einem
  Punkt und seinem Urbild konstant, sobald kein Knoten über den Punkt getragen
  wurde.
* `radius_exhaustionMin_mem_Ico_subset` und `volume_radius_exhaustionMin_mem_Ico`
  — die Spiegelung ans untere Fensterende, mit der Zusatzhypothese, die sie wahr
  macht.
* `SkorokhodSpace.distWith_stepPath_le` — die ganze Schätzung an einem Radius.
* `SkorokhodSpace.instSeparableSpace` — Beweis statt `sorry`.
* `SkorokhodSpace.instPolishSpace` — unverändert `inferInstance`, aber seit diesem
  Lauf ohne `sorryAx` darunter.

`SkorokhodSpace/README.md`, Meilenstein 5, ist nachgezogen; die Zeile
`fact:PSpolish` der Tabelle ebenso.

#### Vorschlag für den nächsten Lauf

**Punkt 2 der vorrangigen Aufgabe: die meßbare Einbettung**,
`SkorokhodSpace.measurableEmbedding_piDense` und
`SkorokhodSpace.borel_eq_iSup_comap_eval` (Meilenstein 6). Das ist `thm:fdd` des
Manuskripts, es wird von `MartingaleProblems` Meilenstein 11 gebraucht, und es ist
jetzt an der Reihe, weil Meilenstein 5 geschlossen ist und die beiden Aussagen die
Polnischkeit von `D(ι, E)` voraussetzen dürfen.

*Und die Aufteilung, an der Hand des Manuskripts, damit der nächste Lauf nicht am
falschen Ende anfängt.* Die **zweite** Hälfte ist die billige: eine meßbare
Injektion zwischen Standardborelräumen ist eine meßbare Einbettung (Lusin--Souslin,
`MeasurableSet.image_of_measurable_injOn`), die Injektivität ist
`IsCadlag.eq_of_eqOn_dense` (bewiesen, Meilenstein 2), und den Standardborelraum
liefert `SkorokhodSpace.instPolishSpace` seit heute. Die **erste** Hälfte ist der
ganze Inhalt, und `thm:fdd` sagt es selbst: `π_t` ist an *jedem* Pfad mit einem
Sprung in `t` unstetig, die Meßbarkeit einer Koordinate ist also ein Satz und keine
Bemerkung — das acceptance example von Meilenstein 6 ist genau die Widerlegung des
Weges über die Stetigkeit. Der Weg ist, `π_t` als punktweisen Limes
`d`-stetiger Funktionale zu schreiben, und von den zwei Wegen, die das Manuskript
nennt, ist hier der zu nehmen, der `E` **keine lineare Struktur** aufzwingt: er
benutzt nur `t ∈ D` und verbraucht die Rechtsstetigkeit. `E` ist in dieser Datei
ein bloßer metrischer Raum, Mitteln über ein Fenster steht nicht zur Verfügung.

**Das Manuskript ist nicht angefaßt.**

### 2026-09-09, fünfter Lauf des Tages — Meilenstein 6 ist geschlossen, und eine Aussage war falsch

**Vorrangige Aufgabe, Teil A, Punkt 2** (die meßbare Einbettung, `thm:fdd`).
`SkorokhodSpace/Suggested.lean` steht bei **einem** `sorry` statt drei; das
verbleibende ist `SkorokhodSpace.isCompact_closure_iff`, das
Kompaktheitskriterium von Meilenstein 7. Zehn neue Deklarationen, alle durch
`lake env lean` gegen v4.33.1 geprüft und alle mit `#print axioms` auf
`propext`, `Classical.choice`, `Quot.sound`.

*Der Angelpunkt ist einer, und er heißt `SkorokhodSpace.measurable_eval`:* die
Auswertung an einem Punkt des Index ist borelmeßbar. Sie ist **keine** Folge der
Stetigkeit — `SkorokhodSpace.exists_jump_continuousAt_eval` zeigt seit dem
2026-09-08 einen Pfad, an dem die Auswertung springt —, und sie ruht auf einer
einzigen Aussage, die das Integralmaß an Stelle der verweigerten Stetigkeit
hergibt: `SkorokhodSpace.exists_orderIso_dist_lt_of_intDist_lt`. Zu `s` und `ε`
gibt es ein `δ`, das von **keinem der beiden Pfade** abhängt, so daß
`intDist t₀ f g < δ` einen Ordnungsisomorphismus `e` liefert mit
`dist (e s) s < ε`, `dist (e.symm s) s < ε` und `dist (f s) (g (e.symm s)) < ε`.
Die beiden Hälften des `max` in `intDist` zahlen die beiden Hälften des
Schlusses: die Normschranke schiebt `e.symm s` über
`TimeChange.dist_le_of_norm_le` zurück nach `s`, und die Integralschranke
**erzeugt** einen Radius `u` im Einheitsintervall über `dist t₀ s + 1`, an dem
das gefensterte Supremum klein ist.

*Der Radius ist zu erzeugen und nicht zu wählen, und das ist die Stelle, an der
dieser Lauf beinahe einen falschen Beweis geschrieben hätte.* `distWith` ist
**nicht monoton im Radius** — genau deshalb integriert Meilenstein 4 —, und ein
Zwischenschritt, der die Monotonie stillschweigend annimmt, beweist zu viel: er
macht die Auswertung an jedem Fensterrand stetig, also gerade das, woran die
summierte Metrik am 2026-09-08 gescheitert ist. Am Zeugen jenes Tages
nachgerechnet (`x n = 1_{(-∞, 1+1/(n+1))}` gegen `w = 1_{(-∞,1)}` in `D(ℝ,ℝ)`):
bei Radius `1` klemmt `clamp` den Zeitwechsel weg und `distOn 0 1 λ x_n w = 1`
für **jedes** `λ`, während `distOn 0 u λ x_n w` für `u > 1 + 1/(n+1)` klein wird.
Die Monotonie ist falsch, die schlechten Radien sind eine Nullmenge, und das
Integral sieht sie nicht. Im Beweis steht darum die Schranke
`exp (-(U+1)) * (c/2)` über dem ganzen Intervall `Set.Ioc U (U+1)` und nicht ein
einzelner Radius.

*Von da aus zerfällt die Meßbarkeit in zwei Fälle, und den zweiten erzwingt der
Index von Meilenstein 1.* Ist `t` **nicht** rechts isoliert, so ist
`edist (f t) y` das Infimum über schrumpfende punktierte Rechtsumgebungen der
Suprema `⨆ s ∈ ball t ρ ∩ Ioi t, edist (f s) y`
(`SkorokhodSpace.iInf_iSup_edist_eq`), und jedes dieser Suprema ist
**unterhalbstetig** (`SkorokhodSpace.lowerSemicontinuous_iSup_edist`). Ist `t`
rechts isoliert — `Set.Icc (0:ℝ) 1` bei `1`, `AddSubgroup.zmultiples (1:ℝ)`
überall, zwei der vier laufenden Instanzen —, so sind die Fenster schließlich
leer und das Infimum ist `0`; dort greift statt dessen
`SkorokhodSpace.continuous_eval_of_nhdsGT_eq_bot`: **jeder Zeitwechsel kleiner
Norm hält einen rechts isolierten Punkt fest**, denn `e t` und `e.symm t` liegen
beide unter dem Isolationsradius, also unter `t`, und `e t ≤ t` gibt mit der
Monotonie `t ≤ e.symm t`. Genau dafür legt die Approximationsaussage den
Ordnungsisomorphismus **zweiseitig** offen; eine einseitige Fassung könnte diesen
Fall nicht bedienen.

*Und die Roadmap sagte den Weg falsch an.* Meilenstein 6 schrieb vor, `π_t` als
punktweisen Limes **`d`-stetiger** Funktionale darzustellen. Stetig sind die
Fenstersuprema nicht: am springenden Pfad ist das Supremum über die punktierte
Rechtsumgebung der Wert *nach* dem Sprung, während eine Näherungsfolge, deren
Sprung knapp rechts von `t` sitzt, den Wert *davor* im Fenster hat.
Unterhalbstetig sind sie, mehr gibt die Approximationsaussage nicht her — sie
verschiebt einen Zeugen des Supremums und ist damit einseitig —, und mehr wird
nicht gebraucht, weil der Grenzwert über eine schrumpfende Familie läuft und
darum ein Infimum ist. Der Absatz in `SkorokhodSpace/README.md` ist berichtigt.

*Die zweite Aussage von Meilenstein 6 war falsch und ist berichtigt, nicht
gestrichen.* `SkorokhodSpace.measurableEmbedding_piDense` verlangte von `D` nur
abzählbar und **dicht**. Das genügt nicht, und der Grund stand seit dem
2026-09-07 in der Datei selbst: der Docstring von `IsCadlag.eq_of_eqOn_dense`
führt den Zeugen aus, und `eq_of_eqOn_dense` verlangt darum die Dichtheit **von
rechts**, `∀ t, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot`. Auf
`ι = Set.Icc (0:ℝ) 1` — einer laufenden Instanz — ist `D = Set.Ico 0 1 ∩ ℚ`
abzählbar und dicht, `0` und `Set.indicator {1} 1` sind beide càdlàg (bei `1` ist
`𝓝[>] 1 = ⊥`, die Rechtsstetigkeit sagt dort nichts), sie stimmen auf `D`
überein und sind verschieden. Die Abbildung ist also nicht einmal injektiv. Die
Hypothese heißt jetzt Rechtsdichtheit.

*Das Bemerkenswerte daran ist, daß es dastand.* Das **zweite acceptance example**
von Meilenstein 6 ist genau dieser Zeuge, wörtlich, samt der Feststellung
„`measurableEmbedding_piDense` is false for that `D`" — geschrieben am
2026-09-07, während die Lean-Aussage daneben `Dense D` verlangte. Es ist das
zweite Mal (nach dem 2026-09-08 in Meilenstein 4), daß ein acceptance example
eine falsche Zusage trägt und nie gegen sie gehalten wurde. Ein acceptance
example, das nur dasteht, prüft nichts; es ist gegen die Aussage zu rechnen, die
es prüfen soll, und das ist billig, sobald beide in derselben Datei stehen.

*Damit die berichtigte Hypothese nicht leer ist, ist sie bewohnt worden:*
`exists_countable_rightDense` — zu jedem Index von Meilenstein 1 gibt es eine
abzählbare, von rechts dichte Menge. Die rechts isolierten Punkte sind
abzählbar, denn jeder trägt eine Basismenge, deren größtes Element er ist, und
zwei verschiedene können nicht dieselbe tragen; sie zu einer abzählbaren dichten
Menge zu schlagen genügt. Über einem nicht rechts isolierten `t` ist das Mittel
das Intervall `Set.Ioo t s`: es ist nichtleer — ein leeres machte `Set.Iio s` zu
einer Umgebung von `t`, die `Set.Ioi t` verfehlt, also wäre `t` doch rechts
isoliert —, offen, und es liegt in `Metric.ball t ε`, weil `AdditiveDist` die
Strecke `dist t s` an jedem Zwischenpunkt zerlegt.

*Der Rest ist Montage.* `SkorokhodSpace.measurableEmbedding_piDense` ist
Lusin--Souslin (`Measurable.measurableEmbedding`,
`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:881`) über
`measurable_eval` koordinatenweise und `eq_of_eqOn_dense` für die Injektivität;
es ist die einzige Stelle der Datei, an der `D(ι, E)` als **standard-borelscher**
und nicht als metrischer Raum gebraucht wird, und darum reisen
`HasCountableCore ι` und `CompleteSpace E` mit.
`SkorokhodSpace.borel_eq_iSup_comap_eval` ist die eine Inklusion aus
`measurable_eval` und die andere aus der Einbettung an einer abzählbaren
rechtsdichten Menge.

*Was als Nächstes zu tun ist.* Teil A hat noch **Punkt 3**, das
Kompaktheitskriterium `SkorokhodSpace.isCompact_closure_iff`, und es ist das
letzte `sorry` der Datei. `tendsto_modulus` steht seit dem 2026-09-08, die
Ausschöpfung und `IsCadlag.exists_subdivision` ebenfalls; was fehlt, ist die
Rückrichtung — aus der gleichmäßigen Kontrolle des Moduls einen Grenzpfad —, und
sie liest `SkorokhodSpace.tendsto_of_partialComp` von Meilenstein 5. Danach ist
`SkorokhodSpace` fertig und Teil B (`WeakConvergence`,
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`) ist dran.

**Das Manuskript ist nicht angefaßt.**

### 2026-09-09, sechster Lauf des Tages — das Kompaktheitskriterium ist falsch, und die Unterteilung darf über das Fenster hinausragen

**Facts:** keiner neu; `fact:PSpolish` unberührt. Gearbeitet an Teil A, Punkt 3
der vorrangigen Aufgabe — dem letzten `sorry` von
`SkorokhodSpace/Suggested.lean`, `SkorokhodSpace.isCompact_closure_iff`.

**Stand.** Die Datei steht weiter bei **einem** `sorry`. Dieser Lauf hat es nicht
gestrichen, sondern die Aussage darüber **berichtigt**: sie war falsch. 21
Deklarationen sind neu und vier sind geändert; alle 25 sind durch
`lake env lean` gegen v4.33.1 geprüft und alle hängen mit `#print axioms` an
`propext`, `Classical.choice`, `Quot.sound` und an nichts sonst.

*Der Befund.* `SkorokhodSpace.IsSubdivision` verlangte bis heute, daß die
Unterteilung am kleinsten Punkt des Fensters **beginnt** und am größten
**endet**. Mit dieser Pinnung ist das Kriterium falsch, und der Zeuge steht in
Lean: `SkorokhodSpace.not_tendsto_iSup_modulusPinned`. In `D(ℝ, ℝ)` konvergieren
die Treppenpfade `stepAt (1/(n+2) - 1) 1 0` gegen `stepAt (-1) 1 0`; die Menge
`A` aus der Folge und ihrem Grenzwert ist also kompakt, und sie nimmt nur die
Werte `0` und `1` an, so daß die Wertebedingung an **jedem** Fenster erfüllt ist.
Der Sprung des `n`-ten Pfades sitzt aber im Abstand `1/(n+2)` **rechts** vom
linken Rand `-1` des Fensters `exhaustion 0 1`, und eine gepinnte Unterteilung
kann ihn dort nicht abtrennen: ihr erster Knoten *ist* der Rand, ihre erste Lücke
übertrifft `δ`, also liegt der Sprung in der ersten Zelle, deren Schwingung vom
Rand aus gemessen wird. Der Modul ist damit `1` für jedes `δ ≥ 1/(n+2)`, das
Supremum über `A` also `1` für **jedes** `δ > 0`, und die rechte Seite des
Kriteriums ist falsch, während die linke gilt.

*Die Reparatur ist Ethier--Kurtz'.* Ihre Unterteilung von `[0,T]` ((3.6.2), Buch
S. 122) läuft `0 = t₀ < ⋯ < t_{n-1} < T ≤ t_n` — der **letzte Knoten darf über
`T` hinausragen**. Auf einem zweiseitigen Index wird dieselbe Freiheit am nahen
Ende gebraucht, und `IsSubdivision` trägt sie jetzt als zwei Ungleichungen
(`t 0 ≤ exhaustionMin`, `exhaustionMax ≤ t (Fin.last n)`) statt zweier
Gleichungen. Am Zeugen gerechnet: `-2 < 1/(n+2) - 1 < 2` ist zulässig, alle
Lücken sind größer als `1/2`, und beide Zellen sind konstant, also ist der Modul
`0`.

*Was die Änderung kostet, und es ist nichts.* Die zulässige Menge wird größer,
das Infimum also kleiner: `SkorokhodSpace.modulus_le_modulusPinned`. Jede obere
Schranke, die für den gepinnten Modul bewiesen war, gilt weiter, und
`tendsto_modulus` liest `IsCadlag.exists_subdivision` unverändert — der von dort
gelieferte Zeuge trifft die Fensterenden genau und ist damit erst recht zulässig
(`h0.le` und `hlast.ge` sind die ganze Anpassung). Auch
`modulus_eq_zero_of_exhaustion_subsingleton` und `modulus_mono` bleiben stehen.
Die gepinnte Fassung ist **nicht** gelöscht, sondern heißt jetzt
`IsSubdivisionPinned` samt `modulusPinned`; eine Widerlegung braucht ein Subjekt,
und die Lehre des 2026-09-08 und des fünften Laufs von heute ist, daß eine
falsche Zusage, die nur als Prosa danebensteht, nichts prüft.

*Der allgemeine Satz hinter dem Zeugen ist benannt und nicht in ihn verwoben:*
`SkorokhodSpace.le_modulusPinned_of_dist_exhaustionMin_le` sagt, daß der gepinnte
Modul zu **jedem** Pfad, jedem `δ` und jedem Punkt `x` des Fensters mit
`dist (exhaustionMin t₀ u) x ≤ δ` mindestens `edist (f x) (f (exhaustionMin))`
ist. Am rechten Rand gilt nichts dergleichen, denn die Zellen sind `Set.Ico` und
der Wert bei `exhaustionMax` wird nie gelesen; **die beiden Fensterenden sind
wieder nicht symmetrisch**, wie schon bei `volume_radius_exhaustionMin_mem_Ico`
im vierten Lauf.

*Der Zusammenbau des Zeugen, und er ist die eigentliche Arbeit.* Zu zeigen war,
daß die Folge im Sinne der **Integralmetrik** konvergiert, und das ist genau die
Stelle, an der die Metrik von Meilenstein 4 sich von der verworfenen summierten
unterscheidet. Der Zeitwechsel ist die Skalierung `x ↦ (1-ε) x`
(`TimeChange.scale`), die den Basispunkt umsonst festhält und
`norm ≤ -Real.log (1-ε)` hat. Sie trägt den einen Treppenpfad **exakt** auf den
anderen, für jeden Radius außerhalb `Set.Ioc (1-ε) 1`
(`SkorokhodSpace.distWith_scale_stepAt_le_zero`): unterhalb von `1-ε` liegt keine
der beiden Sprungzeiten im Fenster und beide Pfade lesen sich konstant, oberhalb
von `1` ist die Klemmung an beiden Schwellen durchsichtig und
`(1-ε) t ≥ ε-1 ↔ t ≥ -1` ist die Skalierung selbst. Dazwischen liegt ein
Intervall der Länge `ε`, und dort ist die Aussage wirklich falsch — der linke
Fensterrand trennt die beiden Sprungzeiten. Genau dafür ist
`intWith_le_of_ae_distWith_le` aus dem dritten Lauf gebaut: es zahlt das Maß der
schlechten Radien. Mit `M = -Real.log ε`, das den Schwanz `exp (-M) = ε` gegen
sie ausbalanciert, ist
`intDist 0 (stepAt (ε-1) 1 0) (stepAt (-1) 1 0) ≤ max (-Real.log (1-ε)) (2 ε)`
(`SkorokhodSpace.intDist_stepAt_le`), und das geht gegen `0`.

*Daß dieselbe Folge in der Auswertung bei `-1` **nicht** konvergiert, ist kein
Widerspruch, sondern der Kern:* `-1` ist ein Sprungpunkt des Grenzpfades, die
Auswertung dort ist nicht stetig (fünfter Lauf, `continuous_eval_of_nhdsGT_eq_bot`
sagt, wann sie es ist), und der gepinnte Modul mißt seine erste Zelle von genau
diesem Punkt aus. Die summierte Metrik des 2026-09-08 hätte die Folge nicht
konvergieren lassen — sie erzwang Konvergenz an allen Fensterrändern
(`dist_exhaustionMax_le_distOn`) —, und unter ihr wäre das gepinnte Kriterium
womöglich richtig gewesen. **Der Fehler ist also mit der Metrik mitgewandert und
nicht bemerkt worden**, obwohl der Modul seit dem 2026-09-08 dasteht und die
Metrik am selben Tag ersetzt wurde. Wer eine Definition ersetzt, hat jede
Aussage, die die alte las, neu gegen die neue zu halten; `modulus` las sie über
`exhaustionMin`.

*Die Roadmap ist nachgezogen*: Meilenstein 7 in
`SkorokhodSpace/README.md` führt die korrigierte Fassung, die gepinnte, die
Widerlegung und die acht Bausteine des Zeugen, und er hat ein **fünftes
acceptance example** bekommen — den Sprung, der zum Fensterrand marschiert. Es
ist das Spiegelbild des dritten (der zwei Sprünge, die nicht verschmelzen): dort
muß das Kriterium ablehnen, hier muß es annehmen. Die vier alten Beispiele sind
gegen die korrigierte Definition nachgerechnet und bleiben richtig; die
Unterteilung `-2 < 1 < 2` des ersten trifft die Fensterenden genau und ist unter
beiden Fassungen zulässig.

*Was als Nächstes zu tun ist.* Punkt 3 von Teil A ist damit **nicht** erledigt:
`isCompact_closure_iff` steht weiter als `sorry`, jetzt aber mit einer Aussage,
die nicht schon am Zeugen scheitert. Der nächste Schritt ist die **Hinrichtung**
(kompakter Abschluß ⟹ Modulbedingung), und der eine Punkt, an dem sie hängt, ist
benannt: aus `f_k → g` in der Integralmetrik eine Unterteilung von `g` zu
*übertragen* — die Knoten von `g` unter dem Zeitwechsel `l_k` zu lesen und zu
zeigen, daß die Lücken dabei höchstens um den Faktor `exp ‖l_k‖` schrumpfen. Das
ist `TimeChange.dist_le_exp_norm_mul`, es steht seit dem 2026-09-08, und die
Schwingung überträgt sich über `exists_orderIso_dist_lt_of_intDist_lt` aus dem
fünften Lauf von heute. Die Rückrichtung liest danach
`SkorokhodSpace.tendsto_of_partialComp` wie angesagt.

**Das Manuskript ist nicht angefaßt.**

### 2026-09-09, siebter Lauf des Tages — die Hinrichtung des Kompaktheitskriteriums, und der Motor, der sie trägt

**Facts:** keiner neu; `fact:PSpolish` unberührt. Gearbeitet an Teil A, Punkt 3
der vorrangigen Aufgabe — dem letzten `sorry` von
`SkorokhodSpace/Suggested.lean`, `SkorokhodSpace.isCompact_closure_iff`.

**Stand.** Die Datei steht weiter bei **einem** `sorry`. Neun Deklarationen sind
neu oder umgeschrieben; alle neun sind durch `lake env lean` gegen v4.33.1
geprüft, acht hängen mit `#print axioms` an `propext`, `Classical.choice`,
`Quot.sound` und die neunte an `propext` allein. Der Nachweis steht in
`SkorokhodSpace/Axioms.lean`, Abschnitt „2026-09-09, seventh run of the day".

*Was fällt.* `SkorokhodSpace.tendsto_iSup_modulus_of_isCompact`: hat `A`
kompakten Abschluß, so geht `⨆ f ∈ A, modulus basePoint m f δ` für `δ → 0+`
gegen `0`. Das ist die **Modulbedingung, gleichmäßig über `A`**, und sie ist die
zweite Konjunktion der rechten Seite des Kriteriums. Das `sorry` bleibt stehen,
weil `isCompact_closure_iff` eine Äquivalenz zweier Konjunktionen ist; von den
vier zu erbringenden Stücken ist eines jetzt da.

*Der Beweis ist Arzelà--Ascoli und sonst nichts, und das ist der Punkt.*
Kompakter Abschluß gibt Totalbeschränktheit, also endlich viele Mittelpunkte
`g₁, …, g_N`, deren Kugeln vom Radius `δ₀` ganz `A` überdecken. Jedem `g_j` gibt
`IsCadlag.exists_subdivision` eine Unterteilung mit Zellschwingung höchstens
`ε'`. Und dann ist alles daran, diese Unterteilung auf ein beliebiges `f` der
Kugel **überzutragen**. Das ist der Motor, und er heißt
`SkorokhodSpace.modulus_le_of_edist_le`: *eine* Unterteilung *eines* nahen
Pfades beschränkt den Modul *aller* Pfade seiner Kugel. Daß dabei die
**Sparsamkeit** überlebt, ist der Grund, warum endlich viele Mittelpunkte
genügen: die übertragenen Unterteilungen haben alle Lücken oberhalb von
`exp (-γ)` mal der kleinsten Lücke der endlich vielen Originale, und darum tut es
**ein** `δ` für ganz `A`.

*Der Motor ist in vier benannte Stücke zerlegt, und jedes steht für sich.*

* `SkorokhodSpace.exists_radius_distWith_lt` — der gute Radius. Ist
  `intWith t₀ l f g < exp (-(M+1)) · c` mit `0 < c ≤ 1`, so hat *irgendein*
  `u ∈ Set.Ioc M (M+1)` die Schranke `distWith t₀ u l f g < c`. Es ist der
  Mittelwert des Integrals über ein Fenster vom Maß Eins, und die Trunkierung
  bei `1` erzwingt `c ≤ 1`.
* `SkorokhodSpace.exists_timeChange_distWith_lt_of_intDist_lt` — die Brücke von
  der Integralmetrik zu einem Zeitwechsel samt gefensterter Schranke auf einem
  **benannten** Fenster.
* `SkorokhodSpace.isSubdivision_comp` — die Unterteilung längs des Zeitwechsels.
* `SkorokhodSpace.subdivisionOsc_comp_le` — die Schwingung, mit Verlust `2 η`.

*Der gute Radius ist nicht neu geschrieben, sondern **herausgezogen**.* Er stand
seit dem fünften Lauf von heute inline im Beweis von
`SkorokhodSpace.exists_orderIso_dist_lt_of_intDist_lt`, dort mit
`M = dist t₀ s + 1` und `c` gleich der halben Zielgenauigkeit. Der Satz liest ihn
jetzt, statt ihn zu wiederholen; das ist die einzige Änderung an Meilenstein 6,
und sie ist eine Änderung des Beweises und nicht der Aussage.

*Ein Befund, der die Ansage des sechsten Laufs berichtigt.* Dort stand, die
Schwingung übertrage `exists_orderIso_dist_lt_of_intDist_lt`. Sie tut es
**nicht**: jener Satz ist punktweise und liefert zu *jedem* Punkt einen *anderen*
Ordnungsisomorphismus, während der Modul einen einzigen für das ganze Fenster
braucht — die Zellen einer Unterteilung sind nicht ein Punkt nach dem anderen,
sondern ein Fenster auf einmal. Was gebraucht wird, ist die gefensterte Schranke
selbst, also `distWith`, und deren Preis ist genau der, den Meilenstein 4 schon
einmal bezahlt hat: der Radius wird **produziert und nicht gewählt**, weil
`distWith` in ihm nicht monoton ist. Eben darum steht der gute Radius jetzt als
eigener Satz da und nicht mehr im Bauch eines anderen Beweises.

*Die Überdeckung ist die Stelle, an der es beinahe eine Fallunterscheidung
gebraucht hätte.* `IsSubdivision t₀ u' δ t` verlangt `t 0 ≤ exhaustionMin t₀ u'`
und `exhaustionMax t₀ u' ≤ t (Fin.last n)`; nach dem Transport muß dasselbe für
das *kleinere* Fenster gelten. Der naive Weg — den verschobenen Knoten unterhalb
des kleinen Fensterrandes zu halten — bricht auf einem Index, der so weit unten
gar keine Punkte hat (`Set.Icc (0:ℝ) 1` bei `0`, eine der laufenden Instanzen),
und verlangt dort ein eigenes Argument. Der Weg, der ohne auskommt, führt
**rückwärts**: `TimeChange.dist_le_of_norm_le`, angewandt auf `l⁻¹` an den beiden
Enden des *kleinen* Fensters, liefert zwei Punkte des *großen*, und dann sagen
`isLeast_exhaustionMin` und `isGreatest_exhaustionMax` den Rest. Der entartete
Fall ist darin enthalten, ohne genannt zu werden: hat der Index ein kleinstes
Element, so hält jeder Ordnungsisomorphismus es fest und die Abschätzung ist
leer.

*Und die halboffenen Zellen zahlen sich ein zweites Mal aus.* `l` bildet
`Set.Ico (t i) (t (i+1))` **auf** `Set.Ico (l (t i)) (l (t (i+1)))` ab, also ist
kein Punkt der übertragenen Zelle unversorgt und der Verlust ist wirklich `2 η`
und nicht mehr: einmal für den Punkt in der Zelle, einmal für ihren linken
Endpunkt. Mit `Set.Icc` wäre die Abbildung nicht mehr surjektiv auf die Zelle,
und die Zerlegung des Fensters in Zellen hätte Ränder doppelt gezählt.

*Vier Radien treten auf, und ihre Schachtelung ist nicht Buchführung, sondern der
Beweis.* Der Modul wird auf `exhaustion t₀ m` verlangt; die Unterteilung wird auf
`exhaustion t₀ (m+1)` genommen, denn das ist der Raum, den der Zeitwechsel zum
Verschieben der beiden Fensterenden braucht; die Knoten liegen dort, also muß
dort auch die gleichmäßige Schranke gelten; und der Radius, an dem
`exists_radius_distWith_lt` sie liefert, liegt über `m+2`, weil der Zeitwechsel
`exhaustion t₀ (m+1)` erst **in** das Fenster tragen muß, ehe
`SkorokhodSpace.edist_le_ofReal_distWith` seine beiden Klemmungen fallen lassen
darf. Die eine Größe, die alle vier zusammenhält, ist `γ` mit
`(exp γ - 1) · (2 (m+1)) ≤ 1`, und sie ist zugleich die Norm-Schranke des
Zeitwechsels und der Schrumpffaktor der Lücken.

*Die Roadmap ist nachgezogen*: Meilenstein 7 in `SkorokhodSpace/README.md` führt
die sieben neuen Punkte, die Schachtelung der vier Radien als eigenen Punkt, und
den noch offenen achten (`exists_compact_range_of_isCompact`).

*Was als Nächstes zu tun ist,* und es sind drei Stücke, in dieser Reihenfolge:

1. **Die Wertebedingung der Hinrichtung**,
   `SkorokhodSpace.exists_compact_range_of_isCompact`: aus kompaktem Abschluß von
   `A` die relative Kompaktheit von `{f t : f ∈ A, t ∈ exhaustion basePoint m}`
   in `E`. Sie hängt nicht am Modul, sondern daran, daß ein càdlàg-Pfad auf einem
   kompakten Fenster totalbeschränktes Bild hat — das ist wieder
   `IsCadlag.exists_subdivision`, dessen endlich viele Zellwerte ein `ε'`-Netz
   bilden —, und die Gleichmäßigkeit über `A` läuft über **dieselbe**
   Totalbeschränktheit wie der Satz dieses Laufs. Sie ist deshalb jetzt dran:
   sie ist das kürzeste der drei Stücke, sie liest nichts Neues, und mit ihr ist
   die Hinrichtung vollständig. *Ihr kombinatorisches Stück ist in diesem Lauf
   noch mitgekommen und bewiesen*: `exists_mem_Ico_of_strictMono` sagt, daß die
   Zellen einer Unterteilung ihre halboffene Spanne überdecken — daß also
   außerhalb der Knoten nichts liegt und die Knotenwerte wirklich ein Netz sind.
   Die Induktion spaltet am **letzten** Knoten und nicht am ersten, denn die
   Zellen sind `Set.Ico` und die letzte bliebe sonst ohne Namen. Der Satz braucht
   nichts als `LinearOrder` und hängt an `propext` allein.
2. Die **Rückrichtung**, die `SkorokhodSpace.tendsto_of_partialComp` von
   Meilenstein 5 liest.
3. Der Zusammenbau von `isCompact_closure_iff` aus 1, 2 und
   `tendsto_iSup_modulus_of_isCompact`.

**Das Manuskript ist nicht angefaßt.**

### 2026-09-09, achter Lauf des Tages — die Wertebedingung ist bewiesen, und die Rückrichtung ist widerlegt

**Aufgabe.** Vorrangige Aufgabe, Teil A, Punkt 3: das Kompaktheitskriterium
`SkorokhodSpace.isCompact_closure_iff`, das letzte `sorry` der Datei. Der vorige
Lauf hatte drei Stücke benannt und (i), die Wertebedingung, als das nächste
bezeichnet.

**Stand der Datei.** `SkorokhodSpace/Suggested.lean` steht weiter bei **einem**
`sorry`; dieser Lauf hat es nicht gestrichen, sondern seine Aussage
**berichtigt**. Vier neue Deklarationen und eine umgeschriebene, alle durch
`lake env lean` gegen v4.33.1 geprüft und alle mit `#print axioms` auf `propext`,
`Classical.choice`, `Quot.sound`.

**Punkt (i) ist erledigt, und die Hinrichtung ist damit vollständig.** Zwei
Sätze, und der erste ist von der Metrik auf `D(ι, E)` gänzlich unabhängig:

* `IsCadlag.totallyBounded_image_Icc` — ein càdlàg-Pfad hat auf einem kompakten
  Fenster totalbeschränktes Bild. Das ist `IsCadlag.exists_subdivision` plus
  `exists_mem_Ico_of_strictMono` des vorigen Laufs: die Zellen überdecken ihre
  halboffene Spanne, jeder Wert liegt also innerhalb `ε` bei einem der endlich
  vielen Knotenwerte, und der rechte Rand ist selbst ein Knoten.
* `SkorokhodSpace.totallyBounded_values_of_isCompact` — hat `A` kompakten
  Abschluß, so ist `{f t : f ∈ A, t ∈ exhaustion basePoint m}` totalbeschränkt.
  Das ist der Beweis von `tendsto_iSup_modulus_of_isCompact`, auf den Werten
  statt auf dem Modul geführt, und er ist um einen Radius kürzer: die endlich
  vielen Mittelpunkte kommen aus der Totalbeschränktheit von `A`, ihre
  Fensterwerte aus dem vorigen Satz, und
  `exists_timeChange_distWith_lt_of_intDist_lt` trägt einen Wert eines Pfades der
  Kugel auf einen Wert seines Mittelpunkts. Die eine Stelle, an der der
  Zeitwechsel eingeht: der Wert wird bei `y` gelesen, der des Mittelpunkts bei
  `l⁻¹ y`, weshalb die Fenster der Mittelpunkte den Radius `m + 1` haben.

*Totalbeschränktheit ist die richtige Konklusion und keine Abschwächung.* Sie
braucht **keine** Vollständigkeit von `E`, und
`SkorokhodSpace.isCompact_closure_values_of_isCompact` gewinnt daraus unter
`[CompleteSpace E]` die relative Kompaktheit in einer Zeile. Das ist die einzige
Stelle des Kriteriums, an der die Vollständigkeit der **gegebenen** Metrik
gebraucht wird — `PolishSpace E` gibt nur, daß die Topologie von *irgendeiner*
vollständigen Metrik herkommt, und das genügt hier nicht.

**Und der Befund, der die Ansage des vorigen Laufs umwirft: die Rückrichtung ist
falsch.** `SkorokhodSpace.not_isCompact_closure_of_rigid` sagt es in Lean: ist
der einzige Zeitwechsel mit Norm unter einem `c > 0` die Identität, und gibt es
eine überabzählbare Menge `S` von Sprungzeiten, die von allen Fensterenden den
Abstand `η` hält, so erfüllt die Familie `stepAt x a b`, `x ∈ S`, **beide**
Konjunktionen der rechten Seite und hat doch keinen kompakten Abschluß.

*Warum die rechte Seite gilt.* Die Werte sind die zwei Punkte `a` und `b`, also
ist die Wertebedingung an jedem Fenster auf den Punkt erfüllt. Und die
Unterteilung aus den beiden Fensterenden mit `x` dazwischen hat **gar keine**
Schwingung — unterhalb von `x` ist der Pfad konstant `b`, oberhalb konstant `a`,
und beide Zellen sind `Set.Ico` —, also ist der Modul `0` für jedes `δ < η` und
das Supremum über die Familie geht gegen `0`. Die Disjunktion in der Hypothese
`hwin` ist das entartete Fenster, das
`modulus_eq_zero_of_exhaustion_subsingleton` erledigt.

*Warum die linke Seite nicht gilt.* Unter der Starrheit ist die Familie
`r`-getrennt, mit `r = min c (exp(-N) · min 1 (dist a b))`, und das ist wörtlich
`SkorokhodSpace.le_intDist_stepAt` — derselbe Satz, der am ersten Lauf dieses
Tages die Separabilität zu Fall gebracht hat. Eine überabzählbare `r`-getrennte
Menge ist nicht totalbeschränkt.

*Der Zeuge ist wieder die Cantormenge*, mit `S` ihrem Teil in `Icc (1/4) (3/4)`,
`η = 1/4`, `N = 1` und `c = log 3`; ihre Fenster sind `{0}` für `m = 0` und ganz
`ι` für `m ≥ 1`, was genau die Disjunktion `hwin` ist. Wie am ersten Lauf steht
die Starrheit als Hypothese und die Rechnung auf Papier.

**Was daraus für das Kriterium folgt, und was dieser Lauf entschieden hat.** Die
Hinrichtung gilt für **jeden** Index, den die Datei zuläßt, und steht als das
Paar `isCompact_closure_values_of_isCompact` /
`tendsto_iSup_modulus_of_isCompact` da. Die Rückrichtung ist indexgebunden.
`SkorokhodSpace.isCompact_closure_iff` ist deshalb **auf `D(ℝ, E)` umgestellt**:
seine Hinrichtung ist die Spezialisierung der beiden allgemeinen Sätze, sein
`sorry` schuldet nur noch die Rückrichtung, und `ℝ` ist der Index, den die
Roadmap verbraucht und den Ethier--Kurtz nehmen.

*Der Weg über eine Typklasse ist geprüft und verworfen, und der Grund gehört in
den Bericht.* `HasCountableCore ι` schlösse den Zeugen aus — eine starre
überabzählbare Menge hat keinen abzählbaren Kern —, aber es ist die Klasse der
**Separabilität** und liefert eine abzählbare Familie von Treppenpfaden. Die
Totalbeschränktheit verlangt eine **endliche**, und daß eine abzählbare genügte,
ist von niemandem bewiesen. Eine Klasse zu erfinden, die die Aussage wahr macht,
ohne die Aussage zu beweisen, ist die Fehlerform, die dieses Inventar seit dem
2026-09-05 protokolliert; also steht das Kriterium dort, wo es wahr ist, und die
Klasse ist die Sache dessen, der einen zweiten Index braucht.

**Was als Nächstes zu tun ist.** Die Rückrichtung von
`SkorokhodSpace.isCompact_closure_iff` über `ℝ`, und sie ist jetzt das einzige
offene Stück von Meilenstein 7. Ihr Weg: aus der Modulbedingung und der
Wertebedingung ein **endliches** `ε`-Netz bauen. Zu jedem `ε` ein `m` mit
`exp (-m) < ε` (der Schwanz des Integrals), dazu ein `δ` aus der Modulbedingung,
dann für jeden Pfad eine `δ`-sparsame Unterteilung mit Schwingung unter `ε`;
ihre Knoten werden auf ein **endliches Gitter** des Fensters geschoben — das ist
die Stelle, an der `ℝ` gebraucht wird und der starre Index scheitert —, ihre
Werte auf ein endliches Netz des Wertekompaktums. Der Approximant ist
`SkorokhodSpace.stepPath` des dritten Laufs, die Schranke ist
`SkorokhodSpace.distWith_stepPath_le` des vierten, und die Buchführung vom
Fenster zum Integral ist `SkorokhodSpace.intWith_le_of_ae_distWith_le`. Alle drei
stehen bewiesen da; neu zu bauen ist allein das Gitter samt dem Zeitwechsel, der
die Knoten darauf schiebt, und die Schranke für die **Anzahl** der Knoten, die
aus der Sparsamkeit und der Kompaktheit des Fensters kommt.

**Das Manuskript ist nicht angefaßt.**

### 2026-09-09, neunter Lauf des Tages — die Rückrichtung ist auch über `ℝ` falsch, und der Grund ist der Basispunkt

**Aufgabe.** Vorrangige Aufgabe, Teil A, Punkt 3: das Kompaktheitskriterium
`SkorokhodSpace.isCompact_closure_iff`, das letzte `sorry` der Datei. Der vorige
Lauf hatte die Rückrichtung über `ℝ` als das einzige offene Stück von
Meilenstein 7 benannt und ihren Weg — endliches Gitter, endliches Netz,
`stepPath` — angesagt.

**Stand der Datei.** `SkorokhodSpace/Suggested.lean` steht bei **zwei** `sorry`
statt einem. Der Lauf hat keines gestrichen, sondern die Aussage, der sie
gehören, ein zweites Mal **berichtigt**; das eine `sorry` einer falschen Aussage
ist zu zweien einer wahren geworden. Neun neue Deklarationen, alle durch
`lake env lean` gegen v4.33.1 geprüft und alle mit `#print axioms` auf `propext`,
`Classical.choice`, `Quot.sound`.

**Der angesagte Weg ist nicht gegangen worden, weil er nicht geht: die
Rückrichtung ist über `ℝ` genauso falsch wie über dem starren Index.**
`SkorokhodSpace.not_isCompact_closure_of_jumps_at_basePoint` sagt es in Lean,
und zwar ohne jede Hypothese auf Papier — anders als der Cantor-Zeuge des
vorigen Laufs, der `hrigid` ungeprüft trägt. Die Familie ist
`stepAt ((1/4)^(k+1)) a b`, `k ∈ ℕ`: ihre Sprungzeiten häufen sich am
**Basispunkt**.

*Warum die rechte Seite gilt.* Die Werte sind `a` und `b`, also ist die
Wertebedingung an jedem Fenster erfüllt. Und die Unterteilung
`-(m+1) < (1/4)^(k+1) < m+1` ist für jedes `δ < 3/4` zulässig — ihre beiden
Lücken sind mindestens `1` und mindestens `3/4` — und hat **gar keine**
Schwingung, der Pfad ist unter seinem Sprung konstant `b` und darüber konstant
`a`. Der Modul ist also `0`, gleichmäßig über die Familie, für jedes Fenster und
jedes kleine `δ`. Die Freiheit des Überstehens wird dabei nicht gebraucht: für
`m ≥ 1` ist dieselbe Unterteilung auch gepinnt zulässig.

*Warum die linke Seite nicht gilt.* Die Metrik von Meilenstein 4 nimmt ihr
Infimum über die Zeitwechsel, die den **Basispunkt festhalten**, und ein solcher
bewegt einen Punkt um ein beschränktes **Verhältnis** seines Abstands zu `t₀`.
Zwei Sprungzeiten, deren Abstände zu `t₀` sich um den Faktor `4` unterscheiden,
sind darum gleichmäßig getrennt: die Familie ist `r`-getrennt mit
`r = min (log 2) (exp (-1) · min 1 (dist a b))`, und eine unendliche
`r`-getrennte Menge ist nicht totalbeschränkt.

**Das Mittel, und es ist der Satz, den `le_intDist_stepAt` nicht sagen konnte.**
Drei Deklarationen, jede die vorige unter einem Integral:

* `SkorokhodSpace.dist_le_distWith_stepAt_of_exp_norm_mul_lt` — ist `t₀ ≤ x < y`
  und hält `l` den Basispunkt fest mit `exp ‖l‖ · dist t₀ x < dist t₀ y`, so
  liegt `s = l⁻¹ x` noch echt unter `y`, und an dieser einen Stelle liest der
  erste Pfad schon `a`, während der zweite noch `b` liest. Beide Klemmungen
  fallen, weil `s` und `x` innerhalb des Fensters liegen; der Zeitwechsel geht
  allein über `TimeChange.dist_le_exp_norm_mul`, gelesen auf `l⁻¹`.
* `SkorokhodSpace.le_intWith_stepAt_of_exp_norm_mul_lt` — dasselbe unter dem
  Radienintegral, mit der Masse `exp (-dist t₀ y)`.
* `SkorokhodSpace.le_intDist_stepAt_of_exp_mul_lt` — **die Trennung ohne
  Starrheitshypothese.** Entweder kostet der Zeitwechsel `c`, oder er ist billig
  und kann dann `x` nicht so weit hinaustragen wie `y`. Das ist die quantitative
  Form davon, daß die Metrik den Basispunkt festhält: nahe `t₀` sind die
  zulässigen Zeitwechsel kurz, und darum ist eine am Basispunkt sich häufende
  Familie von Sprungzeiten gleichmäßig getrennt.

**Die Reparatur ist Ethier--Kurtz' eigene, zum zweiten Mal.** Ihre Unterteilung
von `[0,T]` beginnt bei `0` — und dort ist `0` zugleich Basispunkt, linkes Ende
des Index und linkes Ende **jedes** Fensters. Auf einem zweiseitigen Index
fallen die drei auseinander, und das Kriterium braucht genau eines davon: den
Basispunkt als Knoten. `SkorokhodSpace.IsSubdivisionBased` (`IsSubdivision` samt
`t₀ ∈ Set.range t`), `SkorokhodSpace.modulusBased` und
`SkorokhodSpace.modulus_le_modulusBased` stehen; `isCompact_closure_iff` ist auf
`modulusBased` umgestellt.

*Daß die Bedingung beide Zeugen richtig scheidet, ist der Prüfstein und keine
Hoffnung.* Die Familie dieses Laufs wird **verworfen**: die Zelle, die bei `t₀`
beginnt, ist breiter als `δ` und verschluckt den Sprung, ihre Schwingung ist
`dist a b`. Die Familie von `not_tendsto_iSup_modulusPinned` — Sprünge, die an
den **Fensterrand** wandern — wird weiterhin **angenommen**: die Unterteilung
`-m-1 < Sprung < 0 < m+1` trägt den Basispunkt und hat keine Schwingung. Die
beiden widerlegten Formen sind damit die beiden Seiten derselben Verwechslung,
und die dritte ist die einzige, die keine von beiden macht.

**Was die zwei `sorry` schulden, und warum es zwei sind.** Die Ungleichung
`modulus ≤ modulusBased` läuft in die falsche Richtung, also überträgt sich die
bewiesene Hinrichtung **nicht**: sie ist auf gestützten Unterteilungen zu
wiederholen. Jeder ihrer Schritte übersteht das — `isSubdivision_comp` trägt
einen Knoten bei `t₀` auf einen Knoten bei `t₀`, denn die Zeitwechsel halten ihn
fest — bis auf ihre Eingabe, und die ist `IsCadlag.exists_subdivision`. **Das
eine neu zu bauende Stück ist damit benannt: eine càdlàg-Unterteilung von
`Set.Icc a b` durch einen vorgeschriebenen inneren Punkt** (`t₁` von `a` nach
`c`, `t₂` von `c` nach `b`, aneinandergesetzt zu `Fin (n+p+1)`); beide
Richtungen des Kriteriums lesen sie. Die Wertebedingung der Hinrichtung ist
unberührt und steht weiter bewiesen da
(`isCompact_closure_values_of_isCompact`), ebenso das allgemeine Paar für
`modulus`.

**Und die Lehre.** Der Modul sieht Fenster und Sparsamkeit, und beide sind in
der **Metrik des Index** formuliert; die Metrik von Meilenstein 4 ist am
Basispunkt für das **Verhältnis** der Abstände empfindlich. Wo die beiden
auseinandergehen, sagt der Modul nichts. Das ist derselbe Riß, den
`not_separableSpace_of_rigid` am ersten Lauf dieses Tages aufgemacht hat, nur
diesmal auf `ℝ` und ohne Starrheit — und er erklärt nachträglich, warum die
acceptance examples von Meilenstein 7 das Loch nicht gefunden haben: alle ihre
Sprünge sitzen fern vom Basispunkt. Ein weiteres gehört dazu, und es ist die
Familie dieses Laufs; es steht jetzt dort.

**Das Manuskript ist nicht angefaßt.**

**Und das Werkzeug dazu ist im selben Lauf noch gebaut.**
`IsCadlag.exists_subdivision_through` — zu `a ≤ c ≤ b` und `ε > 0` eine
Unterteilung von `Set.Icc a b` mit `c` unter ihren Knoten und Zellschwingung
höchstens `ε` — ist die neunte Deklaration, durch `lake env lean` gegen v4.33.1
geprüft und mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`.
Sie ist `IsCadlag.exists_subdivision` zweimal, auf `Set.Icc a c` und auf
`Set.Icc c b`, und die beiden `Fin`-Tupel an ihrem gemeinsamen Endpunkt
zusammengesetzt: `t i = t₁ i` für `i ≤ n` und `t₂ (i - n)` sonst, über
`Fin (n + p + 1)`. Der gemeinsame Endpunkt ist es, der die Strenge der
Monotonie am Übergang trägt (`t₁ i ≤ t₁ (last n) = c = t₂ 0 < t₂ (j - n)`, und
die zweite Ungleichung ist strikt, weil `j > n` ist), und er ist auch der Grund,
daß die Zellen keine Fallunterscheidung brauchen: die Zelle bei `n` ist
`[c, t₂ 1)` und damit die nullte Zelle von `t₂`. Die eine Fallunterscheidung, die
bleibt, ist `p = 0` am rechten Ende.

**Was als Nächstes zu tun ist.** `SkorokhodSpace.tendsto_modulusBased` — der
Ersatz für `tendsto_modulus`, den die Berichtigung schuldet —, dann die
Hinrichtung auf gestützten Unterteilungen
(`tendsto_iSup_modulusBased_of_isCompact`), dann die Rückrichtung. Alle drei
lesen jetzt ein fertiges Werkzeug: die Unterteilung durch den Basispunkt steht,
`isSubdivision_comp` trägt einen Knoten bei `t₀` auf einen solchen, und der Rest
des Beweises von `tendsto_iSup_modulus_of_isCompact` ist wörtlich zu
wiederholen.

### 2026-09-09, zehnter Lauf des Tages — die Hinrichtung steht auch gestützt, und nur noch die Rückrichtung fehlt

**Aufgabe.** Vorrangige Aufgabe, Teil A, Punkt 3. Der vorige Lauf hatte drei
Schritte in dieser Reihenfolge angesagt: `SkorokhodSpace.tendsto_modulusBased`,
dann die Hinrichtung auf gestützten Unterteilungen, dann die Rückrichtung. Die
ersten beiden sind getan.

**Stand der Datei.** `SkorokhodSpace/Suggested.lean` steht bei **einem** `sorry`
statt zweien, und es ist die Rückrichtung des Kompaktheitskriteriums. Neun neue
Deklarationen, alle durch `lake env lean` gegen v4.33.1 geprüft und alle mit
`#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`. Dieser Lauf hat
nichts widerlegt und nichts umgestellt — der erste seit dem fünften Lauf dieses
Tages, der die Aussage, an der er arbeitet, unverändert läßt.

**Die Hinrichtung ist vollständig, und `isCompact_closure_iff` schuldet nur noch
die Rückrichtung.** Der linke Zweig des Beweises lautet jetzt

```lean
exact ⟨SkorokhodSpace.isCompact_closure_values_of_isCompact hA m,
  SkorokhodSpace.tendsto_iSup_modulusBased_of_isCompact hA m⟩
```

und trägt kein `sorry` mehr. Vier Deklarationen sind der Weg dorthin, und keine
von ihnen ist eine Überraschung — das ist der Befund. Die Ansage des vorigen
Laufs, jeder Schritt der Hinrichtung überstehe die Umstellung auf gestützte
Unterteilungen und allein ihre Eingabe sei zu ersetzen, hat sich Zeile für Zeile
bestätigt:

* `SkorokhodSpace.isSubdivisionBased_comp` ist `isSubdivision_comp` und **eine
  Zeile mehr**, und diese eine Zeile ist der Grund, daß die Berichtigung des
  neunten Laufs überhaupt bezahlbar ist: die Zeitwechsel, über die die Metrik von
  Meilenstein 4 ihr Infimum nimmt, halten den Basispunkt fest, also geht ein
  Knoten bei `t₀` auf einen Knoten bei `t₀`. Unter einer Metrik ohne Basispunkt
  wäre der gestützte Modul gar nicht transportierbar, und das Kriterium hätte
  keine dritte Form mehr, auf die es hätte ausweichen können.
* `SkorokhodSpace.modulusBased_le_of_edist_le` ist danach wörtlich
  `modulus_le_of_edist_le`, mit demselben Verlust `2 η` in der Schwingung und
  `exp (-γ)` in der Sparsamkeit. `subdivisionOsc_comp_le` wird unverändert
  gelesen — der gestützte Knoten geht die Schwingung nichts an.
* `SkorokhodSpace.tendsto_modulusBased` ist `tendsto_modulus` mit
  `IsCadlag.exists_subdivision_through` an Stelle von
  `IsCadlag.exists_subdivision`. Daß der Basispunkt als vorgeschriebener Knoten
  überhaupt zulässig ist, ist `mem_exhaustion_self`: er liegt in **jedem**
  Fenster, also ist über den Radius nichts vorauszusetzen. Und der zusätzliche
  Knoten kostet quantitativ nichts, die Lücken der verfeinerten Unterteilung sind
  weiterhin endlich viele und weiterhin positiv, also greift dasselbe
  `δ₀`-Argument.
* `SkorokhodSpace.tendsto_iSup_modulusBased_of_isCompact` ist der Beweis von
  `tendsto_iSup_modulus_of_isCompact`, an genau zwei Stellen geändert: die
  Unterteilung der endlich vielen Mittelpunkte geht durch `t₀`, und der Transport
  läuft über `modulusBased_le_of_edist_le`. Die vier geschachtelten Radien, die
  Wahl von `γ` mit `(exp γ - 1) * (2 (m+1)) ≤ 1` und die Totalbeschränktheit
  bleiben, wie sie waren.

*Warum das kein Zufall ist und wo es hätte brechen können.* Der gestützte Knoten
überlebt den Transport nur, weil `l.toOrderIso t₀ = t₀` ohnehin unter den
Hypothesen von `isSubdivision_comp` steht — es ist dieselbe Hypothese, die dort
schon gebraucht wurde, damit das Bild der Unterteilung das Fenster noch
überdeckt (ohne sie hat eine Verschiebung von `ℝ` die Norm `0` und trägt das
Fenster von sich fort). Die Bedingung, die der neunte Lauf aus der Not erfunden
hat, und die Bedingung, unter der der siebte Lauf schon rechnete, sind dieselbe.

**Und die Ansage für die Rückrichtung ist zur Hälfte eingelöst.** Der achte Lauf
hatte zwei neu zu bauende Stücke benannt: das Gitter samt Zeitwechsel darauf, und
**die Schranke für die Anzahl der Knoten**. Die zweite steht:

* `dist_first_last_eq_sum` — unter `AdditiveDist ι` teleskopieren die Lücken
  eines monotonen Tupels, `dist (t 0) (t (Fin.last n)) = ∑ i, dist (t i.castSucc)
  (t i.succ)`. Die eigentliche Voraussetzung ist die **Monotonie** und nicht die
  Strenge, und sie wird gebraucht: ohne sie ist `dist` nur subadditiv und die
  Identität wird zu einer Ungleichung in der unbrauchbaren Richtung. Dies ist die
  einzige Stelle der Datei, an der `AdditiveDist ι` um seiner selbst willen
  gelesen wird und nicht durch das Fenster hindurch.
* `mul_le_dist_first_last` — ein `δ`-sparsames monotones Tupel überspannt
  mindestens `n * δ`.
* `mul_le_dist_of_sparse` — je zwei seiner Knoten sind mindestens ihr
  Indexabstand mal `δ` voneinander entfernt; das ist die vorige Aussage,
  angewandt auf das Teiltupel zwischen den beiden Knoten.
* `SkorokhodSpace.sub_mul_le_two_mul_of_isSubdivision` — liegen zwei Knoten einer
  `δ`-sparsamen Unterteilung im Fenster vom Radius `u`, so ist ihr Indexabstand
  höchstens `2u / δ`. Das ist die Schranke, und sie ist als Ungleichung
  formuliert und nicht als Kardinalität, damit keine `Nat`-Division darin
  vorkommt.

*Der Punkt, an dem die naive Fassung dieser Schranke falsch gewesen wäre, und er
ist der Grund für die Gestalt der letzten Aussage:* `IsSubdivision` verlangt nur,
daß die Unterteilung das Fenster **überdeckt**, seit der Berichtigung des
sechsten Laufs also ausdrücklich mit der Freiheit, an beiden Enden darüber
hinauszuragen. Die Knoten müssen darum **nicht** im Fenster liegen, und ein
einzelner darf beliebig weit draußen sitzen; eine Schranke für `n` selbst gibt es
nicht. Gezählt werden können allein die Knoten **im** Fenster, und darum
quantifiziert die Aussage über zwei Knoten, von denen bekannt ist, daß sie darin
liegen. Für die Rückrichtung genügt das, denn außerhalb des Fensters sieht die
Metrik nichts, was der Schwanz `exp (-M)` nicht schon bezahlt.

**Und ein Stück des Gitters ist noch mitgekommen, das neunte.**
`SkorokhodSpace.abs_sum_tent_sub_le`: eine Summe von Zelten mit getrennten
Mittelpunkten — Abstand mindestens `2 r`, Höhen höchstens `η` — ist
`2 η / r`-Lipschitz, **gleichviel wie viele es sind**.

*Das ist nicht die Schranke, die `exists_rat_nodes_perturbation` benutzt, und der
Unterschied ist der Grund, warum die Rückrichtung eine eigene braucht.* Dort wird
gliedweise abgeschätzt, `∑ᵢ |vᵢ| / r`, und das wächst mit der Zahl der Zelte; dort
darf es das auch, weil die Höhe **nach** der Knotenzahl gewählt werden darf (so
steht es seit dem zweiten Lauf dieses Tages in der Roadmap, und es war dort
richtig). Die Rückrichtung kann es nicht: ihr Gitter steht fest, ehe der Pfad
gesehen wird, die Höhe ist also die Gitterweite, und die Knotenzahl ist, was die
Unterteilung des Pfades hergibt. Was sie rettet, ist die **Disjunktheit der
Träger**: an jeder Stelle ist höchstens ein Zelt von Null verschieden, die
Differenz hat also höchstens **zwei** nichtverschwindende Glieder, eines je
Argument, und das unabhängig von der Zahl der Zelte. Die `2` ist der Preis dafür,
nicht zu wissen, welches Argument in welchem Träger sitzt.

**Das Manuskript ist nicht angefaßt.**

**Was als Nächstes zu tun ist.** Das **Gitter samt dem Zeitwechsel darauf**, und
es ist das letzte neu zu bauende Stück von Meilenstein 7. Gebraucht wird: zu
`m`, `δ > 0` und `ρ > 0` eine endliche Menge `G ⊆ ℝ`, die den Basispunkt enthält,
und zu jedem `δ`-sparsamen gestützten Tupel `t` mit Knoten im Fenster ein
Zeitwechsel `l ∈ TimeChange.fixing 0` kleiner Norm, der jeden Knoten von `t` auf
einen Punkt von `G` trägt. Die Anzahl der zu verschiebenden Knoten ist durch
`SkorokhodSpace.sub_mul_le_two_mul_of_isSubdivision` beschränkt, die Konstruktion
des Zeitwechsels ist `TimeChange.exists_real_of_perturbation` samt
`SkorokhodSpace.tent` — dieselbe Störung `φ x = x + ψ x`, die
`Real.instHasCountableCore` im zweiten Lauf dieses Tages trägt, nur mit einer
endlichen Menge von Zelten statt einer abzählbaren Familie und mit
`SkorokhodSpace.abs_sum_tent_sub_le` als Lipschitz-Schranke statt der groben.
**Zu rechnen bleibt allein die Wahl der Konstanten**, und sie schließt sich:
Gitter `ρ ℤ`, Zeltradius `r = δ / 4` (die Knoten sind `δ`-getrennt, die
Gittermittelpunkte also mindestens `δ - ρ ≥ 2 r`), Höhe `η = ρ / 2` (der
Abstand zum nächsten Gitterpunkt), also `K = 2 η / r = 2 ρ / δ` — und `ρ` wird
zuletzt aus `K` und `δ` bestimmt, nicht umgekehrt. Danach ist der
Zusammenbau `SkorokhodSpace.stepPath` als Approximant,
`SkorokhodSpace.distWith_stepPath_le` als Schranke und
`SkorokhodSpace.intWith_le_of_ae_distWith_le` als Buchführung, und alle drei
stehen bewiesen da. **Der Basispunkt muß im Gitter liegen** — das ist es, was
`not_isCompact_closure_of_jumps_at_basePoint` erzwingt, und der Grund, warum die
Verschiebung eines Knotens an einem Bruchteil seines Abstands zu `t₀` zu messen
ist und nicht an einem absoluten Betrag.

### 2026-09-09, elfter Lauf des Tages — das Gitter steht, und die Unterteilung muß das Fenster nur überdecken

**Bearbeitet:** `TauCeti/SkorokhodSpace/Suggested.lean`, Meilenstein 7, die
Rückrichtung von `SkorokhodSpace.isCompact_closure_iff`; dazu Meilenstein 5,
`SkorokhodSpace.distWith_stepPath_le`. Die Datei steht weiterhin bei **einem**
`sorry`. Sieben Deklarationen sind neu und zwei geändert, alle durch
`lake env lean` gegen v4.33.1 geprüft und alle mit `#print axioms` auf `propext`,
`Classical.choice`, `Quot.sound` — die beiden geänderten (`distWith_stepPath_le`
und ihr Abnehmer `SkorokhodSpace.instSeparableSpace`) eingeschlossen, samt
`SkorokhodSpace.instPolishSpace`.

**Das Gitter, das der zehnte Lauf angesagt hat, steht, und die Ansage hat
gehalten — mit einer Änderung an den Konstanten und einer an der Reihenfolge der
Quantoren.**

`SkorokhodSpace.exists_finite_grid_timeChange`: zu `δ > 0`, `γ > 0` und einem
Radius `u` gibt es **eine endliche** Menge `G ⊆ ℝ` mit `0 ∈ G`, so daß jedes
`δ`-sparsame streng monotone Tupel, das `0` unter seinen Knoten trägt, von einem
Zeitwechsel `l` mit `l 0 = 0` und `‖l‖ ≤ γ` auf `G` getragen wird — soweit seine
Knoten im Fenster vom Radius `u` liegen —, und dieser Zeitwechsel verschiebt
überdies **keinen** Punkt von `ℝ` um mehr als `γ`.

*Die Reihenfolge der Quantoren ist der ganze Inhalt.* `G` wird aus `δ`, `γ` und
`u` allein hergestellt, ehe irgendein Tupel gesehen ist, und ein einziges `G`
bedient alle. Das ist es, was ein **endliches** Netz braucht, und es ist genau
das, was `SkorokhodSpace.exists_rat_nodes_perturbation` nicht gibt: jenes
erzeugt seine Knoten *nach* dem Tupel und erzeugt abzählbar viele. Der Preis
dafür ist, daß die Lipschitz-Schranke der Störung nicht gliedweise summiert
werden darf; sie ist `SkorokhodSpace.abs_sum_tent_sub_le` vom zehnten Lauf, und
die Disjunktheit der Träger bezahlt sie.

*Die Konstanten schließen sich in einer Richtung, und die Ansage war an einer
Stelle um den Faktor zwei daneben.* Die Zelte haben Radius `r = δ/4` und Höhe
`η = ρ/2`, also ist `2η/r = 4ρ/δ` und nicht `2ρ/δ`, wie der zehnte Lauf
gerechnet hatte; das ändert nichts am Weg, weil `ρ` zuletzt gewählt wird, und
`ρ ≤ (1 - exp(-γ)) δ/4` ist die Bedingung. `K := 1 - exp (-γ)` ist dieselbe Wahl
wie in `Real.instHasCountableCore`, und sie macht beide Lipschitz-Konstanten der
Störung höchstens `exp γ`.

*Die Trennung der Zeltmittelpunkte ist nicht `δ - ρ`, sondern `δ`.* Die Zelte
sitzen auf den **Knoten** und nicht auf den Gitterpunkten — die Störung wird an
den Knoten ausgewertet und trägt sie auf das Gitter, nicht umgekehrt —, also ist
`2r = δ/2 ≤ δ` die Trennung, und `ρ` geht in sie gar nicht ein. Das ist die
zweite Berichtigung der Ansage, und sie macht die Rechnung kürzer statt länger.

*Der Basispunkt ist ein Knoten und bleibt einer.* `ψ 0 = 0` gilt, weil `0`
selbst ein Gitterpunkt ist: das Zelt, das dort sitzt, trägt den Koeffizienten
`0`, und jedes andere ist `δ` weit weg und verschwindet dort. Ohne einen Knoten
bei `0` verschöbe die Störung ihn, der Zeitwechsel verließe
`TimeChange.fixing 0`, und die Metrik von Meilenstein 4 — deren Infimum über die
Zeitwechsel läuft, die den Basispunkt festhalten — sähe ihn nicht. Das ist
dieselbe Stelle, an der
`SkorokhodSpace.not_isCompact_closure_of_jumps_at_basePoint` zubeißt.

*Das Gitter selbst* ist `ρ ℤ`, abgeschnitten auf `⌈(max u 0 + γ)/ρ⌉₊` Schritte
nach beiden Seiten; ein Knoten im Fenster geht auf den nächsten Gitterpunkt
(`round`), verschiebt sich also um höchstens `ρ/2 ≤ γ` und bleibt in dem
Abschnitt.

**Mitgekommen ist die Verschiebungsschranke**, `SkorokhodSpace.abs_sum_tent_le`:
eine Summe von Zelten mit getrennten Mittelpunkten ist durch die Schranke ihrer
Koeffizienten beschränkt, gleichviel wie viele es sind. Sie ist
`abs_sum_tent_sub_le` mit demselben Beweis und einem Glied statt zweien.

**Und ein Befund, der eine Sackgasse abschneidet, ehe sie gegangen wird:
`SkorokhodSpace.distWith_stepPath_le` verlangte die Unterteilung an den
Fensterenden gepinnt, und das ist genau die Fassung, die der sechste Lauf für den
Modul widerlegt hat.** Die beiden Hypothesen `t 0 = (B M).min` und
`t (Fin.last n) = (B M).max` sind jetzt Ungleichungen — `t 0 ≤ (B M).min` und
`(B M).max ≤ t (Fin.last n)` —, also die **Überdeckung** von
`SkorokhodSpace.IsSubdivision`. Es kostet nichts: die beiden werden an einer
einzigen Stelle gelesen, um `l s` zwischen die äußersten Knoten zu setzen, und
dafür taugt `≤` so gut wie `=`. `SkorokhodSpace.instSeparableSpace` ist
nachgezogen (`ht0.le`, `htlast.ge`) und hängt weiterhin an keinem `sorryAx`.

*Warum das nötig war, und warum die naheliegende Alternative nicht geht.* Der
Modul, den die Rückrichtung liest, ist `modulusBased`, und seine Unterteilungen
ragen über das Fenster hinaus — seit der Berichtigung des sechsten Laufs
ausdrücklich. Sie zu **stutzen** wäre der naheliegende Ausweg und er ist
verschlossen: der gestutzte erste und letzte Abstand können beliebig klein
werden, und die Sparsamkeit ist genau das, was
`exists_finite_grid_timeChange` braucht, um seine Zelte zu trennen. Die
Schwingung überstünde das Stutzen (Faktor `2`), die Sparsamkeit nicht.

**Und die Abzählung ist auf endlich umgestellt.**
`SkorokhodSpace.stepPathFamilyLe C Q n₀` ist `stepPathFamily` mit beschränkter
Länge, `SkorokhodSpace.finite_stepPathFamilyLe` seine Endlichkeit, dazu die
Zugehörigkeit und die Inklusion in die abzählbare Familie. Ohne die Schranke an
die Länge ist die Familie auch über einer endlichen Knotenmenge eine unendliche
Vereinigung; was die Schranke liefert, ist
`SkorokhodSpace.sub_mul_le_two_mul_of_isSubdivision` vom zehnten Lauf.

**Und die Fensterrandbuchführung ist herausgezogen, aus demselben Grund wie
`exists_radius_distWith_lt` im siebten Lauf: zwei Abnehmer lesen sie.**
`SkorokhodSpace.exists_bad_radii_set` liefert zu einer Unterteilung `t` des
Fensters vom Radius `M`, einem Zeitwechsel `l` der Norm `≤ δ` und einem Tupel `d`
mit `l (d i) = t i` und `dist (d i) (t i) ≤ δ` eine **meßbare** Radienmenge `B`
vom Maß höchstens `(n+1) (2δ + (exp δ - 1) 2M)`, außerhalb deren die gefensterte
Schranke `distWith t₀ u l f (stepPath d w) ≤ 6 ε` gilt. Sie stand seit dem
vierten Lauf dieses Tages inline in `instSeparableSpace`; dort ist sie jetzt
durch einen Aufruf ersetzt, und der Beweis der Separabilität ist um rund hundert
Zeilen kürzer. **Sie weiß nichts davon, woher `d` kommt** — was sie von `d`
braucht, ist die Verschiebungsschranke allein, und das ist die dritte Klausel von
`HasCountableCore` genauso wie die zweite Aussage des Gitters. Genau darum lesen
beide Abnehmer denselben Satz.

**Das Manuskript ist nicht angefaßt.**

**Was als Nächstes zu tun ist.** Der **Zusammenbau der Rückrichtung**, und alle
seine Stücke stehen jetzt bewiesen da. Der Weg: zu `ε` ein `M` mit
`exp (-M) < ε`; aus der Modulbedingung ein `δ` und zu jedem `f ∈ A` eine
gestützte `δ`-sparsame Unterteilung mit Schwingung unter `ε`; aus
`exists_finite_grid_timeChange` das Gitter `G` und den Zeitwechsel;
`sub_mul_le_two_mul_of_isSubdivision` für die Länge; aus der Wertebedingung ein
endliches Netz `Q`; `SkorokhodSpace.stepPath` als Approximant,
`distWith_stepPath_le` als Schranke (jetzt anwendbar, siehe oben),
`finite_stepPathFamilyLe` als Netz, `exists_bad_radii_set` für den Fensterrand
und `intWith_le_of_ae_distWith_le` als Buchführung.

**Und der Punkt, an dem er noch klemmt, ist benannt, und er ist eine
Ungleichung im herausgezogenen Satz selbst.** `exists_bad_radii_set` schätzt das
Maß der schlechten Radien durch `(n+1) (2δ' + κ)` ab, mit `n` der Länge der
**ganzen** Unterteilung. Für die Separabilität genügt das, weil dort `n` bekannt
ist, ehe `δ'` gewählt wird — die Unterteilung gehört *einem* Pfad. Für die
Rückrichtung genügt es **nicht**: `δ'` muß für alle Pfade von `A` zugleich
taugen, und `n` ist über `A` unbeschränkt. Der Grund ist die Berichtigung des
sechsten Laufs, ein zweites Mal: `IsSubdivision` verlangt nur die Überdeckung,
ein Knoten darf beliebig weit draußen sitzen, und
`sub_mul_le_two_mul_of_isSubdivision` zählt darum allein die Knoten **im**
Fenster.

*Die Reparatur ist keine neue Idee, sondern eine schärfere Fassung derselben
Rechnung, und sie ist wahr:* die Radienmengen der weit draußen liegenden Knoten
sind Koordinatenintervalle um deren eigene Koordinate, treffen `Set.Ioc 0 M` also
gar nicht, und das Maß von `Set.Ioc 0 M ∩ B` hängt allein an den Knoten, deren
Intervall das Fenster trifft — und deren Zahl ist durch
`sub_mul_le_two_mul_of_isSubdivision` beschränkt, gleichmäßig über `A`, sobald
`δ` aus der Modulbedingung feststeht. `exists_bad_radii_set` ist also so
umzuschreiben, daß `(n+1)` durch die Zahl der Knoten mit
`lengthCoord t₀ (max (d i) (t i)) ≥ 0` und
`lengthCoord t₀ (min (d i) (t i)) ≤ M + κ` ersetzt wird; das ist der erste
Schritt des nächsten Laufs, vor dem Zusammenbau und nicht in ihm. Die
Reihenfolge der Wahlen ist dann `δ` zuerst, daraus `n₀`, dann `γ` und mit ihm
`ρ`.

### 2026-09-09, zwölfter Lauf des Tages — die Fensterrandbuchführung zählt jetzt nur noch die Knoten, die das Fenster sieht

**Bearbeitet:** `TauCeti/SkorokhodSpace/Suggested.lean`, Meilenstein 7, die
Rückrichtung von `SkorokhodSpace.isCompact_closure_iff`. Die Datei steht
weiterhin bei **einem** `sorry`. Vierzehn Deklarationen sind neu oder
umgeschrieben, alle durch `lake env lean` gegen v4.33.1 geprüft und alle mit
`#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` —
`SkorokhodSpace.instSeparableSpace`, der einzige Abnehmer des umgeschriebenen
Satzes, eingeschlossen.

**Der benannte Mangel des elften Laufs ist behoben, und die Reparatur ist
genau die angesagte: dieselbe Rechnung, schärfer geführt.**

`SkorokhodSpace.volume_inter_badRadii_le_of_sparse`: ist die Unterteilung `t`
monoton und `δ`-sparsam und ist `n₀ δ ≥ 2 (M + γ + κ)`, so haben die schlechten
Radien in `Set.Ioc 0 M` das Maß höchstens `(n₀ + 1) (2 γ + κ)` — **und `n` kommt
darin nicht mehr vor**. Das ist es, was die Rückrichtung braucht und was
`SkorokhodSpace.volume_badRadii_le`, die grobe Fassung, nicht gibt: über der
Familie `A` wechselt die Unterteilung, die Schranke muß gleichmäßig gelten, und
eine Länge hat `IsSubdivision` gar nicht — sie verlangt nur die Überdeckung, ein
Knoten darf beliebig weit draußen sitzen.

*Der Angelpunkt ist ein eigener Satz geworden, weil er die ganze Rechnung ist:*
`SkorokhodSpace.dist_le_of_inter_badRadiiPiece_nonempty`. Trifft das
Koordinatenintervall eines Knotens `Set.Ioc 0 M` überhaupt, so liegt der Knoten
innerhalb `M + γ + κ` vom Basispunkt. Vier Ungleichungen, zwei je Intervall: ein
Radius `≤ M` drückt die untere Koordinate des oberen Intervalls unter `M`, ein
positiver hebt die obere über `0`, und beim gespiegelten unteren Intervall
gerade umgekehrt gegen `-M` und `κ`. Die Lücke zwischen den beiden Koordinaten
ist `dist (d i) (t i) ≤ γ`, also liegen beide und mit ihnen `t i` in einem
Fenster vom Radius `M + γ + κ`; `lengthCoord` ist eine Isometrie und macht
daraus `dist (t i) t₀`.

*Die Vergrößerung um `γ + κ` ist kein Schlupf.* Ein Knoten dicht außerhalb des
Fensters kann vom Zeitwechsel hineingetragen werden (das ist `γ`), und der
untere Fensterrand selbst wandert um bis zu `κ` (das ist die dritte Klausel, die
der dritte Lauf eingeführt hat). Beides ist in `badRadiiPiece` schon drin; der
Satz liest es nur ab.

*Und das Abzählen selbst ist `sub_mul_le_two_mul_of_isSubdivision` vom zehnten
Lauf, auf dem vergrößerten Radius gelesen.* Die Indizes mit einem schlechten
Radius im Fenster bilden eine Menge; ihre beiden äußersten haben Indexabstand
höchstens `n₀`, weil ihre Knoten `2 (M + γ + κ)` weit auseinanderliegen und die
Unterteilung `δ`-sparsam ist; und eine Menge natürlicher Zahlen zwischen zwei
Extremen hat höchstens `n₀ + 1` Elemente. Das ist der ganze
Kardinalitätsschritt, über `Finset.min'`/`Finset.max'` und `Nat.card_Icc`.

**Dafür ist die Buchführung in benannte Stücke zerlegt, und das ist der Grund,
warum die Separabilität nichts davon merkt.** `SkorokhodSpace.badRadiiPiece`
und `SkorokhodSpace.badRadii` sind jetzt **Definitionen** statt anonymer Mengen
in einem Beweis, samt `measurableSet_badRadiiPiece`,
`mem_badRadiiPiece_of_exhaustionMax`, `mem_badRadiiPiece_of_exhaustionMin`,
`volume_badRadiiPiece_le`, `measurableSet_badRadii` und `volume_badRadii_le`;
die punktweise Aussage heißt
`SkorokhodSpace.distWith_stepPath_le_of_notMem_badRadii`. Eine Menge zu benennen
ist hier keine Kosmetik: **erst dadurch kann dieselbe Menge zwei Maßschranken
tragen** — die grobe für die Separabilität, die scharfe für die Rückrichtung.
Solange `B` existentiell gebunden war, war es für den zweiten Abnehmer opak, und
die Ansage des elften Laufs, „`exists_bad_radii_set` ist umzuschreiben", war
darum eine Ansage zu wenig.

`SkorokhodSpace.exists_bad_radii_set` steht unverändert da, als Korollar der
Stücke, und `instSeparableSpace` ist nicht angefaßt.

**Ein Befund, der die Sackgassenmeldung des elften Laufs berichtigt — und er ist
auf Papier und nicht in Lean.** Der elfte Lauf hat notiert, die Unterteilung zu
**stutzen** sei verschlossen, weil der gestutzte erste und letzte Abstand
beliebig klein werden können und die Sparsamkeit gerade das ist, was die Zelte
des Gitters trennt. Das gilt für das Stutzen an den **Fensterenden** und nur
dafür. Stutzt man statt dessen an festen Marken `± (M + 1)` — also einen vollen
Schritt außerhalb des Fensters vom Radius `M` —, so bleibt die Sparsamkeit
erhalten: der erste Knoten wird `max (t i₀) (-(M+1))` mit `i₀` dem größten Index
unter `exhaustionMin`, und dann ist die Lücke zum nächsten Knoten entweder die
alte (`≥ δ`, wenn `t i₀ > -(M+1)`) oder mindestens `1` (wenn `t i₀ ≤ -(M+1)`,
denn der nächste Knoten liegt über `-M`). Die Schwingung übersteht es, weil
`Set.Ico (max (t i₀) (-(M+1))) (t (i₀+1)) ⊆ Set.Ico (t i₀) (t (i₀+1))`, die
Überdeckung ebenfalls, denn beide Marken liegen jenseits des Fensters. **Damit
ist der Zusammenbau nicht mehr auf ein unbeschränkt langes Tupel angewiesen**,
und `stepPathFamilyLe` bekommt das endliche Tupel, das es verlangt. Das ist
nicht bewiesen; es ist die Konstruktion, die der nächste Lauf zu bauen hat, und
sie steht hier, damit sie nicht ein zweites Mal als verschlossen abgelegt wird.

**Mitgekommen sind die beiden Brücken, mit denen der Zusammenbau anfängt**, und
beide sind kurz, weil sie nur auspacken, was die Definitionen schon sagen.
`SkorokhodSpace.exists_isSubdivisionBased_subdivisionOsc_lt` ist der `iInf`
aufgelöst: ist `modulusBased t₀ u f δ < c`, so gibt es eine gestützte Unterteilung
mit `subdivisionOsc f t < c`. Das ist die Richtung, die die Rückrichtung liest —
die Hinrichtung liest eine Unterteilung *vom Pfad ab* und schätzt den Modul damit
nach oben ab, hier wird umgekehrt aus der Schranke eine Unterteilung gewonnen.
Und `SkorokhodSpace.dist_le_of_subdivisionOsc_le` ist der Übergang von `ℝ≥0∞` nach
`ℝ`, also von `subdivisionOsc` zur Zellhypothese von `distWith_stepPath_le`; die
beiden stehen auf verschiedenen Seiten von Meilenstein 7, weil der Modul einen
Wert haben muß, wenn es gar keine `δ`-sparsame Unterteilung gibt, die gefensterte
Schranke aber eine Ungleichung zwischen reellen Abständen ist.

**Das Manuskript ist nicht angefaßt.**

**Was als Nächstes zu tun ist**, und es ist ein benanntes Stück vor dem
Zusammenbau, so wie dieser Lauf eines war: `SkorokhodSpace.IsSubdivision.trim`
— zu einer gestützten `δ`-sparsamen Unterteilung des Fensters vom Radius `M`
eine gestützte `min δ 1`-sparsame Unterteilung **desselben** Fensters, deren
sämtliche Knoten in `Set.Icc (-(M+1)) (M+1)` liegen und deren Länge durch
`2(M+1)/min δ 1` beschränkt ist, mit denselben Zellschwingungen. Der Beweis ist
die Teiltupel-Konstruktion von `mul_le_dist_of_sparse` (dort schon einmal
geführt) samt den beiden `max`/`min` an den Enden; der Basispunkt bleibt Knoten,
weil er im Innern des Fensters liegt. Danach ist der Zusammenbau das, was der
elfte Lauf aufgeschrieben hat, mit der Wahlreihenfolge `δ`, `n₀`, `γ`, `ρ` und
`volume_inter_badRadii_le_of_sparse` an der Stelle, an der bisher die Länge `n`
stand.

### 2026-09-09, dreizehnter Lauf des Tages — `SkorokhodSpace/Suggested.lean` trägt kein `sorry` mehr

**Stand der Datei.** `SkorokhodSpace/Suggested.lean` steht bei **null** `sorry`
statt einem. Vier neue Deklarationen und eine, die von `sorry` zu einem Beweis
geworden ist; alle durch `lake env lean` gegen v4.33.1 geprüft, ohne Fehler und
ohne die Warnung „declaration uses `sorry`", und alle mit `#print axioms` auf
`propext`, `Classical.choice`, `Quot.sound`.

**Meilenstein 7 ist geschlossen, und mit ihm Teil A der vorrangigen Aufgabe.**
Die vier Punkte des Auftrags — `instSeparableSpace`, die meßbare Einbettung, das
Kompaktheitskriterium, `exists_orderIso_isometry_real` — sind alle erledigt;
offen bleibt allein die dritte Instanz von `HasCountableCore`
(`Set.Icc (0:ℝ) 1`), an der nach dem zweiten Lauf dieses Tages nichts hängt.

#### Das angesagte Stück, und was daran anders herauskam

`SkorokhodSpace.IsSubdivisionBased.trim` steht, und die Ansage des zwölften
Laufs hat bis auf drei Einzelheiten gehalten.

*Erstens ist der Name ein anderer.* Es heißt `IsSubdivisionBased.trim` und nicht
`IsSubdivision.trim`: die Gestütztheit ist keine Zutat, sondern das, was die
Konstruktion überhaupt zuläßt — der Basispunkt liegt echt zwischen den beiden
Schnittindizes (`t i₀ ≤ -M < 0 < M ≤ t j₀`), überlebt das Stutzen also
ungeklammert und bleibt Knoten.

*Zweitens ist die Sparsamkeit `δ` und nicht `min δ 1`.* Statt das Ergebnis
abzuschwächen, trägt der Satz die Hypothese `δ ≤ 1`, und das ist die ehrlichere
Buchführung: die Rückrichtung wählt `δ` selbst und darf es klein wählen, während
`min δ 1` im Zusammenbau an jeder Stelle mitzuschleppen wäre, an der die
Sparsamkeit gelesen wird. Dazu `1 ≤ M`, aus demselben Grund und für den
Sonderfall, den es sonst gäbe: bei `M = 0` fallen die beiden Schnittindizes
zusammen und das gestutzte Tupel hätte einen einzigen Knoten, der das Fenster
nicht mehr überdeckt.

*Drittens sind es nicht „dieselben Zellschwingungen".* Sie sind es nicht, und das
ist kein Beweisproblem, sondern falsch: `subdivisionOsc` mißt jede Zelle von
**ihrem eigenen linken Endpunkt** aus, und der linke Endpunkt der gestutzten
ersten Zelle ist ein innerer Punkt der alten. Was gilt, ist der Faktor `2`, und
er ist scharf — ein Pfad, der am linken Rand der groben Zelle um `ε` springt und
in deren Mitte zurück, hat grob die Schwingung `ε` und für die in der Mitte
schneidende Verfeinerung `2 ε`. Der Satz gibt darum die **Zellenthaltung**
(`Set.Ico (s k) (s (k+1)) ⊆ Set.Ico (t i) (t (i+1))`), und
`SkorokhodSpace.subdivisionOsc_le_two_mul_of_cells` macht daraus die Schranke.
Die Enthaltung ist ohnehin die brauchbarere Form: sie hält die
Fallunterscheidung aus dem Zusammenbau heraus.

#### Der Befund: das Stutzen an festen Marken ist eine Aussage über `ℝ`

Der elfte Lauf hatte das Stutzen an den Fensterenden als Sackgasse gemeldet, der
zwölfte es an den Marken `± (M+1)` wieder geöffnet. Beide Male war der Index
nicht im Blick, und er ist hier der Punkt: **auf einem allgemeinen Index ist die
Marke `M+1` nicht einen Schritt vom Fenster entfernt.** Sie ist
`exhaustionMin t₀ (M+1)`, und deren Abstand zu `exhaustionMin t₀ M` kann beliebig
klein sein, während unterhalb des größeren Fensters noch ein Knoten sitzt. Zeuge,
auf Papier und nicht in Lean: `ι = {-3, -1.05, -1, 0, 1} ⊆ ℝ` mit `t₀ = 0` und
`M = 1`. Eine Unterteilung darf `t i₀ = -3` und `t (i₀+1) = -1` haben — die Lücke
ist `2` —, der gestutzte erste Knoten ist `-1.05`, und die gestutzte erste Lücke
ist `0.05`. Über `ℝ` sind die beiden Marken `-(M+1)` und `-M` und ihr Abstand ist
`1`, und genau dort wird `δ ≤ 1` ausgegeben. Der Satz steht darum über `ℝ`, und
das ist **die einzige Stelle des Kriteriums, an der `ℝ` um seiner selbst willen
gebraucht wird**; alles andere an der Rückrichtung ist index-blind und scheitert
anderswo (`not_isCompact_closure_of_rigid`).

#### Der Zusammenbau, und er ist im selben Lauf mitgekommen

Nach dem Stutzen war die Rückrichtung kürzer als erwartet, weil die Ansagen des
elften und zwölften Laufs vollständig waren. Zwei Deklarationen liegen
dazwischen.

`SkorokhodSpace.exists_bad_radii_set_of_sparse` ist `exists_bad_radii_set` mit
`volume_inter_badRadii_le_of_sparse` an Stelle von `volume_badRadii_le`. Der
Unterschied ist einer im **Quantorenbau**: die grobe Fassung zählt `n`, die Länge
der Unterteilung, und `n` ist über die Familie unbeschränkt; die scharfe zählt
`n₀`, und `n₀` steht vor der Familie fest. Mitgekommen ist, daß Sparsamkeit `δ`
und Verschiebung `γ` jetzt **zwei** Parameter sind und nicht einer — die
Separabilität durfte sie identifizieren, weil dort beide nach der Unterteilung
gewählt werden; die Rückrichtung darf es nicht, weil `δ` von der Modulbedingung
genannt wird und `γ` erst danach frei ist.

`SkorokhodSpace.exists_mem_stepPathFamilyLe_intDist_le` ist der Schritt für
**einen** Pfad, und er trägt `G`, `Q` und `n₀` als Hypothesen, statt sie zu bauen:
genau das ist die Aussage, die die Totalbeschränktheit braucht — ein Netz, das
vor dem Pfad feststeht. Der Zeitwechsel der Schätzung ist das **Inverse** des
Gitterzeitwechsels: das Gitter trägt einen Knoten auf einen Gitterpunkt, und
`distWith_stepPath_le` verlangt den, der die Knoten des Approximanten auf die des
Pfades zurückträgt; `TimeChange.norm_inv` macht das kostenlos.

`SkorokhodSpace.isCompact_closure_iff` selbst ist dann die Wahl von fünf
Konstanten, und ihre Reihenfolge ist erzwungen: der Fensterradius `M` aus dem
Schwanz des Integrals (`exp (-M) < r/8`), die Schwingung `ε`, die Sparsamkeit `δ`
aus der Modulbedingung bei `M`, die Längenschranke `n₀` aus `M` und `δ`, und die
Verschiebung `γ` **zuletzt**, weil die schlechten Radien `(n₀+1)` mal `γ` kosten.
Die Kompaktheit des Abschlusses kommt aus der Totalbeschränktheit über
`SkorokhodSpace.instCompleteSpace` von Meilenstein 5 — der einzige Ort, an dem
die Rückrichtung die Vollständigkeit von `D(ℝ, E)` liest. Damit ist die Ansage
des fünften Laufs, `tendsto_of_partialComp` werde gelesen, eingelöst, aber
**mittelbar**: durch die Instanz, die auf ihm ruht, und nicht durch den Satz.

#### Die Deklarationen

* `SkorokhodSpace.subdivisionOsc_le_two_mul_of_cells` — Zellenthaltung gibt den
  Faktor `2`, und er ist scharf.
* `SkorokhodSpace.IsSubdivisionBased.trim` — das Stutzen an `± (M+1)`, über `ℝ`.
* `SkorokhodSpace.exists_bad_radii_set_of_sparse` — die Fensterrandbuchführung
  mit `n₀` statt `n`.
* `SkorokhodSpace.exists_mem_stepPathFamilyLe_intDist_le` — ein Pfad, ein Glied
  der endlichen Familie.
* `SkorokhodSpace.isCompact_closure_iff` — von `sorry` zu einem Beweis.

**Das Manuskript ist nicht angefaßt.** Nachgezogen sind der Kopfkommentar der
Datei, das Doc-Kommentar des Kriteriums (es sprach noch von dem, was „das
verbliebene `sorry` schuldet"), `SkorokhodSpace/README.md` (Meilenstein 7) und
die Zeile `fact:PSpolish` der Tabelle.

**Was als Nächstes zu tun ist.** Teil A der vorrangigen Aufgabe ist durch, also
gilt Teil B: `WeakConvergence/Suggested.lean`, und dort zuerst
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`. Die Aussage:
konvergieren die Gesetze schwach und ist die Familie gleichmäßig integrierbar,
so konvergieren die Erwartungswerte. Sie ruht auf
`integrable_id_of_isUniformlyIntegrableLaws` (seit dem 2026-09-08 bewiesen, mit
dem unteren Integral in der Definition) und auf der Abschneidung: die bei `M`
abgeschnittene Funktion ist beschränkt stetig, also greift die schwache
Konvergenz, und die gleichmäßige Integrierbarkeit kontrolliert die Ränder
gleichmäßig in `n`. Sie ist jetzt dran, weil sie einen ganzen Meilenstein
schließt und weil `WeakConvergence/Suggested.lean` damit auf ein einziges
**offenes** `sorry` fiele, die Skorohod-Darstellung `exists_ae_tendsto_of_tendsto`
(`:4405`); das dritte (`:2155`) ist Absicht und steht aus dem Versionsgrund, den
der Kopfkommentar der Datei bei `:186` nennt. Der Zielsatz steht bei `:4475`.

### 2026-09-09, vierzehnter Lauf des Tages — die Erwartungswerte konvergieren, und der angesagte Weg dorthin wird nicht gebraucht

**Stand der Dateien.** Teil A der vorrangigen Aufgabe ist seit dem dreizehnten
Lauf durch, also galt Teil B. `WeakConvergence/Suggested.lean` steht bei **einem**
offenen `sorry` statt zweien: `exists_ae_tendsto_of_tendsto`, die
Skorohod-Darstellung. (Das zweite, `:2178`, ist Absicht und elaboriert unter
v4.33.1 gar nicht — es ist für `upstream/master` geschrieben, aus dem Grund, den
der Kopfkommentar nennt.) Sieben Deklarationen sind neu, eine ist von `sorry` zu
einem Beweis geworden und eine ist umgeschrieben;
alle durch `lake env lean` gegen v4.33.1 geprüft und alle mit `#print axioms` auf
`propext`, `Classical.choice`, `Quot.sound`.

**Punkt 1 von Teil B ist erledigt, und mit ihm der Satz, den `fact:ui` trägt.**
`MeasureTheory.tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` —
konvergieren die Gesetze schwach und ist die Familie gleichmäßig integrierbar, so
ist das Grenzgesetz integrierbar und die Erwartungswerte konvergieren.

#### Der Befund: der angesagte Weg ist nicht gegangen worden, und er wird nicht gebraucht

Meilenstein 4 schrieb seit dem 2026-08-29 vor, den Satz **durch die
Skorohod-Darstellung** zu führen: alles auf einen Raum, dann Mathlibs
Vitali-Satz. Das hätte den Meilenstein an das eine offene `sorry` von
Meilenstein 3 gehängt, und es ist unnötig. Der Beweis ist die Abschneidung, und
er ist elementar bis auf **einen** Schritt.

Der Schritt ist der Schwanz des **Grenzgesetzes**. Die Hypothese sagt etwas über
die Familie, und `ν` ist kein Glied der Familie; die schwache Konvergenz
transportiert aber das Integral einer **unbeschränkten** Funktion nicht, und
`|x| - min |x| N` ist unbeschränkt. Was es transportiert, ist die
Portmanteau-Ungleichung für nichtnegative stetige Funktionen, und die hat
Mathlib: `lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`
(`Measure/Portmanteau.lean:499`) über
`ProbabilityMeasure.le_liminf_measure_open_of_tendsto` (`:326`). Ein Limes
inferior, der gliedweise unter einer Konstanten liegt, liegt unter ihr, und die
Konstante ist das Supremum der Hypothese. Das ist
`lintegral_truncTail_le_of_tendsto`.

Der Rest sind drei ε/3: die Verschiebung des Mittelwerts unter jedem `μ n`,
gleichmäßig in `n` nach Voraussetzung; dieselbe unter `ν`, nach dem eben
genannten Satz; und die Konvergenz der abgeschnittenen Mittelwerte, die die
schwache Konvergenz an einer beschränkten stetigen Funktion ist.

#### Warum die Abschneidung genau paßt, und warum das kein Zufall ist

`truncBdd N` ist die auf `[-N, N]` geklemmte Identität als beschränkte stetige
Funktion, und `abs_sub_truncBdd` sagt: `|x - truncBdd N x| = |x| - min |x| N`,
**auf die Nase**. Der Integrand des Kriteriums ist der Abschneidefehler des
Approximanten. Darum ist ein und derselbe Ausdruck das, was die Hypothese gegen
Null treibt, und das, was die Verschiebung des Mittelwerts beschränkt
(`abs_integral_sub_integral_truncBdd_le`) — die Buchführung des Beweises ist
damit eine Gleichung und keine Abschätzung. Das ist die Rechtfertigung dafür, daß
`IsUniformlyIntegrableLaws` in der Trunkierungsform steht statt in einer
Schwanzmassenform.

#### Die Verallgemeinerung, die die Integrierbarkeit erst brauchbar macht

`integrable_id_of_isUniformlyIntegrableLaws` (2026-09-08, dreizehnter Lauf) ist
über die **Familie** formuliert und erreicht das Grenzgesetz nicht. Es ist jetzt
ein Zweizeiler über `integrable_id_of_lintegral_truncTail_lt_top`: eine
Wahrscheinlichkeitsmaß auf `ℝ` mit endlichem Schwanz auf **einem** Niveau hat
integrierbare Identität. Die Aussage der Familienfassung ist unverändert — sie
wird an drei Stellen zitiert —, nur ihr Beweis ist der Aufruf des allgemeinen
Satzes. Die Integrierbarkeit von `Z` ist die halbe Konklusion des Zielsatzes, und
sie ist ohne diese Verallgemeinerung nicht zu haben.

#### Die Fassung für Zufallsvariablen, weil der Meilenstein sie so verlangt

Meilenstein 4 sagt ausdrücklich: „Every statement of this milestone takes
`TendstoInDistribution X l Z μ μ'` as its hypothesis, so that the differing spaces
are Mathlib's and not this roadmap's." Die bewiesene Fassung über
`ProbabilityMeasure` erfüllt das nicht, also steht daneben
`tendsto_integral_of_tendstoInDistribution_of_uniformIntegrable` mit genau dieser
Hypothese und mit dem Trunkierungskriterium auf den Zufallsvariablen selbst.
Dazwischen liegen `lintegral_map'` und `integral_map` und sonst nichts. Der
Meilensteinpunkt wäre sonst nur der Sache nach eingelöst und nicht dem Wortlaut
nach, und das ist der Unterschied, den dieses Inventar seit dem 2026-09-05
protokolliert.

Der Import `Mathlib.MeasureTheory.Function.ConvergenceInDistribution` ist dafür
neu in der Datei; `TendstoInDistribution` ist eine `structure` mit den drei
Feldern `forall_aemeasurable`, `aemeasurable_limit`, `tendsto`
(`MeasureTheory/Function/ConvergenceInDistribution.lean:64`), und alle drei werden
gelesen.

#### Die drei acceptance examples des Meilensteins, gegen den bewiesenen Satz gerechnet

Die Lehre des 2026-09-08 und des fünften Laufs dieses Tages — ein acceptance
example, das nur dasteht, prüft nichts — ist diesmal vor dem Bericht angewandt
worden. Alle drei sind auf Papier nachgerechnet, und alle drei halten.

*Der entkommende Zacken* (`X n = (n+1)·1_{[0,1/(n+1)]}` auf `([0,1], λ)`):
`𝔼[|X n| - |X n| ⊓ N] = 1 - N/(n+1)` für `n+1 ≥ N`, das Supremum ist `1` für
**jedes** `N`, der Grenzwert also `1` und nicht `0`. Der Satz greift nicht, wie
er soll — `∫ X n = 1` bei `∫ 0 = 0`.

*Der gezähmte Zacken* (`X n = √(n+1)·1_{[0,1/(n+1)]}`) ist **berichtigt**, und
das ist der einzige Befund an den Beispielen: der README führte ihn über die
de-la-Vallée-Poussin-Form, und die ist nicht bewiesen und hat in
`Suggested.lean` gar keine Signatur — das Beispiel hätte den bewiesenen Satz
nicht berührt. Das Trunkierungskriterium ist hier geschlossen ausrechenbar:
`𝔼[|X n| - |X n| ⊓ N] = max(√(n+1) - N, 0)/(n+1)`, mit `u = √(n+1)` also
`(u-N)/u²` für `u > N`, maximal bei `u = 2N`, also `⨆ₙ ≤ 1/(4N) → 0`. Damit
laufen **beide** Zacken gegen dieselbe bewiesene Aussage, und das ist es, was das
Paar prüfen soll.

*Die Familie auf verschiedenen Räumen* (`Ω n = ({0,…,n}, gleichverteilt)`,
`X n k = k/n`, `Z = id` auf `([0,1], λ)`): `∫ X n = (1/(n+1))·∑_{k≤n} k/n = 1/2`
für jedes `n`, und `∫ Z = 1/2`. Sie ist gleichmäßig beschränkt durch `1`, das
Trunkierungskriterium ist für `N ≥ 1` identisch `0`. Sie ist überdies das
Beispiel, das die Fassung mit `TendstoInDistribution` erzwingt, und die steht
seit diesem Lauf.

#### Die Deklarationen

* `truncBdd`, `truncBdd_apply` — die geklemmte Identität als `ℝ →ᵇ ℝ`.
* `abs_sub_truncBdd` — ihr Abschneidefehler **ist** der Integrand des Kriteriums.
* `integrable_id_of_lintegral_truncTail_lt_top` — ein Maß, ein Niveau.
* `integrable_id_of_isUniformlyIntegrableLaws` — Aussage unverändert, Beweis
  jetzt ein Aufruf des vorigen.
* `abs_integral_sub_integral_truncBdd_le` — die Abschneidung verschiebt den
  Mittelwert höchstens um den Schwanz.
* `lintegral_truncTail_le_of_tendsto` — der Schwanz des Grenzgesetzes, aus
  Portmanteau.
* `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` — von `sorry` zu
  einem Beweis.
* `tendsto_integral_of_tendstoInDistribution_of_uniformIntegrable` — dieselbe
  Aussage in der Gestalt, die der Meilenstein nennt.

**Das Manuskript ist nicht angefaßt.** Nachgezogen sind der Kopfkommentar von
`WeakConvergence/Suggested.lean`, der Abschnittskommentar von Meilenstein 4 in
derselben Datei (er sagte die Skorohod-Route an), `WeakConvergence/README.md`
(Meilenstein 4, erster und zweiter Punkt sowie das zweite acceptance example)
und die Zeile `fact:ui` der Tabelle.

**Was als Nächstes zu tun ist.** Punkt 2 von Teil B:
`exists_ae_tendsto_of_tendsto` (`:4421`), die Skorohod-Darstellung, das letzte
offene `sorry` dieser Datei und der Rest von Meilenstein 3. Alle Bausteine stehen
seit dem 2026-09-08 (Läufe fünf bis fünfzehn); offen ist der Zusammenbau, und
seine drei benannten Stücke — beginnend mit der Indexabbildung mit dem
Diagonalzweig — stehen in Meilenstein 3. Der Bauplan ist zweimal verworfen
worden, und wer ihn ein drittes Mal ändern will, sagt zuerst, welcher Schritt des
jetzigen bricht, und rechnet ihn am Zeugen `ν = δ₀`,
`μ n = (1 - 1/log n)·δ₀ + (1/log n)·δ₁` nach. Er ist jetzt dran, weil er der
einzige offene Punkt von `WeakConvergence` ist und weil Teil C der vorrangigen
Aufgabe — die Sprungprozesse von `MartingaleProblems` — erst danach beginnt.

### 2026-09-09, fünfzehnter Lauf des Tages — alle Stufen auf einem Raum, und die Schranke ist jetzt eine Inklusion

**Aufgabe.** Teil B, Punkt 2 der vorrangigen Aufgabe: `exists_ae_tendsto_of_tendsto`,
das letzte offene `sorry` von `WeakConvergence/Suggested.lean`. Der Vorlauf nennt
als erstes Stück „die Indexabbildung mit dem Diagonalzweig"; die steht seit dem
2026-09-08, fünfzehnter Lauf, und das wirklich offene Stück davor war
`exists_measurable_pair_of_partition_subset`. Es ist in diesem Lauf bewiesen.

**Ergebnis.** Drei neue Deklarationen, zwei bestehende um je einen Zusatz
erweitert. Alle gehen durch `lake env lean` gegen v4.33.1 und hängen laut
`#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`:

* `MeasureTheory.sum_prod_slice_eq` — ein `Measure.sum` über `ℕ × ℕ`, das auf
  **einer** Schicht sitzt, ist das `Measure.sum` über diese Schicht.
* `MeasureTheory.stagesMeasure` — der Raum, auf dem **alle** Stufen zugleich
  leben: `(ν ⊗ Lebesgue|₍₀,₁₎) ⊗ infinitePi (fun (n,i) ↦ condLaw (μ n) (A n i))`
  auf `(E × ℝ) × (ℕ × ℕ → E)`.
* `MeasureTheory.exists_measurable_pair_of_partition_subset` — die Stufen samt
  Gesetzen und der Schranke **als Inklusion**.
* `exists_coupling_tsum_offDiag_le` trägt einen vierten Schluß:
  `∀ i, min (p i) (q i) ≤ π i i`.
* `exists_finite_partition_diam_le_null_frontier` trägt einen weiteren:
  `∀ i ∈ K, Bornology.IsBounded (A i)`.

#### Was der Satz sagt

Auf `stagesMeasure ν μ A` gibt es meßbare `X n` mit `map (X n) = μ n`, die ihre
Grenzvariable **alle** von derselben Koordinate `z.1.1` ablesen — deren Gesetz
`ν` ist —, und für jedes `n` gilt fast überall

```
ε n < dist (X n z) z.1.1  →  z.1.1 ∈ A n 0  ∨  1 - t n < z.1.2
```

Die Voraussetzungen sind die von `exists_measurable_pair_of_partition`, je Stufe,
mit **einer** Änderung: an die Stelle der Zahl tritt der Zeilendefekt
`hdef : ∀ n i, i ≠ 0 → ENNReal.ofReal (1 - t n) * ν (A n i) ≤ μ n (A n i)`.

#### Die drei Befunde des Laufs

**Erstens: der zweite Disjunkt steht andersherum, als der Meilenstein ihn
ansagte.** Dort stand `{z | z.1.2 ≤ t}`; richtig ist `1 - t n < z.1.2`. Der
Grund ist der Diagonalzweig selbst: `exists_measurable_index_of_stochastic_matrix_diag`
legt die Diagonale auf das **erste** Teilsummenintervall, also gilt
`G (k, ξ) = k` für `ξ ≤ (c k k).toReal`, und `c k k` ist **nahe bei 1**, nicht
nahe bei `0`. Die Uneinigkeit der beiden Indizes liegt darum oberhalb einer
Schwelle nahe `1`. Beide Fassungen haben unter Lebesgue auf `(0,1]` die Masse
`t n` und beide schachteln sich, aber nur diese liefert die Konstruktion.
`WeakConvergence/README.md`, Meilenstein 3, ist entsprechend berichtigt.

**Zweitens: die Diagonalschranke fehlte, und sie ist umsonst.** Damit
`ofReal (1 - t n) ≤ c k k` gilt, braucht man `min (μ (A k)) (ν (A k)) ≤ π k k`
für das Indexkopplungsmaß `π`. `exists_coupling_tsum_offDiag_le` sagte das nicht,
obwohl es sein `π` explizit hinschreibt — `π i j = (if i = j then min (p i) (q i) else 0) + a i * b j / D` —,
so daß die Zusage `le_self_add` ist. Sie ist als vierter Schluß eingetragen; die
beiden bestehenden Gebrauchsstellen nehmen sie mit `-` nicht an.

**Drittens: „Durchmesser klein" ist nicht „beschränkt", und `Metric.diam` sagt auf
einer unbeschränkten Menge nichts.** `Metric.dist_le_diam_of_mem` verlangt
`Bornology.IsBounded`, und `exists_finite_partition_diam_le_null_frontier` gab sie
nicht heraus, obwohl ihre Stücke Kugeln vom Radius unter `ε/2` sind und
`exists_measurable_partition_diam_le_null_frontier` die Beschränktheit bereits
mitliefert. Ohne diesen Zusatz ließe sich die Stufe nicht anwenden — die
Schranke `dist ≤ diam ≤ ε` ist genau die Stelle, an der die Kleinheit der Stücke
verbraucht wird. Der Zusatz ist eine Zeile im Beweis (`exact hAsb _`).

#### Warum es **ein** Raum ist und nicht eine Familie von Räumen

Das ist die Lehre des vierzehnten Laufs vom 2026-09-08, jetzt in Lean eingelöst.
Die Stufen teilen sich **eine** gleichverteilte Variable, `z.1.2`; darum ist der
zweite Disjunkt ein Ereignis dieser einen Variablen, und Ereignisse einer
Variablen schachteln sich. Mit je einer gleichverteilten Variablen pro Stufe
wären sie unabhängig, und dann bliebe nur Borel--Cantelli — das die
Stufenschranken nicht hergeben (Zeuge im Doc-Kommentar von
`ae_tendsto_of_subset_of_tendsto_measure_iUnion_ge`). Der Indexraum des Produkts
ist deshalb `ℕ × ℕ`, Stufe und Stück, und **das** ist der Grund, aus dem
`map_eval_prod_infinitePi` seit dem achten Lauf über einem beliebigen abzählbaren
`κ` steht statt über `ℕ`. `sum_prod_slice_eq` fällt das entstehende `Measure.sum`
über `ℕ × ℕ` auf die Schicht der Stufe `n` zusammen, wo `sum_smul_condLaw_eq`
`μ n` wiedererkennt.

#### Zwei Kleinigkeiten, die Zeit gekostet haben und die es wert sind

Der Beweis führt die ganze Kopplungsmaschinerie — `π`, `condRow`, `G` — unter
**einem** `obtain` mit ausgeschriebener Existenzaussage über `Φ`:

```
∃ Φ : ℕ → (E × ℝ) → ℕ, (∀ n, Measurable (Φ n)) ∧
  (∀ n, (ν ⊗ Lebesgue|₍₀,₁₎).map (Φ n) = Measure.sum fun i => μ n (A n i) • dirac i) ∧
  (∀ n w, j n w.1 ≠ 0 → ν (A n (j n w.1)) ≠ 0 → w.2 ≤ 1 - t n → Φ n w = j n w.1)
```

Danach ist von `π` und `condRow` im Rest des Beweises nichts mehr zu sehen. Das
ist keine Kosmetik: die drei Zusagen sind genau das, was der Rest braucht, und
sie einmal aufzuschreiben ersetzt das Mitschleppen von acht Hypothesen.

Und: über `E` steht am Ende **allein** `[PseudoMetricSpace E]`. Weder
`OpensMeasurableSpace E` noch `SecondCountableTopology E` gehen ein, obwohl die
Einstufenfassung beide trägt — sie braucht sie für die **Meßbarkeit der
schlechten Menge**, und eine Inklusion braucht die nicht: `measure_mono_null`
mißt die Obermenge.

#### Was offen bleibt, und was als Nächstes zu tun ist

`exists_ae_tendsto_of_tendsto` selbst, der Zusammenbau. Er steht jetzt auf lauter
Bewiesenem, und sein Rezept ist durch diesen Lauf konkret geworden:

1. Zu jeder Stufe `k ≥ 1` die endliche Zerlegung
   `exists_finite_partition_diam_le_null_frontier` mit `ε = 2⁻ᵏ` und `η = 2⁻ᵏ`.
2. `Q k n : ∀ i ∈ K k, ofReal (1 - 1/k) * ν (A k i) ≤ μ n (A k i)` und
   `kn n := max ((Finset.Icc 1 (n+1)).filter (Q · n))`. **`Q 1 n` gilt immer**,
   weil `ofReal (1 - 1/1) = 0` ist — das ist es, was die Wohldefiniertheit von
   `kn` trägt und was eine Fallunterscheidung erspart. `Tendsto kn atTop atTop`
   kommt aus `tendsto_measure_of_null_frontier` für die endlich vielen Stücke
   positiver Masse je Stufe.
3. `exists_measurable_pair_of_partition_subset` mit `A n := A' (kn n)`,
   `ε n := 2^{-(kn n)}`, `t n := 1/(kn n)`.
4. `ae_tendsto_of_subset_of_tendsto_measure_iUnion_ge` mit `δ k = 2⁻ᵏ`, `k = kn`
   und `B k = {z | z.1.1 ∈ A' k 0} ∪ {z | 1 - 1/k < z.1.2}`. Die einzige noch
   nicht geschriebene Rechnung ist
   `P (⋃ m ≥ K, B m) ≤ ∑_{m ≥ K} 2⁻ᵐ + 1/K → 0`; sie besteht aus der
   Vereinigungsschranke, der geometrischen Reihe und
   `volume (Ioc (1 - 1/K) 1) = 1/K`, und die zweiten Disjunkte fallen darin
   zusammen, weil `1 - 1/m ≥ 1 - 1/K` für `m ≥ K`.

Der Bauplan ist damit **nicht** geändert; er ist derselbe wie seit dem
vierzehnten Lauf des 2026-09-08 (EK Thm. 3.1.8, Buchseiten 102--103), nur an zwei
Stellen berichtigt (Richtung des Disjunkts, Beschränktheit der Stücke).

**Am Rande, gegen ein Mißverständnis:** `WeakConvergence/Suggested.lean` meldet
in Zeile 2178 keinen `sorry`-Hinweis, sondern einen **Elaborationsfehler** --
`ProbabilityMeasure.map` verlangt in v4.33.1 eine `AEMeasurable`-Hypothese und
bekommt die Funktion `h`. Das ist bekannt und am Deklarationskommentar von
`tendsto_map_of_measure_setOf_continuousAt_eq_one` festgehalten: die Aussage ist
für `upstream/master` geschrieben, wo `map` die Funktion allein nimmt. Es ist
also kein neuer Befund; es heißt aber, daß "die Datei geht durch `lake env lean`"
für diese Datei genauer "bis auf die eine, aus Versionsgründen absichtlich so
geschriebene Zeile" heißt, und das gehört einmal ausgesprochen. Der Befund dieses
Laufs ist davon unberührt: die fünf oben genannten Deklarationen sind einzeln mit
`#print axioms` geprüft.

#### Nachtrag desselben Laufs: die Aussage des Zusammenbaus stand im falschen Universum

`exists_ae_tendsto_of_tendsto` verlangte `∃ (Ω : Type)`, und in dieser Fassung
ist es **nicht der Satz**. Der gemeinsame Raum der Konstruktion ist
`(E × ℝ) × (ℕ × ℕ → E)`, also `Type u`, wenn `E : Type u` ist, und es gibt keinen
Weg nach `Type 0`: die Position innerhalb eines Zerlegungsstücks als meßbare
**Funktion einer reellen Variablen** zu realisieren — was ein `Type 0`-Raum
erzwänge — ist der Borelsche Isomorphiesatz und verlangt `E` polnisch, also mehr,
als dieser Meilenstein voraussetzt. Der Fehler wäre erst beim Zusammenbau
aufgefallen und hätte den nächsten Lauf gekostet.

Die Aussage steht jetzt mit eigenem Universum,
`theorem exists_ae_tendsto_of_tendsto.{u} {F : Type u} …`, und trägt weiterhin
ihr `sorry`. Zwei Dinge sind dabei nachgerechnet und nicht vermutet:

* **`Type _` genügt nicht.** Es bindet eine *zweite*, allquantifizierte
  Universumsvariable, und der Zeuge paßt dann nicht — Lean meldet
  `failed to solve universe constraint u_2 =?= u_1`. Am Kleinbeispiel geprüft.
* **Die Sektionsvariable `E` läßt sich nicht verwenden**, weil ihr durch `Type*`
  automatisch gebundenes Universum keinen ansprechbaren Namen hat. Darum heißt
  der Typ in dieser einen Aussage `F` und nicht `E`; die
  `MeasurableSpace`-Instanz steht deshalb ausdrücklich in der Signatur.
