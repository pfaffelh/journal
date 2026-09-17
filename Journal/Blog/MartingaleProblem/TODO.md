# Was am Wochenende bei Dir liegt

Stand 2026-09-08; die Zahlen im letzten Abschnitt sind am 2026-09-15
nachgeführt. Alles, was ich vorbereiten konnte, ist vorbereitet und gepusht; was
hier steht, braucht Dich. Die Läufe sammeln auf `facts-inventory` — seit dem
7. September zunächst stündlich, dann gestreckt, und seit dem Abend des
15. September durch die Zeitschranke auf fisher **angehalten**; siehe den
letzten Abschnitt.

## 1. Die Einreichung bei Tau Ceti — der einzige echte Engpass

Die vier Roadmaps sind seit dem 29. August fertig und seither erheblich besser
geworden; eingereicht ist nichts. Ohne Fork, `[Intention]`-Issue und PR
formalisiert dort niemand danach.

**Vorbereitet und bereitliegend:**

* `TauCeti/SUBMISSION.md` — der Weg, plus was die Projektdokumente verlangen.
  Keine Größengrenze für PRs; die Grenze ist die Reviewlast.
* `TauCeti/PR-BESCHREIBUNG.md` — Entwürfe aller vier PR-Beschreibungen, samt
  dem KI-Attributionsblock, den `CONTRIBUTING.md` verlangt. **Lies ihn**: er
  nennt Modelle, Zeitraum und die Fehler, die das Verfahren in meiner eigenen
  Arbeit gefunden hat. Das Projekt verlangt ausdrücklich, daß niemand etwas
  postet, was er nicht selbst gelesen hat.
* `TauCeti/VORBILD-OneParameterSemigroups.md` — die Aufbereitung von PR #16 mit
  Reviewverlauf und Checkliste. **Die eine Stelle, die Du kennen solltest:**
  der Reviewer hat verlangt, sich nicht auf eigenes externes Material zu
  stützen, weil KI-Reviewer es sonst als Standard nehmen. Unsere vier Stellen
  dazu sind entschärft.

**Reihenfolge:** `WeakConvergence` zuerst (hängt nur an Mathlib, trägt die
meisten bewiesenen Deklarationen), dann `KolmogorovExtension`,
`SkorokhodSpace`, `MartingaleProblems`. Vier getrennte PRs, `awaiting-review`
als Label.

## 2. Zulip, vor dem PR: wo gehört Feller hin?

Das ist die inhaltlich interessanteste offene Frage, und sie gehört an die
Leute dort, nicht in eine Datei. Ein Feller-Prozeß ist über eine **stark
stetige** Halbgruppe auf $\hat C(E)$ definiert — das Objekt ihrer Teil A — und
ist zugleich ein Markovprozeß, also unser Gegenstand. Er fällt damit zwischen
beide Roadmaps und wird von keiner abgedeckt:

| | Halbgruppe | Raum | wo |
|---|---|---|---|
| Feller | stark stetig auf $\hat C(E)$ | lokal kompakt | **bei niemandem** |
| Markov allgemein | meßbar auf $B(E)$, voller Erzeuger mehrwertig | polnisch | unser M13 |
| Funktionalanalysis | stark stetig auf Banachraum | Banach | `OneParameterSemigroups` |

**Und die lokale Kompaktheit ist keine Sperre** — das war meine erste
Darstellung, und sie war zu eng. Sie gehört zum *klassischen* Begriff; daneben
gibt es $C_b$-Feller auf polnischen Räumen und die *generalized Feller
semigroups* auf gewichteten Räumen $\mathcal B^\psi$ (Dörsek--Teichmann), die
das Manuskript in §7.7 selbst zitiert, weil \CT{} die Markovschen Lifts der
Volterra-Prozesse damit charakterisieren. Die Frage an Zulip ist also nicht
„geht Feller überhaupt", sondern **welcher Begriff** — und gewichtete Räume
passen in deren Banach-Rahmen.

**Der konkrete Satz, den man mitbringen kann.** EK Theorem 4.4.1: *ein
Markovprozeß ist die eindeutige Lösung des Martingalproblems seines Erzeugers*.
Er sitzt direkt auf Hille--Yosida — er verlangt $A$ linear und dissipativ und
eine Teilrelation $A'$ mit $\mathcal R(\lambda-A')=\mathcal D(A')=L$
trennend — also auf **ihrer** Teil A. Unser Meilenstein 6 hat die
Gegenrichtung (aus Eindeutigkeit folgt Markov, EK 4.4.2). **Keine der beiden
Roadmaps hat die vollständige Eindeutigkeitstheorie allein**; zusammen hätten
sie sie. Das ist ein besseres Anliegen als eine Zuständigkeitsfrage.

Dazu: unser Meilenstein 13 (voller Erzeuger einer **meßbaren** Halbgruppe, EK
Prop. 1.5.1) fehlt in ihrer Roadmap ganz, und ihr erklärtes Publikum nennt
„Markov semigroups". Das ist ein Angebot, kein Konflikt. Nach PR #16 gab es
dort schon einen Zulip-Faden „Contention" über Arbeitsteilung — dieselbe Lage.

Topic: `#Tau Ceti > Getting started: roadmaps` auf dem Lean-Zulip.

## 3. Zwei Roadmaps querlesen

`CONTRIBUTING.md` empfiehlt es vor dem ersten PR, und es sind Deine Fachgebiete
— das nehme ich Dir nicht ab, der Nutzen liegt im Lesen:

* `Exchangeability` (47 KB) — de Finetti, Pfadraum $E^{\mathbb N}$
* `OptimalTransport` (152 KB) — schwache Konvergenz, Prohorov, dieselbe
  Mathlib-Schicht wie unser `WeakConvergence`

## 4. Reviewen, wenn Du magst

Braucht keine Rechte: *„Reviewing someone else's roadmap PR is welcome at any
time and does not require permissions. Substantive review, especially from a
subject-area expert, is the thing we are shortest of."* Derzeit sechs offene
PRs mit `awaiting-review`, aber **keiner aus der Stochastik** — Algebra,
Geometrie, Topologie. Fachlich näher liegt Dir keiner; das ist selbst ein
Befund: unsere vier wären die Eröffnung eines Gebiets.

Wenn Du reviewst: KI-gestützte Kommentare tragen ein `:robot:`-Präfix, und ich
kann vorbereiten, aber Du mußt es gelesen haben.

## 5. Deine sieben Mathlib-PRs

Liegen seit Juni bzw. November 2025, sechs mit Mergeability `UNKNOWN`, der
Branch 5231 Commits hinter master. Drei davon — #36089, #36160, #36225 zu
`CompactSystem` — sind der Unterbau, auf den `KolmogorovExtension` zeigt.
Schlafen sie ein, hat die Roadmap eine Lücke, die sie für gefüllt hält. Das ist
Deine Sache; ich kann Dir ansehen, woran sie hängen, wenn Du willst.

## 6. Ein Mathlib-PR, der nebenbei abfällt

Kein Roadmap-Punkt, sondern ein Fund beim Beweisen von `fact:stoneweierstrass`.
Er ist **absichtlich nicht** an die Läufe gegeben, damit sie am Martingalproblem
bleiben; er liegt hier, bis Du Lust darauf hast.

**Was Mathlib hat.** `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
(`MeasureTheory/Measure/LevyConvergence.lean:154`) — schon über einem beliebigen
Filter, das ist also nichts, was wir überbieten müßten. Sie *setzt* aber die
Straffheit voraus.

**Was Mathlib nicht hat.** Einen Weg *zur* Straffheit in einem allgemeinen
metrischen Raum. Alles, was `IsTightMeasureSet` als Konklusion hat, verlangt
`ProperSpace`, ein Innenprodukt samt Orthonormalbasis (`TightNormed.lean`) oder
gleich relative Kompaktheit (`Prokhorov.lean`) — durchweg der normierte Fall.
Unser `isTightMeasureSet_of_stronglySeparatesPoints` zieht sie statt dessen aus
einer Bedingung an die **Funktionenklasse**. Das ist keine Verallgemeinerung
eines vorhandenen Lemmas, sondern eine fehlende Kante.

**Und die kleine, prüfbare Frage**, die einen sauberen PR ergäbe: jenes Lemma
trägt `[PolishSpace E]`, ruft im Beweis aber die schwächere Extensionalität
`ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`
auf. Polnisch wird dort nur noch für `upgradeIsCompletelyMetrizable` und die
Kompaktheit des Abschlusses gebraucht. Ob `CompleteSpace` +
`SecondCountableTopology` reichen, entscheidet sich in einer Viertelstunde:
Aussage abschreiben, Voraussetzungen schwächen, denselben Beweis laufen lassen,
sehen wo er bricht. Geht es durch, ist es ein kleiner PR, der mit unserer
Roadmap nichts zu tun hat und trotzdem aus ihr fällt.

## 7. Zwei Kleinigkeiten, die aus dem 8. September übrigblieben

Beides klein, beides nicht dringend, beides ausdrücklich **nicht** an die Läufe
gegeben.

**a) Die Werkstattdatei einsortieren.** `exists_kernel_pi_of_markov` liegt in
`TauCeti/KolmogorovExtension/scratch/TrajPi.lean`. Sie beweist aus Mathlibs
Ionescu--Tulcea (`ProbabilityTheory.Kernel.traj`) über bloßem
`[MeasurableSpace E]` einen Markovkern `η : Kernel E (ℕ → E)` mit vorgegebenen
Rändern, übersetzt gegen v4.33.1 und hängt an nichts als `propext`,
`Classical.choice`, `Quot.sound`. Für uns ist sie richtig abgelegt; eine
Tau-Ceti-Roadmap soll aber keinen Werkstattkram enthalten. Vor der Einreichung
also entweder in `Suggested.lean` aufnehmen — dort gehört sie hin, wenn
`KolmogorovExtension` das abzählbare Produkt braucht — oder aus dem
Einreichungsbaum heraus.

**b) Ionescu--Tulcea über einen allgemeinen Index.** Mathlibs `Traj.lean` ist auf
`{X : ℕ → Type*}` festgelegt, während die Hilfsdatei `Maps.lean` daneben schon
für `[LinearOrder ι] [LocallyFiniteOrder ι] [DecidableLE ι]` geschrieben ist —
die Tür steht also offen und ist nicht durchschritten.

*Was es wert ist:* wenig Mathematik, etwas Bequemlichkeit. Eine lokal endliche
lineare Ordnung mit kleinstem Element ist ordnungsisomorph zu einem Anfangsstück
von $\mathbb N$ (jedes $x$ hat wegen $|[\bot,x]|<\infty$ endlichen Rang, und
$x \mapsto |[\bot,x)|$ ist der Isomorphismus), es wäre also Umindizierung, kein
Satz. Für uns trotzdem an einer bekannten Stelle nützlich: die Gitter
$h\cdot\mathbb Z_{\ge 0}$ aus `rem:skorokhodform` sind isomorph zu $\mathbb N$,
aber nicht definitionsgleich, und heute müßte man den Isomorphismus jedesmal von
Hand durchschieben.

*Und wo die Grenze liegt:* weiter geht es nicht. Ionescu--Tulcea iteriert Kerne
und braucht eine Nachfolgerstruktur; für überabzählbaren Index — also unser
eigentliches $\T=[0,\infty)$ — gibt es keine Fassung. Dort ist Kolmogorov
zuständig, und der verlangt eine Voraussetzung an den Raum. Das ist die
Arbeitsteilung der beiden Sätze, keine Lücke:

| | Index | Voraussetzung an den Raum |
|---|---|---|
| Ionescu--Tulcea | Ordnungstyp $\omega$ | **keine** |
| Kolmogorov | beliebig | standard-borelsch o. ä. |

## 8. Dreiundzwanzig Lücken in Mathlibs Kernschicht, gefunden beim Bauen der Sprungprozesse

Alle zweiundzwanzig beim Beweisen aufgefallen, und die ersten vier sind kleine,
in sich abgeschlossene Beiträge. Sie gehören thematisch zu
`KolmogorovExtension` und **nicht** in eine der laufenden Aufgaben.

**Sämtliche Negativaussagen dieses Punktes sind am 2026-09-17 gegen
`upstream/master` `f61f3ed7633` (2026-09-17) nachgeprüft.** Eine von ihnen war
falsch geworden und ist berichtigt: die Kompositionsaussage der siebzehnten
Lücke steht auf `master` seit dem 2026-08-25. Alle übrigen stehen. Die Prüfung
ist mechanisiert und wiederholbar — `scripts/check_negatives.py` führt jede
Behauptung mit ihrem Suchmuster und den Dateien, in denen ein Treffer bekannt
und harmlos ist, und meldet jeden Treffer daneben; der Lauf vom 2026-09-17
meldet über 37 Behauptungen **keinen**. Was das Skript nicht leistet, steht in
seinem Dateikopf: es prüft Zeichenketten, nicht Aussagen.

* **Zeithomogenität von `Kernel.traj`.** Daß die Verschiebung einer homogenen
  Markovkette wieder dieselbe Kette ist, steht dort nicht — weder in `v4.33.1`
  noch auf `master`. Wir haben es am 2026-09-09 als `chainKernel_map_shift`
  bewiesen, über die endlichdimensionalen Verteilungen; der ganze Inhalt ist
  unser `partialTraj_succ_map_shiftIic` — der Name ist **unserer**, Mathlib hat
  in `Probability/Kernel/IonescuTulcea/` das Wort `shift` nirgends —, wo die
  verschobene Familie definitionsgleich der nächsten ist, der Rest Induktion und
  Eindeutigkeit des projektiven Limes.
  Für Mathlib wäre die richtige Fassung nicht unsere, sondern eine über
  `Kernel.traj` selbst, mit einer Homogenitätshypothese an die Familie.

* **Gedächtnislosigkeit der Exponentialverteilung.** Die Zeichenkette
  `memoryless` kommt in der ganzen Bibliothek nicht vor. Wir haben sie als
  `expMeasure_Ioi_add` bewiesen. Sie ist der einzige nicht buchhalterische
  Schritt im Beweis von `thm:jumpMP`, und sie ist elementar — ein Kandidat für
  einen Vier-Zeilen-PR neben `Probability/Distributions/Exponential.lean`.
  Dazu gehört der Schwanz selbst, `expMeasure_Ioi`, den Mathlib ebenfalls nicht
  hat (nur die Verteilungsfunktion `cdf_expMeasure_eq`), und seit dem zehnten
  Lauf des 2026-09-13 seine Fortsetzung unterhalb von `0`,
  `expMeasure_Ioi_of_nonpos`: oberhalb eines nichtpositiven Pegels liegt die ganze
  Masse. Die drei gehören in **einen** PR; einzeln sind sie zu klein.

* **Vollständigkeit der Konvergenz im Maß.** `ConvergenceInMeasure.lean` enthält
  das Wort `cauchy` nicht ein einziges Mal; der $L^p$-Fall verlangt eine
  Normgruppe, während der Grenzwert hier *erzeugt* und nicht wiedererkannt werden
  muß. Wir haben es am 2026-09-08 für $M_E$ als
  `exists_tendsto_distInMeasure_of_cauchy` nach Kurtz (4.2)--(4.4) bewiesen.

* **Eine Koordinate gegen ihren Schwanz, im unendlichen Produkt.** Die Aussage
  `(infinitePi μ).map (fun x ↦ (x 0, x ∘ Nat.succ)) = μ.prod (infinitePi μ)` fehlt,
  und zwar dreimal knapp: `Measure.map_infinitePi_infinitePi_of_inj` gibt
  Reindizierungen (rechts stünde wieder ein `infinitePi`, hier steht ein
  Produkt), `Measure.infinitePi_map_eval_prod` gibt das Paar zweier Koordinaten,
  und `iIndepFun.indepFun_finset` trennt aus der Unabhängigkeit der Koordinaten
  nur **endliche** Indexmengen — der Schwanz ist unendlich. Wir haben es am
  2026-09-09 als `infinitePi_map_natCons` bewiesen, in der
  Zusammensetzungsrichtung, weil die eine Aussage über Quader ist und
  `Measure.eq_infinitePi` gerade danach fragt. Für Mathlib wäre die richtige
  Fassung die allgemeine Trennung `iIndepFun` gegen zwei disjunkte **beliebige**
  Indexmengen; sie ist ein Dynkin-Argument und wäre mehr als unsere.

* **Der gestoppte Martingalsatz in stetiger Zeit.** Der fünfte, und der einzige
  große: `Probability/Martingale/OptionalStopping.lean` steht in ganzer Länge
  unter `{𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}` (master `403547feec1`, `:38`),
  also auch `Submartingale.stoppedProcess`, und ein
  `IsStable 𝓕 (fun Y ↦ Martingale Y 𝓕 P)` gibt es in keiner der beiden Fassungen.
  Was da ist, ist das optionale Sampling für Stoppzeiten **abzählbaren
  Wertebereichs**, über beliebigem `[LinearOrder ι] [TopologicalSpace ι]
  [OrderTopology ι]` (`OptionalSampling.lean:90` und `:121`). Wir haben den
  Übergang am 2026-09-10 als `martingale_stoppedProcess` bewiesen, über `ℝ≥0`,
  durch dyadische Approximation der Stoppzeit von oben, und mit **Beschränktheit
  auf jedem Fenster** statt der klassischen gleichgradigen Integrierbarkeit — die
  Fassung, die der beschränkte Erzeuger geschenkt liefert. Für Mathlib wäre die
  richtige Fassung die mit gleichgradiger Integrierbarkeit und über einem
  allgemeineren Index als `ℝ≥0`; sie ist mehr als unsere, und
  `RemyDegenne/brownian-motion` hat mit
  `Martingale.uniformIntegrable_stoppedValue_of_countable_range`
  (`StochasticIntegral/UniformIntegrable.lean:147`) schon das Stück davon, das
  uns fehlt.

* **Die Volterra-Resolvente, und die Faltungsalgebra der kausalen Kerne.** Der
  achte, und der einzige, der eine kleine Theorie und nicht ein Lemma wäre.
  Mathlib hat `volterra`, `renewal`, `resolvent kernel` und `Neumann series` mit
  **null Treffern** (geprüft am 2026-09-11). Vorhanden ist die Faltung
  (`Analysis/Convolution.lean`, 65 Sätze) und die Neumann-Reihe in einer
  *normierten Algebra* (`NormedRing.inverse_one_sub`), die `‖φ‖ < 1` verlangt.
  Der Volterra-Trick braucht das gerade **nicht**: auf `[0,δ]` mit
  `∫₀^δ φ < 1` konvergiert die Reihe, und man schreitet fort — eine Aussage über
  die **Kausalität** des Kerns (`φ * m` bei `t` hängt nur von `m` auf `[0,t]` ab),
  nicht über eine Banachalgebra. Die Algebra der kausalen Kerne auf `[0,∞)`, in
  der jedes Element quasinilpotent ist, fehlt.

  *Woran es bei uns hängt:* das Manuskript beweist damit, daß ein linearer
  Hawkes-Prozeß **nie explodiert** (`ex:hawkes`, über `m = μ₀ + φ * m`), und das
  ist genau die Voraussetzung `𝔼[N_t] < ∞` von `thm:pathjumpMP`(b). Die
  Formalisierung trägt sie deshalb als Hypothese, statt sie zu beweisen — so am
  2026-09-11 entschieden. Wer die Theorie baut, schließt damit die letzte Lücke
  im Hawkes-Beispiel.

* **Die augmentierte Filtration, und die üblichen Bedingungen.** Der neunte.
  Mathlib hat davon **nichts** (geprüft am 2026-09-12, `upstream/master`
  `141f6b64`): weder `augmentedFiltration` noch `Filtration.augment` noch
  `usualConditions` noch `IsRightContinuousFiltration`.

  *Der Baustein ist aber ein anderer, als hier zuerst stand:* nicht
  `NullMeasurableSpace`, sondern `eventuallyMeasurableSpace`
  (`MeasureTheory/MeasurableSpace/EventuallyMeasurable.lean`), die Meßbarkeit
  modulo einer σ-Filter. `NullMeasurableSpace` ist nur ihr Spezialfall bei
  `l = ae μ` und `m` = der ganzen Grund-σ-Algebra; gebraucht wird sie über einer
  **Teil**-σ-Algebra, und das kann nur die allgemeine Fassung.

  Gebraucht wird `𝓕̄ t = σ (𝓕 t ∪ 𝒩)` mit `𝒩` den `P`-Nullmengen, dazu die
  beiden Sätze, die eine Bibliothek dafür braucht: daß die Augmentierung wieder
  eine Filtration ist, und daß **die Martingaleigenschaft unter Vergrößerung um
  Nullmengen erhalten bleibt**. Beides ist am 2026-09-12, siebter Lauf, auf
  unserer Seite gebaut und gegen v4.33.1 übersetzt
  (`MartingaleProblems/Suggested.lean`, `section Augmentation`:
  `Filtration.augment`, `condExp_augment`, `Martingale.augment`,
  `Martingale.of_augment`, `Locally.augment`), siebzehn Deklarationen ohne
  `sorry`. In Mathlib fehlt es weiterhin, und der Kern ist eine einzige Aussage,
  die dort ebenfalls fehlt:
  `condExp_eq_condExp_of_forall_exists_ae_eq` — die bedingte Erwartung ändert
  sich nicht, wenn man die σ-Algebra um Mengen vergrößert, die f.s. schon da
  sind.

  *Woran es bei uns hängt:* der 25. Lauf des 2026-09-12 hat in Lean widerlegt,
  daß die Punktfiltration eines Treppenpfadprozesses mit der kanonischen
  Filtration des Pfades übereinstimmt — die Kette ist eine freie Koordinate des
  Stichprobenraums, „Kette bewegt sich" und „Sprungzeiten wachsen echt" gelten
  nur f.s., und Gleichheit von σ-Algebren ist keine f.s.-Aussage. Für die
  **vervollständigten** Filtrationen sollte die Gleichheit gelten, und dann hätte
  ein Sprungprozeß genau eine Filtration — die des eigenen Pfades. Der Preis ist,
  daß die Aussage ein Maß braucht statt nur σ-Algebren.

  *Zwei Präzisierungen vom 2026-09-12, siebter Lauf, und beide sind Preise:*
  die Augmentierung enthält die **meßbaren** Nullmengen und keine anderen; will
  man jede Teilmenge einer Nullmenge, so ist zuerst `(Ω, 𝓐, P)` zu
  vervollständigen, und das ändert den Grundraum und damit den Sinn jeder
  Aussage darüber. Und die Gleichheit der augmentierten Filtrationen ist **nicht**
  die widerlegte Gleichheit modulo Nullmengen, sondern
  `augment_eq_augment_of_forall_exists_ae_eq`: jede Menge der einen ist f.s.
  eine Menge der anderen. Das ist mehr, als eine Nullmenge schlechter
  Stichprobenpunkte von selbst hergibt, und der Weg dorthin führt über eine
  Abänderung der **Daten** auf einer Nullmenge, nicht über eine Relativierung des
  Beweises.

  Das ist der kleinste der neun Punkte und zugleich der, der am breitesten
  nützt: die üblichen Bedingungen stehen in jedem Lehrbuch der stetigen
  Martingaltheorie am Anfang.

* **Die verallgemeinerte Inverse einer monotonen Funktion.** Der zehnte, und
  der kleinste von allen. Mathlib hat sie nicht: `quantile`,
  `generalized inverse` und `generalised inverse` geben in ganz `Mathlib/` **null**
  Treffer (geprüft am 2026-09-12 an `upstream/master` `141f6b64`; gesucht wurde
  nach der Aussage und nicht nach unserer Vokabel, also auch nach
  `rightInverse` in Verbindung mit `Monotone`, was nur `Data/Set/Monotone.lean`
  trifft, wo es um etwas anderes geht). Vorhanden sind `StieltjesFunction` und
  `leftLim`/`rightLim` — die Bausteine —, aber kein `f⁻(a) = sInf {r | a ≤ f r}`
  und keine der beiden Aussagen, die den Begriff ausmachen.

  *Was zu formulieren wäre, und es ist eine Galois-Verbindung mit einem Haken:*
  für monotones `f : ℝ → ℝ≥0∞` gilt `f⁻(a) ≤ c ↔ a ≤ f(c⁺)` mit dem **rechten
  Grenzwert**, und die Gestalt mit `f c` statt `f(c⁺)` verlangt die
  Rechtsstetigkeit von `f`. Wir haben beide Hälften am 2026-09-12 als
  `rateInverseEE_le_ofReal_iff` und `rateInverseEE_le_ofReal_iff_rat` bewiesen,
  für den einen Fall, den wir brauchen; die allgemeine Fassung ist dieselbe
  Rechnung ohne die kumulierte Rate darin. Und die zweite Hälfte —
  `f⁻` ist meßbar, sobald `f` in einem Parameter meßbar ist, weil die
  Subniveaumenge ein **abzählbarer** Durchschnitt längs der positiven Rationalen
  ist — ist der Grund, aus dem die Aussage sich lohnt: sie ist es, die jede
  Zeitverwandlung meßbar macht, und sie steht in keiner Bibliothek, obwohl jedes
  Lehrbuch sie benutzt.

* **Das Einfrieren, und es ist der Kern jeder bedingten Sprungzeitrechnung.**
  Der elfte. Mathlib hat den **einen** Satz, der eine bedingte Erwartung mit
  Unabhängigkeit ausrechnet, nur im entarteten Fall:
  `MeasureTheory.condExp_indep_eq`
  (`Probability/ConditionalExpectation.lean:42`) sagt, daß `P[f | m₂]` die
  **Konstante** `∫ f` ist, wenn `f` für eine von `m₂` unabhängige σ-Algebra
  meßbar ist. Gebraucht wird die Fassung, in der der Integrand beide Seiten
  liest:

  > `P[F (Z, Y) | σ(Z)] (ω) = ∫ F (Z ω, y) dμ_Y(y)`, für `Y` unabhängig von `Z`.

  Das ist das **Einfrieren** (englisch *freezing lemma*). Gesucht am 2026-09-13
  an `upstream/master` `7d32461a` und in v4.33.1 nach `freezing`,
  `condExp_indep`, `IndepFun.condExp`, `condExp_comp`: **null** Treffer über
  `condExp_indep_eq` und seine einzige Verwendung in
  `Probability/BorelCantelli.lean:50` hinaus. Am selben Tag am neueren Stand
  `710c215f98a3947b3301a21454f1f2c3caf72d0a` (2026-09-13 00:31 UTC)
  nachgeprüft: unverändert, und der einzige Treffer der Suche über
  `Mathlib/Probability/` bleibt `iIndepFun.condExp_natural_ae_eq_of_lt` in
  `Probability/BorelCantelli.lean:50` — wieder der entartete Fall.

  *Woran es bei uns hängt:* die bedingte Überlebensfunktion
  `P (τ_{n+1} > t | ℋ_n) = exp (−(Λ_t − Λ_{τ_n}))`, der Rumpf des Beweises von
  `thm:pathjumpMP`. Das Ereignis ist `{Λ_t < ξ_n}`, und es mischt die beiden
  Seiten — der **Pegel** wird aus der Vergangenheit gelesen, die **Wartezeit**
  ist frisch. `condExp_indep_eq` reicht deshalb an keiner Stelle heran.

  Wir haben es am 2026-09-13 für Indikatoren bewiesen
  (`MartingaleProblems/Suggested.lean`, `section Freezing`:
  `setIntegral_indicator_of_map_prod`, `condExp_indicator_of_map_prod`,
  `setIntegral_indicator_lt_of_map_prod`), was alles ist, was ein
  Martingalproblem braucht und was die Integrierbarkeitsbuchhaltung eines
  allgemeinen `F` erspart: die Antwort ist dann eine Wahrscheinlichkeit und von
  selbst durch `1` beschränkt. Für Mathlib wäre die richtige Fassung die für
  integrierbares `F : γ × β → ℝ`, über `Measure.prod` und Fubini, und sie ist
  mehr als unsere.

* **Die Stammfunktion einer parametrisierten Familie, gemeinsam meßbar in
  Parameter und oberer Grenze.** Der zwölfte, und der kleinste von allen.
  Mathlib hat `MeasureTheory.StronglyMeasurable.integral_prod_right'`
  (`MeasureTheory/Integral/Prod.lean:76`), also die Meßbarkeit von
  `x ↦ ∫ y, f (x, y) ∂ν` bei **festem** Maß, und daraus die Meßbarkeit von
  `x ↦ ∫ y in s, f (x, y)` bei **fester** Menge `s`. Gebraucht wird die Fassung,
  in der das Fenster mitwandert:

  > `x ↦ ∫_0^{a x} f x u du` ist meßbar, für meßbares `a` und eine Familie, die
  > gemeinsam meßbar und in jedem Parameter lokal integrierbar ist.

  Gesucht am 2026-09-13 an `upstream/master`
  `710c215f98a3947b3301a21454f1f2c3caf72d0a` nach `measurable_primitive`,
  `Measurable ... primitive`, `Measurable fun x ↦ ∫ y in ...` und nach
  Meßbarkeitsaussagen im Umfeld von `intervalIntegral`: **null** Treffer.
  Am 2026-09-17 gegen `f61f3ed7633` nachgeprüft: unverändert. Vorhanden sind
  **Stetigkeits**aussagen und keine Meßbarkeitsaussage — die Stammfunktion in
  der oberen Grenze (`intervalIntegral.continuousOn_primitive`,
  `MeasureTheory/Integral/DominatedConvergence.lean:440` in v4.33.1, `:439` auf
  master, samt `continuousOn_primitive_interval` ebendort), und, schärfer als
  es hier zuerst stand, die **parametrische** Fassung
  `intervalIntegral.continuousAt_parametric_primitive_of_dominated` (ebenda
  `:364` auf master), die in Parameter **und** oberer Grenze gemeinsam stetig
  ist. Sie trägt die Anwendung nicht: sie verlangt eine Topologie auf dem
  Parameterraum und Stetigkeit des Integranden darin, und der Parameter ist
  hier der Stichprobenpunkt eines Maßraums ohne Topologie. Die erste der beiden
  ist der halbe Beweis.

  *Der Beweis, und er ist drei Zeilen lang:* meßbar im Parameter bei fester
  Grenze, stetig in der Grenze bei festem Parameter — das ist eine
  Carathéodory-Funktion, und
  `MeasureTheory.measurable_uncurry_of_continuous_of_measurable`
  (`MeasureTheory/Function/StronglyMeasurable/Basic.lean:1262` auf master,
  `:1257` in v4.33.1) macht daraus eine gemeinsam meßbare. Daß die Aussage so
  billig ist und trotzdem fehlt, ist der Grund, sie hier aufzuführen: sie wird
  gebraucht, sobald eine Stoppzeit als Integrationsgrenze auftritt, und das ist
  in der Theorie der Punktprozesse der Regelfall.

  *Woran es bei uns hing:* `measurable_hawkesJumpLevel`. Der Pegel der bedingten
  Überlebensfunktion ist die kumulierte Rate bei `t` abzüglich der kumulierten
  Rate bei `τ_n`, und `τ_n` ist eine Funktion der Bedingungsgröße. Wir haben es
  am 2026-09-13 als `measurable_cumulativeRateF_endpoint` bewiesen, mit
  `continuous_cumulativeRateF` und `measurable_uncurry_cumulativeRateF` als den
  beiden Hälften; unsere Fassung ist an `cumulativeRateF` geschrieben und für
  Mathlib auf `intervalIntegral` umzustellen.

* **Das Vorschieben des *ersten* Faktors eines `compProd`.** Der dreizehnte, und
  der einzige der siebzehn, der nicht fehlt, sondern bloß keinen Namen hat.
  Mathlib hat den zweiten Faktor als benannten Satz —
  `Measure.compProd_map (hf : Measurable f) : μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f)`
  (`Probability/Kernel/Composition/Lemmas.lean:120`, v4.33.1 wie `master`
  `55a449c5f28`). Der erste fehlt:

  > `(μ.map g) ⊗ₘ κ = (μ ⊗ₘ (κ.comap g hg)).map (Prod.map g id)`.

  Er ist aber **bewiesen vorhanden**, als Zwischenschritt einer `calc`-Kette in
  `HasCondDistrib.comp_right` (`Probability/HasCondDistrib.lean:98–102`, in
  v4.33.1 und auf `master` wortgleich). Wir haben ihn am 2026-09-13 als
  `map_compProd_comap` herausgezogen; der Beweis ist derselbe wie dort, vier
  Umschreibungen und ein `rfl`. Der PR wäre: die Zeilen 98–102 durch den Aufruf
  eines neuen Satzes neben `Measure.compProd_map` ersetzen. Das ist der billigste
  Beitrag, den dieser Zweig bisher gefunden hat.

  *Woran es bei uns hing:* `comp_chainKernel_map_split_range`, die
  Markoveigenschaft der eingebetteten Kette an der `n`-ten Stufe. Mathlib rechnet
  über `Finset.Iic n`, unsere bedingende σ-Algebra ist über `Finset.range (n+1)`
  geschrieben, und das Umindizieren schiebt genau den ersten Faktor vor.

* **Die bedingte Erwartung aus einer Desintegration, ohne standard-borelschen
  Zielraum.** Der vierzehnte. `ProbabilityTheory.HasCondDistrib Y X κ P` ist
  definiert als `P.map (fun ω ↦ (X ω, Y ω)) = P.map X ⊗ₘ κ`
  (`Probability/HasCondDistrib.lean:41`) und verlangt an die Räume nichts als
  ihre meßbare Struktur. Was daraus folgen sollte, folgt dort nicht:

  > `P[f ∘ Y | MeasurableSpace.comap X inferInstance] =ᵐ[P] fun ω ↦ ∫ y, f y ∂(κ (X ω))`
  > für meßbares, beschränktes `f`.

  Die Datei enthält in v4.33.1 wie auf `master` **keinen einzigen Treffer** für
  `condExp` (geprüft 2026-09-13). Den Schluß gibt es nur über `condDistrib`,
  `ProbabilityTheory.condExp_ae_eq_integral_condDistrib`
  (`Probability/Kernel/CondDistrib.lean:381`) — und `condDistrib` existiert nur
  über einem `[StandardBorelSpace]`-Zielraum, weil es die Desintegration erst
  **konstruiert**. Liegt sie schon vor, wird davon nichts gebraucht: der Beweis
  ist `ae_eq_condExp_of_forall_setIntegral_eq`, `setIntegral_map` und
  `Measure.setIntegral_compProd` an `A ×ˢ univ`.

  *Woran es bei uns hing:* `condExp_chain_mark_range`, der Kettenfaktor des
  Sprungterms von `thm:pathjumpMP`. Über unserem Zustandsraum steht nichts als
  `[MeasurableSpace E]`, und der Satz geht trotzdem — was zeigt, daß die
  Standardborel-Voraussetzung an dieser Stelle eine Voraussetzung von
  `condDistrib` ist und keine der Aussage. Wir haben ihn am 2026-09-13 für
  beschränktes `f : E → ℝ` bewiesen
  (`MartingaleProblems/Suggested.lean`, `section ChainMarkov`).

* **Die bedingte Erwartung unter Vergrößerung der bedingenden σ-Algebra um einen
  unabhängigen Block.** Der fünfzehnte. Mathlib hat den Fall, in dem die
  unabhängige σ-Algebra die bedingende **ersetzt** —
  `MeasureTheory.condExp_indep_eq` (`Probability/ConditionalExpectation.lean:42`,
  in v4.33.1 wie auf `master` `182c4c30cdc`, nicht `deprecated`): ist `f`
  `m₁`-meßbar und `m₁` unabhängig von `m₂`, so ist `μ[f | m₂]` die Konstante
  `μ[f]`. Den Fall, in dem sie **hinzukommt**, hat es nicht:

  > `μ[f | m₁ ⊔ m₂] =ᵐ[μ] μ[f | m₁]`, wenn `m₂` unabhängig von `σ(f) ⊔ m₁` ist.

  Die beiden sind verschiedene Aussagen — die erste läßt die bedingte Erwartung
  zu einer Zahl zusammenfallen, die zweite läßt sie stehen. Eine Suche in beiden
  Ständen nach einem `condExp` über einem Supremum mit unabhängigem Summanden
  gibt **null Treffer** (geprüft 2026-09-13).

  *Woran es bei uns hing:* `condExp_chain_mark_block`, der Kettenfaktor des
  Sprungterms von `thm:pathjumpMP` über der σ-Algebra `ℋ_n`, die außer der Kette
  auch die ersten `n` Sprungzeiten liest. Wir haben die Produktfassung am
  2026-09-13 als `condExp_comap_prodMap_prod` bewiesen
  (`MartingaleProblems/Suggested.lean`, `section CondExpProdMap`): unter einem
  Produktmaß `P.prod Q` und für meßbare `V : X → S`, `W : Y → T` ist

  > `(P.prod Q)[fun p ↦ g p.1 | comap (fun p ↦ (V p.1, W p.2))] =ᵐ fun p ↦ (P[g | comap V]) p.1`.

  Der Beweis ist Fubini plus die Herausziehung: das Schnittmaß der bedingenden
  Menge ist ein beschränkter `comap V`-meßbarer Faktor, und ein beschränkter
  Faktor geht durch die bedingte Erwartung hindurch. Die allgemeine Fassung über
  `m₁ ⊔ m₂` verlangte statt dessen ein π-System-Argument; die Produktfassung
  kommt ohne aus und deckt jede Anwendung ab, in der der unabhängige Block eine
  eigene Koordinate des Stichprobenraums ist.

* **Fubini für die bedingte Erwartung.** Der sechzehnte, und der einzige, bei dem
  die Lücke einen benennbaren *Grund* hat. Gebraucht wird die Vertauschung eines
  Integrals über einen Parameter mit der bedingten Erwartung,

  > `μ[fun ω ↦ ∫ u, g u ω ∂ν | m] =ᵐ[μ] fun ω ↦ ∫ u, (μ[g u | m]) ω ∂ν`.

  Mathlib hat sie nicht; eine Suche in beiden Ständen nach einem `condExp` eines
  Parameterintegrals gibt nur `condExp_ae_eq_integral_condDistrib` und seine
  Verwandten (`Probability/Kernel/CondDistrib.lean:377`), die gegen einen **Kern**
  integrieren und die Desintegration sind, nicht Fubini.

  **Und die naive Fassung oben ist nicht wohlgestellt.** `μ[g u | m]` ist für
  jedes `u` einzeln nur bis auf eine Nullmenge festgelegt, also braucht
  `u ↦ (μ[g u | m]) ω` überhaupt nicht meßbar zu sein, und die rechte Seite
  existiert im allgemeinen nicht. Wer den Satz in Mathlib haben will, muß ihm
  eine gemeinsam meßbare **Version** mitgeben:

  > sind `g` und `hcand` gemeinsam meßbar und beschränkt und ist `hcand u` für
  > jedes `u` eine Version von `μ[g u | m]`, so ist
  > `μ[fun ω ↦ ∫ u, g u ω ∂ν | m] =ᵐ[μ] fun ω ↦ ∫ u, hcand u ω ∂ν`.

  Das ist die Gestalt, die jede Anwendung ohnehin hat, weil die Version dort in
  geschlossener Form bekannt ist. Wir haben sie am 2026-09-13 als
  `condExp_integral_comm` bewiesen, mit `condExp_intervalIntegral_comm` als
  Intervallfassung (`MartingaleProblems/Suggested.lean`, `section CondExpFubini`);
  der Beweis ist `integral_integral_swap` auf dem eingeschränkten Maß,
  `setIntegral_condExp` innen, und zurückgetauscht — drei Zeilen `calc`.

  *Woran es bei uns hing:* `condExp_compensator_rate_block`, der Kompensatorteil
  des Martingalzuwachses von `thm:pathjumpMP`, Punkt 4 der Gruppe A. Dort ist
  `ν` das Lebesguemaß auf `(0, t]` und die Version die bedingte
  Überlebensfunktion; der Satz steht seit dem 2026-09-13, und er ist die erste
  Anwendung dieser Lücke.

* **Die Komposition einer absolut stetigen mit einer lipschitzstetigen
  Funktion.** Der siebzehnte, und er ist am 2026-09-13 **kleiner geworden, als er
  gemeldet war** — die Berichtigung gehört hierher, weil eine Negativaussage ein
  Versprechen an einen Leser ist.

  *Was gemeldet war:* Mathlib habe den Hauptsatz der Differential- und
  Integralrechnung für eine Stammfunktion mit bloß meßbarem Integranden nicht.
  *Was stimmt:* über die **Substitutionsregeln** ist das richtig — sie verlangen
  alle eine Ableitung an **jedem** Punkt des Intervalls
  (`intervalIntegral.integral_comp_mul_deriv` mit seinen drei gestrichenen
  Verwandten und `integral_comp_mul_deriv_of_deriv_nonneg`,
  `MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:496–548`;
  `integral_comp_mul_deriv_Ioi`,
  `MeasureTheory/Integral/IntegralEqImproper.lean:1121`;
  `integral_image_eq_integral_abs_deriv_smul`,
  `MeasureTheory/Function/JacobianOneDim.lean:66`). Über den **Hauptsatz** ist es
  falsch: Mathlib hat ihn für absolut stetige Funktionen, als
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`
  (`MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean:225`),
  dazu `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`
  (ebenda `:412`) und die Intervallfassung des Lebesgueschen
  Differentiationssatzes `IntervalIntegrable.ae_hasDerivAt_integral`
  (`MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean:66`).
  Mit diesen dreien geht die Rechnung durch, ohne jede Stetigkeitsvoraussetzung
  an den Integranden.

  *Und die zweite Hälfte der Lücke ist am 2026-09-17 als **geschlossen**
  vorgefunden worden — der wertvollste Fund des Laufs, weil eine Negativaussage
  ein Versprechen an einen Leser ist.* Gemeldet war: die absolute Stetigkeit sei
  in Mathlib unter Summe, Produkt und Skalar abgeschlossen
  (`MeasureTheory/Function/AbsolutelyContinuous.lean`) und es gebe „lipschitz ⇒
  absolut stetig" (`LipschitzOnWith.absolutelyContinuousOnInterval`, ebenda
  `:294` in v4.33.1, `:310` auf `master`), aber **keine Kompositionsaussage**.
  Gebraucht wurde

  > ist `f` absolut stetig auf `uIcc a b` und `g` lipschitz auf einer Menge `s`,
  > in die `f` das Intervall abbildet, so ist `g ∘ f` absolut stetig auf
  > `uIcc a b`.

  Genau das steht auf `master` seit dem 2026-08-25, als
  `LipschitzOnWith.comp_absolutelyContinuousOnInterval` (ebenda `:328`, dazu
  `LipschitzWith.comp_absolutelyContinuousOnInterval` `:343`), aus
  `feat(MeasureTheory): absolute continuity preserved by Lipschitz
  postcomposition` (#42996, `c4e2650f16e`, dean cureton) — unter **demselben
  Namen**, den wir unabhängig gewählt haben, mit derselben Voraussetzung
  `MapsTo g (uIcc a b) t` und allgemeiner als unsere: dort geht die äußere
  Funktion in einen beliebigen pseudometrischen Raum, bei uns ist sie reell.
  In **v4.33.1**, an das wir gebunden sind, gibt es sie nicht; unsere Fassung
  vom 2026-09-13 bleibt deshalb stehen und ist keine Doppelarbeit mehr, sondern
  der Stellvertreter für den Stand, gegen den wir übersetzen. Ein PR dieser
  Aussage ist gegenstandslos.

  Die Lipschitzschranke nur auf `s` zu verlangen ist nicht Bequemlichkeit: `exp`
  ist nicht global lipschitz, und ohne die Einschränkung auf ein Kompaktum um
  das Bild käme die Anwendung nicht durch — Mathlibs Fassung stellt sie
  ebenso.

  Daraus fällt die Substitutionsregel in der Allgemeinheit ab, die Mathlib fehlt:

  > `integral_mul_deriv_comp_intervalIntegral` — für `g` von der Klasse `C¹`,
  > `f` bloß intervallintegrierbar auf `a..b` und `c ∈ uIcc a b`:
  > `∫_a^b f_u · g' (∫_c^u f) du = g (∫_c^b f) − g (∫_c^a f)`.

  *Woran es bei uns hing:* Punkt 5 der Gruppe A,
  `condExp_mpFamilyF_increment_eq_zero`, und Punkt 2, die bedingte Dichte. Beide
  Hälften des Martingalzuwachses stehen seit dem 2026-09-13; diese Rechnung war
  das einzige, was sie trennte, und sie steht seit demselben Tag als
  `intervalIntegral_rate_mul_exp_neg_cumulativeRateF`. Der Integrand ist dort
  `h (ν + ∑ φ (u − τ_k))` mit meßbarem `h` und `φ`, und eine
  Stetigkeitsvoraussetzung wäre eine Verschärfung der Hypothesen von
  `ex:hawkes`; sie ist nicht genommen worden.

* **Fortschreitende Meßbarkeit aus Rechtsstetigkeit der Pfade.**
  `Probability/Process/Adapted.lean` leitet sie aus **Stetigkeit** der Pfade her
  (`StronglyAdapted.isStronglyProgressive_of_continuous`, `:365`), aus einem
  diskreten Index (`..._of_discrete`, `:376`) und aus einem Grenzwert
  (`isStronglyProgressive_of_tendsto`, `:359`) — aus **Rechtsstetigkeit** nicht,
  weder in `v4.33.1` noch auf `master`
  (`9cb3970b1fb61911f7e8892dffcde5aa4a0661cc`, geprüft am 2026-09-14). Das ist
  die Lücke, an der jeder Sprungprozeß steht: seine Pfade sind nie stetig, sein
  Index ist nie diskret, und das Kompensatorintegral verlangt gerade diese
  Aussage.

  Der Beweis ist der Grenzwertsatz plus eine Näherung von **oben**, und mehr
  nicht: mit `d_n u = ⌈2ⁿ u⌉/2ⁿ` ist `(u, ω) ↦ h (X (d_n u) ω)` schon ohne jede
  Regularität gemeinsam meßbar, weil `d_n` abzählbar viele Werte annimmt
  (`measurable_from_prod_countable_right`), und die Rechtsstetigkeit sagt nur,
  daß die Stufen gegen den Grenzwert gehen. Wir haben es am 2026-09-14 in der
  gemeinsamen Meßbarkeitsfassung als
  `measurable_uncurry_of_isRightLocallyConstant` bewiesen, mit `dyadAbove`,
  `le_dyadAbove` und `dyadAbove_lt`; für Mathlib wäre die richtige Fassung die
  über `IsStronglyProgressive` und über einem rechtsstetigen Pfad in einem
  metrisierbaren Zielraum statt über der lokal konstanten Fassung, die ein
  diskreter Zustandsraum erlaubt.

  *Ein Nebenbefund über `ℝ≥0`, der beim Beweisen Zeit gekostet hat:*
  `Nat.measurable_floor` trägt `[IsStrictOrderedRing R]`
  (`MeasureTheory/Function/Floor.lean:69`), `ℝ≥0` ist ein Halbring, also gilt es
  dort **nicht**; `Nat.measurable_ceil` (`:78`) hat die Hypothese nicht. Die
  Näherung von oben ist damit auch die, die die Bibliothek trägt. Die Hypothese
  an `Nat.measurable_floor` sieht entbehrlich aus — der Beweis ist
  `measurable_to_countable` über `Nat.preimage_floor_of_ne_zero` —, und das wäre
  ein Einzeiler-PR.

  *Und seit #43352 hat die Lücke einen Namen, in den sie hineinpaßt:*
  `Mathlib/Topology/Order/Cadlag.lean` trägt auf `master` `IsRightContinuous`
  (`:36`, `∀ a, ContinuousWithinAt f (Set.Ioi a) a`) und `IsCadlag` (`:104`) mit
  rund zwanzig Abschlußeigenschaften. Die Aussage, die fehlt, ist damit
  formulierbar geworden, ohne daß ein Begriff erst zu stiften wäre:
  *rechtsstetige Pfade in einem metrisierbaren Zielraum sind fortschreitend
  meßbar.* In `v4.33.1`, an das wir gebunden sind, gibt es die Datei nicht, und
  `IsRightContinuous` kommt dort nur als `Filtration.IsRightContinuous`
  (`Probability/Process/Filtration.lean:373`) vor — eine Klasse über
  Filtrationen und keine über Funktionen. Am 2026-09-14 geprüft.

* **Die Umindizierung einer Filtration.** Der neunzehnte, und der billigste von
  allen. `Filtration` ist eine Struktur aus einer monotonen Familie von
  σ-Algebren; ihre Vorschaltung mit einer monotonen Abbildung `e : ι' → ι` ist
  wieder eine, und die drei Felder sind die alten. `def comp` kommt in
  `Mathlib/Probability/Process/Filtration.lean` **nicht** vor, und die Suche nach
  `Filtration` zusammen mit `comp`, `reindex` oder `precomp` in ganz `Mathlib/`
  gibt einen einzigen Treffer, und der ist ein `Measurable.comp` in
  `Kernel/Disintegration/Density.lean:154`. Am 2026-09-16 gegen
  `upstream/master` `09a9e06` geprüft.

  Der Grund, warum das mehr als eine Bequemlichkeit ist: **jede** Aussage über
  einen stetigzeitlichen Prozeß, die über einen diskret indizierten Satz geführt
  wird — und das sind in `Probability/Martingale/` alle, die Aufkreuzungen oder
  Maxima zählen —, muß den Prozeß längs einer monotonen `ℕ → ι` lesen, und dazu
  braucht sie die Filtration daneben. Ohne `Filtration.comp` ist der Satz, den
  man anwenden will, nicht einmal hinschreibbar. Wir haben es am 2026-09-16 als
  `Filtration.comp` mit `Submartingale.comp_monotone` gebaut; für Mathlib gehören
  beide zusammen in einen PR, und die Martingal- und Supermartingalfassungen
  daneben.

* **Die Minimalungleichung für Submartingale.** Der zwanzigste, und der
  Gegenpol zu einem Satz, den Mathlib hat. `MeasureTheory.maximal_ineq`
  (`Probability/Martingale/OptionalStopping.lean:144` auf master) ist Doobs
  Maximalungleichung für ein nichtnegatives Submartingal; die Gegenrichtung,
  `ε · P{min_{k ≤ n} Y_k ≤ −ε} ≤ 𝔼[Y_n⁺] − 𝔼[Y_0]`, fehlt in jeder Fassung —
  die Zeichenkette `inf'` kommt in `Mathlib/Probability/Martingale/` gar nicht
  vor (0 Treffer, am 2026-09-16 gegen `upstream/master` `09a9e06` geprüft).

  Ihr Beweis ist `Submartingale.expected_stoppedValue_mono` (`ibid.:43`) an der
  konstanten Stoppzeit `0` gegen die Trefferzeit von `Set.Iic (−ε)`, gefolgt von
  der Zerlegung des gestoppten Wertes über das Ereignis, daß der Pegel erreicht
  wird — also derselbe Baustein, aus dem die vorhandene Ungleichung gebaut ist,
  nur an der anderen Seite angesetzt. Zusammen sind die beiden erst das, was ein
  Leser unter „ein Submartingal ist auf einem endlichen Zeitfenster fast sicher
  beschränkt" versteht, und genau das verlangt Doobs Regularisierung.

  **Am 2026-09-16 gebaut**, und der PR sollte **beide** Seiten tragen:
  `Submartingale.mul_measReal_exists_le_neg_le_integral_posPart_sub` ist die
  fehlende Ungleichung, `Submartingale.mul_measReal_exists_ge_le_integral_posPart`
  die vorhandene noch einmal — reellwertig, über dem Ereignis
  `{ω | ∃ k ≤ n, ε ≤ f k ω}` statt über `Finset.sup'`, **ohne** Nichtnegativität
  des Prozesses und **ohne** Vorzeichenbedingung an `ε`. Der Grund, die zweite
  mitzunehmen, ist nicht Bequemlichkeit: die Brücke von `maximal_ineq` in
  `ℝ≥0∞` über `Y⁺` zu der Fassung, die eine zweiseitige Schranke braucht,
  kostet mehr als der Beweis, und die beiden Beweise sind derselbe, an den
  beiden Enden angesetzt. Beide gehen durch `lake env lean` gegen v4.33.1.

* **Ein Martingal hinter einer stetigen linearen Abbildung.** Der
  einundzwanzigste, und der kleinste von allen. Mathlib hat
  `ContinuousLinearMap.comp_condExp_comm`
  (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:359`), also
  `T ∘ μ[f | m] =ᵐ μ[T ∘ f | m]` — die Aussage über die **bedingte Erwartung**.
  Die Aussage über den **Prozeß**, `Martingale f ℱ μ → Martingale (T ∘ f) ℱ μ`,
  fehlt: in `Mathlib/Probability/Martingale/` und `Mathlib/Probability/Process/`
  hat die Suche nach `Martingale` neben `ContinuousLinearMap` **null Treffer**
  (am 2026-09-17 gegen v4.33.1 geprüft und im dritten Lauf desselben Tages gegen
  `upstream/master`, `92fc6042c1d` vom 2026-09-16 — die Zeichenkette
  `ContinuousLinearMap` kommt in keiner der beiden Verzeichnisse dort vor, und
  `RCLike` in `Mathlib/Probability/Martingale/` ebensowenig). `Martingale.smul`
  und `Martingale.add` stehen da, die lineare Abbildung nicht.

  Der Beweis ist vier Zeilen und steht bei uns als
  `MeasureTheory.Martingale.comp_continuousLinearMap`. Was ohne ihn fehlt, ist
  der Übergang von einem `RCLike`-wertigen Martingal zu seinen beiden reellen
  Teilen — in `Mathlib/Probability/Martingale/` kommt `RCLike` **gar nicht** vor
  —, und damit jeder Satz, der ein komplexwertiges Martingal an einen
  reellwertigen Satz übergeben will. Doobs Regularisierung ist genau so ein
  Satz. Der PR sollte die Martingal-, die Sub- und die Supermartingalfassung
  tragen; die letzten beiden verlangen eine Positivitätsbedingung an `T` und
  sind daher nicht dasselbe Lemma.

* **Das Supremum einer Folge von Stoppzeiten.** Der zweiundzwanzigste, gefunden
  am 2026-09-17 beim Zusammenbau der Quasi-Linksstetigkeit. Mathlib hat das
  **Infimum**: `MeasureTheory.IsStoppingTime.iInf` und `…​.biInf`
  (`Probability/Process/Stopping.lean:385` bzw. `:373`), beide mit
  `[Filtration.IsRightContinuous]`, `[DenselyOrdered ι]`, `[NoMaxOrder ι]` und
  `[FirstCountableTopology ι]`. Das **Supremum** fehlt — in
  `Probability/Process/Stopping.lean` kommt `⨆` nur in der Definition von
  `IsStoppingTime.measurableSpace` und in Beweisen vor, und in ganz
  `Mathlib/Probability/` gibt die Suche nach `IsStoppingTime` neben `⨆` **null
  Treffer** (am 2026-09-17 gegen `upstream/master` `f61f3ed7633` geprüft, und
  gegen v4.33.1).

  Die Asymmetrie ist echt und erklärt, warum die eine Hälfte dasteht und die
  andere nicht: das Infimum verlangt die Rechtsstetigkeit der Filtration, weil
  `{⨅ τ n < i}` und nicht `{⨅ τ n ≤ i}` die zugängliche Menge ist. Das Supremum
  verlangt nichts: `{⨆ n, τ n ≤ i} = ⋂ n, {τ n ≤ i}` ist ein abzählbarer
  Durchschnitt von Mengen, die schon `𝓕 i`-meßbar sind. Der Beweis ist fünf
  Zeilen und steht bei uns als `isStoppingTime_iSup`; das einzige, was er über
  den Index liest, ist `ciSup_le_iff` mit `OrderTop.bddAbove` über `WithTop ι`.

  Für Mathlib wäre die richtige Fassung die über einer abzählbaren Indexmenge,
  also `biSup` und `iSup` als Paar zu `biInf` und `iInf`, und ohne jede der vier
  Instanzen, die jene tragen.

* **Gleichgradige Integrierbarkeit über einer Folge *verschiedener*
  Wahrscheinlichkeitsräume, und was sie mit der Verteilungskonvergenz macht.**
  Der dreiundzwanzigste, gefunden am 2026-09-17 beim Beweis von
  `mpSolution_of_tendsto`. `MeasureTheory.UnifIntegrable`
  (`MeasureTheory/Function/UniformIntegrable.lean:73`) ist ein Prädikat über
  **einem** festen Maß `μ`; `MeasureTheory.TendstoInDistribution`
  (`MeasureTheory/Function/ConvergenceInDistribution.lean:64`) läuft dagegen von
  Haus aus über eine **Familie** `μ : (i : ι) → Measure (Ω i)`. Die beiden
  passen also nicht aufeinander, und der klassische Satz

  > konvergieren die Verteilungen und ist die Familie gleichgradig integrierbar,
  > so konvergieren die Erwartungswerte,

  ist in keiner Fassung da. Gesucht wurde am 2026-09-17 gegen `upstream/master`
  `8018f6ac06b` nach `tendsto_integral` zusammen mit `Distribution`, nach
  `UnifIntegrable` in `ConvergenceInDistribution.lean` (kein Treffer) und nach
  `Tendsto`/`Distribution` in `UniformIntegrable.lean` (nur die
  `TendstoInMeasure`-Sätze, also Konvergenz **in Wahrscheinlichkeit** auf einem
  Raum). Wir haben ihn als `integral_eq_zero_of_tendstoLaw` in der Gestalt
  bewiesen, die der Meilenstein braucht — „die Integrale der Folge gehen gegen
  Null, also auch das des Limes" —, samt dem Apparat darunter: `radialTrunc`,
  die Rückziehung eines normierten Raumes auf eine Kugel, `tendsto_integral_tail`
  und `integrable_of_tendstoLaw`.

  Für Mathlib wäre die richtige Fassung die volle Konvergenz der Integrale,
  nicht unser Spezialfall, und der natürliche Ort ist
  `ConvergenceInDistribution.lean`. Die gleichgradige Integrierbarkeit wäre
  dabei über die Schwänze `∫ max (‖ξ i‖ - c) 0 ≤ ε` zu formulieren und nicht
  über `UnifIntegrable`, das ein Maß festhält.

Dazu, aus derselben Baustelle und schon oben unter Punkt 6 vermerkt: die
Indexverallgemeinerung von Ionescu--Tulcea, wo `Maps.lean` bereits für eine
lokal endliche lineare Ordnung geschrieben ist und `Traj.lean` auf `ℕ` festliegt.

## Was inzwischen ohne Dich läuft

*(Die Zahlen dieses Abschnitts sind am 2026-09-15 nachgeführt und einzeln
nachgeprüft; der Rest der Datei ist der Stand vom 8. September.)*

**208 Läufe** bisher (`Facts/STATUS.md`, zuletzt `20260915T210301Z`), Opus 5;
von den 209 Laufcommits tragen 190 `rc=0`, dreizehn `rc=1`, drei einen Timeout
und zwei die überlange Argumentliste vom 10. September. Am 7./8. September sind in
einem Tag rund 4000 Zeilen Lean dazugekommen.

**Stündlich war der Takt aber nicht geblieben.** Die Laufstempel zeigen ihn
gestreckt: stündlich bis zum 11. September, zweistündlich am 12./13.,
vierstündlich am 14. (sechs Läufe, `02:33` bis `22:33` UTC). Am 15. September
liefen nur `02:33` und `06:33`, dann nichts mehr, und der letzte Lauf des Tages
— `20:03` UTC, also 22:03 Ortszeit — steht neben dem Raster.

**Der Grund saß in der Zeitschranke, nicht im Runner:** `~/bin/facts_gate.sh`
auf fisher stand auf `NOT_BEFORE='2026-09-16 22:03'` und übersprang jeden Slot
stillschweigend. Die Crontab dort feuert `3 * * * *`, also **stündlich**;
gebremst hat allein die Schranke.

**Was am Abend des 15. September damit geschah**, der Vollständigkeit halber:
die Schranke wurde um 22:55 aufgehoben, der Slot um 23:03 lief daraufhin
(`20260915T210301Z`, `rc=0`, dreiundzwanzig Minuten) — und gegen 23:30 hat der
Nutzer sie wieder gesetzt, zurück auf `2026-09-16 22:03`. **Stand jetzt ruhen
die Läufe also**, die Crontab-Zeile bleibt unangetastet, und sie greift von
selbst wieder, sobald `NOT_BEFORE` überschritten ist. Eine Zeile in
`~/bin/facts_gate.sh` entscheidet das; die Fassung ohne Schranke liegt als
`~/bin/facts_gate.sh.bak` daneben.

Lean-Stand, alle drei Dateien am 2026-09-15 nach dem Lauf `20260915T210301Z`
über
`lake --dir=~/Code/lean/journal env lean` gegen das gebaute Mathlib v4.33.1 des
Hauptcheckouts geprüft (dort wurde nichts geschrieben):

| | Zeilen | Deklarationen | `sorry` | Fehler |
|---|---:|---:|---:|---:|
| `WeakConvergence` | 6 989 | 196 | 0 | 0 |
| `SkorokhodSpace` | 10 167 | 353 | 0 | 0 |
| `MartingaleProblems` | 33 009 | — | 1 | 0 |

`SkorokhodSpace` ist **ganz bewiesen** und seit dem 10. September unberührt.
`WeakConvergence` ist es seit dem 2026-09-17, achtzehntem Lauf des Tages, und
die Zeile davor ist zu berichtigen: sie nannte die zwei Fehler dort „nachgeprüft,
absichtlich, bleibt so". Das war als Aussage über die *Aussage* richtig und als
Aussage über die *Datei* falsch. Ein `error` gibt keine `.olean`; solange die
eine gegen `upstream/master` geschriebene Deklaration nicht elaborierte, war
`WeakConvergence` von keiner anderen Datei importierbar, und seit der
Entscheidung des Nutzers vom 2026-09-17, daß die vier Roadmaps aufeinander
aufbauen dürfen, hing daran die ganze Kette. Die Aussage ist jetzt über die
Bildmaße als Daten geschrieben, elaboriert gegen **beide** Fassungen und ist
bewiesen: `tendsto_of_measure_setOf_continuousAt_eq_one`.

Die ganze Bewegung steckt seither in `MartingaleProblems`: **1 036 Zeilen am
8. September, 29 092 heute.** Die **fünf** verbliebenen `sorry` stehen in
`isMPSolution_iff_forall_fdd_continuous` (die stetige Fassung des
fdd-Kriteriums — eine Entscheidung über die Anordnung der Dateien, keine offene
Mathematik), den beiden Quasi-Linksstetigkeiten und den beiden Konvergenzsätzen
`mpSolution_of_tendsto` und `isMPSolution_of_forall_condExp_eq_of_dense`.
`exists_cadlag_modification_of_isRegularizingClass` steht seit dem 2026-09-17,
fünftem Lauf des Tages, **bewiesen** — Doobs Regularisierung in der `E`-wertigen
Fassung, und damit der erste der drei `sorry` von Meilenstein 9. Im sechsten
Lauf desselben Tages ist die Voraussetzung `hΦ` dieser Aussage aus dem
Martingalproblem selbst erzeugt worden statt angenommen
(`isRegularizingClass_mpFamily`, über `isCompensatorFor_mpFamily` und die neue
Uhrbedingung `Clock.IsContinuousFor`); was an einer Instanz noch einzulösen ist,
betrifft den Zustandsraum und nicht mehr den Prozeß. Diese fünf Deklarationen
sind bis Zeile 8386 fehlerfrei übersetzt und liegen sämtlich davor; ein
vollständiger Durchlauf mit `#print axioms` steht aus und ist der erste
Handgriff des nächsten Laufs.

Inhaltlich geschlossen sind seit dem 8. September: **Meilenstein 5**
(`restart`, `restart_canonical` — dabei zeigte sich, daß der Aussage, wie sie
dastand, vier Voraussetzungen fehlten und eine überflüssige dastand),
**Meilenstein 6** (`lem:propagation`, `thm:absuniq` (a) und (b), samt
Leerheitsprobe an `lebesgueClock`), der kanonische Pfadraum mit `jumpPath`, das
fdd-Kriterium in meßbarer Fassung und — am 15. September — das **erste
Martingalproblem dieser Entwicklung mit genau einer Lösung**. **Meilenstein 9**
hat begonnen: erst der Schritt, der aus reellen Grenzwerten einen `E`-wertigen
macht, dann im Lauf `20260915T210301Z` die **deterministische Hälfte von Doobs
Regularisierung** — Oszillation längs eines einseitigen Filters *ist*
Aufkreuzung eines rationalen Intervalls, und dieser Teil kommt ohne
Wahrscheinlichkeit aus. Am 2026-09-17 ist der Meilenstein dann in fünf Läufen
bis zu `exists_cadlag_modification_of_isRegularizingClass` durchgezogen worden;
im vierzehnten und fünfzehnten Lauf desselben Tages sind auch die **beiden
Quasi-Linksstetigkeiten** gefallen —
`isQuasiLeftContinuous_of_isRegularizingClass` und die klassische Instanz
`isQuasiLeftContinuous_of_isMPSolutionFor`, letztere **ohne** Atomlosigkeit der
Uhr, die Ethier–Kurtz dort verlangen und die die hiesige Aussagefassung trug.
**Meilenstein 9 hat damit kein `sorry` mehr.** Die Zahl in `MartingaleProblems`
stand seither bei **drei**: die stetige Fassung des fdd-Kriteriums und die beiden
Konvergenzsätze `mpSolution_of_tendsto` und
`isMPSolution_of_forall_condExp_eq_of_dense`. Im siebzehnten Lauf des
2026-09-17 ist der letzte davon **bewiesen** — der Übergang von der
Martingalidentität längs eines dichten `D` auf den ganzen Index —, und die Zahl
steht bei **zwei**. Drei Befunde an seinen Voraussetzungen gehören dazu: die
gleichgradige Integrierbarkeit ist keine Voraussetzung, sondern eine Folgerung
aus der Identität längs `D` selbst; `Dense D` reicht **nicht** und ist durch die
Bedingung ersetzt, die `LiftWitness.exists_countable_right_dense` liefert; und
`D.Countable` wird gar nicht gebraucht.

Kein `sorry` steht in einer *Aussage*, nur in Beweisen: alle sitzen in
`theorem`en.

Manuskript: **134 Seiten**, `check.py` clean — der Runner verwirft `.tex` und
`.pdf` eines Laufs, der durchfällt, und behält den Rest. `master`,
`origin/master` und `facts-inventory` sind synchron; am 2026-09-15 nachgesehen,
es liegt nichts Unmerged herum.
