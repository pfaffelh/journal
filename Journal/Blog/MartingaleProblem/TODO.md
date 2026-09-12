# Was am Wochenende bei Dir liegt

Stand 2026-09-08. Alles, was ich vorbereiten konnte, ist vorbereitet und
gepusht; was hier steht, braucht Dich. Die Läufe arbeiten unterdessen weiter,
seit dem 7. September stündlich, und sammeln auf `facts-inventory`.

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

## 8. Elf Lücken in Mathlibs Kernschicht, gefunden beim Bauen der Sprungprozesse

Alle elf beim Beweisen aufgefallen, alle elf gegen `upstream/master` geprüft,
und die ersten vier sind kleine, in sich abgeschlossene Beiträge. Sie gehören
thematisch zu `KolmogorovExtension` und **nicht** in eine der laufenden Aufgaben.

* **Zeithomogenität von `Kernel.traj`.** Daß die Verschiebung einer homogenen
  Markovkette wieder dieselbe Kette ist, steht dort nicht — weder in `v4.33.1`
  noch auf `master`. Wir haben es am 2026-09-09 als `chainKernel_map_shift`
  bewiesen, über die endlichdimensionalen Verteilungen; der ganze Inhalt ist
  `partialTraj_succ_map_shiftIic`, wo die verschobene Familie definitionsgleich
  der nächsten ist, der Rest Induktion und Eindeutigkeit des projektiven Limes.
  Für Mathlib wäre die richtige Fassung nicht unsere, sondern eine über
  `Kernel.traj` selbst, mit einer Homogenitätshypothese an die Familie.

* **Gedächtnislosigkeit der Exponentialverteilung.** Die Zeichenkette
  `memoryless` kommt in der ganzen Bibliothek nicht vor. Wir haben sie als
  `expMeasure_Ioi_add` bewiesen. Sie ist der einzige nicht buchhalterische
  Schritt im Beweis von `thm:jumpMP`, und sie ist elementar — ein Kandidat für
  einen Vier-Zeilen-PR neben `Probability/Distributions/Exponential.lean`.

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
  `Probability/BorelCantelli.lean:50` hinaus.

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

Dazu, aus derselben Baustelle und schon oben unter Punkt 6 vermerkt: die
Indexverallgemeinerung von Ionescu--Tulcea, wo `Maps.lean` bereits für eine
lokal endliche lineare Ordnung geschrieben ist und `Traj.lean` auf `ℕ` festliegt.

## Was inzwischen ohne Dich läuft

78 Läufe bisher, seit dem 7. September stündlich, Opus 5. Am 7./8. September
sind in einem Tag rund 4000 Zeilen Lean dazugekommen. Vier Läufe fielen am
7. September an der Sitzungsgrenze des Kontos aus; der Runner erkennt sie jetzt,
merkt sich den Rücksetzzeitpunkt und setzt bis dahin aus, statt stündlich
dagegenzulaufen.

Lean-Stand, alle drei Dateien gegen Mathlib v4.33.1 geprüft:

| | Deklarationen | bewiesen | `sorry` |
|---|---:|---:|---:|
| `WeakConvergence` | 133 | 131 | 2 |
| `SkorokhodSpace` | 109 | 98 | 11 |
| `MartingaleProblems` | 67 | 58 | 9 |

Ganz bewiesen sind seither `fact:monotoneclass` (der funktionale
Monotone-Klassen-Satz, den Mathlib nur für Mengen hat), `fact:stoneweierstrass`
und die erste Hälfte von `fact:convdet`; `fact:PSpolish` steht bis auf den
Übergang vom atomaren zum allgemeinen Fall.

Drei Stellen im Manuskript sind dabei korrigiert worden, alle in dieselbe
Richtung — die Formalisierung war schärfer als die Prosa: `rem:skorokhodform`
(die Sprungtheorie braucht (T2b) nicht, nur Properness), `fact:monotoneclass`
(stand fälschlich unter „was Mathlib hat"), `fact:convdet` (die Separabilität
ist für die erste Hälfte entbehrlich).

Kein `sorry` steht mehr in einer *Aussage*, nur noch in Beweisen.

Manuskript: 132 Seiten, `check.py` clean. `master` und `facts-inventory` sind
synchron; wenn Du zurückkommst, frag nach einem Update, dann merge ich, was
sich angesammelt hat.
