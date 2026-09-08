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
