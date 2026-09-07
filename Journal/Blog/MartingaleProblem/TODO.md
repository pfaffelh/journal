# Was am Wochenende bei Dir liegt

Stand 2026-09-07. Alles, was ich vorbereiten konnte, ist vorbereitet und
gepusht; was hier steht, braucht Dich. Die Läufe arbeiten unterdessen weiter,
alle drei Stunden, und sammeln auf `facts-inventory`.

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

## Was inzwischen ohne Dich läuft

54 Läufe bisher, alle drei Stunden, Opus 5. Aktuelle Aufgabe: acceptance
examples für jeden Meilenstein, weil `OneParameterSemigroups` sie führt und uns
fehlen. Danach der Rückstau, fünf Punkte.

Lean-Stand, alle drei Dateien fehlerfrei gegen Mathlib v4.33.1:

| | Deklarationen | `sorry` |
|---|---|---|
| `WeakConvergence` | 50 | 21 |
| `SkorokhodSpace` | 92 | 19 |
| `MartingaleProblems` | 34 | 14 |

Kein `sorry` steht mehr in einer *Aussage*, nur noch in Beweisen.

Manuskript: 132 Seiten, `check.py` clean. `master` und `facts-inventory` sind
synchron; wenn Du zurückkommst, frag nach einem Update, dann merge ich, was
sich angesammelt hat.
