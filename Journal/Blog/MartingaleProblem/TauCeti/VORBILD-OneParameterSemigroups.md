# Was PR #16 lehrt — `OneParameterSemigroups` als Vorbild

Aufbereitet am 2026-09-07, zur Vorbereitung unserer eigenen Einreichung.
`CONTRIBUTING.md` empfiehlt, vor dem ersten PR zwei oder drei gemergte Roadmaps
aus einem verwandten Gebiet zu lesen — „the review discussion on their pull
requests is often more instructive than the merged result". Hier ist die
Diskussion, und sie ist es.

**Warum diese.** Von rund fünfzig gemergten Roadmaps liegen drei in unserer
Nähe: `OneParameterSemigroups` (19 KB), `Exchangeability` (47 KB),
`OptimalTransport` (152 KB). Die erste ist die kürzeste und die einzige, die
unmittelbar an unsere Arbeit stößt — sie ist der Gegenstand von
`MartingaleProblems` Meilenstein 13, den wir für Halbgruppen und den vollen
Erzeuger angelegt haben. **Vor der Einreichung ist zu prüfen, ob unser
Meilenstein 13 mit ihr kollidiert.**

Nebenbei beantwortet `OptimalTransport` mit 152 KB die Größenfrage: eine
Obergrenze, die uns beträfe, gibt es nicht.

## Der Gegenstand

> Roadmap: one-parameter semigroups, completely monotone and positive-definite
> functions, and Bochner-type representations

C₀-Halbgruppen, Erzeuger und Resolventen, Hille–Yosida; vollständig monotone
Funktionen und Bernstein; positiv definite Funktionen und Bochner; die
BCR-Darstellung auf involutiven Halbgruppen. Eingereicht von `mrdouglasny`,
gemergt am 2026-06-20 nach zwei Runden Review durch `kim-em`.

## Der Aufbau, den wir übernehmen sollten

281 Zeilen, neun Abschnitte, 62 in Backticks gesetzte Bezeichner:

```
Generality bar (decide these up front; do not silently specialize)
What Mathlib already has (consume, and connect to)
What is missing (build here)
Part A — Strongly continuous semigroups
Part B — Completely monotone (and Bernstein) functions
Part C — Positive-definite functions and Bochner's theorem
Dependency ordering
References
```

Drei Dinge daran sind bei uns anders, und zwei davon sollten es nicht bleiben.

* **„Generality bar … do not silently specialize"** steht *vor* allem
  Inhaltlichen. Das ist genau unsere „Stehende Regel: minimale
  Voraussetzungen", nur als Abschnitt der Roadmap selbst statt als Regel für
  die Läufe. Unsere Bündel (T0)–(T4) und (E0)–(E3) gehören dorthin.
* **„What Mathlib already has (consume, and connect to)"** — dieselbe
  Überschrift, die unsere vier Roadmaps seit dem 2026-08-30 tragen. Gut.
* **Je Teil: API → Meilenstein → acceptance examples.** Das ist die
  Bibliotheksbau-Struktur, die der Reviewer erzwungen hat (siehe unten). Unsere
  Meilensteine listen Zielaussagen, aber **keine acceptance examples**. Das
  würde ich nachziehen.

## Der Review, und was er verlangt hat

`kim-em` hat in Runde 1 vier Dinge beanstandet. Alle vier betreffen uns.

**1. Bibliotheksbau statt Zielsatz-Jagd.**

> I would like to see this rewritten to have a more „library building" focus.
> Rather than racing to particular theorems, we should be asking to fill in the
> basic theory of the objects introduced.
> I *hope* that the review rubrics would fight against PRs that directly
> followed this roadmap, but I'm not sure.

Konkret verlangt: erst allgemeine C₀-Halbgruppen, **dann** Kontraktionen als
Unterklasse; Hille–Yosida bei allgemeinem $(M,\omega)$ und Kontraktion als
Korollar; Aussagen wie „der Erzeuger bestimmt die Halbgruppe eindeutig"; und
die Resolventen an Mathlibs vorhandene Resolventen **anbinden**.

*Für uns:* wir stehen hier gut da — die abstrakte Schicht ist bei uns das
Primitiv, die Markovsche der Spezialfall. Aber der Punkt „an Vorhandenes
anbinden" ist der, an dem wir viermal gestolpert sind.

**2. Nicht auf eigenes externes Material stützen.**

> Could try to rewrite it so it doesn't rely on the existing external material
> you have? … there are references to particular files in your existing
> material, and I worry this will hinder the AI reviewers, who might be inclined
> to just take your existing material as „the standard", and then accept things
> without sufficient adversarial review.

**Das ist der Punkt, der uns am direktesten trifft.** Unsere Roadmaps verweisen
an mehreren Stellen auf `RemyDegenne/brownian-motion` und auf
`kolmogorov_extension4` als zu übernehmenden Code, und `SUBMISSION.md` baut
darauf. Nach diesem Review ist das genau die Form, die ein Reviewer
zurückweist: das fremde Repository darf **zitierte Quelle** sein, nicht
Spezifikation. Die Meilensteine müssen ohne es lesbar und prüfbar sein.

*Zu tun:* jede Stelle durchgehen, an der eine Roadmap sagt „is to be taken over
from …", und die Aussage so ausschreiben, dass sie ohne den Blick ins fremde
Repository steht.

**3. KI-Beteiligung nennen, mit Modell.**

> Could you add an AI attribution in the PR description, which specifies which
> model you used here? (It doesn't feel much like Claude or Codex to me … I'm
> just trying to calibrate how much the things I don't like in the text are
> merely consequences of the model used!)

Der Autor hat geantwortet: „Drafted by Claude (Opus 4.8), with advice from
Gemini and Codex. Lightly human-edited and directed by me." Bei uns wären es
Opus 5 und zeitweise Fable 5, rund fünfzig autonome Läufe, protokolliert in
`Facts/INVENTAR.md`. Das gehört so in die PR-Beschreibung.

**4. Rebase auf aktuelles `main`.** Formalie, aber sie kostet eine Runde.

## Die zweite Runde, und was sie über den Maßstab sagt

Der Reviewer hat nach der Überarbeitung nicht einfach gemergt, sondern **neun
weitere Punkte** geschickt, ausdrücklich KI-gestützt vorbereitet und als solche
markiert, mit dem Zusatz „I don't mind how much of this you decide to
incorporate". Der Autor hat alle neun eingearbeitet und dabei drei echte
Fehler gefunden — Bernstein braucht vollständige Monotonie auf dem
**abgeschlossenen** $[0,\infty)$ für ein endliches Maß; die Resolvente muss ein
punktweises $X$-wertiges Bochner-Integral sein, nicht operatorwertig;
`IsCompletelyMonotone` muss Glattheit bündeln.

*Die Lehre:* der Review ist inhaltlich und findet Fehler in Aussagen. Genau die
Sorte, die bei uns das Übersetzen gefunden hat — die fehlende
`[OpensMeasurableSpace E]`-Instanz, die sieben `True`-Sätze, die falsche
gefensterte Norm. Dass wir mit übersetzten Dateien kommen, ist deshalb kein
Schmuck, sondern nimmt dem Reviewer Arbeit ab, die er sonst hätte.

## Und ein Hinweis auf Arbeitsteilung

Nach dem Merge hat der Autor beobachtet, dass der Reviewer selbst anfing, Teile
der Roadmap zu formalisieren, und eine Aufteilung vorgeschlagen — er die
Objekt-API, der Autor die Darstellungssätze. Die Diskussion lief auf Zulip
unter „Contention" weiter.

*Für uns:* nach der Einreichung ist damit zu rechnen, dass jemand anfängt. Wer
die 129 bewiesenen Deklarationen beisteuern will, sollte das früh sagen.

## Checkliste vor unserer Einreichung

1. ~~Meilenstein 13 gegen `OneParameterSemigroups` halten~~ — **erledigt
   2026-09-07, und die erste Antwort war zu eng.** Der Überlapp ist groß, aber
   mit **Ethier--Kurtz**, nicht mit unserem Manuskript: EK Kapitel 1 ist
   Halbgruppentheorie, und deren Roadmap deckt genau das ab. Unser Manuskript
   benutzt davon nichts (`rem:noch1` zählt die ausgelassenen Sätze einzeln
   auf), also stoßen die beiden Roadmaps aneinander, statt zu kollidieren.
   **Was dort fehlt**, ist der *messbare* Zweig: ihre Teil-A-Halbgruppen sind
   stark stetig mit `LinearPMap`-Erzeuger, und sie merken selbst an, daß eine
   stark stetige Halbgruppe nicht normmeßbar sein muß — behandeln aber weder
   meßbare Halbgruppen noch den vollen Erzeuger noch mehrwertige Erzeuger. Das
   ist EK Prop. 1.5.1, und es ist genau unser Meilenstein 13.
   **Empfehlung: anbieten statt behalten.** Der meßbare Zweig gehört in ihre
   Teil A; ihr erklärtes Publikum nennt „Markov semigroups" ausdrücklich. Das
   ist zugleich der Anlaß, sie vor dem PR auf Zulip anzusprechen — dort lief
   nach PR #16 schon eine Diskussion über Arbeitsteilung.
2. Jede Stelle entschärfen, die `brownian-motion` oder
   `kolmogorov_extension4` als Spezifikation statt als Zitat führt.
3. Die beiden auslaufenden Meilensteine (12, 13) als *roadmap-for-a-roadmap*
   kennzeichnen.
4. Acceptance examples je Meilenstein ergänzen.
5. KI-Attribution mit Modellen in die PR-Beschreibung.
6. `Exchangeability` und `OptimalTransport` querlesen, bevor der PR aufgeht.
