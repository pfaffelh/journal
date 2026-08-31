# Rückstau

Damit nie ein Lauf ohne Arbeit dasteht. Der Prompt schickt einen Lauf hierher,
wenn die vorrangigen Aufgaben leer sind, das Inventar geschlossen ist und Task 23
gerade nicht weiterkommt. **Von oben nach unten**; wer einen Punkt erledigt,
streicht ihn hier und berichtet im Inventar unter „Läufe".

Wer einen Punkt für erledigt hält, ohne ihn erledigt zu haben, schadet mehr als
ein Lauf, der nichts tut. Im Zweifel: Punkt stehen lassen, Zwischenstand
anhängen.

**Der \EK{}-Scan ist erreichbar**, entgegen einer Notiz vom 2026-08-31. Er liegt
nicht im Worktree, sondern unter
`/home/pfaffelh/Code/lean/journal/references/EthierKurtz1986.pdf`, und das
`Read`-Werkzeug liest ihn mit `pages`. Der Seitenversatz ist **+10**:
Buchseite $n$ ist PDF-Seite $n+10$. Am 2026-08-31 geprüft an den Buchseiten
102--104, 111--116, 126--133 und 142--145.

## Offen

1. **`rem:skorokhodform` Stelle 2238 korrigieren.** Dort heißt
   `[Preorder ι] [TopologicalSpace ι]` „\eqref{T2b}"; das ist falsch, (T2b)
   verlangt mehr. Manuskriptänderung, also erst nach `check.py`. *Zwischenstand
   2026-08-31: dieser Punkt liegt außerhalb dessen, was ein Lauf tun darf. Die
   nicht verhandelbare Regel 2 des Auftrags — „Das Manuskript wird nicht
   verändert" — lässt nur Task 23 als Ausnahme zu, und diese Korrektur gehört
   nicht dazu. Der Befund steht seit dem 2026-08-30 unter den Auffälligkeiten
   des Inventars mit dem Beleg aus `PRAEORDNUNG.md` Teil 2; ausführen muss ihn
   der Nutzer.*

2. **Task 23, unvergleichbare Atome.** Der offene Punkt aus
   `Task23/PROTOKOLL.md`: die Vermutung ist durch $58081$ Konfigurationen
   belegt, der Beweis fehlt. Ansatzpunkt steht dort unter „Wo der Beweis hakt":
   die einzelnen Gleichungen über der Antikette der maximalen Elemente von
   $\T_{<t^*}$.

3. **Prüfen, ob die Roadmaps noch zu Mathlib master passen.** Alle zitierten
   Deklarationen gegen master, auf Existenz und `deprecated`. Am 2026-08-29
   fanden sich so drei Fehler. Sinnvoll etwa alle zwei Wochen.

4. **Die Grundtheorie von `ProbabilityMeasure E` als metrischem Raum
   formalisieren.** Am 2026-08-31 als Lücke belegt und als Block an den Kopf von
   `WeakConvergence` Meilenstein 3 eingetragen: Mathlib hat die Metrisierbarkeit
   (`MeasureTheory.instMetrizableSpaceProbabilityMeasure`,
   `Measure/LevyProkhorovMetric.lean:695`) und weder die Separabilität noch die
   Vollständigkeit — `SeparableSpace (ProbabilityMeasure`,
   `PolishSpace (ProbabilityMeasure` und `CompleteSpace (ProbabilityMeasure`
   haben in v4.33.1, im Arbeitsbranch und auf master (`gh search code`) null
   Treffer. Das ist die erste Hälfte von `fact:PSpolish`, und sie ist der
   Untergrund jedes Teilfolgenarguments des Konvergenzteils.
