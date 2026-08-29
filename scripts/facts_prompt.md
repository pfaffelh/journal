Du arbeitest autonom und unbeaufsichtigt am **Formalisierungs-Inventar** des
Manuskripts `Journal/Blog/MartingaleProblem/MartingaleProblem.tex`. Du bist in
einem git-Worktree auf dem Branch `facts-inventory`. Zeitbudget: 120 Minuten.

## Worum es geht

Die 29 mit `\begin{fact}` ausgezeichneten Aussagen des Manuskripts sind seine
Voraussetzungsfläche — alles, was zitiert und nicht bewiesen wird. Sie müssen
alle formalisiert sein, damit die Formalisierung des Manuskripts überhaupt
aufgeht. `Journal/Blog/MartingaleProblem/Facts/INVENTAR.md` hält je Fact fest,
ob er in Mathlib liegt, von einer der vier Roadmaps unter
`Journal/Blog/MartingaleProblem/TauCeti/` abgedeckt wird, oder eine Lücke ist.

## Zuerst

Lies `Facts/INVENTAR.md` ganz, dann `git log --oneline -15`. Nimm dir die
Zeilen mit Status `?` vor, in der Reihenfolge der Spalte **tragend**
(absteigend). Ein Lauf schafft vielleicht zwei bis vier Facts gründlich — das
ist besser als zehn oberflächlich.

## Je Fact

1. Lies die Aussage im Manuskript nach, ganz. Nicht den Titel, den Wortlaut.
2. Stelle fest, ob Mathlib sie hat. Der Worktree hat kein `.lake`; die
   Mathlib-Quellen sind über `--add-dir` erreichbar, unter
   `~/Code/lean/journal/.lake/packages/mathlib/Mathlib` (v4.33.1) und
   `~/Code/lean/mathlib4/Mathlib` (Arbeitsbranch des Nutzers). Für Aussagen
   über **master** — worauf Tau Ceti aufsetzt — nimm `gh api` oder
   `gh search code`, wie es der Durchgang am 2026-08-29 getan hat. Suche
   **nach dem Begriff, nicht nach dem Dateinamen**: Mathlib nennt Dinge oft anders, als das Manuskript sie nennt.
   Am 2026-08-29 kostete genau das drei Fehler — `Locally` statt „local
   martingale", `IsStronglyProgressive` statt `ProgMeasurable`,
   `upcrossingsBefore` statt `upcrossing`. Prüfe für jeden gefundenen Namen,
   dass er als Deklaration existiert und **nicht `deprecated`** ist.
3. Trage den Status mit Beleg ein. Ohne Beleg gilt `?`, nicht `Mathlib`.
4. Ist es eine **Lücke**, so trage sie als benannten Punkt in den passenden
   Meilenstein der passenden Roadmap ein — mit der Aussage, worauf sie ruht,
   und in Mathlibs Namenskonventionen. Passt sie in keinen Meilenstein, lege
   einen neuen an. Halte die Formatregeln von Tau Ceti ein: keine Lücken, keine
   konditionale Sprache („optional", „später", „blockiert durch"), zeitlos,
   vollständige Grundtheorie je Objekt.
5. Deckt eine Roadmap den Fact schon ab, nenne den Meilenstein in der Spalte
   Beleg — und prüfe bei der Gelegenheit, ob das dortige Zitat noch stimmt.

## Regeln, die nicht verhandelbar sind

1. **Nichts aus dem Gedächtnis.** Jeder Mathlib-Name wird am Quelltext belegt.
2. **Das Manuskript wird nicht verändert.** Du arbeitest an `Facts/INVENTAR.md`
   und an den Roadmaps. Fällt Dir am Manuskript etwas auf, schreibe es unter
   „Offene Auffälligkeiten" ins Inventar.
3. **Nur dieser Branch.** Kein Wechsel auf `master`, kein Merge, kein
   Force-Push. Der Runner committet und pusht selbst.
4. **Kein Vortäuschen.** Ein Fact, dessen Lage Du nicht klären konntest, bleibt
   `?` mit einer Notiz, woran es lag. Das ist ein gutes Ergebnis.

## Am Ende jedes Laufs, verpflichtend

Hänge an `Facts/INVENTAR.md` unter „Läufe" einen Abschnitt mit Datum an:
welche Facts bearbeitet wurden, was der Befund war, was offen blieb. Und
**mindestens ein konkreter Vorschlag, was als Nächstes formalisiert werden
soll** — als benanntes Ziel, nicht als Richtung: eine Aussage, worauf sie ruht,
warum sie jetzt dran ist. Ist der Vorschlag reif, trage ihn direkt in die
betreffende Roadmap oder in `PLAN.md` ein, auf diesem Branch.

## Wenn das Inventar vollständig ist

Sind alle 29 Zeilen belegt, wechselst Du zu **Task 23** — dem Beweis der
Dualitätsidentität für eine rein atomare Uhr. Auftrag, Modell, Stand und
Sackgassen stehen in `Journal/Blog/MartingaleProblem/Task23/PROTOKOLL.md`, das
Orakel in `Task23/oracle.py`. Dieselben Regeln gelten; das Manuskript darf
dann angefasst werden, aber erst wenn ein Beweis vollständig und verifiziert
ist, und danach muss `python3 Journal/Blog/MartingaleProblem/check.py` `clean`
melden.
