# Offene Punkte nach der Kürzung der READMEs (2026-09-23)

Die vier `README-kurz.md` liegen neben den Originalen. Was noch aussteht:

## 1. Fünf Deklarationen sind beim Lean-Schnitt falsch einsortiert

Diese fünf sind **allgemeine** Aussagen über `mpFamily` und regularisierende
Klassen. Die Abhängigkeitshülle des Schnitts vom 2026-09-22 hat sie nach
`JumpProcesses/Suggested.lean` gezogen, weil ihre *Beweise* Sprungmaterial
berühren; ihre *Aussagen* gehören nach `MartingaleProblems`:

* `isRegularizingClass_mpFamily`
* `isCompensatorFor_mpFamily`
* `exists_cadlag_modification_of_isRegularizingClass`
* `isQuasiLeftContinuous_of_isRegularizingClass`
* `not_isQuasiLeftContinuous_of_isRegularizingClass_of_free_solutionSet`

Die gekürzte `MartingaleProblems/README.md` nennt sie in Meilenstein 8, wo sie
hingehören. Beim nächsten Anfassen des Schnitts sind sie zurückzuholen — dabei
ist zu prüfen, welche Beweiszeilen tatsächlich Sprungmaterial lesen und ob sich
das durch eine Hypothese ersetzen läßt.

## 2. Die Numerierung ist in den Kurzfassungen neu und lückenlos

`MartingaleProblems` hat in der Kurzfassung die Meilensteine 1–12 ohne Lücken;
die alten Nummern 4 und 14 sind nach `JumpProcesses` gewandert. Die Zuordnung:

    alt  1 2 3 5 6 7 8 9 10 11 12 13
    neu  1 2 3 4 5 6 7 8  9 10 11 12

Verweise in `Suggested.lean` auf „Milestone N" tragen noch die **alten** Nummern.

## 3. Deutsch in den Originalen

`MartingaleProblems/README.md` hat 291 deutsche Zeilen, `JumpProcesses/README.md`
1676 — 28 % der Datei. Die Kurzfassungen sind durchgehend englisch, womit der
Punkt erledigt ist, sobald sie die Originale ersetzen.

## 4. `KolmogorovExtension` braucht nichts

1737 Wörter, unter dem Median der 46 bestehenden Roadmaps. Keine Kurzfassung
angelegt.
