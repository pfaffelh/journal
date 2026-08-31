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

1. **Den Halbordnungssatz ins Manuskript setzen.** Am 2026-08-31, sechster Lauf,
   ist der Fall unvergleichbarer Atome **bewiesen**: auf jeder endlichen
   Halbordnung mit nichtnegativen Massen ist $\delta\equiv0$. Beweis, explizite
   Konstruktion und Nachrechnung stehen im PROTOKOLL, Abschnitt „Der
   Halbordnungsfall, 2026-08-31 (sechster Lauf)", geprüft von `selfadjoint.py`.
   Zu tun ist damit dreierlei am Manuskript, und das ist eine Aufgabe für den
   **Anfang** eines Laufs, weil danach `python3 check.py` laufen und `clean`
   melden muss: (i) die Statuszeile „purely atomic, atoms incomparable" in
   `rem:atomsnotchange` (Stelle 5535) von „verified exhaustively up to five
   points; not proved" auf `proved` bringen; (ii) `prop:atomicdual` von der
   Kettenhypothese befreien oder eine zweite Proposition daneben setzen — die
   Kette behält die stärkere Konklusion $\Phi(s,t)=\Phi(t,s)$ und erlaubt Massen
   beider Vorzeichen, die Halbordnung gibt nur den Defekt und verlangt
   $m\ge0$; (iii) im Text von `rem:atomicdual` festhalten, dass der Diamant mit
   $m_a=1$, $m_b=-1$ der Zeuge dafür ist, dass $m\ge0$ nicht wegfällt.

2. **Task 23, was danach offen bleibt.** Zwei Punkte, beide unberührt von diesem
   Beweis. **Ordnungsdichte Atommengen** fallen aus der Hypothese heraus (unter
   einem Punkt liegen dann unendlich viele Atome); der Grund ist scharf und steht
   im PROTOKOLL unter „Was offen bleibt". **Stufe 3, die gemischte Uhr,** ist
   nie angegangen worden. Von beiden ist die gemischte Uhr die nähere: der
   atomlose und der atomare Teil sind einzeln erledigt, und zu klären ist, ob
   sich der Defekt entlang der Lebesgue-Zerlegung von $q$ addiert.

3. **Prüfen, ob die Roadmaps noch zu Mathlib master passen.** Alle zitierten
   Deklarationen gegen master, auf Existenz und `deprecated`. Am 2026-08-29
   fanden sich so drei Fehler. Sinnvoll etwa alle zwei Wochen. *Am 2026-08-31,
   dritter Lauf, ist die Liste „What Mathlib already has" von `WeakConvergence`
   erledigt: elf Deklarationen, alle vorhanden, keine `deprecated`. Es fehlen
   also noch die drei übrigen Roadmaps und die Zitate in den Meilensteinen.*

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

   *Zwischenstand 2026-08-31, dritter Lauf: der Block war so, wie er dastand,
   nicht formalisierbar, und beide Gründe sind behoben. `CompleteSpace
   (ProbabilityMeasure E)` ist ein Typfehler — die Metrik sitzt auf der Struktur
   `LevyProkhorov (ProbabilityMeasure E)`, `ProbabilityMeasure E` trägt keine
   Uniformität —, und der angegebene Beweisweg der Vollständigkeit war zirkulär,
   weil er `isTightMeasureSet_of_isCompact_closure` für einen Schritt nannte, der
   den kompakten Abschluss erst herstellen soll. Der Meilenstein führt jetzt vier
   Punkte, den Weg über Ulam (`isTightMeasureSet_singleton`) und, als eigene
   Aussage, die Herauslösung des Straffheitsskeletts aus `Measure/Prokhorov.lean`
   (`isTightMeasureSet_of_forall_exists_finite_iUnion_ball`). Übersetzt ist
   nichts: der Worktree hat kein `.lake`. Der Punkt bleibt deshalb offen, und der
   erste Schritt ist jetzt benannt — siehe den Laufbericht im Inventar.*
