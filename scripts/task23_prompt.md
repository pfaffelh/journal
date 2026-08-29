Du arbeitest autonom und unbeaufsichtigt an **Task 23** des Manuskripts
`Journal/Blog/MartingaleProblem/MartingaleProblem.tex`: dem Beweis der
Dualitätsidentität für eine **rein atomare Uhr**. Du bist in einem
git-Worktree auf dem Branch `task23-atomic-duality`. Zeitbudget: 120 Minuten.

## Zuerst

Lies `Journal/Blog/MartingaleProblem/Task23/PROTOKOLL.md` vollständig. Dort
stehen der Auftrag, das festgeschriebene Modell, der Stand und die bereits
bekannten **Sackgassen**. Gehe keine davon erneut. Lies dann
`git log --oneline -15`, um zu sehen, was die letzten Läufe getan haben.

## Auftrag

Die Stufenleiter steht im Protokoll: (1) endlich viele Atome, (2) abzählbar
viele, insbesondere ordnungsdichte Atommengen, (3) gemischte Uhr. Arbeite an
der niedrigsten Stufe, die noch offen ist. Ein Lauf muss keine Stufe
abschließen — ein sauber verifizierter Teilschritt plus ein ehrlicher
Protokolleintrag ist ein guter Lauf.

## Regeln, die nicht verhandelbar sind

1. **Jede Behauptung wird am Orakel geprüft, bevor sie aufgeschrieben wird.**
   `Journal/Blog/MartingaleProblem/Task23/oracle.py` rechnet den Defekt
   $\Phi(N,1)-\Phi(1,N)$ symbolisch aus. Erweitere es, wenn Du eine andere
   Konfiguration brauchst (andere Atomlagen, mehrdimensionaler Index, gemischte
   Uhr), aber prüfe nach jedem Umbau, dass es für gleiche Massen die bekannte
   Aussage „$\Phi$ konstant auf Antidiagonalen" reproduziert. Ein falsches
   Orakel vergiftet alle Folgeläufe.
2. **Das Manuskript wird erst angefasst, wenn ein Beweis vollständig und
   verifiziert ist.** Bis dahin arbeitest Du in `Task23/`. Wenn Du es anfasst:
   danach `python3 Journal/Blog/MartingaleProblem/check.py`, und der muss
   `clean` melden.
3. **Nur dieser Branch.** Kein Wechsel auf `master`, kein Merge, kein
   Force-Push. Der Runner committet und pusht den Branch selbst.
4. **Kein Vortäuschen.** Wenn nichts vorangeht, schreibe das ins Protokoll.
   Ein Lauf, der eine Sackgasse sauber dokumentiert, ist mehr wert als einer,
   der plausible Prosa produziert.

## Am Ende jedes Laufs, verpflichtend

Hänge an `Task23/PROTOKOLL.md` einen Abschnitt an mit dem Datum, und darin:

* **Was versucht wurde** und was das Orakel dazu gesagt hat, mit den konkreten
  Zahlen oder Ausdrücken.
* **Ergebnis**: Teilschritt bewiesen / widerlegt / offen geblieben, und warum.
* Neue **Sackgassen** in den Abschnitt „Sackgassen", damit sie kein zweiter
  Lauf wiederholt.
* **Mindestens ein konkreter Vorschlag, was als Nächstes formalisiert werden
  soll** — als benanntes Ziel, nicht als Richtung. Zulässig sind: ein neuer
  Meilenstein oder Meilenstein-Punkt in einer der vier Roadmaps unter
  `Journal/Blog/MartingaleProblem/TauCeti/`, oder ein neuer Task für
  `PLAN.md`. Nenne die Aussage, worauf sie ruht, und warum sie jetzt dran ist.
  Wenn der Lauf selbst etwas bewiesen hat, ist der naheliegende Vorschlag die
  Lean-Fassung davon; wenn nicht, nimm etwas, das der Lauf beim Lesen als
  reif erkannt hat.

Wenn ein Vorschlag reif genug ist, trage ihn zusätzlich direkt in die
betreffende Roadmap bzw. in `PLAN.md` ein — auf diesem Branch, nicht auf
`master`.
