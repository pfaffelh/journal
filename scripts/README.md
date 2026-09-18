# Prüfwerkzeuge für die Tau-Ceti-Roadmaps

Skripte, mit denen ein Lauf die vier `README.md` und die drei
`Suggested.lean` unter `Journal/Blog/MartingaleProblem/TauCeti/` gegen Mathlib
prüft. Jedes ist allein lauffähig, jedes verankert seine Pfade an der Wurzel des
Worktrees und läuft daher aus jedem Verzeichnis, und keines schreibt außerhalb
von `scripts/_citations/`.

Die Quellen und ihre Rangfolge stehen im Auftrag: maßgeblich ist
`git show upstream/master:Mathlib/…` im Checkout `~/Code/lean/mathlib4`, daneben
der Release v4.33.1 unter `~/Code/lean/journal/.lake/packages/mathlib`. Der
**Arbeitsbaum** von `~/Code/lean/mathlib4` wird von keinem Skript angefaßt; es
wird nur gelesen und nichts ausgecheckt.

## Der Durchgang

```
python3 scripts/extract_citations.py        # was die Roadmaps zitieren
python3 scripts/mathlib_index.py master     # Deklarationsindex von upstream/master
python3 scripts/mathlib_index.py v4331      # Deklarationsindex von v4.33.1
python3 scripts/check_citations.py          # -> _citations/report.md
python3 scripts/check_cited_lines.py        # -> _citations/cited_lines.md
python3 scripts/check_negatives.py          # -> _citations/negatives.md
python3 scripts/check_suggested.py          # -> _citations/lean_check.md
python3 scripts/check_master.py             # -> _citations/lean_check_master.md
```

**Seit dem 2026-09-18 ist `check_master.py` die maßgebliche Prüfung** und
`check_suggested.py` die Gegenprobe: die Kette ist auf Mathlib `master`
umgestellt, und ihre Fehler gegen v4.33.1 sind zu **berichten**, nicht zu
beheben.

`git fetch upstream master` gehört davor, und der Commit gehört in den
Laufbericht.

## Was jedes tut

* **`extract_citations.py`** zieht aus den sieben Dateien alle zitierten
  `Mathlib/…lean`-Pfade und alle in Backticks stehenden Bezeichner, abzüglich
  der Namen, die die `Suggested.lean` selbst deklarieren.
* **`mathlib_index.py`** baut aus einer der beiden Quellen einen Index aller
  Deklarationsnamen mitsamt Namespace. Zwei Dinge, an denen eine naive Fassung
  falsche Funde erzeugt und die hier behandelt sind: `@[deprecated …] alias foo
  := bar` gilt dem Alias und nicht der nächsten Deklaration, und die von
  `@[to_dual foo]`, `@[to_additive foo]` und `@[to_fun foo]` erzeugten Namen
  stehen in keiner Quellzeile als `theorem`. Ein drittes ist am 2026-09-19
  dazugekommen: ein Attribut **vor** der Deklaration in derselben Zeile —
  `@[simp] lemma find_eq_zero …` — wurde vom Abschneiden an `@[` nicht
  erfaßt, und der Index war dadurch um **8 866 Deklarationen zu klein**,
  darunter `Nat.find_eq_zero`. Ein beliebiger Git-Revision-Ausdruck ist als
  Argument zugelassen, damit gegen **den** Commit indiziert werden kann, den die
  Roadmaps nennen, und nicht gegen den Stand des Tages.
* **`check_cited_lines.py`** prüft das andere Stück derselben Angabe: nicht, ob
  der zitierte Name existiert, sondern ob er auf der zitierten **Zeile** steht.
  Es paart nicht auf gut Glück, sondern fragt umgekehrt, ob *irgendein*
  Bezeichner des Umfelds dort steht; nur was dort nicht steht, wird gepaart, und
  nur, wenn genau ein Bezeichner des Umfelds in der zitierten Datei wohnt. Drei
  Klassen bleiben ausdrücklich draußen und werden getrennt gezählt: eine
  Fundstelle, die auf eine *andere* Deklaration oder auf ein `variable`-Bündel
  zeigt (die ist gemeint, nicht veraltet), eine, die sich selbst auf v4.33.1
  beruft (die ist ein Versionsvergleich), und eine, die sich nicht paaren ließ.
  Dazu ein Test, der ohne jede Paarung auskommt: zeigt eine Fundstelle in eine
  Datei, die es nicht mehr gibt, die nur noch ein `deprecated_module`-Rumpf ist,
  oder hinter deren Ende — das fand am 2026-09-19 drei Zitate in
  `MeasureTheory/Measure/MeasureSpace.lean`, das auf `master` seit dem
  2026-08-19 vierzehn Zeilen hat.

  ```
  python3 scripts/check_cited_lines.py            # gegen den gepinnten Commit
  python3 scripts/check_cited_lines.py --fix      # schreibt die Abweichungen um
  ```

  rc 1, wenn eine Zeile verschoben oder eine Fundstelle tot ist.
* **`check_citations.py`** schlägt jeden Namen in beiden Indizes nach und
  sortiert nach: auf beiden, nur v4.33.1 (also von master verschwunden), nur
  master, `deprecated`, gar nicht gefunden.
* **`check_negatives.py`** trägt die Negativaussagen der Roadmaps — „Mathlib hat
  X nicht" — als Liste und sucht zu jeder das Muster, das sie widerlegen würde.
  **Wer eine solche Aussage in eine Roadmap schreibt, trägt sie hier nach**, sonst
  wird sie nie wieder geprüft.
* **`check_suggested.py`** typprüft die drei `Suggested.lean` gegen das fertig
  gebaute Mathlib des Hauptcheckouts und zählt Fehler und `sorry`. Es benutzt
  `lake --dir=…` statt `cd`.
* **`iter_mp.py`** übersetzt eine einzelne `Suggested.lean` gegen einen
  **bleibenden** `.olean`-Baum `scratch/_iter/`, damit ein Durchgang während des
  Schreibens nicht die beiden Abhängigkeiten mitbaut. Es gibt die Fehlerblöcke
  ungefiltert aus und **ersetzt `check_suggested.py` nicht**: der Abschlußbefund
  eines Laufs wird mit jenem Skript erhoben, das seinen Baum bei jedem Lauf
  löscht und damit keine veraltete `.olean` durchgehen läßt.

  ```
  python3 scripts/iter_mp.py WeakConvergence SkorokhodSpace   # einmal je Lauf
  python3 scripts/iter_mp.py MartingaleProblems               # je Durchgang
  ```

* **`check_axioms.py`** gibt die Axiomabhängigkeiten benannter Deklarationen
  einer `Suggested.lean` aus. Jeder Lauf prüft seine neuen Deklarationen mit
  `#print axioms`; bisher geschah das von Hand, indem die Zeilen an die Datei
  angehängt und wieder entfernt wurden — ein Abbruch dazwischen hinterläßt die
  Quelle verändert. Das Skript arbeitet auf einer Kopie neben der Quelle und
  räumt sie in einem `finally` weg.

  ```
  python3 scripts/check_axioms.py MartingaleProblems isStoppingTime_jumpTime
  ```

* **`check_master.py`** ist `check_suggested.py` gegen den Worktree
  `~/Code/lean/mathlib-master` auf `upstream/master`. Es leitet das
  Repositorium aus dem eigenen Dateipfad ab, arbeitet also im Worktree, aus dem
  es aufgerufen wird, und nicht im Hauptcheckout.

  **Sein Rückgabewert ist seit dem 2026-09-18 eine Schranke**, nicht bloß eine
  Meldung: rc 1 bei einem Fehler *oder* bei einem veralteten Namen. Die übrigen
  Warnungen (am 2026-09-18: 160, davon 58 `unusedSectionVars`) bleiben
  ausdrücklich draußen — sie sind Stilfragen, und `unusedSectionVars` zu
  befolgen hieße Signaturen ändern. Der Grund für die Schranke ist gemessen: von
  den 354 Veraltungen, die der dreiundzwanzigste Lauf des 2026-09-18 abtrug,
  waren **78 schon gegen v4.33.1 veraltet**, eine seit zehn Monaten. Sie sind
  eingesickert, weil `check_suggested.py` nur Fehler zählt.
* **`check_axioms_master.py`** ist `check_axioms.py` gegen denselben Worktree.
  Es braucht den `.olean`-Baum, den `check_master.py` anlegt, und ist deshalb
  nach ihm zu laufen.
* **`show_master_errors.py`** zeigt die Meldungen eines `check_master.py`-Laufs
  **ungekürzt**, wahlweise auf einen Zeilenbereich eingeschränkt;
  **`master_error_families.py`** gruppiert sie nach dem Kopf der Anwendung, in
  der sie auftreten, also nach dem Mathlib-Namen, dessen Signatur sich geändert
  hat. Beide sind Lesehilfen und ersetzen `_citations/lean_check_master.md`
  nicht.

  ```
  python3 scripts/show_master_errors.py MartingaleProblems 3000 3200
  python3 scripts/master_error_families.py MartingaleProblems
  ```

* **`count_sections.py`** und **`count_range.py`** zählen Zeilen und
  Deklarationen einer `Suggested.lean` — das erste je `section`, das zweite je
  Zeilenbereich. Beide lesen nur und drucken die gefundenen Deklarationsnamen
  mit, damit die Zuordnung zu einem Weg nachprüfbar ist statt geglaubt werden zu
  müssen; sie lösen die ad-hoc-Zähler unter `_citations/count_*.py` ab, die je
  einen Weg fest verdrahten.

  ```
  python3 scripts/count_sections.py <datei.lean> [Abschnitt ...]
  python3 scripts/count_range.py <datei.lean> 15331-15560 15561-16092
  ```

`show_master.py` daneben zeigt Kontextzeilen aus `upstream/master` oder aus
v4.33.1, ohne etwas auszuchecken:

```
python3 scripts/show_master.py Mathlib/Topology/Order/Cadlag.lean:104 8
python3 scripts/show_master.py Mathlib/Order/Basic.lean:71 --v4331
```

## Was nicht ins Repository gehört

Die beiden Deklarationsindizes sind je rund 20 MB und in Minuten neu gebaut;
`_citations/.gitignore` hält sie draußen. Die Berichte daneben bleiben, weil der
Laufbericht in `Facts/INVENTAR.md` auf sie verweist.
