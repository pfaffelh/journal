# Prüfwerkzeuge für die Tau-Ceti-Roadmaps

Fünf Skripte, mit denen ein Lauf die vier `README.md` und die drei
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
python3 scripts/check_negatives.py          # -> _citations/negatives.md
python3 scripts/check_suggested.py          # -> _citations/lean_check.md
```

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
  stehen in keiner Quellzeile als `theorem`.
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
