Du arbeitest autonom und unbeaufsichtigt am **Formalisierungs-Inventar** des
Manuskripts `Journal/Blog/MartingaleProblem/MartingaleProblem.tex`. Du bist in
einem git-Worktree auf dem Branch `facts-inventory`. Zeitbudget: 120 Minuten.

## Vorrangige Aufgaben

Stehen hier Aufgaben, so haben sie Vorrang vor allem Übrigen, in der genannten
Reihenfolge. Ist eine erledigt, streicht der Lauf sie hier heraus und trägt das
Ergebnis an der genannten Stelle ein; sind alle erledigt, gilt wieder die
Reihenfolge weiter unten. Eine Aufgabe, die mehr als einen Lauf braucht, wird
nicht gestrichen, sondern um einen Zwischenstand ergänzt.

Zurzeit stehen hier keine Aufgaben.

### Aufgabe: die mengen-indizierte Literatur, und die Summierbarkeit *(gestellt 2026-09-01)*

Zwei Hälften, die zusammengehören. Beide gehen auf eine Beobachtung des Nutzers
zurück: eine Uhr sieht aus wie ein Lévy-Maß, und Atome sind Sprünge zu festen
Zeiten.

**(a) Die Literatur einordnen.** Es gibt eine ausgebaute Theorie
**mengen-indizierter Lévy-Prozesse**: E. Herbin, E. Merzbach, *The set-indexed
Lévy process: Stationarity, Markov and sample paths properties*, Stochastic
Processes Appl. **123** (2013), arXiv:1108.0873; Vorläufer Bass--Pyke und
Adler--Feigin für $\R^N$, dazu Ivanoff--Merzbach für mengen-indizierte
Martingale. Der Index ist dort eine Klasse $\mathcal A$ kompakter
zusammenhängender Mengen, unter Durchschnitten abgeschlossen — ein unterer
Halbverband —, und die Zuwächse laufen über
$\mathcal C_0=\{U\setminus V\}$ bzw. $\mathcal C=\{U_0\setminus\bigcup_i U_i\}$.

Das ist auffällig nah an unserem Aufbau: unser Intervall
$[s,t)=\T_{<t}\setminus\T_{<s}$ ist ein Element von $\mathcal C_0$ mit
$\mathcal A$ = die Abwärtsmengen; ihre Stationarität über das Maß $m$ ist
unsere Uhr; ihre Reduktion auf einen Parameter über *flows* ist strukturell
`cor:atomless`, und dass dafür *simple* flows nötig sind, entspricht
`rem:fddnochain`.

Zu klären, am Text und nicht aus dem Gedächtnis:

1. Wie genau verhält sich ihre Axiomatik zu \eqref{T0}--\eqref{T4}? Welche
   ihrer fünf Axiome an $\mathcal A$ haben bei uns eine Entsprechung, welche
   nicht, und was verlieren oder gewinnen wir dadurch?
2. Steht dort etwas zu **Dualität** oder zu bivariaten Zuwachsdarstellungen mit
   gemeinsamer Dichte? Das ist die eigentliche Frage. Wenn nein, sag das
   deutlich — ein Negativbefund ist hier wertvoll.
3. Gibt die **Flow-Projektion** für den ordnungsdichten Fall etwas her? Sie ist
   die Art Reduktion, die Task 23 seit vier Läufen sucht.
4. Gibt es weitere Literatur zu Lévy-Prozessen über allgemeinen Indexmengen, die
   näher an einer Präordnung liegt als an einer Mengenklasse?

**(b) Die Summierbarkeit als tragende Struktur.** `def:clock` verlangt
$q(\T_{\le t})<\infty$, für eine atomare Uhr also $\sum_{a_k\le t}m_k<\infty$
bei $m_k\ge0$ — das ist die Bedingung $\int(1\wedge|x|)\,\nu(\dif x)<\infty$ des
Lévy-Bildes, der Fall **endlicher Variation**. Kompensation gibt es hier nicht,
weil ein Maß nicht kompensiert werden kann.

Die bisherigen vier Anläufe an den ordnungsdichten Fall haben Aussagen über
**beliebige endliche Massenvektoren mit Slack** gesucht und sind alle
gescheitert — Frobenius, linear, quadratisch —, und der dreizehnte Task-23-Lauf
hält selbst fest, dass „die schlimmsten Muster als Uhren nicht realisierbar
sind: eine ordnungsdichte Uhr mit durchweg wachsenden Massen hätte unendliche
Masse". Die Vermutung ist also, dass die Relaxation genau die Instanzen zulässt,
die keine Uhr sind. Stelle die Frage neu über der Klasse der **summierbaren**
Massen und prüfe, ob die Summierbarkeit dieselbe ausschließende Rolle spielt wie
die endliche Variation im Lévy-Fall.

**Zum Vorgehen.** Teil (a) ist Nachschlagen und Einordnen, Teil (b) ist Rechnen;
sie dürfen auf mehrere Läufe verteilt werden, dann bleibt die Aufgabe mit
Zwischenstand stehen. Das Ergebnis von (a) gehört als eigene Datei
`Facts/SETINDEXED.md`, und **falls** eine Manuskriptbemerkung samt
Bibliographieeinträgen fällig wird, schreibe ihren Text als Vorschlag dorthin,
statt das Manuskript zu ändern — diese Einordnung will der Nutzer sehen, bevor
sie steht.

**Zwischenstand 2026-09-02 (fünfzehnter Task-23-Lauf).** ~~Teil (a) ist
erledigt~~: `Facts/SETINDEXED.md` beantwortet alle vier Fragen am Text
(Herbin–Merzbach über ar5iv, Pedersen–Sato direkt am PDF) und enthält den
Vorschlag für die Manuskriptbemerkung samt Bibliographie. Kernbefunde:
Dualität/bivariate Darstellungen kommen dort **nicht** vor (Negativbefund,
Frage 2); die Flow-Projektion ist der Zeitwechsel von `cor:atomless` und
endet per Axiom vor den Atomen (Frage 3); Pedersen–Sato ist die
\eqref{T0}+\eqref{T4}-nächste Theorie, mit Negativsätzen der Sorte
`rem:chainonly` (Frage 4). Teil (b) ist begonnen: `Task23/summable_lp.py`
misst auf fünf geschachtelten summierbaren Uhren (auch langsame Schwänze
$\varepsilon_J\sim1/J$, $1/\log J$) den Kollaps
$v_J\approx c\sqrt{M\varepsilon_J}$ mit je Uhr stabilem $c\le1.08$ — die für
freie Systeme widerlegte Energieform kehrt auf echten Trunkierungen zurück;
uniform über Uhren ist sie weiterhin falsch (geformter Zwei-Atom-Zeuge: 3,
Präfix: $\sim k$). Offen für den nächsten Lauf: der Interferenztest
(hierarchisch geschachtelte Motoren mit summierbaren $\lambda_i$) und die
Stufenpaar-Rekursion; beides steht präzise in `Task23/PROTOKOLL.md`,
fünfzehnter Lauf, „Was als Nächstes zu rechnen bzw. zu beweisen ist".

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
   `~/Code/lean/mathlib4` — dort aber **nicht der Arbeitsbaum**. Die
   Rangfolge der Quellen, und sie ist wichtig:

   * **`git show upstream/master:Mathlib/...`** in `~/Code/lean/mathlib4`.
     `upstream` zeigt auf `leanprover-community/mathlib4` und ist aktuell.
     Das ist die maßgebliche Quelle für Aussagen über master, worauf Tau Ceti
     aufsetzt. `git grep <Begriff> upstream/master -- Mathlib/` sucht darin,
     ohne etwas auszuchecken.
   * `~/Code/lean/journal/.lake/packages/mathlib/Mathlib` — Release v4.33.1,
     ein brauchbarer Stellvertreter und bequem zu durchsuchen, aber ein
     Release und nicht master.
   * **Nicht benutzen: der Arbeitsbaum von `~/Code/lean/mathlib4`.** Er steht
     auf dem PR-Branch des Nutzers, ist vom März 2026 und über fünftausend
     Commits hinter master — älter als der `.lake`-Release. `origin` dort ist
     der Fork des Nutzers und ebenfalls veraltet; `origin/master` ist **nicht**
     master.

   `gh api`/`gh search code` bleibt zulässig, ist aber langsamer als
   `git show upstream/master:` und nur nötig, wenn `upstream` nicht frisch
   geholt ist (`git fetch upstream master`). Suche
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

## Stehende Regel: minimale Voraussetzungen

Eine Roadmap-Aussage trägt **die schwächsten Hypothesen, unter denen sie gilt**,
nicht die bequemsten. Reicht separabel metrisch, steht dort nicht polnisch;
reicht messbar, steht dort keine Topologie. Der Maßstab ist das Manuskript: es
führt in §2 die Bündel \eqref{E0}–\eqref{E3} und \eqref{T0}–\eqref{T4} genau
dafür, und jede Aussage dort ist mit dem Bündel annotiert, das sie wirklich
braucht. Übernimm diese Annotation, statt sie neu zu erraten.

Wo eine Roadmap heute mehr verlangt als das Manuskript, ist das ein Befund und
gehört korrigiert. Wo das Manuskript selbst mehr verlangt, als der Beweis
braucht, gehört es unter „Offene Auffälligkeiten" — das Manuskript wird von
diesen Läufen nicht geändert.

Umgekehrt gilt: eine Abschwächung wird **belegt**, nicht vermutet. Wer
„polnisch" durch „separabel metrisch" ersetzt, nennt die Stelle, an der die
Vollständigkeit im Beweis nicht mehr vorkommt. Prohorovs Satz zum Beispiel
braucht sie in der Rückrichtung; der Satz von der stetigen Abbildung nicht.

## Regeln, die nicht verhandelbar sind

1. **Nichts aus dem Gedächtnis.** Jeder Mathlib-Name wird am Quelltext belegt.
2. **Das Manuskript wird nicht verändert.** Du arbeitest an `Facts/INVENTAR.md`
   und an den Roadmaps. Fällt Dir am Manuskript etwas auf, schreibe es unter
   „Offene Auffälligkeiten" ins Inventar.
3. **Nur dieser Branch.** Kein Wechsel auf `master`, kein Force-Push. Der
   Runner committet und pusht selbst, und er zieht zu Beginn jedes Laufs
   `origin/master` nach — Du arbeitest also immer auf aktuellem Stand.
   **Ob der Branch nach `master` wandert, entscheidet der Nutzer, nicht der
   Lauf.** Das ist die Stelle, an der ein Mensch die Vorschläge prüft, und sie
   wird nicht wegautomatisiert.
4. **Kein Vortäuschen.** Ein Fact, dessen Lage Du nicht klären konntest, bleibt
   `?` mit einer Notiz, woran es lag. Das ist ein gutes Ergebnis.

## Am Ende jedes Laufs, verpflichtend

Hänge an `Facts/INVENTAR.md` unter „Läufe" einen Abschnitt mit Datum an:
welche Facts bearbeitet wurden, was der Befund war, was offen blieb. Und
**mindestens ein konkreter Vorschlag, was als Nächstes formalisiert werden
soll** — als benanntes Ziel, nicht als Richtung: eine Aussage, worauf sie ruht,
warum sie jetzt dran ist. Ist der Vorschlag reif, trage ihn direkt in die
betreffende Roadmap oder in `PLAN.md` ein, auf diesem Branch.

## Es gibt immer Arbeit

Ein Lauf endet **nie** mit „nichts zu tun". Die Reihenfolge:

1. die vorrangigen Aufgaben oben, falls welche dastehen;
2. Zeilen mit Status `?` im Inventar;
3. `Journal/Blog/MartingaleProblem/Facts/BACKLOG.md`, von oben nach unten;
4. Task 23, siehe unten.

Kommst Du bei einem Punkt nicht weiter, gehst Du zum nächsten und schreibst in
den Bericht, woran es lag. Ist der Rückstau leer, hänge selbst einen Punkt an —
etwas, das Dir beim Lesen als reif aufgefallen ist, mit derselben Begründung,
die auch ein Vorschlag am Ende eines Laufs tragen muss.

## Wenn das Inventar vollständig ist

Sind alle 29 Zeilen belegt, wechselst Du zu **Task 23** — dem Beweis der
Dualitätsidentität für eine rein atomare Uhr. Auftrag, Modell, Stand und
Sackgassen stehen in `Journal/Blog/MartingaleProblem/Task23/PROTOKOLL.md`, das
Orakel in `Task23/oracle.py`. Dieselben Regeln gelten; das Manuskript darf
dann angefasst werden, aber erst wenn ein Beweis vollständig und verifiziert
ist, und danach muss `python3 Journal/Blog/MartingaleProblem/check.py` `clean`
melden.
