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

### ~~Aufgabe: die mengen-indizierte Literatur, und die Summierbarkeit~~ *(gestellt 2026-09-01, erledigt 2026-09-02, siebzehnter Task-23-Lauf)*

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

**Zwischenstand 2026-09-02 (sechzehnter Task-23-Lauf).** Teil (b) ist
beantwortet, und zwar negativ: **die Frage (S) ist falsch.** Die
hierarchische Motor-Uhr (`Task23/interference.py`: Block $i$ = schweres Atom
$\lambda_i$ über einem $k$-Präfix der Masse $\lambda_i$, $\lambda_{i+1}=
\lambda_i/4$, summierbar, intervallendlich, Typ $\omega^*$) hält $v_J$ von
$0$ weg — exakt zertifiziert (`interference_certificate.py`: $v_8\ge0.144$
bei $E_8=1.6\cdot10^{-5}$). Die Skalen **teilen** sich die fehlende Masse
(Antwort auf den Interferenztest); die Massenbilanz-Heuristik und die
Kontraktions-Deutung sind Sackgassen (vierzehnter Nachtrag). Auch die
separable Residuengestalt (`interference_separable.py`, Punkt 3 des
dreizehnten Laufs erstmals als LP) kollabiert nicht: $v_i^{\rm sep}=
\tfrac1{24}+E_i\downarrow\tfrac1{24}$, exakt auf den Stufen 3–10. Da die Uhr
intervallendlich ist, **gilt** auf ihr die Dualität (Satz des vierzehnten
Laufs) — die LP-Relaxation ist also als Beweisvehikel für aufsteigende
Strukturen bewiesen zu schwach, und ein Kompaktheitsargument aus den
Messwerten kollidiert scheinbar mit dem Satz. Die Adjudikation dieser
Kollision (erzwingt das unendliche $h$-System 1–3 auf $\omega^*$ die
Diagonale? Hauptverdächtiger: die Äquivalenz des zwölften Laufs ankert am
Bodenatom, das $\omega^*$ nicht hat) ist die präzise Aufgabe des nächsten
Laufs; sie steht in `Task23/PROTOKOLL.md`, sechzehnter Lauf, „Was als
Nächstes zu klären ist".

**Abschluss 2026-09-02 (siebzehnter Task-23-Lauf).** Die Adjudikation ist
entschieden, durch Beweis: **das exakte $h$-System 1–3 ist auf jeder
intervallendlichen Kette starr** — $\widehat w(s,t):=H(s,t)+\Delta(t)-\Delta(s)$
erfüllt exakt die Relation $(\ast)$ des vierzehnten Laufs (das $h$- und das
$\Phi$-System sind im antisymmetrischen Sektor isomorph), die
Zwei-Diagonalen-Induktion und zwei Schwanzlimiten geben $\Delta\equiv0$;
Bedingung 3 ersetzt das Bodenatom, der Verdacht gegen die Äquivalenz des
zwölften Laufs war unbegründet (ihre Rückrichtung braucht allerdings
$\kappa(a,0)=-h(a,a)$ statt $0$). Der Fehler lag im Kompaktheitsargument,
und zwar allein in der extrapolierten Prämisse $\lim v_i=\tfrac1{24}$:
tatsächlich gilt $v_i\le 2B\,M_{<u_l}+(K_l+2B)E_i$ mit stufenunabhängigem
$K_l$ (Fensterschranke), also $v_i\to0$ — nur sind die $K_l$ Produkte von
Massenverhältnissen ($\ge10^4$ schon auf Stufe 9, roh $\lesssim10^{48}$),
das Plateau ist praeasymptotisch und hält numerisch bis Stufe 14
(`Task23/adjudicate.py`, mit mechanischer Verifikation der Beweisalgebra am
Optimum, Proben (a) und (d)). **„(S) ist falsch" ist damit zurückgenommen**:
für intervallendliche Uhren mit stabilisierenden Fenstern ist (S) wahr, die
Summierbarkeit trägt genau die Schwanzlimiten — das ist die im
Aufgabenteil (b) vermutete ausschließende Rolle der endlichen Variation.
Offen bleibt (S) nur noch für ordnungsdichte Atommengen, zusammen mit dem
ordnungsdichten Kern selbst; einziger benannter Weg: die Schwanzrelationen
über Häufungspunkte (vierzehnter Lauf), jetzt mit dem
$\widehat w$-Isomorphismus als Werkzeug. Alles in `Task23/PROTOKOLL.md`,
siebzehnter Lauf.


### ~~Aufgabe: Meilenstein 1 von `WeakConvergence` ruht auf einem falschen Befund~~ *(gestellt 2026-09-05, erledigt 2026-09-05, vierter Lauf des Tages)*

**Ergebnis** in `Facts/INVENTAR.md`, Läufe, „2026-09-05, vierter Lauf des
Tages". Kurz: Punkt 1 der Aufgabe trägt nur zur Hälfte — der Satz ist da, aber
die Straffheit ist **nicht** geschenkt. Der Weg über
`isTightMeasureSet_of_isCompact_closure` ist zirkulär (die Konvergenz ist die
Behauptung), und die straffheitsfreie Fassung unter bloßer Punktetrennung ist
falsch, mit `E = ℝ`, $A=\{f\in C_b: \lim_{x\to\infty}f(x)=f(0)\}$ und
$\mu_n=\delta_n$. Das Manuskript verlangt an dieser Stelle **starke** Trennung,
und genau der Schritt von starker Trennung zur Straffheit ist der einzige, der
noch fehlt; er steht als `isTightMeasureSet_of_stronglySeparatesPoints` in
Meilenstein 1. Punkt 2 fand eine Folgestelle
(`MartingaleProblems` M11, `isRelativelyCompact_of_approx`), berichtigt. Punkt 3
erledigt. `fact:convdet` war überdies ein leeres Zitat und hat jetzt zwei eigene
Punkte in M1. Die Lehre steht als Abschnitt „Regel für den Negativbefund" im
Inventar. `Suggested.lean` ist erstmals mit `lake env lean` typgeprüft.

**Der Befund.** Seit dem 2026-08-29 steht in `WeakConvergence` Meilenstein 1,
Mathlib beweise nur die *separierende* Hälfte des Stone--Weierstraß-Schritts und
die *konvergenzbestimmende* fehle. Das stimmt nicht. Mathlib hat sie, unter
ihrem mathematischen Namen statt unter unserem:

`MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
(`MeasureTheory/Measure/LevyConvergence.lean:153`) — ist $A$ eine
`StarSubalgebra` von `E →ᵇ 𝕜`, die Punkte trennt, ist `E` polnisch, ist
`{μ n}` straff im Sinne von `IsTightMeasureSet`, und konvergieren die Integrale
über $A$, so gilt `Tendsto μ 𝓕 (𝓝 μ₀)`. Der Beweis ist genau der, den unser
Meilenstein als zu leisten beschreibt: Prohorov liefert einen Häufungspunkt,
`ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`
identifiziert ihn, Ultrafilter schließen ab.

**Zu tun.**

1. Meilenstein 1 auf diesen Satz umstellen: was dort als zu bauen steht, ist
   gebaut. Was bleibt, ist die Fassung **ohne** Straffheitshypothese — und die
   ist vermutlich geschenkt, denn eine konvergente Folge samt Limes ist kompakt,
   und `MeasureTheory.isTightMeasureSet_of_isCompact_closure`
   (`Measure/Prokhorov.lean:634`, unter `[CompleteSpace]` und
   Zweitabzählbarkeit) macht daraus Straffheit. Prüfe das, und wenn es trägt,
   formuliere den straffheitsfreien Satz als den eigentlichen Meilensteinpunkt
   und leite ihn ab.
2. Prüfe **alle** Punkte, die auf dem falschen Befund aufbauen — in
   `WeakConvergence` Meilenstein 1 und in jedem Punkt anderer Roadmaps, der
   „die konvergenzbestimmende Hälfte fehlt" als Begründung führt.
3. Trage im Inventar bei `fact:stoneweierstrass` und `fact:convdet` den
   berichtigten Beleg ein, mit Datum und mit dem alten Befund als
   durchgestrichener Notiz — nicht löschen, damit die Fehlerquelle sichtbar
   bleibt.

**Und die Lehre, die in die Suchregel gehört.** Das ist der vierte Fehler
dieser Art. Alle vier hatten dieselbe Ursache: gesucht wurde nach dem *Begriff*,
den unser Text benutzt, statt nach der *Aussage*. Es gibt in Mathlib kein
Prädikat „konvergenzbestimmend", also schien der Satz zu fehlen — er steht unter
`SeparatesPoints` und `IsTightMeasureSet`. Wer künftig „Mathlib hat das nicht"
schreiben will, formuliert die Aussage vorher **ohne unsere Vokabeln**, in
Mathlibs eigenen Begriffen, und sucht danach; und wer sie dann noch immer nicht
findet, sagt im Bericht, mit welchen Formulierungen er gesucht hat.

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
   **nach der Aussage, nicht nach unserer Vokabel**: Mathlib nennt Dinge oft anders, als das Manuskript sie nennt.
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

## Wie geschrieben wird, damit ein Abbruch nichts kaputt macht

Ein Lauf kann jederzeit abgeschnitten werden — von der Nutzungsgrenze, vom
Zeitlimit. Zwei Vorkehrungen, beide aus echten Ausfällen gelernt:

1. **Schreibe in Dateien, nicht in lange Antworten.** Am 2026-09-03 starb ein
   Lauf an `Claude's response exceeded the 64000 output token maximum` und
   hinterließ nichts. Halte einzelne Antworten kurz und lege Ergebnisse
   fortlaufend in `Task23/PROTOKOLL.md`, `Facts/INVENTAR.md` oder eigenen
   Dateien ab, sobald sie feststehen. Eine Abschlusszusammenfassung am Ende ist
   ein Absatz, kein Bericht — der Bericht steht in den Dateien.

2. **Hinterlasse nichts, was auf Ungeschriebenes verweist.** Derselbe Ausfall
   hinterließ ein Prüfskript, das sich auf einen „Beweis des zwanzigsten Laufs"
   berief, den es nicht gab, und das wegen einer toten Platzhalterzeile nicht
   einmal startete. Die Reihenfolge ist daher: erst der Protokolleintrag mit
   dem Ergebnis, dann das Skript, das darauf zeigt. Ein Skript muss allein
   lauffähig sein; ein Zwischenstand, der abbricht, soll lieber weniger
   dastehen lassen als etwas Widersprüchliches.

## Lean übersetzen — das geht, entgegen dem, was frühere Läufe notiert haben

Mehrere Läufe haben Rückstaupunkte mit „wartet auf `.lake`" liegen lassen. Der
Worktree hat wirklich kein `.lake`, aber das ist keine Blockade: der
Hauptcheckout hat ein **fertig gebautes Mathlib** (v4.33.1), und

```
lake env lean <absoluter Pfad zur Datei>
```

typprüft **jede** Datei dagegen — auch eine im Worktree. Es schreibt nichts,
weder in den Worktree noch in den Hauptcheckout, und braucht keinen Build. Am
2026-09-05 geprüft; ein Durchlauf über
`TauCeti/WeakConvergence/Suggested.lean` meldete echte Fehler (fehlende
`TopologicalSpace (ProbabilityMeasure E)`-Instanz, fehlender Import für die
`→ᵇ`-Notation, eine Universenbedingung).

Der Hauptcheckout `~/Code/lean/journal` ist dafür über `--add-dir` erreichbar
und `lake`, `lean`, `elan` sind freigegeben. **Dort wird nur gelesen und
übersetzt, niemals geschrieben** — er steht auf `master`, und eine Änderung dort
landet außerhalb Deines Branches. Geht `lake env lean` in Deinem Lauf trotzdem
nicht, so prüfe das mit `lean --version` als erstes, halte es im Bericht fest
und arbeite mit Signaturprüfung am Quelltext weiter, statt Übersetztes zu
behaupten.

Damit gilt: **wer Lean schreibt, übersetzt es auch.** Eine Deklaration, die
nicht durch `lake env lean` geht, ist kein Ergebnis, sondern ein Entwurf, und
gehört als solcher gekennzeichnet. `sorry` ist erlaubt, wo die Aussage die
Arbeit ist; ein Fehler in der *Aussage* ist es nicht. Der erste Durchlauf einer
großen Datei dauert einige Minuten, weil Mathlib geladen wird — das ist normal
und im Zeitbudget vorgesehen.

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
