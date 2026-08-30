Du arbeitest autonom und unbeaufsichtigt am **Formalisierungs-Inventar** des
Manuskripts `Journal/Blog/MartingaleProblem/MartingaleProblem.tex`. Du bist in
einem git-Worktree auf dem Branch `facts-inventory`. Zeitbudget: 120 Minuten.

## Vorrangige Aufgaben

Stehen hier Aufgaben, so haben sie Vorrang vor allem Übrigen, in der genannten
Reihenfolge. Ist eine erledigt, streicht der Lauf sie hier heraus und trägt das
Ergebnis an der genannten Stelle ein; sind alle erledigt, gilt wieder die
Reihenfolge weiter unten. Eine Aufgabe, die mehr als einen Lauf braucht, wird
nicht gestrichen, sondern um einen Zwischenstand ergänzt.

### Aufgabe 1: den bp-Abschluss loswerden *(gestellt 2026-08-30, vom Nutzer bewilligt)*

Anders als Aufgabe 2 ist diese **auszuführen**, nicht nur vorzubereiten — der
Nutzer hat der Empfehlung zugestimmt.

Der bp-Abschluss taucht bei \EK{} nur an einer Stelle auf: in Theorem 4.3.8
dient er dazu, die Identität
$E[f(Y(t))]=E[f(X(0))]+E[\int_0^{\tau\wedge t} g(X(s))\dif s]$ von $A$ auf
den Abschluss auszudehnen, damit man $(\chi_E,0)$ einsetzen kann; die
Indikatorfunktion ist unstetig und liegt nicht in $A$. **Proposition 4.3.9
vermeidet ihn**: dort genügt eine einzelne Folge $(f_n,g_n)\subset A$ mit
bp-$\lim f_n=\chi_E$, $\inf_n\inf_x g_n>-\infty$ und $g_n\to0$ punktweise,
und der Beweis ist Einsetzen plus Fatou. Proposition 4.3.10 erledigt damit auch
$E=\bigcap_k E_k$. Der Unterschied ist der zwischen bp-*Konvergenz* einer Folge
(kostet nichts) und dem bp-*Abschluss* (transfinite Rekursion über die
abzählbaren Ordinalzahlen).

Zu tun:

1. Prüfe, ob \EK{} Proposition 4.3.1 — gleiche bp-Abschlüsse, gleiche Lösungen
   — im Manuskript irgendwo **trägt**. Zitiert wird sie in `cor:bpclosure`;
   entscheidend ist, ob ein Beweis sie benutzt. Der Scan liegt unter
   `~/Code/lean/journal/references/EthierKurtz1986.pdf` (Bildscan ohne
   Textebene, Buchseite = PDF-Seite − 10; §4.3 endet auf Buchseite 182).
2. **Trägt sie nicht:** streiche den bp-Block aus `MartingaleProblems`
   Meilenstein 2 — `BpTendsto`, `bpClosure`, `Submodule.bpClosure`,
   `isMPSolutionFor_bpClosure` — und setze an seine Stelle die Fatou-Form von
   Prop. 4.3.9 samt der Variante 4.3.10 für abzählbare Schnitte. `lem:closure`
   (`IsMPSolutionFor.insert_of_tendsto`) bleibt und ist die tragende Aussage.
   Setze `fact:bp` im Inventar auf einen Status, der festhält, dass er nicht
   mehr gebraucht wird, mit Begründung und Datum — nicht löschen.
3. **Trägt sie doch:** nenne die Stelle, lass den Block stehen und schärfe ihn
   auf das, was wirklich gebraucht wird (nach `fact:bp` nur, dass der
   bp-Abschluss eines Unterraums ein Unterraum ist).

Das Manuskript wird dabei nicht geändert; `cor:bpclosure` darf als bequeme
Formulierung stehen bleiben. Halte das Ergebnis im Inventar unter „Läufe" fest.

### Aufgabe 2: Trägt die Präordnung außerhalb von §6? *(gestellt 2026-08-30)*

Die Uhr definiert ihr Intervall als Differenz von Abwärtsmengen,
`Set.Iio t \ Set.Iio s`, und nicht als Mathlibs `Set.Ico s t`. Auf einer
linearen Ordnung fallen beide zusammen; auf einer echten Halbordnung nicht — am
Diamanten $0 < a,b < t$ mit $a,b$ unvergleichbar ist `Set.Ico a t = {a}`, aber
`Set.Iio t \ Set.Iio a = {a,b}`. Die Differenzform wird gewählt, weil die
Additivität der Intervalle nur `Set.Iio_subset_Iio` braucht, also `[Preorder]`,
während dieselbe Aussage für `Set.Ico` Vergleichbarkeit verlangt.

Zu klären ist, **was diese Allgemeinheit trägt**. Gehe die Aussagen des
Manuskripts durch, die mit \eqref{T0}, \eqref{T1} oder \eqref{T2b}
annotiert sind und *nicht* mit \eqref{T2a}; die Bündeltabelle in §2
(„Which result needs which bundle") ist die Ausgangsliste, aber prüfe sie, statt
ihr zu glauben. Für jede solche Aussage:

1. Kommt die Uhr überhaupt vor? Ohne Uhr stellt sich die Frage nicht.
2. Wenn ja: benutzt der Beweis das Intervall so, dass er unter `Set.Ico`
   bräche? Die Additivität ist der Prüfstein, nicht das Vorkommen des Symbols.
3. Wird die Aussage irgendwo im Manuskript auf einem **wirklich nicht
   linearen** Index instanziiert? Nenne die Stelle oder halte fest, dass es
   keine gibt.

Ergebnis ist eine Tabelle in `Facts/PRAEORDNUNG.md` (neu) mit einer Zeile je
Aussage, und daraus eine Empfehlung, die zwei Möglichkeiten gegeneinander stellt:
die Differenzform als Primitiv behalten, oder die Uhr auf `[LinearOrder ι]`
festlegen und direkt `Set.Ico` nehmen, wobei §6 seine Halbordnungs-Zeile
verlöre. Nenne bei jeder Möglichkeit, was sie kostet und was sie einspart.

**Zweiter Teil: wie weit reicht (T3').** \eqref{T3p} ist nach `thm:T3sharp`(a)
gleichwertig zu „abgeschlossene Teilmenge von $\R$", und die Additivität längs
der Ordnung ist klassisch die **Menger-Zwischenrelation** (K. Menger,
*Untersuchungen über allgemeine Metrik*, Math. Ann. 100 (1928), 75–163): das
Ordnungsintervall stimmt mit dem metrischen Intervall
$[a,b]=\{x: d(a,x)+d(x,b)=d(a,b)\}$ überein. Nicht zu verwechseln mit
Menger-*Konvexität*, die $h\Z$ verletzt. Von 15 Vorkommen von \eqref{T3p}
liegen 14 in §Skorokhod. Trenne **drei** Dinge und bestimme für jedes die
schwächste Indexhypothese:

1. das **Prädikat** càdlàg. `RemyDegenne/brownian-motion` definiert `IsCadlag`
   unter `[Preorder ι] [TopologicalSpace ι]`; verlangt `SkorokhodSpace`
   Meilenstein 2 irgendwo mehr, als das Prädikat braucht?
2. die **Sprungtheorie** — Abzählbarkeit von `leftJumpSet`, Diskretheit von
   `largeLeftJumpSet`, `IsCadlag.measurable`, Bestimmtheit durch eine dichte
   Menge. Nenne genau, was hier mehr nötig wird: Linearität,
   Zweitabzählbarkeit oder die Metrik.
3. den **Raum** $D(\T,E)$ mit $J_1$. Hier greift `thm:T3sharp`(b): ohne
   Additivität ist $d$ keine Metrik.

**Die Gegenprobe: stetige Pfade.** Mathlibs `Probability/Process/Kolmogorov.lean`
führt `IsKolmogorovProcess` über `[PseudoEMetricSpace T]` — der Index braucht
dort keine Ordnung und erst recht keine Teilmenge von $\R$; die
Kettenkonstruktion in `RemyDegenne/brownian-motion`, `Continuity/`, verlangt
zusätzlich eine Schranke an Überdeckungszahlen. Das Manuskript hat dazu
**nichts**: `\CE` kommt zehnmal vor, durchweg als abgeschlossener Teilraum in
§Skorokhod, und einen Stetigkeitssatz analog zu `thm:absreg` gibt es nicht.
Halte fest, was ein solcher Satz an Hypothesen bräuchte, wo er im Manuskript
stünde, und ob er als Meilenstein in `SkorokhodSpace` oder in
`MartingaleProblems` gehört. Belege dabei, dass Kolmogorov--Chentsov ein
**Momentenkriterium** ist und kein Martingalargument — der Mechanismus ist ein
anderer als bei der càdlàg-Modifikation, und das ist der Grund, warum er
allgemeinere Indexräume verträgt.

**Dritter Teil: Typklasse oder Teilmenge.** Ist (T3') dasselbe wie
„abgeschlossene Teilmenge von $\R$", so ist `AdditiveDist` im Prinzip
verzichtbar. Wäge das in Lean-Kosten ab, nicht in Mathematik: das Experiment des
Nutzers in `scratch/AdditiveDistTest.lean` (im Hauptcheckout
`~/Code/lean/journal`) hat gemessen, dass der Gitterfall $h\Z$ als Teiltyp
weder `OrderTopology` noch die Subtyp-Instanz durch die `SetLike`-Hülle bekommt.
Nenne für beide Wege, was sie an Instanzen kosten.

**Die Entscheidung trifft der Nutzer, nicht der Lauf.** Ändere weder die Uhr
noch die Roadmaps noch das Manuskript in dieser Sache; die Aufgabe endet mit der
Tabelle und der Empfehlung in `Facts/PRAEORDNUNG.md`.

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

## Wenn das Inventar vollständig ist

Sind alle 29 Zeilen belegt, wechselst Du zu **Task 23** — dem Beweis der
Dualitätsidentität für eine rein atomare Uhr. Auftrag, Modell, Stand und
Sackgassen stehen in `Journal/Blog/MartingaleProblem/Task23/PROTOKOLL.md`, das
Orakel in `Task23/oracle.py`. Dieselben Regeln gelten; das Manuskript darf
dann angefasst werden, aber erst wenn ein Beweis vollständig und verifiziert
ist, und danach muss `python3 Journal/Blog/MartingaleProblem/check.py` `clean`
melden.
