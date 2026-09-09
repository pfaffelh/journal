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

**`lake env lean` immer mit dem `cd` im selben Befehl aufrufen**, also
`cd ~/Code/lean/journal && lake env lean <absoluter Pfad>`. Das
Arbeitsverzeichnis der Shell bleibt zwischen Werkzeugaufrufen stehen; wer den
`cd` einmal wegläßt, ruft `lake` im Worktree auf, und `lake` fängt dann an, sich
ein eigenes Mathlib zu klonen. Am 2026-09-06 ist genau das passiert und hat
`/home/pfaffelh/Code/lean/journal-facts/.lake` angelegt — 671 MB
halbfertiger Paketklone, die der Lauf nicht wieder löschen durfte (die
Sandbox verbietet `rm` dort). **Am 2026-09-08, zwölfter Lauf, ist es ein
zweites Mal passiert**, diesmal aus dem Mathlib-Verzeichnis heraus (ein `cd` in
einem vorangegangenen `grep` blieb stehen): `lake` hat acht Pakete nach
`~/Code/lean/journal/.lake/packages/mathlib/.lake/packages/` geklont, 57 MB, und
die Sandbox verbietet das `rm` auch dort. Die Lehre ist dieselbe und schärfer:
**jeder Werkzeugaufruf beginnt mit seinem eigenen `cd`**, auch der harmlose
`grep`, denn das Arbeitsverzeichnis des vorigen ist noch da. Und die zweite Hälfte derselben
Lehre, im selben Lauf teuer gelernt: **in Skripten stehen absolute Pfade**. Ein
`python3`-Einzeiler mit dem relativen Pfad `Journal/Blog/…/INVENTAR.md` lief
nach einem `cd ~/Code/lean/journal` gegen die **Inventardatei des
Hauptcheckouts** statt gegen die des Worktrees — hier folgenlos, weil das Skript
nichts zu ersetzen fand und die Datei byteweise gleich zurückschrieb
(`git status` im Hauptcheckout blieb leer), aber der nächste Fall dieser Art
schreibt außerhalb des Branches. Die beiden Inventare haben verschiedene Längen;
das ist die billigste Probe, ob man die richtige Datei vor sich hat. **Der Ordner ist unbrauchbar und gehört
gelöscht**; solange er dasteht, ist die Notiz „der Worktree hat kein `.lake`"
im Auftrag irreführend, aber weiterhin praktisch richtig: dieses `.lake` hat
kein gebautes Mathlib und taugt zu nichts.

**Die Axiomprobe gehört nach `scratch/`.** Der billigste Weg, eine ganze Datei zu
prüfen, ist eine Kopie mit `#print axioms` je Deklaration; `lake env lean` läuft
darüber wie über das Original. Sie darf aber **nicht** in die Wurzel des
Worktrees: die Sandbox verweigert `rm` auch dort, wo sie das Schreiben erlaubt,
und der Lauf bleibt auf seiner Kopie sitzen. Am 2026-09-08, einundzwanzigster
Lauf, passiert; `axcheck_tmp.lean` steht seither eingedampft und in `.gitignore`.
`scratch/` ist ohnehin ignoriert und ist der Ort.

## Offen

1. ~~**`IsSeparating` samt `IsSeparating.ae_eq_of_forall_condExp_eq`**~~
   *(erledigt 2026-09-06, erster Lauf des Tages.)* Der Beweis steht in
   `TauCeti/WeakConvergence/Suggested.lean` und geht durch `lake env lean`
   gegen `v4.33.1`, ohne Fehler und ohne Warnung; die Datei hat an dieser
   Stelle kein `sorry` mehr. Er ist der Zweischritt, den die Roadmap
   beschreibt, mit der Fallunterscheidung nach `P G` — im Nullfall
   verschwindet die Restriktion selbst (`Measure.restrict_eq_zero`), was
   kürzer ist als die „beide Seiten $\le P(G)$" des Nachtrags vom
   2026-09-05.

   **Zwei Befunde, beide an der Aussage und nicht am Beweis.**

   * Die Aussage brauchte `[OpensMeasurableSpace E]`, das ihr fehlte. Ohne
     es ist kein $f\in\Gamma$ meßbar, also sind alle Integrale $0$ und der
     Satz unbeweisbar. Es ist die Hypothese von
     `Continuous.stronglyMeasurable`
     (`MeasureTheory/Function/StronglyMeasurable/Basic.lean:718`; die
     zweitabzählbare Seite von `SecondCountableTopologyEither` ist `ℝ`) und
     von `BoundedContinuousFunction.integrable`
     (`MeasureTheory/Integral/BoundedContinuousFunction.lean:99`).
   * **Die Reihenfolge der beiden σ-Algebren war falsch, und das ist keine
     Kosmetik.** Die Aussage stand auf `{mΩ : MeasurableSpace Ω}
     {m : MeasurableSpace Ω}`. Beide sind lokale Instanzen von
     `MeasurableSpace Ω`, und die Instanzsuche nimmt die **letzte** — also
     las das unannotierte `Measurable U` in Wahrheit `Measurable[m] U`, die
     echt stärkere und falsche Hypothese, unter der der Satz viel weniger
     sagt. Sichtbar wurde es erst beim Übersetzen, an einem
     `m ≤ m`-Typfehler. Mathlib schreibt aus genau diesem Grund durchweg
     `{m m0 : MeasurableSpace α}`, die umgebende σ-Algebra zuletzt; die
     Aussage tut es jetzt auch. Das ist eine Fehlerquelle für jede Aussage
     mit zwei σ-Algebren, und `MartingaleProblems` führt mehrere.

   Im selben Lauf mit erledigt, als billigster Nachbar:
   `StronglySeparatesPoints.separatesPoints` — sechs Zeilen, `δ := dist y x`,
   und `[MeasurableSpace E]` unter `omit`, weil der Beweis es nicht benutzt.
   Damit tragen sieben Deklarationen von Meilenstein 1 Beweise. Offen bleibt
   dort `IsSeparating.of_subalgebra`; der Weg steht im Laufbericht.

   Mitgefunden: `measure_inter_add_diff` ist seit dem 2026-06-03
   `deprecated` (jetzt `measure_inter_add_sdiff`,
   `Measure/MeasureSpace.lean:118`), ebenso `Set.diff_eq` (jetzt
   `Set.sdiff_eq`).

1. **`SkorokhodSpace` und `MartingaleProblems` weiter beweisen.** *(Stand
   2026-09-07, vom Nutzer nachgezogen; die frühere Fassung dieses Punktes war
   in ihrer Begründung falsch — beide Dateien übersetzten schon, als er
   gestellt wurde, und die Zahlen darin sind längst überholt.)*

   Alle drei Dateien gehen fehlerfrei durch `lake env lean` gegen v4.33.1, und
   **kein `sorry` steht mehr in einer Aussage**, nur noch in Beweisen. Stand:

   | | Deklarationen | `sorry` |
   |---|---|---|
   | `WeakConvergence` | 50 | 21 |
   | `SkorokhodSpace` | 102 | 12 |
   | `MartingaleProblems` | 50 | 9 |

   Arbeite die verbleibenden `sorry` ab, von oben je Datei, und nimm dabei
   `MartingaleProblems` mit. Was sich nicht billig beweisen läßt, laß
   stehen und sag im Bericht, woran es hängt; ein `sorry` mit benannter Ursache
   ist mehr wert als einer ohne.

   *Zwischenstand 2026-09-07, sechster Lauf des Tages:
   `MartingaleProblems` ist von elf auf zehn `sorry` und von 38 auf 50
   Deklarationen; die Zahlen der Tabelle sind die gemessenen. Bewiesen sind
   `Clock.interval_union`, die Additivität von Meilenstein 1, und
   `not_isQuasiLeftContinuous_of_not_ae_tendsto`, die Umkehrung von
   `IsQuasiLeftContinuous.ae_eq_leftLim`; dazu steht der Namensraum
   `AtomWitness` mit elf bewiesenen Deklarationen — die faire Münze, die Uhr
   `atomClock u` mit ihrem Atom, der Pfad, der bei `u` umspringt, seine
   càdlàg-Eigenschaft und das Scheitern der Quasi-Linksstetigkeit. Der nächste
   Schritt in dieser Datei ist die Filtration samt der Martingaleigenschaft, die
   `not_isQuasiLeftContinuous_of_atom` schließt; die Rechnung steht im
   Laufbericht im Inventar. Mitgefunden und dort ebenfalls notiert: die Aussage
   von `not_isQuasiLeftContinuous_of_atom` war leer und ist berichtigt.*

   *Zwischenstand 2026-09-07, siebter Lauf des Tages:
   `not_isQuasiLeftContinuous_of_atom` **ist bewiesen**, die Datei steht bei
   neun `sorry` (rc = 0, keine Warnung). Zehn neue Deklarationen schließen den
   Zeugen ab — `integrable_bool`, `integral_coinMeasure`, `coinPair`,
   `coinClass`, `isSeparating_coinClass`, `atomClock_real_of_mem` und
   `atomClock_real_of_notMem`, `integral_coinPair_snd`, `coinFiltration`,
   `isMPSolution_coinProcess` —, alle bewiesen. Die Zahl der Deklarationen
   steigt von 48 auf 58, gezählt mit
   `grep -cE "^(noncomputable |private |protected )*(theorem|lemma|def|structure|inductive|instance|abbrev) "`;
   die 50 der Tabelle stammt aus einer anderen Zählung desselben Standes, die
   Sorry-Zahlen sind die des Übersetzers. Der erste verbleibende `sorry` der
   Datei ist `isMPSolution_iff_forall_fdd` (Meilenstein 3).*

   *Zwischenstand 2026-09-07, achter Lauf des Tages: `SkorokhodSpace` steht bei
   **elf** `sorry` — `IsCadlag.measurable` ist bewiesen, und die Roadmap
   verlangte dafür ein Bündel, das der Beweis nicht braucht (Befund im
   Inventar). `MartingaleProblems` bleibt bei neun und gewinnt
   `not_isAtomless_atomClock`. **Für `SkorokhodSpace` ist dieser Punkt damit
   ausgereizt**: von den elf verbleibenden `sorry` hängen zehn an der
   parameterlosen `MetricSpace`-Instanz — dort ist der nächste Schritt eine
   Signaturänderung an zehn Deklarationen und kein Beweis —, und der elfte,
   `exists_orderIso_isometry_real`, ist ein eigener Satz. Wer diesen Punkt
   weiterträgt, nimmt `MartingaleProblems` und `WeakConvergence`.*

   *Zwischenstand 2026-09-07, zehnter Lauf des Tages: `MartingaleProblems` steht
   bei **67 Deklarationen und 9 `sorry`** (vorher 58 und 9), rc = 0 und ohne
   jede Warnung außer `sorry`. Kein `sorry` ist gefallen, und das ist der
   Bericht: das vom neunten Lauf benannte Ziel
   `isMPSolution_iff_forall_fdd_continuous` ist in dieser Datei **nicht
   formulierbar** — die drei `Suggested.lean` importieren nur `Mathlib.*` und
   einander nicht, `induction_on_mulSystem` liegt also außerhalb des Kontexts.
   Wer die stetige Form will, entscheidet zuerst, wo sie stehen soll; die drei
   Möglichkeiten stehen im Laufbericht. Stattdessen ist die **Grundform
   berichtigt**: sie war in beiden Formen nicht beweisbar, weil `Martingale` die
   Adaptiertheit enthält und der Kompensator ohne gemeinsame Meßbarkeit von
   `(u,ω) ↦ X u ω` sein Ersatzwert `0` ist. Beide tragen jetzt
   `Clock.IsProgressive Q X 𝓕`, und sechs Deklarationen des Beweises sind
   gebaut: die drei Intervall-Lemmata der Uhr,
   `stronglyMeasurable_integral_comp`, `integrableOn_of_bounded` und die
   Inkrementidentität `mpFamily_sub_of_measurable_path`. Der nächste Schritt ist
   `forall_fdd_of_isMPSolution`, die Richtung von links nach rechts; die
   Rechnung steht im Laufbericht.*

   *Zwischenstand 2026-09-08, sechster Lauf des Tages: `WeakConvergence` steht
   bei **zwei** `sorry` (gemessen am Übersetzerlauf, dazu die zwei bekannten
   Fehler in `tendsto_map_of_measure_setOf_continuousAt_eq_one` aus dem
   Versionsgrund) — `exists_measurable_map_restrict_volume_eq_sum_smul_dirac`
   ist bewiesen, und `exists_coupling_tsum_offDiag_le` ist als neue, bewiesene
   Deklaration dazugekommen. Übrig sind `exists_ae_tendsto_of_tendsto`
   (Meilenstein 3) und `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`
   (Meilenstein 4). Der nächste Schritt in dieser Datei ist die einstufige
   Kopplung auf dem Produktraum, in drei benannten Stücken (b1)–(b3) im
   Laufbericht im Inventar; ihr Bauplan ist im selben Lauf berichtigt worden,
   weil er auf `((0,1], Lebesgue)` allein nicht durchgeht.*

   *Zwischenstand 2026-09-08, zwölfter Lauf des Tages: `WeakConvergence` steht bei
   **168 Deklarationen und drei `sorry`** (gemessen am Übersetzerlauf; dazu
   unverändert die zwei bekannten Fehler bei `:2125` aus dem Versionsgrund).
   Gefallen sind die vier `sorry` von Meilenstein 6 — `distInMeasure_triangle`,
   `distInMeasure_eq_zero_iff`, `tendsto_iff_tendstoInMeasure` und
   `exists_tendsto_distInMeasure_of_cauchy` —, dazu drei neue bewiesene
   Hilfssätze. Übrig sind `exists_ae_tendsto_of_tendsto` (Meilenstein 3),
   `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (Meilenstein 4) und
   `exists_countable_dense_distInMeasure` (Meilenstein 6, die Separabilität von
   $M_E$). Der nächste benannte Schritt in dieser Datei ist die letzte davon; die
   Begründung steht im Laufbericht im Inventar.*

   *Zwischenstand 2026-09-08, dreizehnter Lauf des Tages: **das benannte Ziel ist
   gefallen, und mit ihm Meilenstein 6 ganz.** `WeakConvergence` steht bei **176
   Deklarationen und zwei `sorry`** (vorher 168 und drei), rc = 1 mit unverändert
   genau den zwei angekündigten Fehlern bei `:2125`. Acht neue Deklarationen sind
   bewiesen: `exists_countable_dense_distInMeasure` samt `separableSpace`,
   `secondCountableTopology` und `polishSpace` — der Raum $M_E$ ist polnisch —,
   dazu `distInMeasure_mk_le_add`, `stepFun`, `stronglyMeasurable_stepFun`,
   `exists_mem_stepFun` und `stepClass`; alle mit `#print axioms` geprüft. Der
   Bauplan des Meilensteins war an einer Stelle nicht typrichtig (die
   approximierende Familie als Summen von Indikatoren, über einem `E` ohne
   Addition) und ist berichtigt; der Ersatz ist die Stufenfunktion über einer
   Liste von Indexpaaren, und sie erspart überdies die Disjunktifizierung der
   überdeckenden Mengen. Übrig sind `exists_ae_tendsto_of_tendsto`
   (Meilenstein 3) und `tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`
   (Meilenstein 4); der nächste benannte Schritt ist die erste davon, die
   Begründung steht im Laufbericht im Inventar. Mitgefunden und berichtigt, beim
   Durchsehen des zweiten: `IsUniformlyIntegrableLaws` war mit dem
   **Bochner**-Integral formuliert und dadurch **entartet** — der Ersatzwert `0`
   für einen nichtintegrierbaren Integranden machte das Kriterium von jeder
   Familie mit unendlichem ersten Moment erfüllbar, und der Satz darüber war
   falsch. Es steht jetzt mit dem unteren Integral, und
   `integrable_id_of_isUniformlyIntegrableLaws` ist bewiesen; damit **177
   Deklarationen** bei unverändert zwei `sorry`.*

   *Zwischenstand 2026-09-08, zwanzigster Lauf des Tages: in `SkorokhodSpace`
   sind **die vier Metrikaxiome der Integralmetrik von Meilenstein 4 bewiesen**,
   und `SkorokhodSpace.metricSpaceInt (t₀ : ι) : MetricSpace D(ι, E)` ist aus
   ihnen gebaut; neunzehn neue Deklarationen, alle mit `#print axioms` geprüft,
   rc = 0 und keine Warnung. Die Zahl der `sorry` bleibt bei **fünf**: keines
   der vier Axiome stand als `sorry` da, sie waren seit der Widerlegung der
   summierten Metrik (achtzehnter Lauf) gar nicht formuliert. Drei der Axiome
   sind die entsprechende Aussage über `distWith` bei festem Radius, integriert;
   das vierte, die Trennung, ist es **nicht** — ein Infimum gleich `0` nennt
   keinen Radius, sondern liefert eine Folge von Zeitwechseln, und der Beweis
   geht über die fast überall endliche Summe ihrer Integranden. Mitgefunden und
   eingespart: `measurable_distWith` und `integrableOn_intDist` brauchen von den
   fünf Meßbarkeitsannahmen, unter denen sie standen, nur
   `[SecondCountableTopology E]`; die vier Borel-Annahmen kamen nie in der
   Aussage vor und werden jetzt im Beweis eingeführt, weshalb die Metrik keine
   Maßtheorie in ihrer Signatur trägt. Wer diesen Punkt fortsetzt, hängt die
   Instanz um, und das ist eine Signaturarbeit und kein Satz: die beiden
   Widerlegungssätze des achtzehnten Laufs sind für die Topologie der *Instanz*
   formuliert und gelten für die summierte Metrik, nicht für die neue.*

   *Zwischenstand 2026-09-08, einundzwanzigster Lauf des Tages: **die Instanz ist
   umgehängt** — `SkorokhodSpace.instMetricSpace` ist `metricSpaceInt basePoint`,
   `dist_eq` liest `intDist basePoint`, beides `rfl` und beides frei von
   `sorryAx`. Der Preis ist `SkorokhodSpace.totalTopology`, die benannte Topologie
   der summierten Metrik: die beiden Widerlegungssätze nennen sie jetzt, statt
   ihre Topologie von der Instanz abzulesen, und sind neu bewiesen. Damit sind
   `CompleteSpace` und `SeparableSpace` wieder Verpflichtungen von Meilenstein 5
   (`PolishSpace` ist `inferInstance` und schuldet nichts), also **sieben `sorry`
   statt fünf** bei 188 Deklarationen — die Zahl steigt, weil die Datei wieder
   etwas verspricht, und nicht, weil etwas mißlungen wäre. Bezahlt ist im selben
   Lauf die einzige Sprosse, die der Metrikwechsel gekostet hat:
   `SkorokhodSpace.ae_summable_min_one_distWith`, summierbare Kosten in `intWith`
   ergeben an fast jedem Radius summierbare Fensterabstände. Offen ist die
   Montage `tendsto_of_partialComp`; sie ist die letzte Sprosse von
   `instCompleteSpace`. Zwei Handgriffe, die Zeit kosteten und beim nächsten Mal
   nicht mehr: `totalTopology` braucht `@[instance_reducible]`, sonst schließt
   der Beweis nicht, und `[SecondCountableTopology E]` gehört **auf die
   Instanz** und nicht in eine `variable`-Zeile, weil es sonst in den
   Meilensteinen 6 und 7 mit `[PolishSpace E]` überlappt, das es erweitert.*

   *Zwischenstand 2026-09-08, zweiundzwanzigster Lauf des Tages: `SkorokhodSpace`
   steht bei **193 Deklarationen und unverändert sieben `sorry`** (rc = 0, keine
   Warnung außer den sieben). Bewiesen ist die Montage, die der Vorlauf als
   letzte offene Sprosse von `CompleteSpace` benannt hatte:
   `SkorokhodSpace.tendsto_of_partialComp` liefert aus verankerten Zeitwechseln
   mit summierbaren Normen und summierbaren `intWith`-Kosten den Grenzpfad `z`,
   den einen Zeitwechsel `L` und die gleichmäßige Konvergenz von
   `x n ∘ ((partialComp l n)⁻¹ * L)` gegen `z` auf jedem Fenster; dazu
   `SkorokhodSpace.exists_gt_summable_distWith` (gute Radien sind unbeschränkt,
   weil die schlechten null sind und `Set.Ioi c` nicht),
   `summable_of_summable_min_one`, `SkorokhodSpace.dist_le_distWith` und
   `TimeChange.eq_of_gap_of_norm_lt`. Alle fünf mit `#print axioms` geprüft, alle
   nur auf `propext`, `Classical.choice`, `Quot.sound`. **Die Zahl der `sorry`
   bleibt, und das ist der Befund:** der Schritt von der lokal gleichmäßigen
   Konvergenz zurück zu `intDist` ist keine Folgerung aus der Montage, sondern
   ein eigener Satz — `distWith` schneidet die beiden Pfade getrennt ab und liest
   oberhalb von `exhaustionMax t₀ u` den Term `r (x n A) (z A)` an einem Punkt
   ab. Er steht jetzt als
   `SkorokhodSpace.tendsto_intDist_of_tendsto_of_partialComp` in
   `SkorokhodSpace/README.md`, Meilenstein 5, samt der Dichotomie, deren eine
   Hälfte `TimeChange.eq_of_gap_of_norm_lt` bezahlt; der Meilenstein zählt
   seither sieben benannte Sprossen statt sechs, davon sechs bewiesen. Wer diesen
   Punkt fortsetzt, nimmt ihn.*

   *Zwischenstand 2026-09-08, siebter Lauf des Tages: `WeakConvergence` steht
   weiterhin bei **zwei** `sorry` und denselben zwei bekannten Fehlern, aber die
   einstufige Kopplung ist bewiesen — `exists_coupling_of_partition` und
   `exists_coupling_of_tendsto`, dazu `condLaw` mit vier Hilfssätzen. Der
   Bauplan (b1)–(b3) des Vorlaufs hat sich dabei auf (b1) und (b3) verkürzt:
   (b2), der Produktraum, ist entfallen, weil der gemeinsame Raum `E × E` ist
   und nicht `((0,1], Lebesgue) × Measure.pi`. Der nächste Schritt in dieser
   Datei ist `exists_ae_tendsto_of_tendsto` selbst, in drei benannten Stücken
   (c1)–(c3) im Laufbericht im Inventar; (c2) — das Verkleben der Stufen zu
   **einem** Raum — ist der einzige, der eine Entscheidung verlangt, und die
   Frage daran ist, ob er `E` polnisch statt bloß separabel braucht.*

   *Nachtrag des sechsten Laufs zu `WeakConvergence`: gemessen sind es **48
   Deklarationen und 18 `sorry`**, nicht 50 und 21; und der Übersetzer meldet
   `rc = 1`, an genau einer Stelle und mit Absicht — der Modulkopf sagt seit dem
   2026-09-06, daß `tendsto_map_of_measure_setOf_continuousAt_eq_one` für
   `upstream/master` geschrieben ist, wo `ProbabilityMeasure.map` die Funktion
   nimmt und nicht wie in v4.33.1 einen `AEMeasurable`-Beweis. Wer diese Datei
   übersetzt, erwartet also **zwei** Fehler an dieser einen Aussage und keine
   sonst.*

   *Zweiter Zwischenstand desselben Laufs: in `SkorokhodSpace` ist die
   **Metrik von Meilenstein 4 gebaut und bewiesen** —
   `SkorokhodSpace.totalDist`, `summable_totalDist`, `totalDist_self`,
   `totalDist_comm`, `totalDist_triangle`, `eq_of_totalDist_eq_zero` und
   `SkorokhodSpace.metricSpace (t₀ : ι) : MetricSpace D(ι, E)`, sieben
   Deklarationen, alle bewiesen; rc = 0, keine Warnung. Die Zahl der `sorry`
   bleibt bei **zwölf**: der parameterlose `instance` darunter, gegen den zehn
   spätere Deklarationen elaborieren, hat keinen Basispunkt, und den kann keine
   Aussage über die Metrik ihm geben. Wer die zwölf weiter drücken will, fängt
   deshalb nicht bei einem Beweis an, sondern beim Umschreiben dieser zehn
   Deklarationen auf `SkorokhodSpace.metricSpace t₀` — das ist eine
   Signaturänderung und kein Satz.*

   *Zwischenstand 2026-09-07, dreizehnter Lauf des Tages: `WeakConvergence` steht
   bei **12 `sorry`** statt 13, und der gefallene ist der größte, der noch offen
   war — `isSeparating_pi`, trennende Klassen über einem beliebigen Indextyp, die
   Produkthälfte von `fact:fdd`. Mit ihm sind siebzehn Deklarationen neu und
   bewiesen; die tragende darunter ist
   `integral_indicator_mul_eq_of_isSeparating`, die eine trennende Klasse gegen
   ein **Gewicht** statt gegen ein zweites Maß anwendbar macht, ohne daß ein
   signiertes Maß im Beweis auftritt. Zwei Befunde stehen im Laufbericht: der vom
   zwölften Lauf vorgeschlagene Weg über `ext_of_forall_integral_eq_of_isMulSystem`
   trägt **nicht** (Produkte trennender Klassen sind kein multiplikatives System;
   Zeuge in der Roadmap), und die Aussage brauchte zwei Hypothesen, die sie nicht
   hatte — Beschränktheit und Meßbarkeit der Mitglieder. Die beiden Fehler bei
   `:804` sind unverändert die angekündigten. Wer diesen Punkt fortsetzt, hat in
   `WeakConvergence` als nächsten benannten Schritt `isConvergenceDetermining_pi`,
   und dessen erster Teil ist eine Straffheitsaussage über abzählbare Produkte,
   kein Satz über trennende Klassen.*

   *Zwischenstand 2026-09-07, vierzehnter Lauf des Tages:
   **`isConvergenceDetermining_pi` ist bewiesen**, samt der Straffheitsaussage,
   die der dreizehnte Lauf als ersten Schritt benannt hatte. Vier neue
   Deklarationen, alle bewiesen: `IsTightMeasureSet.pi` (Straffheit abzählbarer
   Produkte aus der Straffheit der Einkoordinatenränder — Mathlib hat nur den
   Zweifaktorfall `IsTightMeasureSet.prodMk`, `Measure/Tight.lean:144`),
   `isTightMeasureSet_of_tendsto`,
   `tendsto_of_isSeparating_of_isTightMeasureSet` (Prohorov samt Identifikation,
   für eine Klasse statt für eine `StarSubalgebra`) und der Satz selbst. Die Zahl
   der `sorry` bleibt bei **12**, weil der Lauf keinen gefällt, sondern einen
   Meilensteinpunkt gebaut hat, der noch keine Deklaration hatte; die Datei zählt
   81 Deklarationen, rc = 1 mit unverändert genau den zwei angekündigten Fehlern,
   deren Zeile jetzt `:1041` ist und nicht mehr `:804`. Der nächste benannte
   Schritt in dieser Datei ist
   `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support`
   (`fact:convdet`); die Begründung steht im Laufbericht im Inventar.*

   *Zwischenstand 2026-09-07, fünfzehnter Lauf des Tages: **dieser Schritt ist
   getan**. `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support`
   ist bewiesen, `WeakConvergence` steht bei **11 `sorry`** und 91
   Deklarationen (vorher 12 und 81), rc = 1 mit unverändert genau den zwei
   angekündigten Fehlern, jetzt bei `:1300`. Neun Deklarationen sind neu:
   `ballCutoff` mit sechs Lemmata, `lipschitzWith_mul_of_bounded` und
   `integrable_of_continuous_of_bounded`. Die Aussage hat dabei ihre
   Separabilitätshypothese **verloren** — EK und das Manuskript verlangen sie,
   der Beweis benutzt keine abzählbare dichte Menge; Auffälligkeit und
   Begründung im Inventar. Der nächste benannte Schritt in dieser Datei ist
   `isConvergenceDetermining_setOf_hasCompactSupport`, die zweite Hälfte
   desselben Facts, und was zwischen den beiden Klassen liegt, ist genau ein
   Abschneidelemma; der Laufbericht nennt es.*

   *Zwischenstand 2026-09-07, sechzehnter Lauf des Tages: **auch dieser Schritt
   ist getan**, und `fact:convdet` ist damit ganz bewiesen.
   `isConvergenceDetermining_setOf_hasCompactSupport` geht durch
   `lake env lean`; `WeakConvergence` steht bei **10 `sorry`** und 92
   Deklarationen (vorher 11 und 91), rc = 1 mit unverändert genau den zwei
   angekündigten Fehlern, jetzt bei `:1414`. Das angekündigte Abschneidelemma
   war **nicht** das, was der fünfzehnte Lauf vermutet hatte: eine gleichmäßige
   Approximation der größeren Klasse durch die kleinere gibt es nicht (Zeuge im
   Laufbericht). Was trägt, ist die Herauslösung des Abschneideschritts aus dem
   Beweis der ersten Hälfte —
   `tendsto_integral_of_tendsto_integral_mul`, ohne Metrik —, den beide Hälften
   jetzt teilen. Der nächste benannte Schritt in dieser Datei ist
   `isTightMeasureSet_of_stronglySeparatesPoints` — nach diesem Lauf der
   **einzige** `sorry` von Meilenstein 1, den nicht sein eigenes Korollar
   trägt, und das Ganze dessen, was `fact:stoneweierstrass` noch schuldet; die
   Begründung steht im Laufbericht. Derselbe Lauf hat den Beweis von EK 3.4.5(b)
   in vier benannte Schritte zerlegt (in `WeakConvergence/README.md`,
   Meilenstein 1) und den zweiten davon bewiesen,
   `StronglySeparatesPoints.exists_finite_cover`, den geometrischen Kern; damit
   93 Deklarationen bei unverändert 10 `sorry`. Als Nächstes ist Schritt (1)
   dran, die schwache Konvergenz der Pushforwards nach $\R^k$.*

   *Zwischenstand 2026-09-07, siebzehnter Lauf des Tages: **die Schritte (1)
   und (3) sind bewiesen, ebenso die tragende Hälfte von Schritt (4)**, und die
   Zielaussage war **falsch**. `WeakConvergence` steht bei **101 Deklarationen
   und 10 `sorry`** (vorher 93 und 10, unverändert — sechs neue Deklarationen
   sind bewiesen, keine neu als `sorry` liegengeblieben), rc = 1 mit
   unverändert genau den zwei angekündigten Fehlern. Neu und bewiesen:
   `coordMap`, `coordAlgebra`, `separatesPoints_coordAlgebra`,
   `exists_mem_subalgebra_comp_of_mem_coordAlgebra`,
   `tendsto_integral_comp_of_forall_tendsto_integral` (Schritt (1), über einem
   beliebigen `Fintype` statt über `Fin k` — das ist es, was Schritt (3) die
   Numerierung der Funktionen erspart), `le_liminf_measure_preimage_of_isOpen`,
   `le_liminf_measure_thickening_of_stronglySeparatesPoints` (Schritt (3)) und
   `isTightMeasureSet_of_forall_exists_isCompact_measure_compl_thickening_le`,
   das gelockerte Straffheitskriterium EK Thm. 3.2.2 — eine eigene
   Mathlib-Lücke, jetzt **geschlossen**, ohne Separabilität.
   `isTightMeasureSet_of_stronglySeparatesPoints` stand über einem beliebigen
   `NeBot`-Filter und ist so widerlegt (`𝓕 = pure 0` auf `ℕ`, `A = ⊤`,
   `μ n = δ n`); die fehlende Hypothese `Filter.cofinite ≤ 𝓕` steht jetzt in
   der Aussage. Der nächste benannte Schritt in dieser Datei ist
   `isTightMeasureSet_of_stronglySeparatesPoints` selbst **fertig zu
   beweisen** — nach diesem Lauf reine Buchhaltung über den drei bewiesenen
   Sätzen (Straffheit von `μ₀`, Schritt (3), das gelockerte Kriterium) und
   keine eigene Mathlib-Lücke mehr; die Begründung und der Beweisplan stehen
   im Laufbericht.*

   *Zwischenstand 2026-09-08, erster Lauf des Tages: **dieser Schritt ist
   getan, und `fact:stoneweierstrass` ist damit ganz bewiesen.**
   `isTightMeasureSet_of_stronglySeparatesPoints` und sein Korollar
   `isConvergenceDetermining_of_stronglySeparatesPoints` — der Fact in der Form
   des Manuskripts — gehen durch `lake env lean` und hängen laut
   `#print axioms` nur an `propext`, `Classical.choice`, `Quot.sound`.
   `WeakConvergence` steht bei **101 Deklarationen und 8 `sorry`** (vorher 101
   und 10), rc = 1 mit unverändert genau den zwei angekündigten Fehlern, jetzt
   bei `:1925`; **Meilenstein 1 trägt kein `sorry` mehr**, alle acht liegen in
   den Meilensteinen 2 und 3. Eine Hypothese hat sich geändert:
   `[PolishSpace E]` ist durch `[CompleteSpace E] [SecondCountableTopology E]`
   ersetzt — dieselbe Raumklasse, aber die Vollständigkeit an der gegebenen
   Metrik, in der `Metric.thickening` lebt; Zeuge und Begründung im
   Laufbericht.*

   *Fortsetzung desselben Laufs: **Meilenstein 2 und der erste Punkt von
   Meilenstein 3 sind dazugekommen.** `tendsto_of_measure_setOf_not_continuousAt_eq_zero`
   (`fact:cmt`, die f.ü.-stetige Abbildung) ist bewiesen — die Bildmaße treten
   als Daten mit ihren definierenden Gleichungen auf, wodurch **eine** Aussage
   gegen v4.33.1 und gegen `upstream/master` elaboriert; die verpackte Fassung
   `tendsto_map_of_measure_setOf_continuousAt_eq_one` behält ihr `sorry` allein
   aus dem Versionsgrund. Und `isTightMeasureSet_of_forall_exists_finite_iUnion_ball`
   (`fact:PSpolish`) ist das gelockerte Straffheitskriterium von Meilenstein 1
   in vier Zeilen. Stand danach: **102 Deklarationen, 7 `sorry`**, rc = 1 mit
   den zwei angekündigten Fehlern. Zwei Abschwächungen sind mitgefallen:
   `SecondCountableTopology` aus dem Ball-Kriterium, `MetricSpace` und
   `BorelSpace` aus dem gelockerten Kriterium (jetzt `[PseudoMetricSpace E]
   [CompleteSpace E]`). Der nächste benannte Schritt in dieser Datei ist
   `separableSpace_probabilityMeasure` (Meilenstein 3), und vor dem Beweis steht
   eine Suche auf `upstream/master`, ob Mathlib die Aussage schon hat;
   Begründung im Laufbericht.*

   *Zwischenstand 2026-09-08, zweiter Lauf des Tages: das benannte Ziel
   `separableSpace_probabilityMeasure` ist **nicht** gefallen, aber die beiden
   Schätzungen, auf denen es ruht, sind bewiesen und gehen durch
   `lake env lean`: `levyProkhorovEDist_sum_dirac_le` (die geometrische Hälfte —
   eine endliche meßbare Zerlegung mit Vertretern im `ε`-Abstand außerhalb einer
   Menge der Masse `ε` bringt `∑ i, μ (A i) • dirac (y i)` in
   Lévy--Prokhorov-Abstand `ε`), `levyProkhorovEDist_sum_dirac_weights_le` (die
   arithmetische — Störung der Gewichte um insgesamt `δ` kostet `δ`) und die
   Auswertung `sum_smul_dirac_apply`. `WeakConvergence` steht bei **105
   Deklarationen und 7 `sorry`** (vorher 102 und 7), rc = 1 mit unverändert
   genau den zwei angekündigten Fehlern, jetzt bei `:2011`. Die vom Vorlauf
   verlangte Suche ist gelaufen und negativ: Mathlib hat die Separabilität von
   `ProbabilityMeasure E` auf `upstream/master` `572e4d091bc` nicht, neun
   Formulierungen im Laufbericht. Der nächste benannte Schritt ist die
   **Zerlegung** (`exists_finite_partition_ball_of_denseRange`), nicht die
   rationalen Gewichte; Begründung im Laufbericht.*

   *Zwischenstand 2026-09-08, vierter Lauf des Tages: **das benannte Ziel ist
   gefallen, und drei Nachbarn mit ihm.** `separableSpace_probabilityMeasure`,
   `separableSpace_levyProkhorov_probabilityMeasure` (dieselbe Aussage auf dem
   Synonym, wo die Metrik lebt), `secondCountableTopology_probabilityMeasure`
   (ein Meilensteinpunkt, der bis dahin keine Deklaration hatte) und
   `isProbabilityMeasure_natWeightMeasure` sind bewiesen und hängen laut
   `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`; die
   approximierende Familie steht als Definition `natWeightMeasure`, was ihre
   Abzählbarkeit zu drei Zeilen macht. Mitgefallen ist
   `polishSpace_probabilityMeasure`, jetzt Beweis statt `sorry` und allein auf
   `isCompletelyMetrizableSpace_probabilityMeasure` ruhend — **mit schwächeren
   Hypothesen**, weil eine mitgegebene Metrik auf `E` den Aufstieg zur
   vollständigen blockiert (Befund im Laufbericht). `WeakConvergence` steht bei
   **6 `sorry`** (vorher 7), rc = 1 mit unverändert genau den zwei
   angekündigten Fehlern, jetzt bei `:2029`.*

   *Fortsetzung desselben Laufs: **auch die Vollständigkeit ist bewiesen**, und
   damit der ganze Block „der Raum der Gesetze" von Meilenstein 3.
   `isTightMeasureSet_of_forall_exists_levyProkhorovEDist_lt` (eine Cauchy-Folge
   von Gesetzen ist straff — der Kern, und die Stelle, an der die
   Vollständigkeit von `E` zweimal bezahlt wird: Ulam für den endlichen Kopf,
   `isTightMeasureSet_of_forall_exists_finite_iUnion_ball` für den Schluß),
   `isTightMeasureSet_of_cauchySeq`,
   `completeSpace_levyProkhorov_probabilityMeasure` und
   `isCompletelyMetrizableSpace_probabilityMeasure` sind bewiesen; alle fünf
   betroffenen Sätze samt `polishSpace_probabilityMeasure` hängen laut
   `#print axioms` allein an `propext`, `Classical.choice`, `Quot.sound`.
   `WeakConvergence` steht danach bei **3 `sorry`** (zu Beginn des Laufs 7),
   rc = 1 mit unverändert genau den zwei angekündigten Fehlern. Übrig sind die
   Skorokhod-Darstellung (zwei Deklarationen) und Meilenstein 4. Der nächste
   benannte Schritt ist `exists_measurable_partition_diam_le_null_frontier`, die
   Zerlegung mit Nullrändern; Begründung im Laufbericht.*

   *Zwischenstand 2026-09-08, zehnter Lauf des Tages: `WeakConvergence` steht
   weiterhin bei **zwei** `sorry` und denselben zwei bekannten Fehlern, und das
   benannte Ziel der beiden Vorläufe ist gefallen:
   `exists_measurable_pair_of_partition` — eine Stufe der Skorokhod-Darstellung
   als *eine* Aussage, mit der Grenzvariablen als fester erster Koordinate — ist
   bewiesen, mit acht Hilfsaussagen (`sum_smul_condLaw_eq`,
   `tsum_measure_inter_eq`, `condRow` samt `tsum_condRow` und `mul_condRow`,
   `measure_index_ne_prod`, `stageMeasure`,
   `isProbabilityMeasure_volume_restrict_Ioc`); alle neun mit `#print axioms`
   geprüft. Der nächste Schritt in dieser Datei ist
   `exists_ae_tendsto_of_tendsto` selbst, und von den drei Stücken (c1)–(c3) des
   siebten Laufs ist (c2) damit erledigt; was bleibt, sind die Teilfolge, Borel--
   Cantelli und die Umindizierung aller Stufen auf `(E × (ℕ → ℝ)) × (ℕ × ℕ → E)`
   — Buchhaltung über bewiesenen Sätzen, keine neue Idee. Der Bauplan steht im
   Laufbericht im Inventar.*

   *Werkzeugnotiz aus dem ersten Lauf des 2026-09-08: die übliche Zählung
   `grep -cE "^(theorem|lemma|def|…)"` zählt Fließtextzeilen des Modulkopfes
   mit, die mit `theorem` beginnen. Zweimal an einem Tag hat das eine
   Deklaration zu viel gemeldet; wer die Zahl nennt, prüft sie mit
   `git diff --unified=0 HEAD | grep -E "^\+(theorem|lemma|def|…) "`.
   **Ein drittes Mal am 2026-09-08, dreizehnter Lauf**, und diesmal nicht im
   Modulkopf, sondern in einem `/-- … -/` an einer Deklaration, wo ein Umbruch
   die Zeile mit `instance at …` beginnen ließ. Die Probe über den Diff hat es
   gefunden; der Satz ist umgebrochen worden, damit die Zählung stimmt. Wer
   Fließtext schreibt, in dem `theorem`, `def` oder `instance` vorkommt, achtet
   auf den Zeilenanfang.*

   *Werkzeugnotiz aus dem zweiten Lauf des 2026-09-08, und sie spart Minuten:
   neue Beweise gehören in eine **eigene kleine Datei** mit nur den Imports, die
   sie brauchen — drei Durchläufe von je unter einer Minute gegen minutenlange
   Durchläufe der 3300-Zeilen-Datei —, und erst der fertige Text wird eingesetzt
   und einmal im Ganzen geprüft. Die Hilfsdatei geht danach mit
   `git clean -f <pfad>` weg; `rm` auf einen Pfad im Worktree ist von der
   Sandbox blockiert, `git clean` nicht.*

2. ~~**`MeasureTheory.induction_on_mulSystem`**, der funktionale
   Monotone-Klassen-Satz (`WeakConvergence` Meilenstein 5, Task 25 in
   `PLAN.md`).~~ *(erledigt 2026-09-07, neunter Lauf des Tages.)* Der Satz und
   **alle drei** Folgerungen tragen Beweise und gehen durch `lake env lean`
   gegen v4.33.1: `induction_on_mulSystem`, `ext_of_forall_integral_eq_of_isMulSystem`,
   `integral_mul_eq_zero_of_isMulSystem` und `condExp_eq_of_forall_integral_mul_eq`.
   Der Weg dahin steht in der Roadmap und im Laufbericht; die vier Schritte sind
   `of_tendstoUniformly_of_mono_lim`, `of_continuous_comp_of_isMulSystem`,
   `of_indicator_mem_ioiCells` mit `of_indicator_of_measurable`, und
   `of_simpleFunc` mit `of_nonneg_of_measurable`. Was jetzt darauf wartet, steht
   nicht mehr hier, sondern in `MartingaleProblems`
   (`isMPSolution_iff_forall_fdd_continuous`) und in `SkorokhodSpace`
   Meilenstein 8.

   *Zwischenstand 2026-09-06, zweiter Lauf des Tages: der Unterbau steht und
   ist übersetzt, der Satz selbst nicht.* In
   `TauCeti/WeakConvergence/Suggested.lean` tragen jetzt sieben Deklarationen
   von Meilenstein 5 Beweise, die alle durch `lake env lean` gegen `v4.33.1`
   gehen: `IsMulSystem`, `indicatorFuns` samt `indicatorFuns_mono`,
   `isMulSystem_indicator_of_isPiSystem`, `generateFromFuns` samt
   `measurable_generateFromFuns_of_mem`, `generateFromFuns_le_iff` und
   `generateFromFuns_mono`, die Brücke `generateFromFuns_indicatorFuns`, das
   π-System `ioiCells` samt `isPiSystem_ioiCells` und
   `generateFromFuns_eq_generateFrom_ioiCells`, und — als erster Schritt des
   Induktionssatzes — `of_tendstoUniformly_of_mono_lim`.

   **Zwei Befunde an den Aussagen, beide beim Aufschreiben gefunden, beide in
   der Roadmap berichtigt.** Erstens war
   `isMulSystem_indicator_of_isPiSystem` in der Fassung der Roadmap **falsch**:
   ein π-System muß `∅` nicht enthalten, und für $s\cap t=\emptyset$ ist das
   Produkt der beiden Indikatoren die konstante $0$. Zeuge: $\mathcal C=
   \{\{0\},\{1\}\}$ auf $\N$. Die Aussage steht jetzt über
   `indicatorFuns (insert ∅ 𝒞)`, was nach
   `MeasurableSpace.generateFrom_insert_empty` nichts kostet. Zweitens fehlte
   `integral_mul_eq_zero_of_isMulSystem` die Hypothese über die Konstante:
   für `K = {0}` ist `generateFromFuns K = ⊥`, dessen beschränkte meßbare
   Funktionen die Konstanten sind, und `∫ g * c ∂μ = 0` verlangt `∫ g ∂μ = 0`.
   Dieselbe Lücke wie die Gesamtmasse in
   `ext_of_forall_integral_eq_of_isMulSystem`, die die Roadmap dort schon
   richtig hatte.

   Mitberichtigt: `induction_on_inter` liegt in `MeasurableSpace`, nicht in
   `MeasureTheory`; `generateFromFuns` braucht `@[instance_reducible]` wie
   `MeasurableSpace.generateFrom`, sonst meldet der Linter für
   Klassendefinitionen.

   **Was noch fehlt, und in welcher Reihenfolge.** Der Beweis von
   `induction_on_mulSystem` in vier Schritten, von denen anderthalb stehen:
   (i) Abschluß unter gleichmäßigen Limiten — erledigt,
   `of_tendstoUniformly_of_mono_lim`; (ii) `P (φ ∘ (f₁,…,fₙ))` für stetiges
   `φ`, über Polynome und Stone--Weierstraß auf dem kompakten Bild — offen,
   und der eigentliche Brocken; (iii) die Indikatoren des π-Systems
   `ioiCells K` und `MeasurableSpace.induction_on_inter` — die π-System-Hälfte
   ist erledigt (`isPiSystem_ioiCells`,
   `generateFromFuns_eq_generateFrom_ioiCells`, über `measurable_of_Ioi`), es
   fehlt die Approximation des Indikators einer Box durch stetige Funktionen;
   (iv) einfache Funktionen und ein letzter monotoner Limes — Routine.
   Der nächste eigenständige Punkt ist (ii); der Anker in Mathlib ist
   `ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints`
   (`Topology/ContinuousMap/StoneWeierstrass.lean:297`, die ε-Fassung),
   angewandt auf die von `f₁,…,fₙ` erzeugte Unteralgebra über dem kompakten
   Bild in `Fin n → ℝ`.

   *Zwischenstand 2026-09-07, neunter Lauf des Tages: **`induction_on_mulSystem`
   ist bewiesen**, und mit ihm zwei seiner drei Folgerungen. Die Schritte (iii)
   und (iv) sind gebaut — `ioiApprox` samt sechs Lemmata,
   `of_indicator_mem_ioiCells`, `of_indicator_of_measurable`, `of_simpleFunc`,
   `of_nonneg_of_measurable` —, der Satz selbst ist die Verschiebung
   `f = (f + C) + (-C)`, und `ext_of_forall_integral_eq_of_isMulSystem` sowie
   `integral_mul_eq_zero_of_isMulSystem` tragen Beweise. Alles durch
   `lake env lean` gegen v4.33.1, ohne Warnung außer `sorry`. **Damit ist dieser
   Punkt bis auf `condExp_eq_of_forall_integral_mul_eq` erledigt**; dessen Weg
   steht im Laufbericht im Inventar. Einzelheiten dort.*

   *Zwischenstand 2026-09-07, achter Lauf des Tages: **(ii) ist bewiesen**,
   `of_continuous_comp_of_isMulSystem`, durch `lake env lean`. Der Anker ist
   nicht der hier genannte, sondern
   `ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`
   (`ibid.:323`), die Fassung ohne Kompaktheit des Raumes — sie erspart den
   Subtyp `↥box` vollständig. Offen sind damit noch (iii), die Approximation
   des Indikators einer Box durch stetige Funktionen, und (iv), die einfachen
   Funktionen und der letzte monotone Limes; danach ist
   `induction_on_mulSystem` selbst zusammenzusetzen. Der nächste Schritt ist
   (iii), und er ist der letzte mit Inhalt.*

   *Zwischenstand 2026-09-06, dritter Lauf des Tages: die algebraische Hälfte
   von (ii) steht und ist übersetzt, die Approximationshälfte nicht.* Drei
   weitere Deklarationen tragen Beweise und gehen durch `lake env lean`:
   `mul_mem_span_insert_one_of_isMulSystem`, `of_mem_span_insert_one` und
   `exists_bound_of_mem_span_insert_one`. Dazu die Aussage von (ii) als
   `of_continuous_comp_of_isMulSystem`, mit `sorry`.

   **Der Befund, der die Gestalt von (ii) bestimmt.** Die naheliegende
   Induktion über `Algebra.adjoin` **geht nicht**: ihr `mul`-Fall verlangt, daß
   `P` unter Produkten abgeschlossen ist, und das ist `P` gerade nicht — es ist
   linear, enthält die Konstanten und ist unter beschränkten monotonen Limiten
   abgeschlossen, mehr nicht. Die Multiplikativität muß in `K` bleiben. Das
   tragende Objekt ist deshalb `Submodule.span ℝ (insert 1 K)`: der Spann ist
   unter Multiplikation abgeschlossen, weil `K * K ⊆ K` ist und die
   hinzugefügte `1` eine Einheit ist, und `P` gilt auf ihm allein aus
   Linearität. Er liegt also zwischen `K` und `P`, und (ii) zieht die
   Approximanten durch ihn hindurch.

   Der bessere Anker für die Approximationshälfte ist
   `ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints`
   (`:313` in v4.33.1 wie auf master), die **unbebündelte** ε-Fassung: sie nimmt
   `φ` als Funktion samt `Continuous`-Beweis und erspart das Bündeln zu
   `C(X, ℝ)`. Was zu tun bleibt: die kompakte Box in `Fin n → ℝ`, die
   Punktetrennung der von den Koordinaten erzeugten Unteralgebra, und der
   Rückzug entlang `x ↦ (f₁ x, …, fₙ x)` in den Spann.

   Mitgefunden: `abs_add` heißt in v4.33.1 `abs_add_le`.

3. ~~**Die drei `Suggested.lean` zum Übersetzen bringen.**~~ *(erledigt
   2026-09-05, vierter Lauf des Tages.)* Alle drei gehen jetzt durch
   `lake env lean` gegen Mathlib `v4.33.1`, ohne Fehler und ohne Warnung; die
   Köpfe halten das fest, mit Datum. Gefunden und behoben wurden sieben Dinge,
   die die reine Signaturprüfung nicht sehen konnte:

   * `WeakConvergence` — zwei doppelte Doc-Kommentare, an denen die Datei nicht
     einmal parste, und ein fehlendes `[TopologicalSpace E]` in
     `IsSeparating.ae_eq_of_forall_condExp_eq`.
   * `SkorokhodSpace` — ein fehlendes `[MeasurableSpace ι]` in
     `IsCadlag.measurable`, `Real.exp` ohne seinen Import, eine ganze
     Meilensteinhälfte über meßbare Abbildungen aus `D(ι, E)` ohne meßbare
     Struktur darauf (jetzt als Borelstruktur der Metrik deklariert, und
     `noncomputable`, weil die Metrik es ist), und ein `omit` an
     `dist_eq_sub_of_le`, dessen Beweis weder `OrderTopology` noch
     `ProperSpace` benutzt — die stehende Regel über minimale Voraussetzungen,
     vom Linter gefunden.
   * `MartingaleProblems` — `Shift.eval_comp` als nacktes `sorry` in einem
     Strukturfeld hat keine ableitbare Universe und ist jetzt `(sorry : Prop)`.

   Die Werkzeuglage, die der dritte Lauf hier notiert hatte, gilt **nicht
   mehr**: `lean --version`, `cd ~/Code/lean/journal` und `lake env lean` auf
   Dateien im Worktree sind freigegeben und wurden benutzt. Der erste Durchlauf
   je Datei dauert wenige Minuten.

   Was offen bleibt und in Punkt 1 und 2 gehört: die Beweise. `sorry` steht in
   allen drei Dateien noch überall, und in `MartingaleProblems` stehen an vier
   Stellen `True` oder `sorry` in der **Aussage** — das sind die
   Meilensteintexte der Meilensteine 3, 5, 9 und 10, die noch keine Proposition
   sind. Wer diese aufnimmt, arbeitet an den Aussagen, nicht am Übersetzen.

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

5. **Prüfen, ob die Roadmaps noch zu Mathlib master passen.** Alle zitierten
   Deklarationen gegen master, auf Existenz und `deprecated`. Am 2026-08-29
   fanden sich so drei Fehler. Sinnvoll etwa alle zwei Wochen. *Am 2026-08-31,
   dritter Lauf, ist die Liste „What Mathlib already has" von `WeakConvergence`
   erledigt: elf Deklarationen, alle vorhanden, keine `deprecated`. Am
   2026-09-01, zweiter Lauf, die Liste „Mathlib supplies" von
   `MartingaleProblems`: 38 Namen aus elf Dateien, gegen master geprüft, alle
   vorhanden. Ein Fehler, und ein systematischer — vier Namen standen in
   `MeasureTheory` statt in `ProbabilityTheory`, siehe die Auffälligkeit im
   Inventar. Mitgeprüft und weiterhin richtig: `ProgMeasurable` ist ein
   `@[deprecated (since := "2026-04-24")]`-Alias von `IsStronglyProgressive`
   (`Process/Adapted.lean:381`), Doobs `Lᵖ`-Ungleichung fehlt weiterhin für jeden
   Index (`OptionalStopping.lean:143` sagt es selbst), und `IsStable` ist für
   keine hier interessierende Eigenschaft bewiesen (`gh search code`: der
   Bezeichner kommt in genau einer Wahrscheinlichkeitsdatei vor).*

   *Am 2026-09-01, vierter Lauf, sind `KolmogorovExtension` und `SkorokhodSpace`
   erledigt, und zwar vollständig — Kopfliste **und** Meilensteine; bei
   `SkorokhodSpace` zitieren nur die Meilensteine 1, 2, 3 und 8 überhaupt
   Mathlib. Sieben Fehler, alle berichtigt: zwei Namensräume in
   `KolmogorovExtension` (`MeasureTheory.Measure.isProjectiveLimit_infinitePi`,
   `ProbabilityTheory.isProjectiveLimit_map`), ein Meilensteinpunkt, den Mathlib
   längst hat (`MeasureTheory.IsProjectiveLimit.unique`,
   `Constructions/Projective.lean:150`), eine zu schwach angegebene Hypothese
   (`innerRegular_isCompact_isClosed_measurableSet_of_finite` braucht neben
   `IsCompletelyPseudoMetrizableSpace` auch `SecondCountableTopology` und
   `BorelSpace`), und in `SkorokhodSpace` die sechs `Monotone.`-Sätze, die die
   Kopfliste als „die ganze Einseitiglimes-API" führte, der Selbstwiderspruch um
   `Monotone.countable_not_continuousAt` und der Typfehler `LipschitzWith.const`
   in der Definition von `TimeChange.norm`. Zwei Funde in die andere Richtung
   sind mit eingetragen: `isCompactSystem_isCompact_isClosed`
   (`Topology/Compactness/CompactSystem.lean:163`) und
   `OrderTopology.of_linearLocallyFinite` (`Instances/Discrete.lean:63`).
   Einzelheiten im Inventar unter „Läufe" und bei den Auffälligkeiten.*

   *Am 2026-09-01, fünfter Lauf, sind die Meilensteine von `WeakConvergence`
   erledigt — fünf Befunde, darunter der größte des ganzen Rückstaupunktes:
   `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` mit
   `MeasureTheory.TendstoInDistribution` war der Roadmap unbekannt, und vier
   Punkte der Meilensteine 2 und 3 verlangten, was darin steht. Dazu
   `measurableSet_of_continuousAt`, das Meilenstein 2 unter einem erfundenen
   Namen suchte, und vier Zeilennummern aus v4.33.1. Von `MartingaleProblems`
   sind die Meilensteinstellen mit ausgeschriebenem Mathlib-Pfad erledigt (ein
   Namensraumfehler, zwei Zeilennummern, eine verschwiegene Hypothese, ein
   präzisiertes Zitat); es fehlen die Nennungen **ohne** Pfad, und das sind die
   meisten. Einzelheiten im Inventar unter „Läufe".*

   *Werkzeug, und es spart den halben Aufwand: `~/Code/lean/mathlib4` hat neben
   `origin` (Fork des Nutzers, master vom 2026-03-23, untauglich) das Remote
   `upstream` auf `leanprover-community/mathlib4`. Nach
   `git -C ~/Code/lean/mathlib4 fetch --no-tags upstream master` beantwortet
   `git grep -n <muster> upstream/master -- Mathlib` in einem Aufruf, wofür
   `gh api` ein Dutzend braucht, und liefert Zeilennummern, Namensraumgrenzen
   und Variablenblöcke mit. So ist dieser Lauf gegen `981fa8f5` geprüft.*

   *Am 2026-09-01, sechster Lauf, ist die Restmenge erledigt — die
   Meilensteinnennungen von `MartingaleProblems` **ohne** Pfad, rund dreißig aus
   den Meilensteinen 1, 2, 8, 9, 12 und 13, geprüft gegen `e076e1ca8f3`. Damit
   ist dieser Punkt für alle vier Roadmaps einmal durchgelaufen; die nächste
   Runde ist in etwa zwei Wochen fällig und fängt wieder bei
   `KolmogorovExtension` an. Drei Befunde, alle in der Lokalisierungs- und
   Stoppzeitschicht: Meilenstein 2 stand auf `[Preorder ι]` und benutzte
   `ProbabilityTheory.Locally`, das `[LinearOrder ι] [OrderBot ι]
   [TopologicalSpace ι] [OrderTopology ι] [Zero E]` verlangt; Meilenstein 9
   nannte `⊥` ohne `[OrderBot ι]`; und `IsQuasiLeftContinuous` typisierte
   Stoppzeiten als `Ω → ι`, während Mathlibs `IsStoppingTime` `Ω → WithTop ι`
   ist. Alle drei berichtigt, `Suggested.lean` mit. Einzelheiten im Inventar.*

   *Die Lehre dieses Laufs, neben der des fünften: die drei Fehler waren keine
   Versionsdrift — jede der Deklarationen steht in v4.33.1 wortgleich da. Was
   ungeprüft blieb, war nicht der **Name**, sondern die **Signatur**: der
   Variablenblock, in dem eine Deklaration steht, und der Typ ihrer Argumente.
   Wer den Punkt fortsetzt, lese zu jedem zitierten Namen die `variable`-Zeilen
   des umgebenden `section` mit, nicht nur die Zeile der Deklaration.*

   *Die Lehre aus dem Hauptbefund, für den nächsten Durchgang: die Datei stand
   in v4.33.1 wortgleich da. Der Fehler war keine Versionsdrift, sondern eine
   nie gestellte Suche — nach dem Wort des Manuskripts („weak convergence")
   statt nach Mathlibs Begriff („convergence in distribution"). Wer den Punkt
   fortsetzt, sehe zu jedem Meilensteinpunkt zuerst das **Verzeichnis** durch,
   in dem er läge, und lese dessen Dateinamen, bevor er nach Deklarationen
   sucht.*

6. **Task 23, was sonst offen bleibt.** **Stufe 3, die gemischte Uhr,** ist
   erledigt, und seit dem zehnten Lauf des 2026-09-01 ohne jede Bedingung an die
   stetige Masse: `prop:mixeddual` samt `lem:rectangle` steht im Manuskript, der
   Beweis im PROTOKOLL, das Orakel in `Task23/mixed.py`. Der zweite Rest — zwei
   benachbarte Atome ohne stetige Masse dazwischen — ist damit gestrichen; die
   beiden Mechanismen sind verschränkt, und zwar als die zwei Fälle **einer**
   Induktion, nicht als zwei Beweise nebeneinander.

   Offen bleibt allein die **ordnungsdichte Atommenge**. Der Grund ist scharf
   und unverändert: es gibt keine Aufzählung $a_1<a_2<\dots$, entlang der
   induziert werden könnte, und unter einem Punkt liegen dann unendlich viele
   Atome. Beide bisherigen Wege — die Induktion über $d=i-j$ und die
   Nilpotenz der Matrix $V$ in `prop:atomicposet` — brauchen Endlichkeit an
   einer benannten Stelle.

   *Zwischenstand 2026-09-01, elfter Lauf: die Ausschöpfung ist durchgerechnet
   und scheitert, aber an einer anderen Stelle als vermutet.* Der Beweis des
   sechsten Laufs ist störungsweise gelesen worden und liefert die **Identität**
   $\langle\delta,T\mathbb 1\rangle=-\frac12\operatorname{tr}(TE)$, wenn (S) nur
   bis auf einen Rest $E$ gilt. Damit hängt die ganze Ausschöpfung an einer
   berechenbaren Zahl, $C(V,t)=\|T\|_F$ für $T=T^{\mathsf T}$,
   $TV=V^{\mathsf T}T$, $T\mathbb 1=e_t$: der Defekt verschwindet, sobald
   $|F|C_F\varepsilon_F\to0$ für eine Folge endlicher $F$ gilt. `Task23/dense.py`
   misst $C$ exakt in Brüchen. Befund, und er ist scharf: $C$ ist
   skaleninvariant, hängt also nur an der *Gestalt* des Massenvektors, und eine
   kleine Masse $\varepsilon$ an Stelle $k$ einer Kette aus $n$ Atomen kostet
   $C\sim\varepsilon^{-\max(n-2k,0)}$ — geprüft für $n=4,6,8,10$ an jeder
   Stelle, ohne Abweichung. Kleine Massen **oben** sind gratis, kleine Massen
   **unten** ruinieren die Schranke. Fallende Massenprofile geben $C\approx1.6$
   gleichmäßig, steigende $C\sim\rho^{n^2/2}$. Eine ordnungsdichte Menge erzwingt
   das teure Profil, weil unter jedem Punkt unendlich viele Atome liegen.
   Wer den Punkt aufnimmt, fängt deshalb **nicht** mehr bei der Ausschöpfung an,
   sondern bei der Frage, ob die Cauchy--Schwarz-Ungleichung in
   $|\operatorname{tr}(TE)|\le\|T\|_F\|E\|_F$ durch eine Paarung ersetzt werden
   kann, die die Struktur von $E$ als Schwanzbeitrag benutzt statt sie
   wegzuwerfen. Widerlegt ist die grobe Ausschöpfung, nicht die Aussage; ein
   Gegenbeispiel ist nicht gesucht und nicht gefunden. Einzelheiten im
   `Task23/PROTOKOLL.md`, Abschnitt „Die ordnungsdichte Atommenge, 2026-09-01
   (elfter Lauf)", Sackgassen im zehnten Nachtrag.

   *Zwischenstand 2026-09-01, zwölfter Lauf: die Frage nach der feineren
   Paarung ist beantwortet — linear gibt es sie nicht, quadratisch sitzt die
   Numerik exakt auf ihr.* Das Problem ist auf drei Bedingungen an den
   verschobenen antisymmetrischen Anteil $h(a,t)=\kappa(a,t)-\kappa(a,0)$
   reduziert, die Behauptung ist äquivalent zu $h(a,a)=0$ je Atom, und die
   Reduktion trägt in beide Richtungen — wer ein Gegenbeispiel sucht, sucht
   eine Lösung mit nichtverschwindender Diagonale. Auf Level-Trunkierungen der
   dyadischen Uhr ist das ein LP (`Task23/lp_dense.py`; Kontrolle $\eta=0$
   reproduziert den endlichen Satz exakt). Befund: der maximale Defekt fällt
   für alle drei gemessenen Massenprofile gegen $0$ — **kein beschränktes
   Gegenbeispiel auf der dyadischen Uhr** —, die beste lineare
   Zertifikatskonstante ist exakt $n+\frac12$ (linear in der Atomzahl, darum
   scheiterte der elfte Lauf), und alles sitzt auf dem Zwei-Regime-Gesetz
   $v\approx\min(\kappa\eta,\,0.85\sqrt{BM\eta})$ mit Übergang bei
   $BM/\kappa^2$. Wer den Punkt aufnimmt, beweist die **Energieschranke**
   $\Delta(t)^2\le C\,B\,M\,\eta$ ($C\le1$) für endliche Kettensysteme mit
   Residuum $\eta$ und $|h|\le B$ — sie schließt per Ausschöpfung jede rein
   atomare Uhr endlicher Masse mit beschränktem $\kappa$, ordnungsdicht
   eingeschlossen. Der erste Paarungsschritt und die Sackgassen stehen im
   PROTOKOLL, zwölfter Lauf; dort auch die noch zu prüfende Skizze, dass
   Nachbaratome ohne Bodenatom (Typ $\omega^*$, $\mathbb Z$-Ketten) schon der
   bisherigen Induktion zugänglich sind.

   *Zwischenstand 2026-09-01, dreizehnter Lauf: die Energieschranke ist
   **falsch**, in jeder Konstante.* Der kleinste Zeuge hat zwei Atome
   (Massen $(\mu,1)$, $\eta=2\mu^2/3$, Verhältnis $\to 3/2$, analytisch und in
   exakter Bruchrechnung), und entlang aufsteigend-geometrischer Ketten ist
   $\Delta^2/(BM\eta)$ unbeschränkt — zertifizierte Instanzen bis $27588$
   (`Task23/energy_counterexample.py`). Auch masse-lokale Residuenbudgets
   retten nichts. Damit ist der Ausschöpfungsweg über eine profilfreie
   Schranke dreifach zu (Frobenius, linear, quadratisch) und im Ganzen zu:
   die Relaxation „endliches System plus Slack" ist echt schwächer als
   „Trunkierung eines exakten Systems". Wer den Punkt aufnimmt, hat zwei
   Wege: die $\omega^*$-Skizze des zwölften Laufs nachrechnen (unverändert
   offen), oder die **Gestalt** des Trunkierungsresiduums benutzen — es ist
   selbst $\sum_{\text{fehlend}}m_ah(a,\cdot)$ mit global gebundenem $h$,
   und ordnungsdichte Uhren mit durchweg aufsteigenden Massen existieren
   nicht (Summierbarkeit). Einzelheiten in `Task23/PROTOKOLL.md`,
   dreizehnter Lauf.

   *Zwischenstand 2026-09-01, vierzehnter Lauf: die $\omega^*$-Skizze ist
   nachgerechnet und **Satz**.* Für jede rein atomare Uhr, deren Atome unter
   $t^*$ eine **intervallendliche** Kette bilden — je zwei Atome schließen nur
   endlich viele ein; das erfasst $\omega$, $\omega^*$ und $\mathbb Z$-Ketten
   und enthält `prop:atomicdual` —, gilt die Dualität in beiden Konventionen,
   ohne Schranke an $\kappa$: die Zwei-Diagonalen-Induktion braucht weder
   Boden noch Deckel (`Task23/neighbor.py`, Test R), und die Ränder kommen als
   Schwänze der absolut konvergenten Atomsummen, die \eqref{eq:incrementrep}
   ohnehin voraussetzt — die $B$-Hypothese des zwölften Laufs ist damit für
   den Kettenfall vom Tisch. Zwei Korrekturen an der Skizze: ihre wörtliche
   Hypothese „beidseits ein Nachbaratom" ist echt schwächer als die
   Intervallendlichkeit (zwei $\zeta$-Ketten übereinander trennen beide, und
   Test X zeigt, dass die lokalen Relationen die Kreuzpaare dort nicht
   erzwingen), und ihre Schritte über $\kappa$ sind nur für die volle
   Symmetrie nötig. Beweis und Befunde in `Task23/PROTOKOLL.md`, vierzehnter
   Lauf; Roadmap-Einträge `atomGrid_symm_int` und
   `duality_of_atomic_intervalFinite` in `MartingaleProblems` Meilenstein 8.
   Offen am ordnungsdichten Kern: unverändert die in sich dichte Atommenge
   und neu benannt die diskrete, nicht intervallendliche Kette; beide hängen
   am Überqueren eines Häufungspunkts.

   *Zwischenstand 2026-09-02, fünfzehnter bis siebzehnter Lauf: die
   LP-Schiene ist ausgeschöpft, und zwar beweisbar.* Der fünfzehnte Lauf
   maß auf geschachtelten summierbaren Uhren den Kollaps
   $v_J\approx c\sqrt{M\varepsilon_J}$, der sechzehnte baute die
   hierarchische Motor-Uhr, auf der $v_J$ bis Stufe 14 bei $\tfrac1{24}$
   klebt, und erklärte deshalb „(S) ist falsch"; der siebzehnte hat das
   **zurückgenommen und die Kollision entschieden**: das exakte $h$-System
   1–3 ist auf jeder intervallendlichen Kette starr —
   $\widehat w(s,t):=H(s,t)+\Delta(t)-\Delta(s)$ erfüllt exakt die
   Kreuzrelation $(\ast)$, $h$- und $\Phi$-System sind im antisymmetrischen
   Sektor **isomorph** —, also gilt dort $v_J\to0$ (Fensterschranke
   $v_i\le2B\,M_{<u_l}+(K_l+2B)E_i$), nur mit Konstanten $K_l$, die als
   Produkte von Massenverhältnissen jede Messung überdauern. Endliche
   LP-Werte sagen über den Limes nichts; wer den ordnungsdichten Kern
   aufnimmt, arbeite mit dem $\widehat w$-Isomorphismus an den
   Schwanzrelationen über Häufungspunkte (kleinste Instanz: zwei
   $\zeta$-Ketten) und lasse die LPs liegen. `Task23/PROTOKOLL.md`,
   fünfzehnter bis siebzehnter Lauf.

   *Zwischenstand 2026-09-02, achtzehnter Lauf: die Viertelgitterfrage (V)
   der zwei $\zeta$-Ketten ist strukturiert, teilbeantwortet und scharf
   lokalisiert.* Normalform: eine kommutierende Evolution
   $F(\cdot,j{+}1)=(I+\nu_jL)F(\cdot,j)$ mit einem einzigen Operator $L$;
   (V) ist die Injektivität des Geschlecht-0-Produkts $\Pi_j(L)$ auf
   westabfallenden Zeilen — eine Quasianalytizitätsfrage. Bewiesen: ohne
   Summierbarkeit ist (V) **falsch** (Buckel bei Massen $\equiv1$); mit
   Summierbarkeit sterben endliche Modensuperpositionen (Momentenschritt
   plus Vandermonde), endlich getragene $x$, jeder einzelne Schritt
   (injektiv), und jedes reelle Spektralmaß mit exponentiellem
   Abfallspielraum (Streifenanalytizität). Sackgasse mit Beleg: die exakte
   Energieidentität ist indefinit, mit demselben Faktor
   $\mu_i\nu_j(\nu_j-\mu_i)$ wie der Dispersionsdefekt des
   charakteristischen Ansatzes. Offen ist genau der quasipolynomiale
   Bereich: zulässige Spektralmaße müssen nur $e^{\Phi_\mu+\Phi_\nu}$
   integrieren ($O((\log r)^2)$ bei geometrischen Massen), dort existieren
   Maße mit lauter Nullmomenten, und ob eines die ganze
   $\{\lambda_j\}$-Familie annihiliert, ist eine Vollständigkeitsfrage, in
   die die Massen über ihre Zählfunktion eingehen — möglicherweise die
   erste echt massenabhängige Stelle von Task 23. Wer den Punkt aufnimmt:
   Weg (α) Spektraldarstellung westabfallender Lösungen bzw.
   Carleman-Argument an der Evolution, Weg (β) Gegenbeispielsuche bei stark
   lakunären Massen; beides präzise in `Task23/PROTOKOLL.md`, achtzehnter
   Lauf, mit `Task23/zeta_cross.py` (Proben (a)–(f), exakt, rc=0) als
   mechanischer Verifikation der Beweisalgebra.

   *Zwischenstand 2026-09-02, neunzehnter Lauf: Weg (β) ist zu, durch
   Beweis.* Die „Vollständigkeitsfrage" des achtzehnten Laufs war keine:
   die Geschlecht-0-Produkte haben nichtnegative Taylorkoeffizienten, und
   die Zulässigkeitsschranke $e^{\Phi_\mu+\Phi_\nu}$ ist genau ihre
   Koeffizienten-Majorante — also paart die Taylorreihe jeder Mode gegen
   jedes zulässige $\sigma$ absolut, und **die Momente entscheiden alles**
   (Theorem 6: Nullmomente ⟺ Annihilation aller $\lambda_j$ ⟺ aller
   $\beta_i$ ⟺ jeder ganzen Funktion mit zulässiger Majorante; die
   Polynomgewichte der Zulässigkeit von Proposition 5 sind dabei
   entbehrlich). Folgen: jeder zulässige reelle Spektralkandidat, der (Q)
   löst, ist identisch null — ohne den Exponentialspielraum von
   Proposition 5.2 —, die drei (β)-Bedingungen sind äquivalent zu den
   Nullmomenten und von jedem Stieltjes-Maß erfüllt, das aber nur die
   Null darstellt; die Denjoy–Carleman-Spekulation (Massenzählfunktion)
   ist zurückgenommen. Mechanisch verifiziert in
   `Task23/spectral_closed.py` (mpmath, 50 Stellen, rc=0): alle
   $\mathcal E$-Paarungen $<10^{-47}$ relativ bei $\|\sigma\|_{TV}=0.94$,
   Kontrollfunktion $e^{-3c}$ außerhalb der Klasse bei $5\cdot10^{-13}$ —
   37 Größenordnungen Trennung. Wer (V) aufnimmt, hat nur noch Weg (α),
   und der ist leichter geworden: es genügt, jeder westabfallenden Lösung
   **irgendeine** zulässige reelle Spektraldarstellung zu verschaffen
   (quasipolynomialer Abfall reicht), oder Carleman direkt an der
   Evolution. `Task23/PROTOKOLL.md`, neunzehnter Lauf.

   *Zwischenstand 2026-09-03, zwanzigster Lauf: Weg (α) trägt — (V) ist
   bewiesen für quadrantensummierbare Lösungen, insbesondere für alle
   beschränkten.* Der Transformationsbeweis: $G_j(c)=\sum_i\mu_iF(i,j)
   W^c_i$ mit den Geschlecht-0-Schwänzen $W^c_i=\prod_{i'>i}(1+c\mu_{i'})$
   ist ganz vom Typ 0, erfüllt exakt die Nordrekursion
   $G_{j+1}=(1+c\nu_j)G_j+\nu_jR_j$, ist rechts beschränkt und fällt
   reell — Phragmén–Lindelöf (Titchmarsh §5.62) plus Liouville geben
   $G_j\equiv0$, und die **unbedingte** Injektivität der W-Transformation
   auf $\ell^1$ (Theorem 9: Fußpunktzerlegung, noch einmal PL) holt
   $x\equiv0$ zurück. Die Hypothese (H)
   $\sum_{j\ge j_0}\nu_j\sum_i\mu_i|x_{ij}|<\infty$ steht genau am
   Nordlimes und an der Reihe der Identität I; beschränktes $x$ erfüllt
   sie. **Damit sind die zwei $\zeta$-Ketten in der Klasse $|h|\le B$
   geschlossen** — der Klasse aller LPs und Messungen des zwölften bis
   siebzehnten Laufs; die Identität I ist das erste Argument von Task 23,
   das einen Häufungspunkt überquert. Offen: (V) in der nackten Klasse
   (nur zeilen-/spaltenweise absolute Konvergenz) — beide Seiten der
   Transformationsmethode brauchen dieselbe gemeinsame Summe, (H) ist
   ihre Grenze; benannte Angriffe: Bootstrap ((H) aus (Q) selbst) oder
   eine Paarung ohne gemeinsame Summe. Und jenseits der zwei Ketten der
   Cantor–Bendixson-Weg. `Task23/PROTOKOLL.md`, zwanzigster Lauf;
   `Task23/quarter_transform.py` (exakt, rc=0; der abgeschnittene Lauf
   08:23 hatte es mit Syntaxfehler hinterlassen).

   *Zwischenstand 2026-09-03, einundzwanzigster Lauf: „(H) ist die Grenze
   der Methode" ist zurückgenommen — (V) gilt, sobald der Fluss nach Norden
   beschränkt ist, und das ist die Manuskriptklasse.* Der Beweis von
   Theorem 10 benutzt (H) an genau drei Stellen und dort nur durch zwei
   Folgerungen; abgezogen ergibt das **(U)** = Straffheit nach Norden
   ($\sup_{j\ge j_0}\sum_{|i|>N}\mu_i|F(i,j)|\to0$) plus
   $\sum_{j\ge j_0}\nu_j|R_j|<\infty$, und **Theorem 12** schließt daraus
   $x\equiv0$. (U) hat zwei unvergleichbare hinreichende Kriterien: (H) —
   Theorem 10 ist damit Korollar — und
   $\sup_{i,\,j\ge j_0}|F(i,j)|<\infty$, die Beschränktheit des
   **Dualitätsdefekts** $\Phi(s,t)-\Phi(t,s)$. Das zweite ist die
   Hypothesengestalt, die `thm:duality` (\EK{} 4.4.11) in
   \eqref{eq:dual1}+\eqref{eq:dual2} ohnehin trägt: die Dominante $\Gamma_T$
   gibt $|\Phi|\le e^{C_T}E[\Gamma_T]$ auf $[0,T]^2$. Mitgefallen: die
   Identität I des zwanzigsten Laufs ist entbehrlich (Koeffizientenvergleich
   in (B$\infty$)), und die Fortsetzung nach Süden ist ein eigener,
   hypothesenfreier Schritt. Jedes Gegenbeispiel hat jetzt eine scharfe
   Gestalt (Proposition 15): unbeschränkter Defekt auf **jedem**
   Nordquadranten, $\sup_j\rho_j=\infty$, und $|x|$ zeilen- und
   spaltenweise integrierbar, aber auf keinem Nordquadranten
   $\mu\otimes\nu$-integrierbar. **Und Theorem 12 iteriert** (Korollar 16):
   ist die Atomkette diskret — jedes Atom hat Nachbarn — und ist die Ordnung
   ihrer Blöcke (Klassen der Relation „nur endlich viele Atome dazwischen",
   sämtlich vom Typ $\zeta$) intervallendlich, so gilt die Dualität bei
   beschränktem $\Phi$; die Induktion läuft über den Blockabstand, die zwei
   Abfälle stehen an den einander zugewandten Rändern und kommen aus der
   Induktionsvoraussetzung. Damit sind abzählbar viele Häufungspunkte
   erfaßt, nicht nur einer. Offen bleibt (V) bei unbeschränktem Defekt —
   der Bootstrap richtet sich jetzt auf die **Straffheit** statt auf die
   Summierbarkeit —, die nicht intervallendliche Blockordnung (dieselbe
   Frage eine Cantor–Bendixson-Stufe höher) und die nichtdiskrete, in sich
   dichte Atommenge, wo es keine Einschrittrelationen gibt.
   `Task23/PROTOKOLL.md`, einundzwanzigster Lauf;
   `Task23/naked_class.py` (Proben (A)–(F), exakt, rc=0); Roadmapeinträge
   `tailProduct`, `norm_le_of_bddOn_imAxis_of_subexponential`,
   `tailProduct_pairing_eq_zero`, `crossGrid_eq_zero_of_bddFlux`,
   `duality_of_atomic_twoChains_of_bounded`, `Clock.atomBlocks` und
   `duality_of_atomic_blockStack_of_bounded` in `MartingaleProblems`
   Meilenstein 8.

   *Zwischenstand 2026-09-04, zweiundzwanzigster Lauf: der ordnungsdichte
   Kern ist gefallen — die Einschrittrelation war nie nötig.* Der
   einundzwanzigste Lauf hatte den Rest als „die Algebra der
   Einschrittrelation" diagnostiziert; das war, wie „(H) ist die Grenze der
   Methode" davor, eine Prämisse aus der Rechnung statt aus dem Beweisbedarf.
   Die Abelsche Summation von Theorem 12 ist in Wahrheit eine
   **Stieltjes-Produktregel** (Lemma 17.1: haben $f$ und $V$
   Zuwachsdarstellungen mit $\ell^1$-Sprüngen, so hat es $fV$ mit den
   Produktsprüngen), und die kennt keine Nachbarn — sie gilt auf **jeder**
   abzählbaren Kette. Damit läuft die ganze Transformationsmethode auf einer
   beliebigen Atomkette: die Gewichte $W^c(a)=\prod_{a'>a}(1+cm_{a'})$, die
   Identität $K(t;c)-cG(t;c)=\psi(t)-\Delta(t)V_0(c)$, und aus ihr an
   $t=b\in A$, $t=0$ und $t=t^*$ die drei Gleichungen $P=V_0Q$,
   $R=\Delta(t^*)+cQ$ und $S=R(1-V_0)$. Die letzte macht $R$ auf $\Re c\ge0$
   beschränkt (denn $|V_0(c)|\ge\prod(1+m_a^2|c|^2)^{1/2}\to\infty$), also
   nach Phragmén–Lindelöf und Liouville konstant, also $Q\equiv0$, also
   $\Delta\equiv0$ auf den Atomen: **Theorem 17**, $h(a,a)=0$ für jedes Atom
   einer beliebigen Kette, ordnungsdicht eingeschlossen. Einzige
   Zusatzhypothese ist **(F)** $\sum_{a,b}m_am_b|h(a,b)|<\infty$ — die
   $m\otimes m$-Integrierbarkeit der Dichte auf Atompaaren, hinreichend dafür
   $|\gamma|$ beschränkt auf $A\times A$; sie steht an genau zwei Stellen
   (Fubini in $P=V_0Q$, Existenz von $P$). Mitgefallen: der Blockstapel des
   einundzwanzigsten Laufs braucht in dieser Klasse weder Diskretheit noch
   intervallendliche Blockordnung, und die Bemerkung des zwölften Laufs, der
   Mechanismus brauche einen Punkt echt zwischen Atom und Nachfolger, ist
   widerlegt (Probe (E): die lückenfreie Bedingungsmenge erzwingt die
   Diagonale bis $n=7$). Offen bleiben nur noch zwei benannte Dinge: die
   **nackte Klasse** (weder (F) noch $\Phi$ beschränkt — dieselbe Lücke wie
   „(V) bei unbeschränktem Defekt", jetzt für beliebige Ketten; jedes
   Gegenbeispiel hat nach Proposition 15 unbeschränkten Defekt *und*
   $\sum_{a,b}m_am_b|\kappa(a,b)|=\infty$) und die **unendliche
   Halbordnung**, die von keinem der Sätze erfaßt ist.
   `Task23/PROTOKOLL.md`, zweiundzwanzigster Lauf; `Task23/dense_chain.py`
   (Proben (A)–(G), exakt, rc=0); Roadmapeinträge `HasAtomIncrements`,
   `HasAtomIncrements.mul`, `chainTailProduct`,
   `chainTailProduct_pairing_eq_zero`, `atomDiag_eq_zero_of_integrable` und
   `duality_of_atomic_chain_of_integrable` in `MartingaleProblems`
   Meilenstein 8.

   *Zwischenstand 2026-09-04, dreiundzwanzigster Lauf: die zweite der beiden
   Restfragen ist entschieden — die unendliche Halbordnung ist **falsch**.*
   Auf der abzählbaren Antikette $\T=\{0\}\cup A\cup\{t^*\}$ mit positiven
   summierbaren Massen $m_i$, Schwänzen $\sigma_i$ und
   $\kappa(a_i,a_j)=\operatorname{sgn}(i-j)/(\sigma_n\sigma_{n+1})$,
   $n=\min(i,j)$, teleskopiert $m_jf(j)=1/\sigma_{j+1}-1/\sigma_j$ die
   Zeilensummen zu $\sum_jm_j\kappa(a_j,a_i)=1/M$ — konstant und von Null
   verschieden, jede Zeile absolut konvergent ($r_i=2/\sigma_i-1/M$). Das löst
   alle Relationen und gibt $\Phi(t^*,0)-\Phi(0,t^*)=1/M$ (Theorem 19).
   Die Endlichkeit in `prop:atomicposet` ist damit unentbehrlich, und (F) ist
   im Halbordnungsfall scharf: unter Integrierbarkeit schließt auf der
   Antikette schon Fubini (Proposition 19.1). Zwei Befunde, die die
   Hypothesenwahl künftiger Läufe festlegen: das Gegenbeispiel hat
   **beschränktes $\Phi$** (drei Werte) — Korollar 14 ist ein Kettenphänomen
   und außerhalb von Ketten wertlos —, und es braucht $q(\{0\})=0$
   (Proposition 19.2), also genau die Bedingung, die `sharp.py` im dritten
   Lauf im Endlichen als notwendig gefunden hat; die Unendlichkeit kauft hier,
   was dort die negativen Massen kauften. Offen bleiben jetzt drei benannte
   Dinge: die Halbordnung **unter (F)**, die nackte Klasse auf Ketten
   (unverändert), und ob ein Gegenbeispiel mit durchweg positiven
   Abwärtsmassen existiert. Für das erste steht der Weg schon da: unter (F)
   trägt die Ausschöpfung wieder, aber mit der massegewichteten Supremumsnorm
   $\|T\|_m=\sup_{s,t}|T_{st}|/(m_sm_t)$ statt der Frobeniusnorm, an der der
   elfte Lauf gescheitert ist — $|\operatorname{tr}(TE)|\le4M\|T\|_m
   \varepsilon_F$ mit $\varepsilon_F=\sum_{a\notin F}m_a\sum_tm_t|\kappa(a,t)|
   \to0$, und das ist (F) (Proposition 19.3). Wer den Punkt aufnimmt, mißt
   zuerst $\|T\|_m$ für das explizite Zertifikat des sechsten Laufs auf den
   Familien von `Task23/dense.py`. `Task23/PROTOKOLL.md`, dreiundzwanzigster Lauf;
   `Task23/poset_infinite.py` (Proben (A)–(H), exakt, rc=0); Roadmapeinträge
   `duality_of_atomic_antichain_of_integrable` und
   `exists_atomic_antichain_duality_ne` in `MartingaleProblems`
   Meilenstein 8.

   *Zwischenstand 2026-09-04, vierundzwanzigster Lauf: die Ausschöpfung ist
   gemessen und erledigt; dafür fällt die Halbordnung unter (F), sobald ihre
   Unvergleichbarkeit transitiv ist.* Die vom dreiundzwanzigsten Lauf
   aufgegebene Rechnung — $\|T\|_m$ für das explizite Zertifikat des sechsten
   Laufs — steht in `Task23/certificate_m.py` (exakt, Konstruktion an
   $70\,956$ Fällen geprüft). Befund dreifach: auf der Antikette ist
   $\|T\|_m$ **gleichmäßig $1$** mit geschlossener Formel (Theorem 20), also
   schließt Proposition 19.3 dort und liefert Proposition 19.1 ohne Fubini;
   auf der dyadischen ordnungsdichten Uhr ist $\|T\|_m=1/m_{\min}^2$ exakt und
   $\varepsilon_F\|T\|_m\sim8^n\to\infty$ — und das auf einer **Kette**, wo
   Theorem 17 die Konklusion längst gibt, die Ausschöpfung ist damit als
   Methode erledigt (vierte Norm nach Frobenius, linear, quadratisch); und die
   „freie Wahl innerhalb von $\mathcal L$" ist ausgenutzt und wertlos — 37
   lineare Programme geben als Minimum von $\|\cdot\|_m$ durchweg genau den
   Wert des expliziten Zertifikats. Der Ertrag steht daneben: die gemessene
   **Breiteninvarianz** gestufter Halbordnungen ist eine Mittelung der Daten,
   nicht der Zertifikate, und gibt **Theorem 21** — auf jeder abzählbaren
   *schwachen Ordnung* (totale Präordnung, äquivalent: transitive
   Unvergleichbarkeit, äquivalent: Stapel von Antiketten) gilt die Dualität
   unter (F), mit Theorem 17 auf der Stufenkette. Das enthält Theorem 17 und
   Proposition 19.1 als die beiden Extremfälle und erlaubt unendlich breite
   Stufen. Offen bleibt jetzt die Halbordnung mit **nicht** transitiver
   Unvergleichbarkeit (kleinste Gestalt: ein unendliches „N"), dazu
   unverändert die nackte Klasse auf Ketten und das Gegenbeispiel mit
   durchweg positiven Abwärtsmassen. `Task23/PROTOKOLL.md`,
   vierundzwanzigster Lauf; `Task23/weakorder.py` (Proben (A)–(E), exakt,
   rc=0) und `Task23/certificate_m.py`; Roadmapeinträge `Clock.atomLayers`,
   `Clock.atomLayerKernel`, `atomLayerKernel_increment_eq`,
   `atomLayerKernel_rel` und `duality_of_atomic_weakOrder_of_integrable` in
   `MartingaleProblems` Meilenstein 8.

   *Zwischenstand 2026-09-04, fünfundzwanzigster Lauf: die Halbordnung mit
   nicht transitiver Unvergleichbarkeit fällt bei **endlicher Höhe**, und die
   Ausschöpfung war nie der Weg dorthin.* Statt Zertifikate auf endlichen
   Ausschnitten zu bauen und auf gleichmäßige Schranken zu hoffen, schreibt
   man das Zertifikat **direkt auf der unendlichen Halbordnung** hin: ein
   symmetrisches $T$ mit $|T_{su}|\le Cw_sw_u$ ($w=m+\mathbb 1_Z$, $Z$
   endlich), $TV=V^{\mathsf T}T$ und $T\mathbb 1=e_t$ schließt unter (F),
   weil die vier auftretenden Reihen absolut konvergieren und der Zweizeiler
   des sechsten Laufs dann wörtlich durchgeht (**Theorem 22**). Und die Formel
   des sechsten Laufs liefert ein solches $T$, sobald $V^r=0$ ist, also sobald
   die Ketten aus Atomen positiver Masse beschränkte Länge haben — die
   Schranke ist eine Zeile, $\|V^{\mathsf T}x\|_1\le M\|x\|_1$ und
   $|(V^{\mathsf T}x)_c|\le m_c\|x\|_1$ (**Theorem 23**). Damit gilt die
   Dualität unter (F) auf **jeder abzählbaren Halbordnung endlicher Höhe**,
   bei beliebiger, insbesondere nicht transitiver Unvergleichbarkeit und
   beliebig breiten Ebenen (Korollar 23.2): das unendliche „N", die Krone, die
   Leiter, und die Antikette als Fall $r=2$. Die Grenze ist scharf und benannt:
   auf einer Kette ohne kleinstes und ohne größtes Element existiert **kein**
   solches $T$ (**Proposition 23.1**) — dort trägt Theorem 17, und die beiden
   Methoden haben disjunkte blinde Flecken. Wer den Punkt aufnimmt, hat die
   Halbordnung **unendlicher** Höhe mit nicht transitiver Unvergleichbarkeit
   (kleinste Gestalt: zwei $\omega$-Ketten mit $a_i<b_j\iff i<j$), und der
   Weg steht da: das Problem ist in $m$ homogen, also darf man $M<1$ annehmen,
   $\sum_kV^k$ konvergiert auf $\ell^1$, und ein Zertifikat ist bei
   zyklischem $\mathbb 1$ dasselbe wie eine **Hankelform**
   $B(V^k\mathbb 1,V^l\mathbb 1)=c_{k+l}$ mit $c_k=(V^k\mathbb 1)_t$,
   $0\le c_k\le M^k$ — zu zeigen ist ihre Beschränktheit, hinreichend dafür
   ist, daß $(c_k)$ eine Momentenfolge auf $[0,M]$ ist. `Task23/PROTOKOLL.md`,
   fünfundzwanzigster Lauf; `Task23/finite_height.py` (Proben (A)–(E), exakt,
   rc=0); Roadmapeinträge `Clock.IsAtomCertificate`,
   `atomDiag_eq_zero_of_isAtomCertificate`,
   `exists_isAtomCertificate_of_finiteHeight`,
   `duality_of_atomic_finiteHeight_of_integrable` und
   `not_exists_isAtomCertificate_of_denseChain` in `MartingaleProblems`
   Meilenstein 8.

   *Zwischenstand 2026-09-05, sechsundzwanzigster Lauf: die Grenze ist nicht
   die Höhe, sondern die Fundiertheit — und der Hankelweg ist entwertet.*
   **Proposition 24.1**: hat $\T$ ein Maximum $t^*$ mit $m_{t^*}=0$ und ist die
   Atommenge $A$ nichtleer, abwärts gerichtet und **ohne minimales Element**,
   so gibt es kein unendliches Zertifikat an der Stelle $t^*$ — das
   verallgemeinert Proposition 23.1 (keine Kette nötig, größtes Element
   erlaubt) und ist kürzer, weil der Widerspruch aus der Symmetrie von $T$
   kommt. Umgekehrt hat die $\omega$-Kette, obwohl von unendlicher Höhe und mit
   nicht nilpotentem $V$, sehr wohl ein Zertifikat: $\|T\|_m$ konvergiert auf
   den Trunkierungen, für $m_i=\rho^{-i}$ exakt gegen $\rho^3/(\rho-1)^2$.
   **Proposition 24.2** löst dort die drei Bedingungen vollständig auf: die
   Spitzenzeile ist erzwungen ($T_{t^*\cdot}=e_{a_1}$), und der Atomblock ist
   genau eine symmetrische Funktion $\Phi$ auf $\N_0^2$ mit $\Phi(i,0)=0$, der
   Zwei-Diagonalen-Rekursion
   $(m_i-m_j)\Phi(i,j)=m_i\Phi(i,j-1)-m_j\Phi(i-1,j)$, der Schwanzbedingung
   $\Phi(i,k)\to[i=1]/m_1$ und der Lipschitzschranke
   $|\Phi(i,j)-\Phi(i,j-1)|\le Cm_j$. **Der Hankelweg des fünfundzwanzigsten
   Laufs trägt nicht**: auf der Leiter ist $\mathbb 1$ nicht zyklisch (Rang
   $n+2$ gegen Dimension $2n+2$), der Lösungsraum hat Dimension $n+2$ statt
   $1$, und in genau diesem Spielraum liegt die Lösung — deshalb läuft die
   explizite Formel des sechsten Laufs dort davon ($6190$ bei $n=12$), während
   das Minimum über alle Zertifikate bei $18$ stehenbleibt. Wer den Punkt
   aufnimmt, zeigt für die $\omega$-Kette, daß die Zwei-Diagonalen-Rekursion
   mit der Schwanzbedingung eine Lipschitzlösung hat — dieselbe Aufgabe wie im
   siebzehnten Lauf, nur mit Existenz statt Eindeutigkeit. Vermutung des
   Laufs: **fundiertes $A$** genügt für die Existenz.
   `Task23/PROTOKOLL.md`, sechsundzwanzigster Lauf;
   `Task23/infinite_height.py` (Proben (A)–(E), rc=0).

   *Zwischenstand 2026-09-05, siebenundzwanzigster Lauf: die $\omega$-Kette
   hat ein Zertifikat in geschlossener Form, und bei geometrisch fallenden
   Massen ist seine Existenz **bewiesen**.* Mit
   $\pi_k(i)=\prod_{l>i}(1-m_l/m_k)$ und
   $\beta_k=\bigl(m_k\prod_{l\ne k}(1-m_l/m_k)\bigr)^{-1}$ erfüllt die
   punktweise **endliche** Summe
   $\Phi(i,j)=\sum_{k\le\min(i,j)}\beta_k\pi_k(i)\pi_k(j)$ Symmetrie, Rand,
   Zwei-Diagonalen-Rekursion und Schwanzbedingung — **unbedingt**, ohne
   Hypothese an das Massenprofil außer der Verschiedenheit der Massen
   (Theorem 25); die Rekursion trägt bausteinweise wegen
   $w_k(i)-w_k(i-1)=\frac{m_i}{m_k}w_k(i)$, und die Schwanzbedingung ist die
   Residuensumme $-\sum_{k\le i}\operatorname{Res}_{c_k}\Pi_i(c)^{-1}$ mit
   $\Pi_i(c)=\prod_{l\le i}(1-cm_l)$. Damit sitzt die ganze Last auf
   Bedingung 1, also auf der Beschränktheit von
   $G(i,j)=-T_{a_ia_j}/(m_im_j)$; deren Limiten sind exakt
   ($1/m_1^2$, $-1/(m_1m_2)$, $0$ für $j=1,2,\ge3$, Korollar 25.1 — was die
   gemessene Form $\rho^3/(\rho-1)^2$ des sechsundzwanzigsten Laufs beweist),
   und $G(i,j)$ ist eine **dividierte Differenz** der Ordnung $j-1$ von
   $c\mapsto cP_{>i}(c)$ an den Knoten $1/m_k$ (Theorem 25.2), woraus bei
   $m_{l+1}\le\theta m_l$ die Schranke
   $\theta^{(j-1)(j-4)/2}$ und damit das Zertifikat folgt (Korollar 25.3).
   Der übertragbare Fund: $T=xx^{\mathsf T}$ ist mit Bedingung 2 genau dann
   verträglich, wenn $V^{\mathsf T}x\parallel x$ — auf der Trunkierung ist
   $V^{\mathsf T}$ nilpotent und hat keine Eigenvektoren, auf der unendlichen
   Kette ist $x_k=(0,(m_i\pi_k(i)[i\ge k])_i,-m_k)$ einer zum Eigenwert
   $-m_k$. Wer den Punkt aufnimmt, rechnet die Eigenvektoren von
   $V^{\mathsf T}$ auf der **Leiter** aus; offen bleiben ferner Bedingung 1
   ohne geometrische Hypothese (Vermutung
   $\sup|G|=\max(1/m_1^2,1/(m_1m_2))$; die Dreiecksungleichung reicht
   nachweislich nicht) und der Fall gleicher Massen.
   `Task23/PROTOKOLL.md`, siebenundzwanzigster Lauf; `Task23/omega_chain.py`
   (Proben (A)–(F), rc=0); Roadmapeinträge
   `Lagrange.sum_inv_prod_sub_eq_zero`, `Clock.atomTailProduct`,
   `Clock.atomTailProduct_sub_eq`, `Clock.omegaChainPotential` und
   `exists_isAtomCertificate_of_omegaChain` in `MartingaleProblems`
   Meilenstein 8.

7. **`MeasureTheory.HasLaw` prüfen und, wenn es trägt, übernehmen.** *(gestellt
   2026-09-09 vom Nutzer; **erst nach `jumpProcess_isMPSolution`**, nicht davor.)*

   Mathlib hat seit kurzem
   ```
   structure HasLaw (X : Ω → 𝓧) (μ : Measure 𝓧) (P : Measure Ω) : Prop where
     protected aemeasurable : AEMeasurable X P
     protected map_eq : P.map X = μ
   ```
   (`Probability/HasLaw.lean:39`), also genau das Paar, das unsere drei Dateien
   überall von Hand mitführen — `HasLaw` selbst kommt in keiner von ihnen vor.
   Dafür spricht: es bündelt die zwei Verpflichtungen, trägt `@[fun_prop]` auf
   der Meßbarkeit, und es ist die Vokabel, in der Mathlib inzwischen über
   Verteilungen spricht, was für eine Roadmap ein Wert an sich ist.

   **Die Frage, die zu beantworten ist, bevor irgend etwas umgestellt wird:**
   `HasLaw` verlangt `AEMeasurable X P`, also Meßbarkeit modulo einer Nullmenge
   *eines festen* `P`. Unsere Sprungkonstruktion arbeitet seit dem 2026-09-09
   mit **Kernen** — `jumpKernel` statt `jumpMeasure` war die Antwort darauf, daß
   sich über bloßem `[MeasurableSpace E]` sonst nichts hinschreiben ließ — und
   liefert echte Meßbarkeit. Trägt `HasLaw` die Kernfassung, oder erzwingt es den
   Rückschritt auf ein festes Anfangsgesetz? Prüfe das an
   `jumpMeasure_map_chain_zero` und an `integral_jumpKernel_zero_eq`, **ehe** Du
   umschreibst; kommt heraus, daß es nicht trägt, so ist das der Befund und die
   Umstellung unterbleibt.

   Umfang, falls es trägt: jede Gesetzesaussage in `MartingaleProblems`, dazu die
   `P.map (X n) = μ n` in `WeakConvergence`. Mechanisch, aber breit — deshalb
   nicht vor dem offenen Beweis.
