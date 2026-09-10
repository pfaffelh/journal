Du arbeitest autonom und unbeaufsichtigt am **Formalisierungs-Inventar** des
Manuskripts `Journal/Blog/MartingaleProblem/MartingaleProblem.tex`. Du bist in
einem git-Worktree auf dem Branch `facts-inventory`. Zeitbudget: 120 Minuten.

## Vorrangige Aufgaben

### ~~SPARLAUF — gilt nur für Läufe am 2026-09-09 nach 16:00~~ *(gestellt vom Nutzer, erledigt 2026-09-09, zwanzigster Lauf des Tages)*

**Ergebnis.** `jumpMeasure_integral_eq_of_firstJump` ist bewiesen, samt drei
Hilfssätzen (`jumpTime_one`, `jumpProcess_of_lt_jumpTime_one`,
`comp_chainKernel_map_zero`); ganze Datei durch `lake env lean` gegen v4.33.1,
alle vier mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`.
Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-09, zwanzigster Lauf des Tages".
Damit gilt wieder Teil C der Aufgabe darunter; sein Punkt 2 schuldet nur noch die
Markoveigenschaft für den zweiten Term der Zerlegung.


Stehen hier Aufgaben, so haben sie Vorrang vor allem Übrigen, in der genannten
Reihenfolge. Ist eine erledigt, streicht der Lauf sie hier heraus und trägt das
Ergebnis an der genannten Stelle ein; sind alle erledigt, gilt wieder die
Reihenfolge weiter unten. Eine Aufgabe, die mehr als einen Lauf braucht, wird
nicht gestrichen, sondern um einen Zwischenstand ergänzt.

### Aufgabe: `SkorokhodSpace` fertig, dann Meilenstein 4 von `MartingaleProblems` *(gestellt 2026-09-08 vom Nutzer)*

Drei Teile, streng nacheinander. Ein Teil wird **nicht** angefangen, solange ein
früherer offen ist. (Reihenfolge vom Nutzer am 2026-09-09 so festgelegt: erst
der Pfadraum, dann die schwache Konvergenz fertig, dann die Prozesse.)

~~**Teil A — `SkorokhodSpace` zu Ende bringen.**~~ *(erledigt 2026-09-09,
dreizehnter Lauf des Tages)*

**Ergebnis.** `SkorokhodSpace/Suggested.lean` trägt **kein `sorry`** mehr. Alle
vier Punkte des Auftrags sind erledigt: `instSeparableSpace` (vierter Lauf), die
meßbare Einbettung samt `measurable_eval` (fünfter Lauf, Meilenstein 6
geschlossen), das Kompaktheitskriterium `isCompact_closure_iff` (dreizehnter
Lauf, Meilenstein 7 geschlossen) und `exists_orderIso_isometry_real`
(2026-09-08, vierundzwanzigster Lauf). Offen bleibt allein die dritte Instanz
von `HasCountableCore` (`Set.Icc (0:ℝ) 1`), an der nichts hängt.

Die dreizehn Zwischenstände dieser Läufe standen bis zum vierzehnten Lauf des
2026-09-09 hier und sind herausgestrichen; sie stehen vollständig in
`Facts/INVENTAR.md` unter „Läufe", 2026-09-08 (sechzehnter bis
fünfundzwanzigster Lauf) und 2026-09-09 (erster bis dreizehnter Lauf). Vier
Befunde daraus sind für die weitere Arbeit wichtig genug, um hier zu bleiben:

* **`SeparableSpace D(ι, E)` ist ohne Zusatzhypothese falsch**
  (`not_separableSpace_of_rigid`, Zeuge Cantormenge). Die Instanz und
  `instPolishSpace` tragen die Typklasse `SkorokhodSpace.HasCountableCore ι`,
  bewiesen für `ℝ` und für jeden abzählbaren Index.
* **Das Kompaktheitskriterium ist zweimal berichtigt worden**, beide Male an der
  Unterteilung: sie darf über die Fensterenden hinausragen
  (`not_tendsto_iSup_modulusPinned`) und sie muß den **Basispunkt als Knoten**
  haben (`not_isCompact_closure_of_jumps_at_basePoint`). Es heißt darum
  `modulusBased`, und seine Rückrichtung steht über `ℝ`.
* **Die Metrik ist ein Integral über den reellen Radius** (`intDist`), nicht eine
  Summe über ganzzahlige Fenster; die summierte Fassung machte die Auswertung an
  jedem Fensterrand stetig und `CompleteSpace` falsch.
* **Zwei acceptance examples trugen falsche Zusagen** und wurden nie gegen sie
  gehalten (2026-09-08 und 2026-09-09, fünfter Lauf). Ein acceptance example, das
  nur dasteht, prüft nichts.

~~**Teil B — `WeakConvergence` fertigmachen.**~~ *(erledigt 2026-09-09,
sechzehnter Lauf des Tages)*

**Ergebnis.** `WeakConvergence/Suggested.lean` trägt **kein `sorry`** mehr.
Beide Punkte des Auftrags sind erledigt:
`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws` (vierzehnter Lauf)
und `exists_ae_tendsto_of_tendsto`, die Skorohod-Darstellung (sechzehnter
Lauf), letztere mit `#print axioms` auf `propext`, `Classical.choice`,
`Quot.sound`. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-09, sechzehnter
Lauf des Tages"; Meilenstein 3 von `WeakConvergence` ist geschlossen. Der
einzige Fehler, den die Datei noch meldet, ist der bekannte in Zeile 2178: sie
ist für `upstream/master` geschrieben, wo `ProbabilityMeasure.map` die Funktion
allein nimmt. Ohne Signatur bleiben von Meilenstein 4 die
de-la-Vallée-Poussin-Form und die vier Stabilitätslemmata; Meilenstein 6 (der
Raum `M_E`) steht seit dem elften Lauf des 2026-09-08 als eigene Aufgabe da.

Zwei Befunde daraus sind für die weitere Arbeit wichtig genug, um hier zu
bleiben:

* **Nur einer der beiden Disjunkte des schlechten Ereignisses wird summiert.**
  Die Stücke `{z | z.1.1 ∈ A^{(m)} 0}` haben Masse `≤ 2⁻ᵐ` und kosten eine
  geometrische Reihe; die Stücke `{z | 1 - 1/m < z.1.2}` sind Ereignisse der
  **einen** gemeinsamen gleichverteilten Variablen, schachteln sich und fallen
  über `m ≥ K` zu `{ξ > 1 - 1/K}` zusammen, Masse `1/K`. Summierte man auch
  sie, käme `∑ 1/m = ∞` heraus. Das ist der Punkt, an dem der Aufbau von
  `stagesMeasure` bezahlt wird, und der Grund, aus dem
  `ae_tendsto_of_subset_of_tendsto_measure_iUnion_ge` nach den **Schwänzen**
  fragt und nicht nach den Gliedern.
* **`Q 1 n` gilt immer**, weil `ofReal (1 - 1/1) = 0` ist; das macht die
  Niveauwahl `kn` total, ohne Fallunterscheidung.

*Der ursprüngliche Wortlaut des Teils:*

1. ~~`tendsto_integral_of_tendsto_of_isUniformlyIntegrableLaws`~~ *(erledigt
   2026-09-09, vierzehnter Lauf des Tages)*. Bericht in `Facts/INVENTAR.md`,
   Läufe, „2026-09-09, vierzehnter Lauf des Tages". Sieben neue Deklarationen,
   eine von `sorry` zu einem Beweis geworden und eine umgeschrieben; alle durch
   `lake env lean` gegen v4.33.1 geprüft und alle
   mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`.

   Der angesagte Weg über die **Skorohod-Darstellung** ist nicht gegangen worden
   und wird nicht gebraucht — er hätte diesen Meilenstein an Punkt 2 gehängt. Der
   Beweis ist die Abschneidung: `truncBdd N` ist die auf `[-N, N]` geklemmte
   Identität als `ℝ →ᵇ ℝ`, und `abs_sub_truncBdd` sagt, daß ihr Abschneidefehler
   **auf die Nase** der Integrand des Kriteriums ist. Der einzige nicht
   elementare Schritt ist der Schwanz des **Grenzgesetzes**, das kein Glied der
   Familie ist; er kommt aus der Portmanteau-Ungleichung für nichtnegative
   stetige Funktionen (`lintegral_truncTail_le_of_tendsto`). Mitgekommen:
   `integrable_id_of_lintegral_truncTail_lt_top` (ein Maß, ein Niveau — die
   Familienfassung erreicht das Grenzgesetz nicht) und
   `tendsto_integral_of_tendstoInDistribution_of_uniformIntegrable`, die Fassung
   mit Mathlibs `TendstoInDistribution`, die der Meilenstein dem Wortlaut nach
   verlangt. Ohne Signatur bleiben von Meilenstein 4 die
   de-la-Vallée-Poussin-Form und die vier Stabilitätslemmata.
2. `exists_ae_tendsto_of_tendsto` — die Skorohod-Darstellung, der Zusammenbau.
   Alle Bausteine stehen.

   **Zwischenstand 2026-09-09, fünfzehnter Lauf des Tages.** Das letzte Stück vor
   dem Zusammenbau ist bewiesen: `exists_measurable_pair_of_partition_subset`,
   alle Stufen auf **einem** Raum (`stagesMeasure` auf `(E × ℝ) × (ℕ × ℕ → E)`),
   mit einer allen Stufen gemeinsamen gleichverteilten Variablen und der
   Stufenschranke als **Inklusion**. Dazu `sum_prod_slice_eq` und je ein Zusatz
   an `exists_coupling_tsum_offDiag_le` (`min (p i) (q i) ≤ π i i`) und an
   `exists_finite_partition_diam_le_null_frontier`
   (`∀ i ∈ K, Bornology.IsBounded (A i)`). Alle durch `lake env lean` gegen
   v4.33.1 und mit `#print axioms` geprüft. Bericht in `Facts/INVENTAR.md`,
   Läufe, „2026-09-09, fünfzehnter Lauf des Tages".

   **Zwei Berichtigungen daraus, die der nächste Lauf braucht.** Der zweite
   Disjunkt heißt `1 - t n < ξ` und nicht `ξ ≤ t` — der Diagonalzweig legt die
   Diagonale auf das *erste* Teilsummenintervall, also liegt die Uneinigkeit der
   Indizes **oberhalb** einer Schwelle nahe `1`. Und die Aussage des Zusammenbaus
   selbst stand im falschen Universum: `∃ (Ω : Type)` ist nicht der Satz, weil
   der Raum in `Type u` liegt und ein `Type 0`-Raum den Borelschen
   Isomorphiesatz erzwänge; sie heißt jetzt
   `exists_ae_tendsto_of_tendsto.{u} {F : Type u}` und trägt weiter ihr `sorry`.
   *(Nachtrag: das `sorry` ist im sechzehnten Lauf gefallen; beide
   Berichtigungen haben sich beim Ausschreiben als richtig erwiesen.)*

   **Was noch fehlt, in vier Schritten** (ausgeschrieben im Laufbericht und in
   `WeakConvergence/README.md`, Meilenstein 3): die Stufen `A^{(k)}` mit
   `ε = η = 2⁻ᵏ`; die Niveauwahl
   `kn n = max ((Finset.Icc 1 (n+1)).filter (Q · n))` zum Prädikat
   `Q k n : ∀ i ∈ K k, ofReal (1 - 1/k) * ν (A^{(k)} i) ≤ μ n (A^{(k)} i)`, die
   total ist, weil `Q 1 n` immer gilt; die Anwendung des Stufensatzes; und die
   einzige noch ungeschriebene Rechnung
   `P (⋃ m ≥ K, B m) ≤ ∑_{m ≥ K} 2⁻ᵐ + 1/K → 0` mit
   `B k = {z | z.1.1 ∈ A^{(k)} 0} ∪ {z | 1 - 1/k < z.1.2}`.

   **Zur Vorgeschichte, damit sie sich nicht wiederholt:** der Bauplan ist
   zweimal verworfen worden — das Verkleben einstufiger Kopplungen zugunsten des
   Alles-auf-einmal-Raums `(E × ℝ) × (ℕ × ℕ → E)`, und danach der Schluß über
   Borel--Cantelli, den es nicht gibt (die Schranke einer Stufe darf beliebig
   langsam fallen; Zeuge `ν = δ₀`, `μ n = (1-1/log n)·δ₀ + (1/log n)·δ₁`). Was
   trägt, ist EK Thm. 3.1.8, Buchseiten 102--103: **eine** allen Stufen
   gemeinsame gleichverteilte Variable, eine **Inklusion** statt einer Zahl,
   endlich viele Stücke positiver Masse. Wer den Plan ein drittes Mal ändern
   will, sagt zuerst, welcher Schritt des jetzigen bricht, und rechnet ihn am
   Zeugen nach.

**Teil D — die Roadmaps gegen Mathlib `master` prüfen.** Nach Teil C, vor allem
anderen. Das ist Rückstaupunkt 5, vom Nutzer am 2026-09-10 vorgezogen.

Unsere vier `README.md` und die drei `Suggested.lean` zitieren Mathlib-Namen mit
**Datei und Zeile**. Die letzte Prüfung ist vom 2026-09-06; seither sind vier
Tage vergangen, und die Bibliothek bewegt sich. Eine Roadmap, die auf einen
Namen zeigt, den es nicht mehr gibt, ist schlimmer als eine, die schweigt.

Zu tun, in dieser Reihenfolge:

1. Frisches `upstream/master` holen und den Commit im Bericht **nennen**.
2. Jeden zitierten Namen prüfen: existiert er noch, heißt er noch so, steht er
   noch in der genannten Datei? Zeilennummern sind nachrangig — falsch ist ein
   verschwundener oder umbenannter *Name*, nicht eine verschobene Zeile.
3. Jede **Negativaussage** nachprüfen — „Mathlib hat X nicht". Davon stehen
   inzwischen viele in den Roadmaps und in `TODO.md` Punkt 8, und jede ist ein
   Versprechen an einen Leser. Ist eine inzwischen falsch, ist das der wertvollste
   Fund des Laufs.
4. Die drei `Suggested.lean` gegen v4.33.1 übersetzen (das ist unsere Bindung),
   und **zusätzlich** melden, welche Deklarationen auf `master` brechen würden,
   soweit das ohne Umbau erkennbar ist.

Was **nicht** zu tun ist: auf `master` umstellen. Wir sind an v4.33.1 gebunden,
und die eine bewußt gegen `master` geschriebene Aussage in
`WeakConvergence/Suggested.lean` bleibt, wie sie ist.

**Teil E — Meilenstein 6 von `MartingaleProblems`.** Nach Teil D.

Der abstrakte Eindeutigkeitssatz `thm:absuniq`, und er hat in Lean **keine
einzige Deklaration**, während sein Unterbau — Meilenstein 5, `restart` — bewiesen
dasteht. Fünf Aussagen sind im `README.md` ausformuliert:
`isMarkov_of_unique_onedim`, `subsingleton_mpSolutions_of_unique_onedim`,
`eq_of_forall_onedim`, die klassische Fassung als Instanz, und `isStrongMarkov`.

Zwei Dinge, die dabei nicht verlorengehen dürfen:

* **Markov ist die Konklusion, nicht die Voraussetzung.** Ethier--Kurtz 4.4.1
  läuft andersherum und sitzt auf Hille--Yosida; das ist ausdrücklich nicht
  unsere Richtung (`rem:noch1`). Wer die Aussage so hinschreibt, daß sie Markov
  voraussetzt, hat einen anderen Satz.
* **Die Eindeutigkeit der eindimensionalen Verteilungen muß für *jeden* Shift
  `r` gelten**, nicht nur bei `r = 0` — die endlichdimensionalen Verteilungen
  werden über `restart` aus den geshifteten Problemen gebaut. Das
  Akzeptanzbeispiel dazu steht im Meilenstein und ist der Prüfstein.

**Teil C — Meilenstein 4 von `MartingaleProblems`, die Sprungprozesse.** Teil A
und Teil B sind beide durch (2026-09-09, dreizehnter und sechzehnter Lauf), also
gilt dieser Teil. Er ist damit der laufende Auftrag.

Der Grund, und er ist kein ästhetischer: **die Existenztheorie hat sonst keinen
Boden.** §`sec:Existence` des Manuskripts hat drei Zweige, und zwei davon sind
relativ — aus einem dualen Prozeß (`thm:exduality`; Meilenstein 12 ist
ausdrücklich *not to be attempted as stated*, weil Kolmogorov für überabzählbaren
Index fehlt) und aus Konvergenz (`thm:absconv`, das die Approximanten schon
voraussetzt). Der dritte, die Übergangshalbgruppe, ist durch `rem:noch1`
ausgeschlossen: kein Hille--Yosida, kein Kapitel 1 von Ethier--Kurtz. Bleibt
`thm:jumpMP`, und das ist die **einzige Konstruktion von Hand**. Ohne sie steht
in keiner der drei Dateien ein Prozeß, von dem in Lean bewiesen wäre, daß er ein
Martingalproblem *löst* — die Münze aus `AtomWitness` ist ein Gegenbeispiel, kein
Beispiel.

Der Meilenstein steht ausformuliert in `TauCeti/MartingaleProblems/README.md`.
Reihenfolge:

*Reihenfolge, auf Wunsch des Nutzers: erst das eigentliche Ziel, die Beispiele
danach.*

0. ~~**`IsStepPath` zuerst, als Prädikat.**~~ *(erledigt 2026-09-09, sechzehnter
   Lauf des Tages)* Drei Deklarationen in
   `TauCeti/MartingaleProblems/Suggested.lean`: `IsStepPath`,
   `IsStepPath.isCadlagPath` und `IsStepPath.finite_setOf_not_continuousAt_inter`,
   alle bewiesen und mit `#print axioms` geprüft. Der Punkt ist als **Prädikat**
   umgesetzt, wie verlangt, und nicht als Typklasse.

   **Aber die unten angesagte Definition ist nicht genommen worden, weil die
   angesagte Brücke falsch ist.** `Function.leftLim` ist total: existiert kein
   linksseitiger Limes, gibt es `f x` zurück. Damit hat ein Pfad ohne
   linksseitige Limiten eine **leere** Sprungmenge, und eine Bedingung an die
   Sprungmenge allein sieht keine der beiden Hälften von càdlàg. Zeuge gegen
   `IsStepPath f → IsCadlag f` in der Fassung unten:
   `f = Set.indicator {0} 1` auf `ℝ`, Sprungmenge `{0}`, an `0` nicht
   rechtsstetig; in Lean als
   `exists_finite_setOf_leftLim_ne_not_isCadlagPath`. Genommen ist statt dessen,
   was die Konstruktion wirklich liefert — zwischen zwei Sprungzeiten bewegt
   sich der Pfad nicht:
   ```
   def IsStepPath (f : ι → E) : Prop :=
     (∀ x, ∀ᶠ y in 𝓝[≥] x, f y = f x) ∧ ∀ x, ∃ c, ∀ᶠ y in 𝓝[<] x, f y = c
   ```
   Die lokale Endlichkeit der Unstetigkeitsstellen ist daraus ein **Satz**.
   Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-09, sechzehnter Lauf des
   Tages", Abschnitt „Derselbe Lauf, zweiter Teil".

   *Der ursprüngliche Wortlaut:* Die Konstruktion liefert Pfade, die in
   endlicher Zeit nur endlich oft springen, und drei sonst unangenehme Stellen
   werden auf ihnen leicht: die Meßbarkeit in `(t, ω)` ist eine Summe über
   endlich viele Stücke statt eines Grenzwertarguments, `Nat.find` für die
   Zuordnung `t ↦ n` ist formbar, und càdlàg folgt. Also
   ```
   def IsStepPath (f : ι → E) : Prop :=
     ∀ K : Set ι, IsCompact K → (leftJumpSet f ∩ K).Finite
   ```
   mit der Brücke `IsStepPath f → IsCadlag f`. **Keine Typklasse** — es ist eine
   Eigenschaft eines Terms, die Instanzensuche hätte nichts, woran sie ansetzt,
   und Mathlibs Ausweichkonstruktion `Fact` ist ausdrücklich nicht dafür gedacht
   (`Logic/Basic.lean:167`, library_note „fact non-instances"). Erst wenn mehr
   als zwei Sätze sie tragen, wird daraus eine gebündelte Struktur nach dem
   Muster von `D(ι, E)`. Die halbe Arbeit steht schon:
   `IsCadlag.finite_largeLeftJumpSet_inter` in `SkorokhodSpace/Suggested.lean`
   sagt dasselbe für die **großen** Sprünge und ohne Zusatzvoraussetzung; hier
   sind es alle. Das Manuskript nennt die Menge dieser Pfade `F` in
   `set:pathjump`.
1. ~~`jumpProcess lam mu nu` als Konstruktion auf einem expliziten
   Wahrscheinlichkeitsraum, mit càdlàg und stückweise konstanten Pfaden.~~
   *(erledigt 2026-09-09, siebzehnter Lauf des Tages)* Dreiunddreißig
   Deklarationen im Abschnitt `JumpConstruction` von
   `TauCeti/MartingaleProblems/Suggested.lean`, alle bewiesen und dreißig davon
   einzeln mit `#print axioms` geprüft. Bericht in
   `Facts/INVENTAR.md`, Läufe, „2026-09-09, siebzehnter Lauf des Tages".

   Der Raum ist `(ℕ → E) × (ℕ → ℝ)` mit
   `jumpMeasure mu nu = (chainKernel mu ∘ₘ nu).prod waitingMeasure`;
   `jumpMeasure_map_chain_zero` sagt, daß das Anfangsgesetz `nu` ist,
   `measurable_jumpProcess` gibt die Meßbarkeit in `(t, ω)`, und
   `isStepPath_jumpProcess`/`isCadlagPath_jumpProcess` die Pfade.

   **Der angesagte Unterbau war zur Hälfte der falsche.**
   `exists_kernel_pi_of_markov` ist das **Produkt** von Kernen (die Kerne lesen
   nur den Basispunkt) und gibt überdies allein die Randverteilungen heraus,
   nicht das gemeinsame Gesetz; für die Kette ist Mathlibs
   `ProbabilityTheory.Kernel.traj` unmittelbar zu nehmen, mit der Familie, die
   die **letzte** Koordinate liest. Für die Wartezeiten ist es nicht
   `exponentialPDF`, sondern `MeasureTheory.Measure.infinitePi` über
   `ProbabilityTheory.expMeasure 1`, weil dieses die Unabhängigkeit mitbringt.
   Richtig war: keiner der beiden braucht eine Topologie auf `E`.

   **Zwei Befunde für die weitere Arbeit.** (a) Die Pfadsätze stehen unter
   `StrictMono T` und nicht `Monotone T`; die Differenz ist genau der Fall, in
   dem `x` selbst eine Sprungzeit ist. (b) **Die Positivität der Rate ist eine
   echte Einschränkung**: `x / 0 = 0` in Lean, also verläßt der Pfad einen
   Zustand mit `lam x = 0` — den das Modell absorbierend meint — sofort. Der
   absorbierende Fall verlangt Sprungzeiten in `ℝ≥0∞`; Punkt 2 braucht ihn
   nicht, Punkt 5 (der lokale Fall) wird ihn nicht umgehen können.

   ~~**Was noch fehlt, und es ist klein:** die beiden f.s.-Aussagen über
   `waitingMeasure`.~~ *(erledigt 2026-09-09, achtzehnter Lauf des Tages)* Zehn
   weitere Deklarationen, alle bewiesen und alle mit `#print axioms` geprüft;
   `ae_isStepPath_jumpProcess` und `ae_isCadlagPath_jumpProcess` sind jetzt
   **unbedingte** f.s.-Aussagen über `jumpMeasure mu nu` unter `0 < lam ≤ L`
   allein. Punkt 1 ist damit vollständig. Bericht in `Facts/INVENTAR.md`, Läufe,
   „2026-09-09, achtzehnter Lauf des Tages".

   **Der angesagte Weg zur Unabhängigkeit war ein Umweg, und der Befund gehört
   zur Suchregel.** `iIndepFun_iff_map_fun_eq_infinitePi_map` liefert
   `iIndepFun` der Koordinaten, und `measure_limsup_eq_one` verlangt
   `iIndepSet` der Ereignisse; von dem einen zum anderen hat Mathlib **kein**
   Lemma. Genommen ist `ProbabilityTheory.iIndepSet_iff_meas_biInter`
   (`Independence/Basic.lean:623`), das sagt, daß `iIndepSet` *die
   Produktformel für endliche Durchschnitte ist* — und die ist für
   Koordinatenereignisse `MeasureTheory.Measure.infinitePi_pi`. Sieben Zeilen
   statt eines eigenen Bausteins.
2. ~~`jumpProcess_isMPSolution` für beschränktes `lam` — das ist `thm:jumpMP`, und
   es ist **das eigentliche Ziel des Meilensteins**: die erste in Lean bewiesene
   Lösung eines Martingalproblems überhaupt.~~ *(erledigt 2026-09-10, dritter
   Lauf des Tages)*

   **Ergebnis.** `jumpProcess_isMPSolution` ist bewiesen, und Meilenstein 4 von
   `MartingaleProblems` trägt in `Suggested.lean` **kein `sorry`** mehr (die
   Datei steht bei neun, alle in den Meilensteinen 3, 5, 9 und 10). Der
   Abschluß kostete drei Deklarationen — `abs_setIntegral_compensator_le`,
   `integrable_mpFamily_jumpProcess` und den Satz selbst —, die ganze Datei
   geht durch `lake env lean` gegen v4.33.1 ohne einen Fehler, und alle drei
   sind mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`
   geprüft. Über `E` steht nichts als `[MeasurableSpace E]`.

   Die neun Zwischenstände der Läufe achtzehn bis siebenundzwanzig des
   2026-09-09 und der Läufe eins bis drei des 2026-09-10 standen bis zum
   dritten Lauf des 2026-09-10 hier und sind herausgestrichen; sie stehen
   vollständig in `Facts/INVENTAR.md` unter „Läufe". Fünf Befunde daraus sind
   für die weitere Arbeit wichtig genug, um hier zu bleiben:

   * **`Clock.IsProgressive` ist für den Sprungprozeß vermutlich nicht
     beweisbar** und wird nicht gebraucht. Ein Limes `E`-wertiger meßbarer
     Abbildungen ist nur meßbar, wenn die Diagonale von `E` es ist. Der
     Kompensator wird statt dessen über
     `measurable_uncurry_min_of_eventuallyEq` in `ℝ` behandelt, für jedes
     reelle Funktional `h ∘ X`. Wer `isMPSolution_iff_forall_fdd` benutzen
     will, stößt außerdem darauf, daß **dieser Satz selbst ein `sorry` trägt**
     (`Suggested.lean:382`).
   * **Die Positivität der Rate ist eine echte Einschränkung**: `x / 0 = 0` in
     Lean, also verläßt der Pfad einen Zustand mit `lam x = 0` sofort. Der
     absorbierende Fall verlangt Sprungzeiten in `ℝ≥0∞`; Punkt 5 wird ihn nicht
     umgehen können.
   * **Die Explosionsmenge ist eine Nullmenge, aber nicht die leere Menge, und
     die beiden Hälften von `Martingale` gehen verschieden mit ihr um.**
     `StronglyAdapted` ist keine f.s.-Aussage, also muß die Meßbarkeit des
     Kompensators an *jedem* Punkt gelten (darum ist
     `eventuallyEq_nhdsGE_stepPath` ohne jede Hypothese bewiesen); die bedingte
     Erwartung dagegen darf schneiden, und `IsPastFunctional` tut es.
   * **`0 < L` ist kein Zusatz, sondern abgeleitet**: aus
     `[IsProbabilityMeasure nu]` folgt `Nonempty E`, und dort ist
     `0 < lam x ≤ L`.
   * **Zwei Lücken in Mathlib, die dabei geschlossen wurden und die auch sonst
     brauchbar sind**: `expMeasure_Ioi_add`, die Gedächtnislosigkeit der
     Exponentialverteilung, und `integral_expMeasure_one`,
     `∫ F d(expMeasure 1) = ∫_{Ioi 0} exp(-s) F s`, ohne jede Voraussetzung an
     `F`. Ebenso fehlt Mathlib die Zeithomogenität von
     `ProbabilityTheory.Kernel.traj` (hier `chainKernel_map_shift`) und die
     Abspaltung einer Koordinate von ihrem Schwanz bei `Measure.infinitePi`
     (hier `infinitePi_map_natCons`).
3. ~~`norm_apply_le` und `exists_unique_of_bounded`, die Picard-Iteration; nach der
   Roadmap „no analysis beyond `NormedSpace`".~~ *(erledigt 2026-09-10, sechster
   Lauf des Tages)*

   **Ergebnis.** `exists_unique_of_bounded` steht ganz, endlichdimensionale
   Verteilungen eingeschlossen; damit trägt Meilenstein 4 von
   `MartingaleProblems` keine offene Zusage mehr außer den Punkten 5 (lokaler
   Fall) und der pfadabhängigen Variante. Siebzehn neue Deklarationen, die ganze
   Datei ohne einen Fehler durch `lake env lean` gegen v4.33.1, alle siebzehn mit
   `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft; die
   Zahl der `sorry` bleibt bei neun (Meilensteine 3, 5, 9, 10). Bericht in
   `Facts/INVENTAR.md`, Läufe, „2026-09-10, sechster Lauf des Tages".

   Der Schlußstein ist
   `integral_fddProd_eq_of_isMPSolution_of_map_eq`: zwei Lösungen desselben
   beschränkten Sprungerzeugers mit demselben Anfangsgesetz, auf zwei
   verschiedenen Räumen, haben dieselben **endlichdimensionalen** Verteilungen.
   `jumpMeasure_integral_fddProd_eq_fddExp` sagt dasselbe vom konstruierten
   Prozeß gegen `nu`.

   **Vier Befunde, die zu behalten sind.**

   * **Der Faktor der Vergangenheit muß eine beschränkte Funktion sein und darf
     keine Indikatorfunktion bleiben.** Der Vorschlag des fünften Laufs lautete
     `∫_S f (X (s+t)) dP` über Mengen `S ∈ 𝓕 s`; das trägt die Induktion
     **nicht**, denn beim Abschälen des ersten Faktors entsteht `K ω · g (X (s+t) ω)`,
     und `g` ist keine Indikatorfunktion. Die Fassung mit dem Faktor kostet
     nichts mehr: `MeasureTheory.condExp_stronglyMeasurable_mul_of_bound` zieht
     ihn aus der bedingten Erwartung, `integral_condExp` setzt die Erwartung
     zurück (`integral_mul_eq_of_martingale`).
   * **Die Picard-Iteration ist einmal geschrieben, nicht zweimal.**
     `abs_sub_sum_le_of_recursion` läuft über ein abstraktes Funktional
     `I : ℝ≥0 → (E → ℝ) → ℝ` mit drei Voraussetzungen — Schranke, gemeinsame
     Meßbarkeit in der Zeit, Rekursion —, und die unbedingte wie die bedingte
     Fassung sind Korollare. Die alte `abs_integral_sub_sum_le_of_isMPSolution`
     ist auf sechs Zeilen zusammengeschrumpft.
   * **Die endlichdimensionale Testvariable ist eine Liste von Zuwächsen**
     (`fddProd`, `fddExp`) und keine `Fin n`-indizierte Familie. Der Grund ist
     die Induktion: das Abschälen des ersten Faktors läßt eine Liste derselben
     Gestalt stehen, von der späteren Zeit aus gelesen, während eine
     `Fin n`-Familie bei jedem Schritt umindiziert werden müßte.
   * **`IsMPSolution` liefert die Adaptiertheit von `X` nicht.** Das
     `StronglyAdapted`, das `Martingale` trägt, betrifft die **kompensierten**
     Prozesse, nicht `h ∘ X`. Der endlichdimensionale Satz führt darum die
     Voraussetzung `hXad` mit; ohne sie ist der abgeschälte Faktor
     `g (X (s+t))` nicht meßbar für `𝓕 (s+t)` und damit im nächsten Schritt gar
     kein Faktor der Vergangenheit. Für den konstruierten Prozeß ist sie eine
     Zeile (`stronglyMeasurable_jumpFiltration`).
   * **Eine Koordinate prüft die Schachtelungsreihenfolge nicht, zwei prüfen
     sie.** `jumpMeasure_integral_fddProd_flip` rechnet an der Zweizustandskette
     „bei `t` in `true` und bei `t + u` in `true`" = `(1-e^{-2t})/2 ·
     (1+e^{-2u})/2` aus; eine umgekehrt geschachtelte `fddExp` gäbe
     `(1-e^{-2u})/2 · (1+e^{-2t})/2`, eine andere Zahl für `t ≠ u`. Sie ging
     beim ersten Durchlauf durch.

   *Der ursprüngliche Wortlaut des Punktes und seine Zwischenstände:*

   **`norm_apply_le` ist erledigt** (2026-09-09, achtzehnter Lauf des Tages), als
   `abs_jumpApply_le` in punktweiser Gestalt
   `(∀ x, |f x| ≤ C) → |jumpApply lam mu f x| ≤ 2 * L * C`. Es ist außer der
   Reihe gefallen, weil es beim Hinschreiben des Erzeugers ohnehin anfiel und
   vier Zeilen kostete. **Punkt 2 ist durch, also ist dies der laufende
   Auftrag.**

   **Zwischenstand 2026-09-10, vierter Lauf des Tages.** Die
   **eindimensionale Hälfte** von `exists_unique_of_bounded` steht:
   `integral_eq_expJumpApply_of_isMPSolution` und, als Lesart davon,
   `integral_eq_of_isMPSolution_of_map_eq`. Vierzehn Deklarationen, Abschnitt
   `Uniqueness`; Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-10, vierter
   Lauf des Tages".

   **Zwischenstand 2026-09-10, fünfter Lauf des Tages.** Der **konstruierte**
   Prozeß erfüllt jetzt beide Voraussetzungen jenes Satzes, und damit ist die
   zweite Zusage des Punktes — „die eindimensionalen Verteilungen sind
   `nu.map (exp (t • A))`" — für einen benannten Prozeß bewiesen:
   `jumpMeasure_integral_jumpProcess_eq_expJumpApply`. Die dabei verlangte
   gemeinsame Meßbarkeit ist die für die **volle** σ-Algebra
   (`measurable_uncurry_comp_jumpProcess`, zwei Zeilen aus
   `measurable_jumpProcess`) und **nicht** das gefilterte
   `measurable_uncurry_jumpProcess`, das der Kompensator braucht; der Vorschlag
   des vierten Laufs, sie als punktweisen Limes über `min u n` zu gewinnen, war
   ein Umweg um eine Aussage, die schwerer ist als die gebrauchte. Damit fiel
   auch Punkt 4 ganz.

   ~~**Was offen bleibt, und nur das:** der Schritt von den eindimensionalen zu
   den **endlichdimensionalen** Verteilungen, den „genau eine Lösung" meint.~~
   *(erledigt im sechsten Lauf; der dort angesagte Weg über Mengen der
   Vergangenheit trug nicht, siehe den ersten Befund oben.)*
4. ~~**Erst danach das Akzeptanzbeispiel**, und dann wirklich als Beweis: `E = ℕ`,
   `lam ≡ 1`, `mu x = dirac (x+1)`, also `A f x = f (x+1) - f x` — der
   Poissonprozeß, mit den eindimensionalen Verteilungen gegen
   `ProbabilityTheory.poissonMeasure` geprüft.~~ *(erledigt 2026-09-10, fünfter
   Lauf des Tages)*

   **Ergebnis.** `jumpMeasure_map_jumpProcess_poisson`:
   `(jumpMeasure poissonKernel (dirac 0)).map (jumpProcess poissonRate t)`
   `= poissonMeasure t`, mit `poissonMeasure` aus Mathlib. **Es kommt heraus,
   wie es soll**, also gibt es keinen Befund gegen `jumpTime`, `stepIndex` oder
   `waitingMeasure` — und das ist die einzige Stelle, an der sich einer gezeigt
   hätte. Acht Deklarationen, alle mit `#print axioms` auf `propext`,
   `Classical.choice`, `Quot.sound` geprüft, die ganze Datei ohne einen Fehler
   durch `lake env lean` gegen v4.33.1. Bericht in `Facts/INVENTAR.md`, Läufe,
   „2026-09-10, fünfter Lauf des Tages".

   **Der Weg ist der angesagte billigere, die Eindeutigkeit**, und der
   Negativbefund zur Erlangverteilung unten bleibt stehen — er ist nicht
   ausgeräumt, sondern umgangen. Was ihn umgeht, ist ein Fund: der Erzeuger
   dieser Daten **ist** Mathlibs `fwdDiff 1`
   (`Mathlib/Algebra/Group/ForwardDiff.lean`), also greift dort
   `shift_eq_sum_fwdDiff_iter`, die Gregory--Newton-Formel; ein einziges
   Cauchyprodukt mit `exp t = ∑ t^m/m!`
   (`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`) macht daraus die
   Poissonsumme (`tsum_fwdDiff_iter_eq`, für **jedes** reelle `t` und jedes
   beschränkte `f`). Der Vergleich der Maße selbst ist dann
   `Measure.ext_of_singleton` auf `ℕ` gegen `poissonMeasure_real_singleton`.

   **Und das zweite Akzeptanzbeispiel gleich mit** (derselbe Lauf, zweiter
   Teil): die **Zweizustandskette** `E = Bool`, `lam ≡ 1`, `mu x = dirac (!x)`,
   sieben Deklarationen in `section TwoStateExample`. Sie prüft, was der
   Poissonprozeß nicht prüfen kann — dort ist der Erzeuger eine Verschiebung,
   also liefe ein Vorzeichenfehler unbemerkt in eine Poissonverteilung anderen
   Mittelwerts; hier zyklen die Iterierten mit dem Faktor `-2`
   (`iterate_jumpApply_flip`), und das Gesetz ist eine Zahl,
   `(1 - e^{-2t})/2`, die bei `t = 0` gleich `0` sein muß und gegen `1/2` gehen
   muß und nicht gegen `1`.

   *Der ursprüngliche Wortlaut, und der Zwischenstand des dritten Laufs:* Es
   instanziiert jede Einzelheit des Meilensteins auf einmal; steht es nur als
   Prosa da, prüft es nichts (die Lehre des 2026-09-08). Bricht es, so ist der
   Befund wertvoller als der Satz darüber, und er gehört in den Bericht statt in
   eine Abschwächung.

   **Zwischenstand 2026-09-10, dritter Lauf des Tages.** Vorgezogen, weil es die
   einzige Probe darauf ist, daß die sechs Voraussetzungen von
   `jumpProcess_isMPSolution` gemeinsam erfüllbar sind — die Leerheitsprobe, die
   das Inventar seit dem 2026-09-07 verlangt, und sie gehört an den Satz, den
   derselbe Lauf bewiesen hat. Sieben Deklarationen in `section PoissonExample`
   von `TauCeti/MartingaleProblems/Suggested.lean`, ohne einen Fehler beim
   ersten Durchlauf, die vier tragenden mit `#print axioms` geprüft. **Der
   Erzeuger kommt heraus, wie er soll** (`jumpApply_poisson`), also gibt es
   keinen Befund gegen die Form von `set:jumpdata`;
   `poissonProcess_isMPSolution` löst jede Voraussetzung auf Daten ein, und
   `martingale_compensated_poisson` ist ein wirkliches
   `MeasureTheory.Martingale` und kein Prädikat. Bericht in
   `Facts/INVENTAR.md`, Läufe, „2026-09-10, dritter Lauf des Tages", zweiter
   Teil.

   ~~**Was fehlt, und es ist die eigentliche Kontrolle:** die
   **eindimensionalen Verteilungen** gegen `ProbabilityTheory.poissonMeasure`
   (`Probability/Distributions/Poisson/Basic.lean:41`), also
   `(jumpMeasure poissonKernel (dirac 0)).map (jumpProcess poissonRate t)`
   `= poissonMeasure (Real.toNNReal t)`.~~ *(erledigt im fünften Lauf; der
   Zeitindex ist `ℝ≥0`, also steht dort `poissonMeasure t` ohne
   `Real.toNNReal`.)* Das ist ein eigener Beweis und kein Einsetzen von Daten,
   und es ist die einzige Stelle, an der sich ein Fehler in `jumpTime`,
   `stepIndex` oder `waitingMeasure` überhaupt zeigen würde.

   **Der Negativbefund zur klassischen Route bleibt gültig.** Der klassische
   Weg ginge über die Erlangverteilung von `T n`; **Mathlib trägt ihn nicht**:
   `gammaMeasure` (`Distributions/Gamma.lean:128`) und `expMeasure` stehen als
   Dichten da, aber weder v4.33.1 noch `upstream/master` hat ihre **Faltung** —
   in beiden Dateien kommt `conv`, `HasLaw`, `IndepFun` überhaupt nicht vor
   (anders als auf der Poissonseite, die `poissonMeasure_conv_poissonMeasure`
   und `IndepFun.hasLaw_add_poissonMeasure` hat). Es bleiben zwei Wege, beide
   eigene Arbeit: die **Erneuerungsinduktion** über das schon bewiesene
   `jumpMeasure_integral_eq_renewal` (`p 0 t = e^{-t}`,
   `p n t = ∫_0^t e^{-s} p (n-1) (t-s) ds`), oder die **Eindeutigkeit**, unter
   der es ein Korollar von Punkt 3 ist — so führt es Meilenstein 4 selbst.
   Punkt 3 zuerst ist darum der billigere Weg.
5. Der lokale Fall und die pfadabhängige Variante zuletzt; sie liefern die
   Beispiele für die Meilensteine 7 und 9. **Die Punkte 0 bis 4 sind durch, also
   ist dies der laufende Auftrag** (seit dem sechsten Lauf des 2026-09-10).
   ~~Der Befund des siebzehnten Laufs des 2026-09-09 gilt weiter und ist die
   erste Hürde: `x / 0 = 0` in Lean, also verläßt der Pfad einen Zustand mit
   `lam x = 0` sofort; der absorbierende Fall verlangt Sprungzeiten in
   `ℝ≥0∞`.~~ *(die Hürde ist genommen, 2026-09-10, siebter Lauf des Tages.)*
   Die drei Akzeptanzbeispiele darunter — M/M/1, linearer Geburt-Tod, Hawkes —
   gehören zu diesem Punkt, und der lineare Geburt-Tod ist das einzige, das den
   lokalen Zweig prüft.

   **Zwischenstand 2026-09-10, siebter Lauf des Tages.** Die Sprungzeiten in
   `ℝ≥0∞` stehen, samt Pfaden und Akzeptanzbeispiel: `jumpTimeE`,
   `jumpProcessE`, `jumpProcessE_of_absorbing` (der Pfad bleibt für alle Zeiten
   im absorbierenden Zustand), `isStepPath_jumpProcessE`,
   `isCadlagPath_jumpProcessE` und `jumpProcessE_eq_jumpProcess` (bei positiver
   Rate stimmen alte und neue Konstruktion überein — es ist eine Fortsetzung und
   kein Konkurrent). Zweiundvierzig Deklarationen, die ganze Datei ohne einen
   Fehler durch `lake env lean` gegen v4.33.1, alle mit `#print axioms` geprüft,
   die Zahl der `sorry` bleibt bei neun. Bericht in `Facts/INVENTAR.md`, Läufe,
   „2026-09-10, siebter Lauf des Tages".

   **Der Zeuge stand vor dem Satz, wie verlangt, und er ist schärfer als
   angesagt.** `jumpProcess_absorbing_const`: auf den Daten `E = Bool`,
   `lam false = 0`, `lam true = 1` ist der Pfad der alten Konstruktion
   **konstant `true`** — er nimmt den absorbierenden Wert nicht zu spät an,
   sondern nie. Der Grund ist, daß `T n = 1` für alle `n ≥ 1` und danach
   `{n | t < T (n+1)}` leer ist: **der absorbierende Zustand und die Explosion
   sind für die alte `stepIndex` dasselbe Ereignis**, und der Müllwert `sInf ∅ =
   0`, der auf der Explosionsmenge harmlos ist, ist hier die Antwort auf jede
   Frage.

   **Drei Befunde für den nächsten Lauf.** (a) Die Positivität der Haltezeit ist
   im erweiterten Modell **voraussetzungsfrei** (`jumpTimeE_increment_pos`), also
   ist `∀ x, 0 < lam x` nicht abgeschwächt, sondern überflüssig geworden.
   (b) `StrictMono` ist im lokalen Fall nicht bloß unbewiesen, sondern **falsch**;
   was der Pfadbeweis wirklich benutzt, ist die Fortpflanzung der Strengheit
   **nach unten**, und die ist in `ℝ≥0∞` geschenkt. (c) Deshalb stehen
   `stepIndex` und `stepPath` jetzt über einer beliebigen
   `ConditionallyCompleteLinearOrder`, und `exists_stepIndex_window` fragt nach
   Nichtexplosion **an dem einen Punkt** — an `⊤` ist sie falsch, sobald
   absorbiert wird.

   ~~**Was fehlt, in zwei Schritten**: erstens die gemeinsame Meßbarkeit von
   `jumpProcessE` in `(t, ω)`; zweitens das Nichtexplosionskriterium.~~ *(der
   erste Schritt ist erledigt, 2026-09-10, achter Lauf des Tages; der zweite ist
   zerlegt.)*

   **Zwischenstand 2026-09-10, achter Lauf des Tages.** Der lokale Prozeß **ist
   ein Prozeß**, und Nichtexplosion ist **eine** Reihe. Zweiunddreißig
   Deklarationen (vier Definitionen, achtundzwanzig Sätze), die ganze Datei ohne
   einen Fehler durch `lake env lean` gegen v4.33.1, alle Sätze mit
   `#print axioms` auf `propext`, `Classical.choice`,
   `Quot.sound` geprüft, die Zahl der `sorry` bleibt bei neun. Bericht in
   `Facts/INVENTAR.md`, Läufe, „2026-09-10, achter Lauf des Tages"; die neuen
   Punkte stehen in `MartingaleProblems/README.md`, Meilenstein 4.

   **Die Meßbarkeit ist als Verallgemeinerung gefallen und nicht als Kopie.**
   `measurable_stepIndex_comp` und `measurable_stepPath_comp` führen die
   **Zeitabbildung** `u : γ → α` mit; die gemeinsame Meßbarkeit in `(t, ω)` ist
   der Fall `u = Prod.fst`, der lokale Fall der Fall
   `u = ENNReal.ofReal ∘ Prod.fst`, und die alten `measurable_stepIndex`,
   `measurable_stepPath` sind Zweizeiler geworden, ohne daß eine ihrer über
   sechzig Gebrauchsstellen anzufassen war. Darauf `measurable_jumpTimeE`,
   `measurable_jumpProcessE`, `measurable_jumpProcessE_apply`.

   **Die Übertragung des Raums war billiger als gedacht, weil `jumpMeasure` die
   Rate gar nicht nennt** — die treibenden Daten sind in beiden Konstruktionen
   dieselben, nur die Uhr ist ausgetauscht. Dabei fiel eine echte Verschärfung
   an: `jumpMeasure_map_jumpProcessE_zero` sagt „der Prozeß startet mit `nu`"
   **ohne jede Voraussetzung an die Rate**, wo die alte Fassung `∀ x, 0 < lam x`
   braucht.

   **Der Fund, und er ist der Angelpunkt des lokalen Falls:**
   ```
   mem_nonExplosiveE_iff_tsum_eq_top :
     (y, xi) ∈ NonExplosiveE lam
       ↔ ∑' k, ENNReal.ofReal (xi k) / ENNReal.ofReal (lam (y k)) = ⊤
   ```
   In `ℝ` sind die beiden Weisen, nicht zu explodieren — divergente Haltezeiten,
   und ein Zustand, den der Pfad nie verläßt — **verschiedene** Bedingungen und
   verlangen überall eine Fallunterscheidung. In `ℝ≥0∞` sind sie **dieselbe**:
   ein absorbierender Zustand steuert einen Summanden `⊤` bei, und `⊤` ist
   gerade, wie eine divergente Reihe aufgeschrieben wird. Damit hat jedes
   Kriterium **eine** Gestalt. Dazu `NonExplosiveE` als Menge samt
   `measurableSet_nonExplosiveE`, `mem_nonExplosiveE_iff_of_pos` (der lokale Fall
   ändert nicht, was Nichtexplosion heißt), und die beiden deterministischen
   Kriterien `mem_nonExplosiveE_of_rate_zero` und `mem_nonExplosiveE_of_traj` —
   letzteres beschränkt die Rate **längs der Trajektorie**, was kein
   Schönheitsstrich ist: eine lokal beschränkte Rate ist auf `E` per definitionem
   unbeschränkt.

   **Beide Seiten des Prädikats haben eine Instanz**, sonst prüfte es nichts:
   `mem_nonExplosiveE_absorb` ist drin, `notMem_nonExplosiveE_explode` draußen
   (`lam n = 2^n` längs `y n = n`, Sprungzeiten `2 - 2/2^m`, erreichen `2` nie).
   **Es ist der andere Defekt** — die Rate ist überall positiv, also nicht der
   Mangel, den `jumpProcessE` behebt.

   ~~**Was fehlt, und es ist eine einzige benannte Aussage:**
   `ae_tendsto_sum_smul_waiting_atTop`.~~ *(erledigt 2026-09-10, neunter Lauf des
   Tages.)*

   **Zwischenstand 2026-09-10, neunter Lauf des Tages.** **Das
   Nichtexplosionskriterium des lokalen Falls steht, und es ist ein Kriterium an
   der Kette allein**; dazu ist der **Erzeuger der Geburt-Tod-Kette** gerechnet.
   Siebenunddreißig Deklarationen (einundzwanzig im Abschnitt `Absorbing`,
   sechzehn im neuen `BirthDeathExample`), die ganze Datei ohne einen Fehler
   durch `lake env lean` gegen v4.33.1, alle achtundzwanzig Sätze mit
   `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft, die
   Zahl der `sorry` bleibt bei neun. Bericht in `Facts/INVENTAR.md`, Läufe,
   „2026-09-10, neunter Lauf des Tages".

   Bewiesen sind `ae_tendsto_sum_smul_waiting_atTop` samt seiner ganzen Mitte
   (`iIndepFun_waiting`, `waitBig` mit `integral_waitBig`, die drei
   Tschebyschew-Eingaben `memLp_mul_waitBig`, `integral_sum_waitBig`,
   `variance_sum_waitBig_le`, und die Abschätzung `measure_sum_waitBig_lt_le`),
   darauf das Kriterium in drei Gestalten — punktweise
   (`mem_nonExplosiveE_of_tendsto_sum`), unter `waitingMeasure`
   (`ae_mem_nonExplosiveE`) und unter `jumpMeasure`
   (`ae_mem_nonExplosiveE_jumpMeasure`) —, und das Akzeptanzbeispiel
   `ae_mem_nonExplosiveE_linear`.

   **Vier Befunde für die weitere Arbeit.**

   * **Der angesagte dritte Mathlib-Baustein war nicht nötig, und der
     Negativbefund dahinter ist einseitig.**
     `ProbabilityTheory.iIndepFun_infinitePi`
     (`Probability/Independence/InfinitePi.lean:127`), an der Identität gelesen,
     *ist* `iIndepFun` der Koordinaten von `waitingMeasure`; es braucht weder
     `iIndepSet_waiting` noch `iIndepSet.iIndepFun_indicator`. Was Mathlib
     wirklich fehlt, ist die **andere** Richtung, die das zweite Borel--Cantelli
     verlangt. Ein Negativbefund über zwei Begriffe ist ein Befund über eine
     **Richtung**; wer ihn zitiert, nennt die Richtung mit.
   * **Die Abschneidung ist nicht eine Bequemlichkeit, sondern das Argument.**
     Für die Integrierbarkeit braucht es `b n ≤ 1` nicht — ein gewichteter
     Indikator ist durch sein Gewicht beschränkt —, sondern an genau einer
     Stelle, nämlich `b n² ≤ b n` in der Varianz. Ohne sie stünde dort `∑ b n²`,
     das konvergieren kann, während `∑ b n` divergiert (`c n = 1/n`), und die
     Schranke sagte nichts.
   * **Die Varianzschranke ist `B N / 4` und nicht `B N`**, ohne Mehrarbeit, weil
     `ProbabilityTheory.variance_le_sq_of_bounded` (Popoviciu, `:499`) für Werte
     in `Set.Icc 0 1` unmittelbar `1/4` gibt; der Weg über
     `variance_le_expectation_sq` hätte die Quadratintegrierbarkeit eigens
     verlangt.
   * **Das Kriterium ist echt schwächer als das deterministische.**
     `mem_nonExplosiveE_of_traj` verlangt `lam (y k) ≤ L`; das neue nur die
     Divergenz von `∑ (lam (y k))⁻¹`. Der Unterschied ist genau der Fall, für den
     der lokale Zweig existiert.
   * **Der absorbierende Fall verlangt zwei Reparaturen und nicht eine.** Der
     Erzeuger der Geburt-Tod-Kette kommt heraus, wie er soll
     (`jumpApply_birthDeath`), also kein Befund gegen `set:jumpdata`. Aber wo
     `b x + d x = 0` ist, ist die Mischung `0/0` das **Nullmaß**, und
     `IsMarkovKernel` scheitert — an genau dem Zustand, den das Modell
     absorbierend meint. `jumpProcessE` behebt dort die **Rate**, nicht den
     **Kern**; der Kern braucht eine eigene Konvention, und `Measure.dirac x` ist
     die einzige, die keinen Erzeuger ändert. Damit tragen
     `isMarkovKernel_birthDeathKernel` und `jumpApply_birthDeath` **keine**
     Positivitätsvoraussetzung, und erst das macht die lineare Kette
     hinschreibbar. Die beiden Instanzen stehen, jede an ihrem Zweig: M/M/1 mit
     Rate in `(0, β+δ]` (`birthDeathRate_mm1_mem`), die lineare Kette mit
     `birthDeathRate_linear_zero` und `not_bddAbove_birthDeathRate_linear`.
   * **M/M/1 ist fertig, und es ist die erste Lösung mit zustandsabhängigem
     Erzeuger.** `mm1_isMPSolution` löst jede Voraussetzung von
     `jumpProcess_isMPSolution` auf den Daten ein, `martingale_compensated_mm1`
     ist ein wirkliches `MeasureTheory.Martingale`. Beim Poissonprozeß ist die
     Rate konstant und der Kern eine Verschiebung, also sieht der Zustand dort
     gar nichts; hier sieht er die Schranke `1 ≤ x`.

   **Zwischenstand 2026-09-10, zehnter Lauf des Tages. Die angesagte
   lokalisierende Folge ist keine, und das ist das Ergebnis des Laufs.** Sechs
   Deklarationen im neuen Abschnitt `LocalFiltration`, die ganze Datei ohne einen
   Fehler durch `lake env lean` gegen v4.33.1, alle sechs mit `#print axioms` auf
   `propext`, `Classical.choice`, `Quot.sound` geprüft; die Zahl der `sorry`
   bleibt bei neun. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-10, zehnter
   Lauf des Tages".

   `not_isStoppingTime_min_jumpTimeE`: die Glieder von
   `τ n ω = min (jumpTimeE lam ω.1 ω.2 n) n` sind **keine Stoppzeiten** für
   `jumpFiltrationE`, die natürliche Filtration des Prozesses, und
   `ProbabilityTheory.IsLocalizingSequence` verlangt das Feld `isStoppingTime`
   exakt. Der Zeuge ist die **konstante Kette** an einem Zustand `x₀` mit
   `0 < lam x₀`, mit den beiden konstanten Wartezeiten `lam x₀ / 4` und `lam x₀`:
   beide haben echt positive Haltezeiten, ihre Pfade sind gleich, ihre ersten
   Sprungzeiten `1/4` und `1` trennt die Schwelle `1/2`. Der Grund ist
   `jumpProcessE_const_chain`, ein `rfl`: `stepPath` liest die Kette am
   Stufenindex, also hinterläßt eine Kette, die sich nicht bewegt, keine Spur der
   Wartezeiten im Pfad — ein Sprung von `x` nach `x` ist unsichtbar.

   **Drei Dinge daran, die der nächste Lauf braucht.**

   * **Es ist nicht durch Wegwerfen einer Nullmenge zu reparieren.**
     `eq_of_measurable_jumpFiltrationE_of_subsingleton`: über einem einpunktigen
     Zustandsraum trennt keine `𝓕 t`-meßbare reelle Funktion zwei
     Stichprobenpunkte, die versagende Menge ist also der **ganze** Raum, während
     die Rate `1` jede Voraussetzung von `jumpProcess_isMPSolution` erfüllt.
     Allgemein: sobald `mu x {x} > 0` ist, ist die unsichtbare Kette keine
     Nullmenge. `IsStoppingTime` ist überdies keine f.s.-Aussage — derselbe
     Punkt, an dem `StronglyAdapted` diese Datei schon einmal zu einer
     voraussetzungsfreien Rechtsstetigkeit gezwungen hat. **Und auch der Übergang
     zur rechtsstetigen Filtration hilft nicht**, der übliche Reparaturweg für
     eine Anfangszeit: `eq_of_measurable_jumpFiltrationE_const_chain` trennt die
     beiden konstanten Ketten zu **keiner** Zeit, und `⨅ s > t, 𝓕 s` liegt unter
     `𝓕 s` für jedes `s > t`. Die Wartezeiten sind im Pfad nicht spät, sie sind
     abwesend.
   * **Die Reparatur ist die, die Meilenstein 7 längst vorschreibt**, und sie
     steht als Punkte in `MartingaleProblems/README.md`, Meilenstein 4: die
     Treffzeiten des **laufenden Supremums der Rate längs des Pfades**,
     `rateSup lam t ω = ⨆ s ∈ Set.Icc 0 t, ENNReal.ofReal (lam (jumpProcessE lam s ω))`
     und `rateTime lam n ω = sInf {t : ENNReal | (n : ENNReal) ≤ rateSup lam t ω}`.
     Was lokalisieren darf, muß ein Funktional des **Pfades** sein, denn nur den
     sieht die Filtration. Meilenstein 7 nennt für das laufende Supremum die
     Striktheit als Grund; die **Sichtbarkeit** ist der schärfere, denn die
     Sprungzeiten sind für *keine* Filtration des Prozesses Stoppzeiten, auch
     nicht für die rechtsstetige.
   * **Der `sInf` gehört nach `ENNReal` und nicht nach `ℝ≥0`**: dort ist
     `sInf ∅ = ⊤`, was die Stoppzeit ohne Fallunterscheidung total macht, während
     `ℝ≥0` denselben Müllwert `0` gäbe, an dem der siebte Lauf die alte
     `stepIndex` scheitern sah.

   ~~**Was von Punkt 5 noch fehlt**, und es ist der nächste Auftrag: `rateSup`
   samt `measurable_rateSup` und `rateSup_right_continuous`, **vor** `rateTime`~~
   *(erledigt 2026-09-10, elfter Lauf des Tages, und über den Auftrag hinaus:
   `rateTime` samt `isStoppingTime_rateTime` und `isLocalizingSequence_rateTime`
   stehen ebenfalls.)*

   **Zwischenstand 2026-09-10, elfter Lauf des Tages. Die lokalisierende Folge
   steht, und sie ist eine.** Siebzehn Deklarationen (zwei Definitionen, fünfzehn
   Sätze), die ganze Datei ohne einen Fehler durch `lake env lean` gegen v4.33.1,
   alle siebzehn mit `#print axioms` auf `propext`, `Classical.choice`,
   `Quot.sound` geprüft, die Zahl der `sorry` bleibt bei neun. Bericht in
   `Facts/INVENTAR.md`, Läufe, „2026-09-10, elfter Lauf des Tages"; die Punkte
   stehen berichtigt in `MartingaleProblems/README.md`, Meilenstein 4.

   **Alles hängt an einer einzigen voraussetzungsfreien Aussage, und sie ist
   allgemeiner geworden als ihr Anlaß.** `eventuallyEq_nhdsGE_stepPath_comp` sagt,
   daß ein Treppenpfad an **jeder** Zeit von rechts lokal konstant ist — ohne
   Monotonie der Sprungzeiten, ohne Nichtexplosion — und führt die Zeitabbildung
   mit, wie `measurable_stepIndex_comp` es tut; der lokale Fall ist
   `ENNReal.ofReal`, das alte `eventuallyEq_nhdsGE_stepPath` der Fall `u = id`
   und auf drei Zeilen zusammengeschrumpft. Daraus die Meßbarkeit
   (`rateSup_eq_sup_rat`, die Reduktion auf ein Supremum über `ℚ`) **und** die
   Rechtsstetigkeit (`eventuallyEq_nhdsGE_rateSup`, in Wahrheit lokale
   Konstanz), und aus diesen beiden `rateTime_le_iff` und
   `isStoppingTime_rateTime`.

   **Drei Befunde für den nächsten Lauf.** (a) Die angesagte Gestalt des `sInf`
   war an einer halben Zeile falsch: `sInf {t : ℝ≥0 | …}` nimmt das Infimum in
   `ℝ≥0` und liefert gerade den Müllwert `0`, vor dem der Punkt darüber warnt. Es
   heißt `⨅ t : ℝ≥0, ⨅ _ : (n:ℝ≥0∞) ≤ rateSup lam t ω, (t : ℝ≥0∞)` — Index in
   `ℝ≥0`, Infimum in `ℝ≥0∞`. (b) Die Rechtsstetigkeit ist als **Intervall**
   `[t, u)` zu formulieren und nicht als Filteraussage: `rateTime_le_iff` braucht
   das Intervall und nicht bloß `∀ᶠ … 𝓝[≥]`. (c) Die Datei hat **kein**
   `open scoped ENNReal` — `ℝ≥0∞` steht dort nur in Kommentaren, im Code steht
   `ENNReal` ausgeschrieben. Wer die Notation benutzt, erntet zwanzig
   Folgefehler an Stellen, die in Ordnung sind.

   ~~**Was von Punkt 5 jetzt noch fehlt, und es ist eine einzige benannte
   Aussage:** `jumpProcess_isLocalMPSolution`.~~ *(die dort zuerst zu klärende
   Frage ist beantwortet, 2026-09-10, zwölfter Lauf des Tages; der Satz selbst
   steht noch aus und hängt jetzt an zwei anderen Aussagen.)* Alle Eingaben
   stehen wirklich und nicht als Beschreibung: die lokalisierende Folge ist
   bewiesen eine (`isLocalizingSequence_rateTime`), der Prozeß ist meßbar
   (`measurable_jumpProcessE`), und `ae_mem_nonExplosiveE_jumpMeasure` löst die
   einzige Voraussetzung jener Folge unter `jumpMeasure mu nu` ein. Dabei ist im
   Auge zu behalten, was die Lokalisierung liefert und was nicht — es ist der
   Punkt, an dem der Satz brechen kann: auf `{t < rateTime lam n}` ist die Rate
   **längs des Pfades** durch `n` beschränkt, was keine Schranke an `lam` ist, so
   daß `jumpProcess_isMPSolution` auf dem gestoppten Prozeß **nicht** durch
   Einsetzen greift. Von den drei Akzeptanzbeispielen ist M/M/1 **fertig** —
   Erzeuger, Lösung und Martingal —, die lineare Kette hat ihren Erzeuger und ihr
   Nichtexplosionsargument und wartet auf `jumpProcess_isLocalMPSolution`, und
   Hawkes wartet auf die pfadabhängige Variante.

   **Zwischenstand 2026-09-10, zwölfter Lauf des Tages. Der gestoppte Prozeß
   *ist* einer von beschränkter Rate, und nicht bloß einer mit denselben
   Martingalen.** Sechzehn Deklarationen im neuen Abschnitt `Truncation` von
   `TauCeti/MartingaleProblems/Suggested.lean`, die ganze Datei ohne einen Fehler
   durch `lake env lean` gegen v4.33.1, alle sechzehn mit `#print axioms` auf
   `propext`, `Classical.choice`, `Quot.sound` geprüft, die Zahl der `sorry`
   bleibt bei neun. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-10, zwölfter
   Lauf des Tages"; die neuen Punkte stehen in
   `MartingaleProblems/README.md`, Meilenstein 4.

   `jumpProcessE_eq_truncRate_of_le_rateTime`: unter Nichtexplosion und
   `ENNReal.ofReal t ≤ rateTime lam n ω` ist
   `jumpProcessE (truncRate lam n) t ω = jumpProcessE lam t ω`, mit
   `truncRate lam n = min lam n`, das auf **ganz `E`** durch `n` beschränkt ist.
   Über `lam` steht nichts — keine Positivität, keine Schranke, keine
   Meßbarkeit. `stoppedProcess_jumpProcessE_truncRate` liest dasselbe als
   Gleichheit der gestoppten Prozesse.

   **Drei Befunde für den nächsten Lauf.**

   * **Der Beweis lebt davon, welche Indizes er *nicht* liest.** Ein leeres
     Fenster braucht gar nichts (`xi m ≤ 0` macht beide Zuwächse `0`, auch bei
     `0 / 0`), und der Zustand, den der Pfad zur fraglichen Zeit einnimmt, wird
     nie gelesen — die Induktion verbraucht die Rate an `y m` allein, um von
     `T m` nach `T (m+1)` zu kommen. Genau deshalb darf die Voraussetzung
     `≤ rateTime` mit Gleichheit stehen, obwohl an der Trefferzeit die Rate
     schon `≥ n` ist.
   * **`rateTime lam 0 ω = 0`, immer** (`rateTime_zero`): das erste Glied der
     lokalisierenden Folge stoppt sofort. Dazu der Zeuge
     `exists_jumpProcessE_truncRate_ne`, daß die Voraussetzung nicht
     wegzulassen ist.
   * **Was jetzt fehlt, ist nicht mehr die Prozeßidentität, sondern die der
     σ-Algebren.** Der Turmschluß „der gestutzte Prozeß ist ein Martingal, also
     ist es der gestoppte auch" bräuchte
     `jumpFiltrationE lam s ≤ jumpFiltrationE (truncRate lam n) s`, und der
     Einschluß fehlt. Zwei benannte Aussagen stehen dafür in der Roadmap:
     `jumpFiltrationE_inter_lt_rateTime` (die beiden Filtrationen stimmen **vor**
     der Trefferzeit überein; die Eingabe dafür ist
     `jumpProcessE_eq_truncRate_of_le_of_le_rateTime` aus diesem Lauf) und
     `jumpProcessE_isMPSolution` (der beschränkte Satz für die **lokale**
     Konstruktion, unter `0 ≤ lam ≤ L`, weil `jumpProcessE_eq_jumpProcess` die
     beiden Konstruktionen nur bei durchweg positiven Wartezeiten identifiziert
     und eine natürliche Filtration keine f.s.-Aussage ist). ~~Die erste
     zuerst.~~ *(die erste ist erledigt, 2026-09-10, dreizehnter Lauf des Tages.)*

   **Zwischenstand 2026-09-10, dreizehnter Lauf des Tages. Die beiden
   Filtrationen stimmen vor der Trefferzeit überein, in beiden Richtungen.**
   Siebzehn Deklarationen im Abschnitt `Truncation` von
   `TauCeti/MartingaleProblems/Suggested.lean`, die ganze Datei ohne einen Fehler
   durch `lake env lean` gegen v4.33.1, alle siebzehn mit `#print axioms` auf
   `propext`, `Classical.choice`, `Quot.sound` geprüft, die Zahl der `sorry`
   bleibt bei neun. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-10,
   dreizehnter Lauf des Tages"; die Punkte stehen in
   `MartingaleProblems/README.md`, Meilenstein 4.

   `jumpFiltrationE_inter_lt_rateTime` und
   `jumpFiltrationE_truncRate_inter_lt_rateTime`: ein Ereignis der einen
   natürlichen Filtration bei `s`, geschnitten mit `{s < rateTime lam n}`, ist
   eines der anderen. Über `lam` steht nichts als `Measurable lam`.

   **Drei Befunde für den nächsten Lauf.**

   * **Der Lauf hat eine Voraussetzung gestrichen, statt eine hinzuzufügen, und
     das war der Angelpunkt.** Die Prozeßidentität des zwölften Laufs stand unter
     **Nichtexplosion**, und für σ-Algebren nützt das nichts — eine natürliche
     Filtration ist keine f.s.-Aussage. `jumpProcessE_eq_of_rate_eq_on_path`
     vergleicht statt dessen **zwei beliebige Raten, die an jedem besuchten
     Zustand übereinstimmen**, an jedem Stichprobenpunkt, ohne Positivität, ohne
     Schranke und **ohne Vergleichbarkeit der beiden Raten**. Nichtexplosion war
     nötig, um ein Fenster zu *benennen*; wo es keines gibt, liegt jede Sprungzeit
     unter `t`, die beiden Sprungzeitfolgen sind gleich, und die Stufenindizes
     sind derselbe Müllwert. Die Monotonie fiel mit, sobald die Hypothese am
     **geschlossenen** Ende `s = t` gelesen wird. Der Preis ist `0 ≤ t`.
   * **Ein Vergleich der Pfade ist nicht die halbe Miete, sondern die halbe
     Arbeit.** Das σ-Algebren-Argument braucht die Schnittmenge selbst als
     Ereignis der **gestutzten** Filtration (`{A | A ∩ N ∈ 𝓖}` ist unter
     Komplementen abgeschlossen, weil `Aᶜ ∩ N = N \ (A ∩ N)` ist — dort wird
     `N ∈ 𝓖` verbraucht). Das liefert erst der **umgekehrte** Vergleich, über
     `rateSup_truncRate_lt_iff` und `setOf_lt_rateTime_eq`. Ohne ihn bleibt nur
     die Spurgleichheit, und die trägt den Turmschluß nicht.
   * **Der Rückgabewert einer Pipe ist der ihrer letzten Stufe.** Ein erster
     Durchlauf `lake env lean … | head -120` verschluckte fünf Fehler und meldete
     `rc=0`. Wer `lake env lean` filtert, filtert mit `grep` und nicht mit `head`.

   *Der ursprüngliche Wortlaut dieses Zwischenstands, und er ist an einem Wort
   falsch:* „Alle drei Zutaten stehen: der Prozeß ist meßbar, er explodiert f.s.
   nicht, und vor dem `n`-ten Sprung besucht der Pfad nur `n` Zustände, die Rate
   ist dort also beschränkt. Der einzige Punkt, an dem es brechen kann, ist, ob
   die gestoppte Konstruktion mit der Konstruktion zur beschränkten Rate
   übereinstimmt oder nur denselben Martingalen genügt." Die dritte Zutat war
   eine **Beschreibung** und keine Voraussetzung: daß `τ n` eine Stoppzeit sei,
   ist nie geprüft worden. Das ist der Fehlertyp der Suchregel vom neunten Lauf
   des 2026-09-08, hier in der Gegenrichtung — einen Kandidaten mit einer
   Beschreibung statt mit einer Voraussetzung **annehmen**.

**Weitere Akzeptanzbeispiele, wenn die Konstruktion steht.** Alle drei sind
*Einsetzen von Daten*, kein neuer Beweis, und jedes prüft einen anderen Zweig:

* ~~**M/M/1**, `b ≡ β`, `d x = δ * 1_{x ≥ 1}` auf `E = ℕ`. Beschränkt, also
  greifen `thm:jumpMP` und `exists_unique_of_bounded` unmittelbar.~~ *(erledigt
  2026-09-10, neunter Lauf des Tages: `jumpApply_mm1`, `mm1_isMPSolution`,
  `martingale_compensated_mm1` — die erste Lösung mit zustandsabhängigem
  Erzeuger.)*
* **Linearer Geburt-Tod**, `b x = β * x`, `d x = δ * x`. Hier ist
  `λ̄ = ∞`, der Satz greift **nicht**, und das Beispiel prüft als einziges den
  lokalen Zweig samt Nichtexplosionskriterium (`∑ 1/(β n)` divergiert). Der
  Yule-Prozeß `δ = 0` fällt als Sonderfall ab und hat geschlossene
  eindimensionale Verteilungen — geometrisch —, also eine unabhängige Kontrolle
  wie `poissonMeasure` beim Poissonprozeß.
* **Hawkes**, prädiktables `Λ(t, ω) = ν + ∫_0^{t-} h(t-s) dN_s`, das
  nicht-markovsche Beispiel und die Instanz von `ex:hawkes`. Es gehört zur
  pfadabhängigen Variante und kommt zuletzt.

~~In jedem Fall zuerst der Erzeuger als Rechnung: für Geburt-Tod kürzt sich `λ`
heraus und es muß `A f x = b x * (f (x+1) - f x) + d x * (f (x-1) - f x)`
herauskommen.~~ *(gerechnet 2026-09-10, neunter Lauf des Tages,
`jumpApply_birthDeath`: es kommt heraus, wie es soll, also kein Befund gegen
`set:jumpdata` — wohl aber einer über den Kern am absorbierenden Zustand, siehe
den Zwischenstand zu Punkt 5.)*

**Was zählt:** eine in Lean bewiesene Lösung eines Martingalproblems. **Was nicht
zählt:** ein Prädikat, das sagt, was eine Lösung wäre.

### ~~Aufgabe: die nächsten vier Läufe an `SkorokhodSpace`~~ *(gestellt 2026-09-08 vom Nutzer, erledigt 2026-09-08, neunzehnter Lauf des Tages)*

**Ergebnis** in `Facts/INVENTAR.md`, Läufe, die vier Abschnitte vom sechzehnten
bis zum neunzehnten Lauf des 2026-09-08. Kurz, an den vier Punkten der Aufgabe
gemessen: `SkorokhodSpace/Suggested.lean` steht bei **fünf** `sorry` statt elf.

*Punkt 1 ist erledigt* (sechzehnter Lauf), und die Wahl ist die Typklasse
`BasePoint ι`; der Grund gegen `Classical.arbitrary` ist, daß der so gewonnene
Punkt opak wäre und kein acceptance example der Meilensteine 4 bis 7 sich dann
noch hinschreiben ließe. `SkorokhodSpace.dist_eq` ist `rfl`.

*Punkt 2 ist nicht erledigt, sondern widerlegt* (achtzehnter Lauf), und das ist
das Ergebnis der vier Läufe: `CompleteSpace D(ι, E)` ist **falsch** für die
summierte Metrik, weil `SkorokhodSpace.dist_exhaustionMax_le_distOn` die
Auswertung an jedem Fensterrand stetig macht. Die Reparatur ist Ethier--Kurtz'
Integral über den reellen Radius; sie steht in der Roadmap, der Radius ist
umgestellt (neunzehnter Lauf), die Metrik ist definiert (`intDist`), und ihre
einzige zusätzliche Beweispflicht — die Meßbarkeit des Integranden — ist
bezahlt. Was von `CompleteSpace` unabhängig von der Metrik war, ist bewiesen:
die unendliche Komposition der Zeitwechsel samt Surjektivität des Grenzwerts
(siebzehnter Lauf) und die beiden Auffangsätze für den Grenzpfad.

*Punkt 3 ist unberührt geblieben*, und das ist die eine Abweichung vom
Auftrag: die meßbare Einbettung steht weiterhin als `sorry`. Der Grund ist, daß
Punkt 2 nicht abgearbeitet, sondern umgeworfen wurde und die Reparatur die
Läufe achtzehn und neunzehn gekostet hat.

*Punkt 4 ist zur Hälfte erledigt* (sechzehnter Lauf): `modulus` ist definiert
statt `sorry`, samt `IsSubdivision`, `subdivisionOsc` und zwei Sätzen über sie;
`tendsto_modulus` und das Kompaktheitskriterium sind offen.

*Was als Nächstes zu tun ist*, steht am Ende des neunzehnten Laufberichts: die
vier Axiome von `intDist`, dann die Umhängung der `MetricSpace`-Instanz, dann
`CompleteSpace`.

*Der ursprüngliche Wortlaut der Aufgabe:*

### ~~Aufgabe: die nächsten vier Läufe an `SkorokhodSpace`~~

`WeakConvergence` hat seit dem 2026-09-07 rund fünfzehn Läufe bekommen und steht
bei zwei `sorry`, von denen eines Absicht ist. `SkorokhodSpace` hat seit dem
2026-09-07 vormittags keinen gesehen und steht bei elf. Für die Einreichung
zählt die schwächste Datei, also wird jetzt dort gearbeitet.

**Diese Aufgabe gilt für vier Läufe.** Trage nach jedem Lauf einen Zwischenstand
hier ein — welcher Punkt fiel, woran der nächste hängt, und der wievielte von
vieren es war. Streiche sie erst nach dem vierten, oder früher, wenn die Datei
kein `sorry` mehr trägt.

**Reihenfolge, und sie ist begründet, nicht beliebig:**

1. **Die `MetricSpace D(ι, E)`-Instanz ohne Basispunkt** (`:1653`). Der Befund
   des fünften Laufs vom 2026-09-07 lautet: ihr fehlt **kein Axiom**, sondern der
   Basispunkt — `SkorokhodSpace.metricSpace (t₀ : ι)` ist bewiesen, samt allen
   vier Axiomen und der Endlichkeit des Supremums. Was fehlt, ist die
   Entscheidung, wie die parameterlose Instanz an ihren Basispunkt kommt, und
   das ist eine Signaturfrage. Zwei Wege stehen offen: `[Nonempty ι]` plus
   `Classical.arbitrary`, oder eine Typklasse `[BasePoint ι]`. Wähle einen,
   **begründe die Wahl im Bericht**, und ziehe die zehn Deklarationen darunter
   nach. Das ist der Angelpunkt: `CompleteSpace`, `SeparableSpace` und
   `PolishSpace` (`:1655`–`:1657`) hängen alle daran und sind ohne sie nicht
   einmal formulierbar.
2. **`CompleteSpace`, `SeparableSpace`, `PolishSpace`** — in dieser Reihenfolge.
   Die Vollständigkeit ist Billingsleys Argument der unendlichen Komposition,
   längs der Ausschöpfung zusammengesetzt; die Separabilität sind die
   Treppenpfade mit Sprungzeiten in einer abzählbar dichten Menge. **Beides
   existiert schon außerhalb von Mathlib** — siehe `rem:skorokhodform` im
   Manuskript und `rem:bmrepo`: die Lizenzfrage ist geklärt, der Code darf
   verwendet werden, aber die Roadmap darf **keinen Implementierer dorthin
   schicken**, wo keine Lizenz steht. Lies, was zu lesen ist, und schreibe
   eigenen Beweis.
3. **Die meßbare Einbettung** (`:1677`, `:1682`): daß die Koordinaten die
   Borel-σ-Algebra erzeugen. Das ist `thm:fdd` im Manuskript und wird von
   `MartingaleProblems` Meilenstein 11 gebraucht.
4. **Meilenstein 7, Modul und Kompaktheit** (`:1687`–`:1695`). `modulus` ist
   heute `sorry` als **Definition** — und eine Definition mit `sorry`-Rumpf macht
   jeden Satz über sie zu einer Aussage über `sorryAx`. Definiere sie zuerst
   wirklich, dann `tendsto_modulus`, dann das Kompaktheitskriterium.

**Was nicht zählt.** Ein `sorry` durch ein schwächeres Statement zu ersetzen; die
Aussage so abzuschwächen, daß sie leicht wird, ohne es zu sagen; oder die
Signaturfrage aus Punkt 1 zu umgehen, indem der Basispunkt überall als Parameter
mitgeschleppt wird — das ist zwar richtig, aber es ist die Aufgabe nicht.

**Was zählt.** Bewiesene Deklarationen, jede mit `#print axioms` geprüft, und
bei jeder Abweichung vom obigen Weg ein Satz darüber, warum.

**Zwischenstand nach dem ersten von vieren (2026-09-08, sechzehnter Lauf des
Tages).** Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-08, sechzehnter Lauf
des Tages". `SkorokhodSpace/Suggested.lean` steht bei **acht** `sorry` statt elf.

*Punkt 1 ist erledigt, und die Wahl ist die Typklasse.* `class BasePoint (α)
where basePoint : α`, mit `Real.instBasePoint := ⟨0⟩` und `BasePoint.ofMem` für
die drei Teilraum-Instanzen. Der Grund gegen `[Nonempty ι]` samt
`Classical.arbitrary` ist einer und er ist entscheidend: der so gewonnene Punkt
ist **opak**, `dist f g` auf `D(ℝ, E)` wäre nie mit `totalDist 0 f g` zu
identifizieren, und damit ließe sich kein einziges der acceptance examples der
Meilensteine 4 bis 7 überhaupt hinschreiben — sie nennen alle ihren Basispunkt,
und alle nennen `0`. Mit `BasePoint` ist die Identifikation
`SkorokhodSpace.dist_eq`, und sie ist `rfl`. `SkorokhodSpace.instMetricSpace`
hängt an `propext`, `Classical.choice`, `Quot.sound` und an nichts sonst.

*Zwei weitere `sorry` fielen mit.* `SkorokhodSpace.instPolishSpace` ist
`inferInstance` (Mathlib baut `PolishSpace` aus `SeparableSpace` und einer
vollständigen Metrik) und schuldet nichts Eigenes mehr. Und `modulus` aus
Punkt 4 ist **definiert** statt `sorry`, samt `IsSubdivision`,
`subdivisionOsc`, `modulus_mono` und
`modulus_eq_zero_of_exhaustion_subsingleton`; die eine Abweichung ist der
Wertebereich `ℝ≥0∞` statt `ℝ`, begründet im Bericht und an der Deklaration.

*Punkt 2 hat seine erste Sprosse.* `IsCadlag.of_tendstoUniformly` ist bewiesen —
der gleichmäßige Limes càdlàg-Pfade ist càdlàg, unter `[CompleteSpace E]` —, und
das ist die Stelle, an der `CompleteSpace D(ι, E)` seinen Grenzpfad auffängt.

*Woran der nächste hängt.* Nicht mehr an der Signatur.
`CompleteSpace D(ι, E)` steht auf drei benannten Schritten, von denen zwei
bewiesen sind: `SkorokhodSpace.exists_lt_distOn_add` liefert die Zeitwechsel,
`TimeChange.tendsto_of_summable_norm` (offen) setzt sie unendlich zusammen,
`IsCadlag.of_tendstoUniformly` fängt den Limes auf. Der harte Punkt der offenen
Sprosse ist nicht die Konvergenz, sondern die **Surjektivität** des
Grenzzeitwechsels.

**Zwischenstand nach dem zweiten von vieren (2026-09-08, siebzehnter Lauf des
Tages).** Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-08, siebzehnter Lauf
des Tages". Die Datei steht weiterhin bei **acht** `sorry` — dieser Lauf hat
keines gestrichen, sondern die Sprosse gebaut, an der zwei von ihnen hängen.
Fünfzehn neue Deklarationen, alle mit `#print axioms` geprüft und alle nur auf
`propext`, `Classical.choice`, `Quot.sound`.

*Die offene Sprosse aus Punkt 2 ist zu.*
`TimeChange.exists_tendsto_of_summable_norm`: sind alle `l n` in
`TimeChange.fixing t₀` und ist `‖l n‖ ≤ γ n` mit summierbarem `γ`, so
konvergieren die Teilkompositionen `TimeChange.partialComp l n` punktweise gegen
einen Zeitwechsel `L` mit `L ∈ fixing t₀` und `‖L‖ ≤ ∑' γ`. Dazu
`TimeChange.exists_tendsto_norm_tail_le` mit der Rate
`‖(partialComp l n)⁻¹ * L‖ ≤ ∑' i, γ (n+i)` — ohne sie sagt die Existenz nur,
daß ein Limes da ist, mit ihr ist die `n`-te Näherung quantitativ nah.

*Die Surjektivität, und sie war wirklich der Punkt.* Ein punktweiser Limes von
Ordnungsisomorphismen ist umsonst monoton und injektiv; daß sein Bild ganz `ι`
ist, folgt nicht — der Index ist nicht zusammenhängend vorausgesetzt, eine der
vier laufenden Instanzen ist `AddSubgroup.zmultiples (1:ℝ)`. Das Mittel ist,
**dieselbe Rechnung auf den Inversen zu führen**: aus
`(partialComp l (n+1))⁻¹ = (l n)⁻¹ * (partialComp l n)⁻¹` folgt, daß die inverse
Folge einen Punkt um genau die Verschiebung von `(l n)⁻¹` bewegt, gelesen auf dem
um `exp (∑' γ)` vergrößerten Fenster; sie ist also ebenfalls Cauchy, hat einen
Limes `M`, und `partialComp l n ((partialComp l n)⁻¹ t) = t` geht in den Limes
über. Der Grenzzeitwechsel ist damit eine Bijektion mit benanntem Inversen.

*Und sechs Aussagen zum Zusammenbau*: `SkorokhodSpace.min_one_distOn_le`,
`SkorokhodSpace.distOn_le_of_two_pow_mul_lt_one` und
`SkorokhodSpace.totalDist_le_sum_add` für den Übergang zwischen Metrik und
Fenster in beiden Richtungen, `exhaustion_subset_of_le`, `clamp_clamp_of_le` und
`SkorokhodSpace.restrictExhaustion_restrictExhaustion` für die algebraische Seite
der Verträglichkeit.

*Woran der nächste hängt.* `CompleteSpace D(ι, E)` steht jetzt auf sechs
benannten Punkten, fünf davon bewiesen. Offen ist allein die **Verträglichkeit
der Fenstergrenzwerte**: die Konstruktion liefert je Fenster einen Limes, mit
von `m` abhängigen Zeitwechseln, und ein einziges `f : D(ι, E)` muß für alle `m`
zugleich taugen. Der naheliegende Weg `distOn t₀ m ≤ distOn t₀ (m+1)` geht
**nicht** — die beiden `clamp` stehen an einem Punkt des kleineren Fensters nicht
zusammen —, der Punkt ist über die Trunkierungen zu führen und steht als
`SkorokhodSpace.exists_restrictExhaustion_limit` in Meilenstein 5.

**Zwischenstand nach dem dritten von vieren (2026-09-08, achtzehnter Lauf des
Tages).** Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-08, achtzehnter Lauf
des Tages". Die Datei steht bei **fünf** `sorry` statt acht. Dreizehn neue
Deklarationen, alle mit `#print axioms` geprüft und alle nur auf `propext`,
`Classical.choice`, `Quot.sound`.

*Punkt 2 ist nicht erledigt, sondern widerlegt, und das ist das Ergebnis.*
`CompleteSpace D(ι, E)` ist **falsch** für die Metrik von Meilenstein 4, und der
Grund ist ein Zweizeiler, den drei Läufe übersehen haben:
`SkorokhodSpace.dist_exhaustionMax_le_distOn` — für `b = exhaustionMax t₀ m` und
**jeden** zulässigen Zeitwechsel `λ` liegt `t = max (λ⁻¹ b) b` so, daß
`clamp t = clamp (λ t) = b`, also enthält das Supremum in `distOn` den Term
`r (f b) (g b)` und das Infimum kommt nicht darunter. Damit erzwingt die Metrik
punktweise Konvergenz an allen Fensterrändern (für `ℝ` mit `t₀ = 0`: an allen
ganzen Zahlen), was die $J_1$-Topologie nicht tut.

*Zwei Folgerungen, beide in Lean.*
`SkorokhodSpace.continuous_eval_exhaustionMax`: die Auswertung am Fensterrand ist
stetig, an jedem Pfad, mit Sprung oder ohne. Und
`SkorokhodSpace.exists_jump_continuousAt_eval`, der konkrete Zeuge in `D(ℝ, ℝ)`,
der `SkorokhodSpace.continuousAt_eval` widerlegt — das war der zweite falsche
`sorry`. Die Cauchy-Folge ohne Grenzwert ist
`x n = 1_{(-∞, 1 + 1/(n+1))}`, von Hand gerechnet und im Bericht vollständig
ausgeführt; ihr Kern, `w 1 = 1` für jeden Kandidaten, ist der bewiesene Satz.

*Entfernt*, mit Begründung an der Stelle: `instCompleteSpace` und
`continuousAt_eval` (falsch), `instSeparableSpace` und `instPolishSpace`
(Aussagen über eine Metrik, die keine Skorokhod-Metrik ist). *Unberührt*: alles
über `TimeChange` und alles über `distOn` — die fünfzehn Deklarationen des
siebzehnten Laufs eingeschlossen. `distOn` ist wörtlich Ethier--Kurtz'
`d(x, y, λ, u)` und übersteht die Reparatur.

*Die Reparatur, und sie steht in `SkorokhodSpace/README.md`, Meilenstein 4.* Der
Radius wird reell und die Metrik ein Integral,
`∫ u in Ioi 0, exp (-u) * min 1 (…)`, mit dem Infimum über `λ` außerhalb. Die
schlechten Radien eines Pfadpaars sind abzählbar, also Lebesgue-null; genau
deshalb schreiben Ethier--Kurtz ein Integral und Billingsley eine Rampe, und die
Rampe scheidet hier aus, weil sie Pfadwerte mit Skalaren multipliziert.

*Und die Probe, die es hätte finden müssen.* Das **erste acceptance example von
Meilenstein 4** ist für die summierte Metrik falsch — beim Radius `1` ist
`f 1 = 1`, `g ε 1 = 0`, also `distOn 1 f (g ε) ≥ 1` für jedes `ε`. Es steht seit
dem 2026-09-07 da. Ein acceptance example, das nur dasteht, prüft nichts.

*Woran der vierte hängt.* Nicht mehr an einem Beweis, sondern an einer Signatur:
`exhaustion`, `clamp`, `restrictExhaustion`, `distOn` auf reellen Radius
umzustellen. Das ist mechanisch — `m` geht in die vorhandenen Beweise nur als
`(m : ℝ)` ein — und ohne es ist keiner der offenen Punkte formulierbar. Was
danach kommt, liegt bereit: `IsCadlag.of_forall_eventuallyEq` und
`IsCadlag.of_tendstoUniformlyOn_exhaustion` sind im selben Lauf bewiesen — càdlàg
ist eine lokale Eigenschaft, und gleichmäßige Konvergenz auf jedem Fenster genügt
—, und sie sind die Stelle, an der `SkorokhodSpace.tendsto_of_partialComp` seinen
Grenzpfad auffängt. Beide sind von der Metrik unabhängig.

Zurzeit stehen hier sonst keine offenen Aufgaben.

### ~~Aufgabe: geht Schritt 1 von `thm:MZconv` über den polnischen Raum $M_E$?~~ *(gestellt 2026-09-08 vom Nutzer, erledigt 2026-09-08, elfter Lauf des Tages)*

**Ergebnis** in `Facts/INVENTAR.md`, Läufe, „2026-09-08, elfter Lauf des
Tages". Kurz, in den vier Punkten der Aufgabe: **(a) ja, (b) ja, (c) ja,
(d) ja** — der Fund trägt vollständig.

*(a) $\DE$ ist borelsch in $(M_E,d_m)$*, und der Beweis braucht kein
Lusin--Souslin und nicht einmal, daß $M_E$ polnisch ist. Die Pseudopfad-Abbildung
$\gamma$ ist auf **ganz** $M_E$ injektiv — `fact:pseudopath` sagt es wörtlich
(„identifies two paths exactly when they agree $\lambda$-a.e."), das Manuskript
zieht daraus nur die schwächere Folgerung für $\DE$ — und stetig
(Teilfolgenprinzip plus dominierte Konvergenz gegen $C([0,\infty]\times\hat E)$).
Da $\gamma(\DE)$ nach `fact:pseudopath`(ii) borelsch im kompakten Modell ist, ist
$\DE = \gamma^{-1}(\gamma(\DE)) \cap M_E$ borelsch.

*(b) Die Spur ist $\sigma(\pi_u)$*, zweimal unabhängig: $\Bor(Y)=\Bor(X)|_Y$ gilt
für **jeden** Teilraum eines topologischen Raums, und die Teilraumtopologie ist
nach `fact:pseudopath`(i) die Pseudopfad-Topologie, deren Borelfeld
`fact:pseudopath`(iii) benennt. Kurtz' Proposition 4.5 (S. 1026) sagt dasselbe
von der Seite der f.ü.-endlichdimensionalen Verteilungen her.

*(c) Der Rest hält*, und Schritt 2 wird **kürzer**: auf dem $M_E$-Weg *ist*
$\int \rho(\tilde X_n,\tilde X)\dif\lambda$ die Metrik $d_m$, die f.s. gegen
$0$ geht, statt erst aus der Konvergenz im Maß gewonnen werden zu müssen.

*(d) `fact:cmt` wird nicht in nicht-polnischer Allgemeinheit gebraucht* — und
das war schon **vor** dieser Prüfung so, aus einem von ihr unabhängigen Grund:
`set:abstract` verlangt unter (E3) für $F$ ausdrücklich eine polnische Topologie,
`def:weakstrong` sagt „let $F$ be Polish", und der Beweis von `thm:MZconv`
benutzt gar kein `fact:cmt`, sondern (C1$'$) aus `rem:absconvtopfree` — er sagt
es selbst. Zwischen `:9314` und `:9400` steht kein einziges `\ref{fact:cmt}`.

*Was es kostet, ehrlich genannt:* die Konstruktion von $M_E$ selbst — Quotient,
Metrik, Vollständigkeit (Kurtz beweist sie), Separabilität (Kurtz: „left to the
reader"). Das steht jetzt als `WeakConvergence` **Meilenstein 6** in der
Roadmap, mit Mathlibs `MeasureTheory.AEEqFun` als Ort, `TendstoInMeasure` als
Anschluß und `Measure.IsSeparable` als richtiger Hypothese.

*Am Manuskript:* `rem:MZcost`, zweiter Absatz, ist korrigiert; `check.py` meldet
`clean` (133 Seiten). Der erste Satz („The path space is not Polish. It is
separable metric …") bleibt, weil er wahr ist; ersetzt ist allein die Folgerung,
durch den Weg über $M_E$ samt `\Ku`-Zitat. **Nicht** angefaßt ist die Liste in
`ssec:available`: sie führt `fact:cmt` und `fact:PSpolish` unter „to be built"
ohne Angabe einer Allgemeinheit und bleibt damit richtig.

*Nicht weggeworfen:* `exists_ae_tendsto_of_tendsto` und die Deklarationen der
Läufe fünf bis zehn. Der polnische Fall ist ein Spezialfall des separablen, und
Mathlib hat die Skorokhod-Darstellung in keiner Fassung; was gebaut ist, deckt
beide Gebrauchsstellen ab. Was sich ändert, ist die Reihenfolge der Not:
`WeakConvergence` M3 ist nicht mehr der Engpaß von `thm:MZconv`.

*Der ursprüngliche Wortlaut der Aufgabe:*

### ~~Aufgabe: geht Schritt 1 von `thm:MZconv` über den polnischen Raum $M_E$?~~

Der Nutzer hat Kurtz (1991), *Random time changes and convergence in distribution
under the Meyer--Zheng conditions*, Ann. Probab. **19**, 1010--1034, beigebracht;
das PDF liegt unter `~/Uni/Download/Papers/Kurtz1991a.pdf` (JSTOR-Scan, reines
Bild, also seitenweise mit dem Read-Werkzeug zu lesen, `pdftotext` liefert
nichts). Daraus ein Fund, der den schwersten offenen Punkt der Roadmap erledigen
könnte und der **noch nicht geprüft ist**.

**Der Fund.** Kurtz definiert auf Seite 1022 auf $M_E[0,\infty)$ — den
Äquivalenzklassen Borel-meßbarer $E$-wertiger Funktionen auf $[0,\infty)$, zwei
gleich, wenn sie Lebesgue-f.ü. übereinstimmen — die Metrik
$$d_m(x,y) = \int_0^\infty e^{-t}\,\bigl(1 \wedge r(x(t),y(t))\bigr)\,dt$$
und stellt fest: sie metrisiert die Konvergenz in Maß, und
$(M_E[0,\infty), d_m)$ ist **vollständig und separabel**, sobald $(E,r)$ es ist —
also polnisch, und `(E3)` fordert $E$ polnisch ohnehin. Nicht polnisch ist nur
$D_E$ **als Teilmenge** davon; dort ist es bloß borelsch. Das ist etwas anderes,
als `rem:MZcost` daraus macht.

**Die Behauptung, die zu prüfen ist.** Schritt 1 von `thm:MZconv` (Manuskript, um
Zeile 9335) beruft sich auf `fact:PSpolish` für den nicht-polnischen
Pseudopfad-Raum $D_E$. Statt dessen sollte gehen:

1. Die Inklusion $D_E \hookrightarrow M_E$ ist stetig — die Pseudopfad-Topologie
   ist nach `fact:pseudopath`(i) genau die Konvergenz in $\lambda$-Maß, und $d_m$
   metrisiert eben diese. Also überträgt sich $X_n \Rightarrow X$ nach $M_E$.
2. Auf dem **polnischen** $M_E$ liefert die gewöhnliche Skorohod-Darstellung die
   f.s. konvergente Realisierung.
3. Jedes $\tilde X_n$ hat das Gesetz von $X_n$, das auf $D_E$ konzentriert ist;
   ist $D_E$ borelsch in $M_E$, so ist $\tilde X_n$ f.s. càdlàg.
4. Schritt 2 braucht ohnehin nur die Konvergenz in $\lambda$-Maß.

**Zu prüfen, in dieser Reihenfolge**, weil ein Scheitern die späteren Punkte
erübrigt:

(a) Ist $D_E$ borelsch in $(M_E, d_m)$? `fact:pseudopath`(ii) sagt es für das
    MZ-Modell (Borelmenge eines kompakten metrisierbaren Raums); für $M_E$ ist es
    zu belegen oder zu widerlegen. **Das ist der Angelpunkt.**
(b) Ist die Spur der Borel-σ-Algebra von $M_E$ auf $D_E$ dieselbe wie
    $\sigma(\pi_u)$, also die aus `fact:pseudopath`(iii)? Sonst reden Schritt 1
    und Schritt 2 nicht von derselben σ-Algebra.
(c) Hält der Rest des Beweises von `thm:MZconv` unverändert?
(d) Wird `fact:cmt` an derselben Stelle in nicht-polnischer Allgemeinheit
    gebraucht, oder erledigt sich das mit?

**Was daran hängt.** Trägt es, so braucht die Roadmap `fact:PSpolish` und
`fact:cmt` **nur für polnische Räume**, und der Punkt, an dem `WeakConvergence`
seit dem Abend des 2026-09-07 arbeitet (`exists_ae_tendsto_of_tendsto` für bloß
separables $S$), entfällt oder wird zur Zugabe. Trägt es nicht, so sag **woran**
es bricht — das ist dann die Begründung, die `rem:MZcost` heute fehlt.

**Manuskript.** `rem:MZcost` behauptet im zweiten Absatz, eine Formalisierung
*müsse* beides in nicht-polnischer Allgemeinheit haben. Ist die Prüfung positiv
und vollständig, so ist das falsch und die Stelle zu korrigieren; sonst bleibt
das Manuskript unberührt und der Befund steht im Inventar.

**Nicht** die laufende Arbeit an `exists_ae_tendsto_of_tendsto` wegwerfen, bevor
die Prüfung durch ist. Was dort bewiesen ist, bleibt richtig und ist auch im
polnischen Fall brauchbar.

### ~~Aufgabe: Ionescu--Tulcea ist in Mathlib, und der Befund des 20. Laufs steht schief~~ *(gestellt 2026-09-08 vom Nutzer, erledigt 2026-09-08, neunter Lauf des Tages)*

**Ergebnis** in `Facts/INVENTAR.md`, Läufe, „2026-09-08, neunter Lauf des
Tages". Kurz, in den drei Teilen der Aufgabe:

*Erstens.* Berichtigt an drei Stellen — durchgestrichen samt Berichtigung im
Bericht des achten Laufs, in der Tabellenzeile `fact:PSpolish`, und der Absatz
„The common space" in `WeakConvergence` Meilenstein 3 neu geschrieben, mit
`ProbabilityTheory.Kernel.traj` (`IonescuTulcea/Traj.lean:518`, gleiche Zeile in
v4.33.1 **und** auf `upstream/master` `572e4d091bc`), `traj_map_frestrictLe`
(`:530`), `trajMeasure` (`:763`), `Kernel.IsMarkovKernel.comap`
(`Composition/MapComap.lean:187`). Warum die Suche danebenging: **nicht** am
Nichtfinden — der achte Lauf hatte `traj` in der Hand und verwarf sie mit „für
eine Filtration", einer *Beschreibung* statt einer *Voraussetzung*, und las
damit die Allgemeinheit von `traj` (die Kerne dürfen die Vergangenheit lesen)
als Einschränkung; überdies stand `traj` mit Namen und Datei bereits fünfmal im
eigenen Bestand (`TauCeti/KolmogorovExtension/README.md`, das Inventar selbst).
Die „Regel für den Negativbefund" im Inventar hat dafür eine zweite Hälfte
bekommen: wer einen Kandidaten verwirft, nennt die Voraussetzung, an der er
scheitert, und durchsucht vorher den eigenen Bestand.

*Zweitens, die Abwägung, an der Gebrauchsstelle gerechnet.* `fact:PSpolish` wird
an zwei Stellen konsumiert: `rem:EKrelcompact` (dort `D_E` unter `J_1`, polnisch)
und `thm:MZconv` Schritt 1 (dort `D_E` in der **Pseudopfad**-Topologie,
nach `fact:pseudopath`(ii) separabel metrisch und ausdrücklich **nicht**
polnisch). Der überraschende Befund: `StandardBorelSpace` ist nicht
`PolishSpace`, sondern eine Eigenschaft der σ-Algebra allein (`Polish/Basic.lean:81`),
und an der Pseudopfad-Stelle ist sie **erfüllt** — `fact:pseudopath`(iii) sagt,
daß die Borel-σ-Algebra dieselbe ist wie die von `J_1`, und unter `J_1` ist der
Raum polnisch. Mathematisch steht es also ohnehin da. Frei ist es trotzdem
nicht, und zwar aus drei benannten Gründen: (1) `fact:PSpolish` ist für `S`
separabel formuliert, und separabel metrisch impliziert nicht standard-borelsch
(Zeuge: nicht-borelsches `A ⊆ ℝ`, sonst machte Lusin--Souslin,
`MeasurableSet.image_of_measurable_injOn`, `A` in `ℝ` borelsch) — der
Meilensteinpunkt wäre schwächer als der Fact, den er abtragen soll; (2) die
Einlösung an der Gebrauchsstelle ist ein Satz über den Pseudopfadraum, den keine
Roadmap baut („pseudo-path" kommt unter `TauCeti/` nirgends vor); (3)
`Measure.condKernel` verlangt zusätzlich `[Nonempty Ω]`. **Also: die Entscheidung
des achten Laufs war im Ergebnis richtig und nur die Begründung schief** — sie
trägt jetzt allein auf der Desintegration, nicht mehr auf einer Abwesenheit.

*Drittens.* Die Route wird **nicht** gewechselt, und der Grund ist gerechnet und
nicht vermutet: der Verklebeweg beweist eine echt kleinere Aussage und würfe die
sieben bewiesenen Aussagen des achten Laufs für eine Montage vergleichbarer
Länge weg. Mitgekommen ist statt dessen der Zeuge, der die Berichtigung
typprüfbar macht: `ProbabilityTheory.exists_kernel_pi_of_markov` in
`TauCeti/KolmogorovExtension/scratch/TrajPi.lean` baut aus Markovkernen
`K : ℕ → Kernel E E` über bloßem `[MeasurableSpace E]` einen Markovkern
`η : Kernel E (ℕ → E)` mit `(η y).map (fun x ↦ x 0) = dirac y` und
`(η y).map (fun x ↦ x (n+1)) = K n y`; durch `lake env lean` gegen v4.33.1, mit
`#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft.

*Der ursprüngliche Wortlaut der Aufgabe:*

### ~~Aufgabe: Ionescu--Tulcea ist in Mathlib, und der Befund des 20. Laufs steht schief~~

Der zwanzigste Lauf hat den Schritt (c2) der Skorohod-Darstellung gegen das
Verkleben entschieden, mit der Begründung, Mathlib habe kein abzählbares Produkt
von Kernen: gesucht wurde nach `infinitePi` und nach `def pi` unter
`Probability/Kernel/`. Es heißt aber weder so noch liegt es dort. Es heißt
**`ProbabilityTheory.Kernel.traj`** und steht in
`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:518`, als *Ionescu--Tulcea
Theorem* im Doc-Kommentar benannt:

```
variable {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
noncomputable def traj (a : ℕ) : Kernel (Π i : Iic a, X i) (Π n, X n)
```

Voraussetzungen: `[∀ n, MeasurableSpace (X n)]` und Markov, **sonst nichts** —
keine Topologie. Die charakterisierende Eigenschaft ist `traj_map_frestrictLe`
(`:530`): die Projektion auf `Iic b` ist `partialTraj κ a b`. Der Nutzer hat es
gefunden, nicht der Lauf; das ist die Suchregel weiter unten, und sie hat hier
nicht gegriffen.

**Erstens: das Inventar richtigstellen.** Der Befund „Mathlib hat kein
abzählbares Produkt von Kernen" ist falsch und steht so im Bericht des
zwanzigsten Laufs und in Meilenstein 3. Trage die Berichtigung dort ein, mit dem
Namen, der Datei und der Zeile, und schreibe dazu, *warum* die Suche danebenging
— damit die nächste nach der Aussage sucht statt nach der Vokabel.

**Zweitens: die beiden Wege gegeneinander abwägen.** Die Begründung stand auf
zwei Beinen; das zweite, die Desintegration, trägt noch. `Measure.disintegrate`
und `condKernel` gibt es, aber der brauchbare Fall verlangt
`StandardBorelSpace`. Der jetzige Weg — alle Stufen auf einmal auf
`(E × (ℕ → ℝ)) × (ℕ × ℕ → E)`, EK Lemma 3.1.3 mit `N = ∞` — zahlt diesen Preis
nicht: seine sieben Aussagen nennen über `E` nichts als `MeasurableSpace E`. Die
Frage ist also **nicht**, welcher Weg schöner ist, sondern:

> Kostet `StandardBorelSpace E` an dieser Stelle etwas, oder steht es ohnehin da?

Beantworte sie an der Stelle, wo die Skorohod-Darstellung *gebraucht* wird
(`fact:PSpolish`, Meilenstein 3, und was im Manuskript darauf zeigt), nicht im
luftleeren Raum. Kommt heraus, daß der Raum dort ohnehin polnisch ist, dann ist
`StandardBorelSpace` gratis und der Verklebeweg womöglich der kürzere; kommt
heraus, daß die Darstellung anderswo unter schwächeren Annahmen gebraucht wird,
dann war die Entscheidung im Ergebnis richtig und nur die Begründung schief.
Beides ist ein Ergebnis. Was **nicht** zählt, ist eine Präferenz ohne Rechnung.

**Drittens, nur wenn Zeit bleibt:** wechsle die Route nicht auf Verdacht. Der
bestehende Weg ist weit gediehen; ein Wechsel lohnt nur, wenn die Abwägung ihn
deutlich trägt, und dann als eigener Lauf mit eigenem Zwischenstand.

### ~~Aufgabe: das Erreichte prüfen, und nach Verallgemeinerungen suchen~~ *(gestellt 2026-09-07 vom Nutzer, erledigt 2026-09-07, sechzehnter Lauf des Tages)*

Ergebnis, damit es nicht noch einmal gesucht wird: geprüft mit einem
`Lean.collectAxioms`-Metaprogramm je Datei. Zwei Instanzen in `SkorokhodSpace`
hängen an `sorryAx`, ohne ein eigenes `sorry` zu tragen — sie erben es vom
Platzhalter `MetricSpace D(ι, E)`. Der Zeuge zu
`not_isQuasiLeftContinuous_of_atom` ist jetzt Lean statt Skizze
(`exists_index_witness_for_atom`). Verallgemeinert wurde
`IsSeparating.of_subalgebra`, weg von `PolishSpace`. Ein Vorbehalt zum Werkzeug,
der beim nächsten Mal Zeit spart: `linter.unusedSectionVars` beantwortet, ob eine
Annahme **ungenutzt** ist, nicht, ob sie sich **abschwächen** ließe; sein
Schweigen schließt die Suche nicht ab. Wer sie fortsetzt, muß die Abschwächungen
einzeln versuchen.

*Der ursprüngliche Wortlaut der Aufgabe:*

### ~~Aufgabe: das Erreichte prüfen, und nach Verallgemeinerungen suchen~~

Dieser Lauf beweist nichts Neues. Er prüft, was dasteht, und sucht, wo es
allgemeiner sein könnte. Beides in dieser Reihenfolge, und das Prüfen zuerst,
weil eine Verallgemeinerung einer leeren Aussage wieder leer ist.

**Erster Teil: prüfen.** Für alle drei Dateien unter `TauCeti/*/Suggested.lean`:

1. `#print axioms` für jede bewiesene Deklaration. Jede, die von `sorryAx`
   abhängt, ist nicht bewiesen, sondern hängt an einem `sorry` weiter oben;
   nenne sie beim Namen. Das läuft am billigsten über eine angehängte Datei mit
   `#print axioms` je Deklaration, nicht über 200 Einzelaufrufe.
2. **Leere Aussagen.** Der Fehler ist zweimal vorgekommen — sieben Aussagen mit
   Rumpf `True` am 2026-09-05, `not_isQuasiLeftContinuous_of_atom` mit dem
   zulässigen Zeugen `A = ∅` am 2026-09-07 — und beide Male hat er einen ganzen
   Lauf gekostet. Prüfe jede Aussage darauf, ob ihre Hypothesen gemeinsam
   erfüllbar sind. Das Mittel ist, für jeden Satz mit nichttrivialen Hypothesen
   **einen Zeugen anzugeben**: eine Instanziierung, unter der die Voraussetzungen
   nachweislich gelten. Wo das mehr als ein paar Zeilen kostet, sag es im
   Bericht, statt es zu behaupten.
3. **Aussage gegen Absicht.** Vergleiche jede Aussage mit dem, was der
   `README.md` des Meilensteins und das Manuskript an der belegten Stelle
   behaupten. Sagt der Lean-Satz weniger, so ist der Beleg im Inventar zu weit.

**Zweiter Teil: verallgemeinern.** Die Frage ist nicht, was noch zu beweisen
ist, sondern was die vorhandenen Beweise schon hergeben.

4. **Hypothesen abbauen.** Für jede bewiesene Deklaration: welche
   Typklassen-Annahme wird wirklich gebraucht? Das Werkzeug ist `omit … in` —
   der Linter meldet, wenn eine weggelassene Annahme doch nötig war, so daß der
   Versuch billig und der Befund sicher ist. Reihenfolge: erst `ProperSpace ι`
   und `AdditiveDist ι`, dann `OrderTopology ι`, dann `LinearOrder ι` gegen
   `Preorder ι`. Beim Ziel dasselbe: geht `MetricSpace E` zu
   `PseudoMetricSpace E`, geht `ℝ` zu `RCLike 𝕜` oder zu einem Banachraum?
5. Trage jede erfolgreiche Abschwächung **in die Datei ein** — als geänderte
   Signatur oder als `omit`-Zeile, nicht als Bemerkung im Bericht.
6. Wo eine Verallgemeinerung möglich aussieht, aber der Beweis nicht durchgeht,
   nenne die Stelle, an der er bricht. Ein benanntes Hindernis ist mehr wert als
   eine Vermutung.

**Woran der Lauf gemessen wird:** an der Liste der Deklarationen, deren
Hypothesen er nachweislich verkleinert hat, und an der Liste derer, die er als
leer, als von `sorryAx` abhängig oder als schwächer-als-behauptet entlarvt hat.
Findet er nichts von beidem, so ist das ein Ergebnis und gehört mit den
durchgeführten Prüfungen ins Inventar — aber nur, wenn die Prüfungen wirklich
liefen.

Das Manuskript bleibt unberührt, es sei denn, eine Prüfung deckt dort eine
falsche Behauptung auf; dann gilt die übliche Regel.

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


### ~~Aufgabe: charakteristische Funktionen als trennende Klasse~~ *(gestellt 2026-09-06, erledigt 2026-09-06, dritter Lauf des Tages)*

**Ergebnis** in `Facts/INVENTAR.md`, Läufe, „2026-09-06, dritter Lauf des
Tages". Kurz: Punkt 1 eingetragen, an `upstream/master` `810b3888` **und** an
v4.33.1 belegt (die Zeilennummern unten sind die von v4.33.1; auf master
`:257`, `:462`, `:103`), nichts davon `deprecated`; mitgefunden, daß `charPoly`
eine **Stern**-Unteralgebra ist, also gerade die Konjugationsabgeschlossenheit
trägt, die `fact:stoneweierstrass` für $\K=\C$ eigens verlangt. Punkt 2 ist mit
einer Tabelle aller acht Fundstellen beantwortet, und die Strukturfrage ist an
**jeder** verneint: die beiden Stellen mit linearer Struktur helfen nicht —
$E=\R^d$ (§7.5) instanziiert gar keine trennende Klasse, sondern läuft über
Stroock--Varadhan, und $\mathcal S'(\R^d)$ ist nach `def:Ebundles` nicht
metrisierbar, scheitert also an `[PseudoEMetricSpace V]`. Die einzige konkrete
trennende Klasse des Manuskripts ist die Hawkes-Dualität, und sie ist ein
Beinahe-Treffer aus zwei unabhängigen Gründen kein Treffer: Laplace statt
Fourier, und $\hat E_t$ ist ein Untermonoid der Maße und kein $\R$-Modul.
Punkt 3 ist **negativ**: Meilenstein 1 spart keinen Punkt ein, Punkt für Punkt
begründet; der Ertrag ist der Beleg für seine Bauform und der Ausschluß
künftiger Charakter-Umwege. Zwei Auffälligkeiten mitgefunden, beide im
Inventar — `def:separating` ist nur für $\Cb(S)$ erklärt, während das
Manuskript „trennend" auch für $\Bdd(E)$ benutzt (folgenlos, weil
`IsSeparating` schon über beliebigen reellen Funktionen erklärt ist), und
`prop:hawkesduality`(D2) zitiert die Bestimmung eines Punktprozesses durch sein
Laplace-Funktional ohne `\begin{fact}` — Mathlib hat Punktprozesse überhaupt
nicht.

**Der Befund, vom Nutzer gefunden und am Quelltext bestätigt.** Mathlib hat
„charakteristische Funktionen trennen Maße" — `Measure.ext_of_charFun`
(`MeasureTheory/Measure/CharacteristicFunction/Basic.lean:248`) und
`Measure.ext_of_charFunDual` (`:453`), beide für **endliche** Maße unter
`[BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]`. Und es ruht
genau auf unserem Angelpunkt: der allgemeine `ext_of_integral_char_eq` (`:101`)
beginnt mit

```
apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    (separatesPoints_charPoly he he' hL hL')
```

also auf dem Satz aus `FiniteMeasureExt.lean`, den `WeakConvergence`
Meilenstein 1 seit dem 2026-08-29 führt. Charakteristische Funktionen sind in
Mathlib **kein eigenes Fundament**, sondern eine Anwendung der punktetrennenden
Unteralgebra; `charPoly` ist die von den Charakteren erzeugte Algebra, und
`separatesPoints_charPoly` liefert die Trennung.

**Zu tun.**

1. Trage den Befund bei `fact:sepcond` und `fact:stoneweierstrass` im Inventar
   ein: der Weg „punktetrennende Unteralgebra ⟹ Maße trennend" ist in Mathlib
   nicht nur vorhanden, sondern **tragend** — Mathlib benutzt ihn selbst für den
   prominentesten Spezialfall. Das ist ein Beleg für die Bauform von
   Meilenstein 1, kein neuer Punkt.

2. Prüfe, **wo das Manuskript trennende Klassen konkret instanziiert**, und ob
   die Charaktere dort eine gangbare Wahl sind. Die Einschränkung ist ernst und
   vorab zu nennen: `ext_of_charFun` verlangt lineare Struktur auf `E`
   (Banach- bzw. Innenproduktraum), während \eqref{E2} und \eqref{E3} nur
   einen polnischen metrischen Raum geben. Die Charaktere sind also **kein**
   Ersatz für die allgemeine trennende Klasse, wohl aber möglicherweise eine
   fertige Wahl für die konkreten Instanzen — $\R^d$, und der Fall
   $\mathcal S'(\R^d)$ aus `rem:E1why`. Nenne für jede Fundstelle, ob die
   Struktur da ist.

3. Ergibt sich daraus ein Punkt, den Meilenstein 1 **einsparen** kann, so
   streiche ihn und begründe es. Ergibt sich keiner, sage das ebenso deutlich —
   ein Negativbefund ist hier so nützlich wie ein Fund, und die Aufgabe ist dann
   erledigt und nicht offen.

Das Manuskript wird dabei nicht geändert; Auffälligkeiten kommen ins Inventar.


### ~~Aufgabe: acceptance examples für jeden Meilenstein~~ *(gestellt 2026-09-07, erledigt 2026-09-07, vierter Lauf des Tages)*

**Ergebnis** in `Facts/INVENTAR.md`, Läufe, „2026-09-07, vierter Lauf des
Tages". Alle **27** Meilensteine der vier Roadmaps tragen den Abschnitt
`**Acceptance examples.**` am Ende — `WeakConvergence` (5), `SkorokhodSpace`
(8), `KolmogorovExtension` (3), `MartingaleProblems` (1–11); 12 und 13 haben
wie verlangt keinen. Der Maßstab, den der Lauf angelegt hat und der beim
Weiterschreiben gilt: je Meilenstein ein **Paar** — die Instanz, an der die API
rechnet, und die danebenliegende, an der eine naheliegende falsche Definition
scheitert —, nicht vier positive Instanzen. Drei der Beispiele sind eigene
Rechnungen und nicht bloß Zitate (die trigonometrische Algebra trennt Punkte,
aber nicht stark; der schrumpfende Buckel scheidet die logarithmische von der
naiven Zeitänderungsnorm; die Ordnungskonvexität der Fenster hängt an
`AdditiveDist`, nicht an `clamp`).

*Der ursprüngliche Wortlaut der Aufgabe:*

### ~~Aufgabe: acceptance examples für jeden Meilenstein~~

**Warum.** Die Einreichung bei Tau Ceti steht in einer Woche an. Die gemergte
Roadmap `OneParameterSemigroups` — die einzige, die unmittelbar an unsere Arbeit
stößt, und diejenige, deren Reviewverlauf in
`TauCeti/VORBILD-OneParameterSemigroups.md` aufbereitet ist — führt je Teil die
Struktur **API → Meilenstein → acceptance examples**. Uns fehlt das Dritte.
Beispiele daraus, zur Kalibrierung des Anspruchs:

> **Acceptance examples.** The multiplication semigroup `S t f = e^{−t·m} f`
> (generator `−m`) and `e^{tA}` for bounded `A`; the resolvent matches the
> Neumann series `R(λ) = (λ−A)⁻¹`; the resolvent identity and `‖R(λ)‖ ≤ 1/λ`
> hold on these concretely.

> **Acceptance examples.** Bochner on `V = ℝ` recovers the classical statement;
> the case `V = 0` (no spatial variable) collapses BCR back to Bernstein.

**Was ein acceptance example ist, und was nicht.** Es ist eine **konkrete
Instanz**, an der sich prüfen läßt, ob die API des Meilensteins das leistet,
wofür sie gebaut wurde — benannt, mit dem Ergebnis, das herauskommen muß, und
so, daß ein Implementierer sie hinschreiben und rechnen kann. Es ist **kein**
weiterer Satz, keine Anwendung „später", und keine Wiederholung des
Meilensteinziels in anderen Worten. Ein gutes Beispiel deckt einen Fall ab, in
dem eine naheliegende falsche Definition scheitern würde.

**Zu tun.** Ergänze für **jeden** Meilenstein der vier Roadmaps unter
`TauCeti/` einen Abschnitt `**Acceptance examples.**` am Ende. Arbeite eine
Roadmap nach der anderen ab, von `WeakConvergence` beginnend; die Aufgabe darf
sich über mehrere Läufe ziehen und bleibt dann mit Zwischenstand stehen.

Woher die Beispiele kommen sollen, in dieser Reihenfolge:

1. **Aus dem Manuskript.** Es ist voll davon, und sie sind geprüft: die
   Sprungprozesse aus §7.4, Hawkes und der Volterra-Limes, `ex:invariance`,
   `ex:atomicdiscontinuity`, das Diamant-Gegenbeispiel, die $\omega$-Kette. Wo
   ein Meilenstein eine Manuskriptaussage trägt, ist deren Beispiel das
   natürliche.
2. **Aus den Gegenbeispielen, die diese Läufe gefunden haben** — der Diamant
   mit $m_c^2=m_am_b$, die Antikette mit Defekt $1/M$, der Zeuge gegen die
   gefensterte Norm, die $\emptyset$-Klasse auf dem einpunktigen Raum. Die sind
   besonders wertvoll, weil sie genau die naheliegenden falschen Definitionen
   ausschließen.
3. **Neu erfunden**, aber nur wenn 1 und 2 nichts hergeben, und dann so
   einfach wie möglich.

**Wo ein Beispiel schon als Lean dasteht**, nenne die Deklaration aus
`Suggested.lean`; das ist der stärkste Beleg, den ein acceptance example haben
kann. Wo es sich billig hinschreiben läßt, schreib es hin und übersetze es.

**Nicht** ändern: das Manuskript, die Meilensteinziele selbst, und die beiden
mit `roadmap-for-a-roadmap` gekennzeichneten Meilensteine 12 und 13 von
`MartingaleProblems` — die bekommen keine acceptance examples, weil sie
ausdrücklich nicht bearbeitet werden sollen.

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
