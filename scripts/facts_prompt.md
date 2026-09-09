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
2. `jumpProcess_isMPSolution` für beschränktes `lam` — das ist `thm:jumpMP`, und
   es ist **das eigentliche Ziel des Meilensteins**: die erste in Lean bewiesene
   Lösung eines Martingalproblems überhaupt.

   **Zwischenstand 2026-09-09, achtzehnter Lauf des Tages.** Der Satz ist noch
   nicht hingeschrieben; von seiner *Aussage* stehen jetzt aber alle Stücke bis
   auf zwei. Gebaut und geprüft sind der Erzeuger `jumpApply`, die Uhr
   `lebesgueClock : Clock ℝ≥0` — **der Index ist `ℝ≥0` und nicht `ℝ`**, weil
   `mpFamily` `[OrderBot ι]` verlangt —, das Anfangsgesetz des Prozesses
   (`jumpMeasure_map_jumpProcess_zero`, nicht dasselbe wie das der Kette) und
   die Gedächtnislosigkeit der Exponentialverteilung (`expMeasure_Ioi_add`, die
   Mathlib nicht hat und die der einzige nicht buchhalterische Schritt des
   Beweises sein wird).

   ~~**Es fehlen zwei Stücke, und das zweite ist das riskante:** der Erzeuger als
   *Menge* `jumpOperator lam mu : Set ((E → ℝ) × (E → ℝ))`, und die
   **Filtration**.~~ *(beide erledigt 2026-09-09, neunzehnter Lauf des Tages)*

   **Zwischenstand 2026-09-09, neunzehnter Lauf des Tages.** Die beiden fehlenden
   Stücke stehen, und mit ihnen die **erste Hälfte des Satzes**: achtzehn neue
   Deklarationen in `TauCeti/MartingaleProblems/Suggested.lean`, alle durch
   `lake env lean` gegen v4.33.1 und alle mit `#print axioms` auf `propext`,
   `Classical.choice`, `Quot.sound` geprüft. `jumpProcess_isMPSolution` ist
   hingeschrieben und trägt sein `sorry`; was ihm fehlt, ist allein die bedingte
   Erwartung. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-09, neunzehnter
   Lauf des Tages".

   **Der angesagte Grund gegen `Filtration.natural` war der falsche, und der
   richtige ist billiger.** Nicht `StronglyMeasurable` über einem topologischen
   `E` ist das Hindernis: die Deklaration
   (`Probability/Process/Filtration.lean:395`) trägt
   `[TopologicalSpace (β i)] [MetrizableSpace (β i)] [BorelSpace (β i)]`, also
   ist sie über einem bloßen `[MeasurableSpace E]` **nicht einmal
   hinschreibbar**. Gebraucht wird von alledem nichts — das Feld `le'` verlangt
   Meßbarkeit und sonst nichts —, also steht jetzt `naturalFiltration` mit
   `Measurable` und ohne Topologie da. Kein Beweis über Treppenpfade, sieben
   Zeilen.

   **Was wirklich riskant war, ist die Progressivität, und sie ist nicht
   `Clock.IsProgressive`.** Für `StronglyAdapted` muß der Kompensator
   `ω ↦ ∫_0^t Af(X_s ω) ds` meßbar für `𝓕 t` sein, also `(s, ω) ↦ Af(X_s ω)`
   gemeinsam meßbar. Der Beweis nähert `X_s` durch `X_r` mit `r` etwas oberhalb
   von `s` und geht zum Limes — und ein Limes **`E`-wertiger** meßbarer
   Abbildungen ist nur meßbar, wenn die Diagonale von `E` es ist, was für eine
   beliebige σ-Algebra falsch ist. Die Aussage `Clock.IsProgressive` für den
   Sprungprozeß ist über bloßem `[MeasurableSpace E]` also vermutlich **nicht
   beweisbar**. Sie wird auch nicht gebraucht: `measurable_uncurry_min_of_eventuallyEq`
   führt dasselbe Argument in `ℝ` für jedes reelle Funktional `h ∘ X`, und der
   Kompensator ist eines. Wer `isMPSolution_iff_forall_fdd` auf den Sprungprozeß
   anwenden will, muß dessen Hypothese vorher auf diese Gestalt abschwächen —
   `mpFamily_sub_of_measurable_path` nimmt ohnehin schon `g ∘ X` und nicht `X`.

   **Und die Rechtfertigung dafür, daß die Rechtsstetigkeit ohne jede Hypothese
   bewiesen ist** (`eventuallyEq_nhdsGE_stepPath`, weder `Monotone T` noch
   Nichtexplosion): `MeasureTheory.Martingale` verlangt `StronglyAdapted` und
   nicht dessen f.s.-Fassung, also muß die Meßbarkeit des Kompensators an
   **jedem** Punkt gelten, die Explosionsmenge eingeschlossen. Die ist eine
   Nullmenge, aber nicht die leere Menge, und `ae_isStepPath_jumpProcess` hilft
   hier darum nicht.

   **Was für den Satz jetzt noch fehlt, ist genau ein Stück:** die bedingte
   Erwartung `P[Y t | 𝓕 s] =ᵐ Y s`. Der Weg dorthin, in der Reihenfolge:
   (a) die Markoveigenschaft des Sprungprozesses an einer festen Zeit, aus
   `expMeasure_Ioi_add` und `chainKernel`; (b) die Erwartungsidentität
   `E_x[f(X_t)] - f x = ∫_0^t E_x[Af(X_s)] ds`; (c) die Kombination beider. Der
   Punkt, an dem es teuer wird, ist (b) — es ist die Rückwärtsgleichung, und sie
   ist der einzige Schritt, der Analysis jenseits der Buchhaltung braucht.

   **Zwischenstand 2026-09-09, einundzwanzigster Lauf des Tages.** Die
   **Verschiebung** steht, in allen drei Stücken, aus denen sie besteht:
   pfadweise (`jumpProcess_jumpShift`), auf den Wartezeiten
   (`waitingMeasure_map_shift`) und auf der Kette (`chainKernel_map_shift`).
   Siebzehn neue Deklarationen in `TauCeti/MartingaleProblems/Suggested.lean`,
   alle durch `lake env lean` gegen v4.33.1 und alle mit `#print axioms` auf
   `propext`, `Classical.choice`, `Quot.sound` geprüft; die Zahl der `sorry` ist
   unverändert zehn. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-09,
   einundzwanzigster Lauf des Tages".

   **Der teure Teil war die Kette, und der Grund ist eine Lücke in Mathlib.**
   `ProbabilityTheory.Kernel.traj` ist für eine **beliebige** Kernfamilie gebaut
   und trägt darum keine Zeithomogenität; weder v4.33.1 noch `upstream/master`
   sagt, daß die Verschiebung einer homogenen Kette wieder dieselbe Kette ist
   (`git grep shift upstream/master -- .../IonescuTulcea/` ist leer). Der Beweis
   geht darum über die endlichdimensionalen Verteilungen: eine Induktion über
   `Kernel.partialTraj`, deren ganzer Inhalt der **eine** Schritt
   `partialTraj_succ_map_shiftIic` ist — der Kern zur Zeit `b+1` liest die
   letzte Koordinate, und die Verschiebung trägt sie auf die letzte Koordinate
   des verschobenen Tupels. Die Induktion selbst ist dann vier Umformungen
   (`map_comp`, `comp_map`, IH, `kernel_comp_comap`), und der Übergang von
   `partialTraj` zu `traj` ist die Eindeutigkeit des projektiven Limes
   (`ext_of_map_frestrictLe`).

   ~~**Was jetzt noch fehlt**, ist die Zusammensetzung: die drei Verschiebungen
   sind einzeln bewiesen und müssen zur Erneuerungsgleichung zusammengeführt
   werden.~~ *(erledigt 2026-09-09, zweiundzwanzigster Lauf des Tages)*

   **Zwischenstand 2026-09-09, zweiundzwanzigster Lauf des Tages.** Die
   **Zusammensetzung** steht: `jumpMeasure_map_split` gibt die gemeinsame
   Verteilung von Anfangszustand, nullter Wartezeit und verschobenen Daten,
   ```
   (jumpMeasure mu nu).map (fun ω ↦ ((ω.1 0, ω.1 ∘ succ), (ω.2 0, ω.2 ∘ succ)))
     = (nu ⊗ₘ (chainKernel mu ∘ₖ mu)).prod ((expMeasure 1).prod waitingMeasure),
   ```
   und `prod_comp_chainKernel_eq_jumpMeasure` erkennt den zweiten Faktor jeder
   Hälfte als `jumpMeasure mu (mu z)` — die verschobenen Daten sind wieder eine
   Sprungkonstruktion, gestartet aus einem Schritt von `mu`. Zwölf neue
   Deklarationen, die ganze Datei durch `lake env lean` gegen v4.33.1
   (unverändert zehn `sorry`), alle zwölf mit `#print axioms` auf `propext`,
   `Classical.choice`, `Quot.sound`. Bericht in `Facts/INVENTAR.md`, Läufe,
   „2026-09-09, zweiundzwanzigster Lauf des Tages".

   **Zwei Befunde, die der nächste Lauf braucht.** (a) Die angesagte
   **Kernidentität** von `chainKernel_map_shift` war nicht das fehlende Stück;
   gebraucht wird die **gemeinsame** Verteilung von `y 0` und `y ∘ succ`, und die
   folgt aus der Randverteilung nicht — über bloßem `[MeasurableSpace E]` ist aus
   `μ.map f = dirac z` **nicht** `f =ᵐ[μ] z` zu gewinnen, weil `{z}` nicht meßbar
   sein muß. Der Weg ist `map_prodMk_of_map_eq_dirac`, das auf meßbaren Rechtecken
   rechnet und nur `μ (f ⁻¹' s) ∈ {0, 1}` benutzt. (b) **Mathlib hat die
   Abspaltung einer Koordinate von ihrem Schwanz nicht.** Es hat die
   Reindizierungen von `Measure.infinitePi` längs Injektionen
   (`Measure.map_infinitePi_infinitePi_of_inj`) und die Unabhängigkeit der
   Koordinaten (`iIndepFun_infinitePi`), aber `iIndepFun.indepFun_finset` trennt
   nur **endliche** Indexmengen, und die Unabhängigkeit einer Koordinate vom
   ganzen Schwanz ist keine Reindizierung. Bewiesen ist sie hier als
   `infinitePi_map_natCons` über `Measure.eq_infinitePi`, mit dem Voranstellen
   `natCons` als der Abbildung, die die Aussage auf Quader zurückführt.

   ~~**Was für den Satz jetzt noch fehlt**, und es ist Punkt (b) des Weges: die
   **Rückwärtsgleichung** `E_x[f(X_t)] - f x = ∫_0^t E_x[Af(X_s)] ds`. Alle
   maßtheoretischen Stücke sind da — `jumpMeasure_integral_eq_of_firstJump`
   zerlegt am ersten Sprung, `jumpMeasure_map_split` benennt das Gesetz des
   zweiten Terms, `jumpProcess_jumpShift` sagt, daß der Integrand dort eine
   Funktion der verschobenen Daten ist. Was fehlt, ist die Analysis: die
   Differentiation der Erneuerungsgleichung nach `t`.~~ *(die
   Erneuerungsgleichung selbst ist erledigt 2026-09-09, dreiundzwanzigster Lauf
   des Tages; es fehlt allein noch die Differentiation.)*

   **Zwischenstand 2026-09-09, dreiundzwanzigster Lauf des Tages.** Die
   **Erneuerungsgleichung** steht, als `jumpMeasure_integral_eq_renewal`:
   ```
   ∫ ω, h (jumpProcess lam t ω) ∂(jumpMeasure mu nu)
     = (∫ z, exp (-(lam z * t)) * h z ∂nu)
       + ∫ z, (∫ s in Ioc 0 (lam z * t), exp (-s) *
           ∫ ω', h (jumpProcess lam (t - s / lam z) ω') ∂(jumpMeasure mu (mu z))) ∂nu.
   ```
   Acht neue Deklarationen in `TauCeti/MartingaleProblems/Suggested.lean`, die
   ganze Datei durch `lake env lean` gegen v4.33.1 **ohne einen Fehler**
   (unverändert zehn `sorry`), alle acht mit `#print axioms` auf `propext`,
   `Classical.choice`, `Quot.sound`. Bericht in `Facts/INVENTAR.md`, Läufe,
   „2026-09-09, dreiundzwanzigster Lauf des Tages". **Damit ist an Punkt 2 nichts
   Maßtheoretisches mehr offen.**

   **Vier Befunde, die der nächste Lauf braucht.** (a) Die Bündelung der beiden
   Schwänze `y ∘ succ` und `ξ ∘ succ` zu einem Punkt von `(ℕ → E) × (ℕ → ℝ)`
   *ist* die Fubini-Vertauschung von `y ∘ succ` gegen `ξ 0`, und nicht etwas
   daneben: `jumpMeasure_map_split` liefert die Koordinaten in der Reihenfolge
   `z, yc, s, xt`, gebraucht wird `z, s, (yc, xt)`, und benachbart werden `yc`
   und `xt` genau dadurch, daß `s` über `yc` hinauswandert. Bezahlt ist das
   einmal und für immer in `integral_jumpMeasure_eq_of_split`; eine geordnete
   Fassung von `jumpMeasure_map_split` hätte nichts gespart. (b) Die
   Beschränktheit des Integranden ist die einzige Voraussetzung und **fünffach**
   nötig — drei Sorten von Integrierbarkeitspflicht (Produkt, Komposition,
   vertauschtes Produkt) —, und was die Schranke nach innen durch die
   Schachtelung trägt, ist `abs_integral_le_of_abs_le`. (c) **Mathlib hat
   `expMeasure` als Dichte, aber nicht als Integralformel**: `expMeasure r` ist
   per `rfl` ein `volume.withDensity`, doch
   `∫ s, F s ∂(expMeasure 1) = ∫ s in Ioi 0, exp (-s) * F s` steht nirgends und
   heißt hier `integral_expMeasure_one`, **ohne jede Voraussetzung an `F`**. Die
   Gestalt ist gewählt, weil `t` dann in der *Grenze* des Integrationsbereichs
   steht und nicht im Integranden — das ist es, worauf die Differentiation
   ansetzt. (d) Die Nichtexplosion braucht **keine Topologie**:
   `ae_exists_lt_jumpTime` steht über bloßem `[MeasurableSpace E]`, während
   `ae_isStepPath_jumpProcess` `[TopologicalSpace E]` trägt.

   ~~**Was jetzt noch fehlt**, und es ist der einzige Schritt mit Analysis: die
   **Differentiation nach `t`**~~ *(an der Stelle `t = 0` erledigt 2026-09-09,
   vierundzwanzigster Lauf des Tages)*.

   **Zwischenstand 2026-09-09, vierundzwanzigster Lauf des Tages.** Die
   **Rückwärtsgleichung in Differentialform an der Stelle `t = 0`** steht. Zwölf
   neue Deklarationen in `TauCeti/MartingaleProblems/Suggested.lean`, die ganze
   Datei durch `lake env lean` gegen v4.33.1 ohne einen Fehler (unverändert zehn
   `sorry`), alle zwölf mit `#print axioms` auf `propext`, `Classical.choice`,
   `Quot.sound`. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-09,
   vierundzwanzigster Lauf des Tages".

   **Die angesagte Aussage ist falsch, und das ist bewiesen.** `HasDerivAt` an
   `0` gilt nicht: vor dem ersten Sprung hat sich der Pfad nicht bewegt, also ist
   `t ↦ ∫ h (X t)` auf ganz `Set.Iic 0` konstant
   (`integral_jumpProcess_of_nonpos`) und die linksseitige Ableitung ist `0`;
   `eq_zero_of_hasDerivAt_integral_jumpProcess` macht daraus den Satz, daß eine
   zweiseitige Ableitung `∫ A h ∂nu = 0` erzwänge. Der Satz heißt darum
   `jumpMeasure_hasDerivWithinAt_integral` und trägt `(Set.Ici 0) 0`. Verloren
   ist damit nichts: `mpFamily` indiziert über `ℝ≥0`.

   **Zwei Befunde, die der nächste Lauf braucht.** (a) **Die
   Erneuerungsgleichung wird nicht differenziert.** Ihre beiden Terme einzeln zu
   behandeln verlangte die Meßbarkeit von
   `z ↦ ∫ s in Ioc 0 (lam z * t), …`, die keine Aussage der Datei hergibt. Der
   Weg geht einen Schritt zurück auf `integral_jumpMeasure_eq_of_split` und wendet
   ihn auf die **Differenz** des wahren Integranden und seiner nullten Näherung
   an; dann erzeugt der Satz selbst die äußere Integration und
   `abs_integral_le_of_abs_le` braucht nur eine punktweise Schranke. (b) Der
   Hauptsatz ist **quantitativ**: `abs_integral_jumpProcess_sub_sub_le` schätzt
   den Rest zweiter Ordnung durch `4 * C * L^2 * t^2` ab, und **die Konstante
   nennt `nu` nicht** — die allgemeine Zeit setzt dort das Gesetz zur Zeit `t`
   ein, und eine von ihm abhängige Schranke wäre wertlos.

   ~~**Was jetzt noch fehlt**, ist die Verschiebung der Ableitung von `0` an jede
   Stelle, und das genaue Ziel steht am Ende des Laufberichts als
   `jumpMeasure_integral_jumpProcess_add`, die zeithomogene Markoveigenschaft in
   integrierter Gestalt.~~ *(erledigt 2026-09-09, fünfundzwanzigster und
   sechsundzwanzigster Lauf des Tages.)*

   **Zwischenstand 2026-09-09, fünfundzwanzigster und sechsundzwanzigster Lauf
   des Tages.** Die **Markoveigenschaft zu einer festen Zeit** steht, als
   `jumpMeasure_integral_jumpProcess_add`, und mit ihr die
   **Erwartungsidentität** `jumpMeasure_integral_sub_eq_intervalIntegral`. Der
   Träger ist `jumpKernel`, die Konstruktion als Kern im Anfangs*zustand*: die im
   vierundzwanzigsten Lauf angesagte Gestalt nennt rechts ein Maß, das keine
   Komposition ist, und die Induktion über die Zahl der Sprünge hätte daran
   nichts zum Ansetzen. Der Hauptsatz ist überdies **einseitig** anzuwenden —
   `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, nicht
   `…_of_hasDerivAt`, denn die zweiseitige Ableitung an `0` existiert nicht.
   Berichte in `Facts/INVENTAR.md`, Läufe, „2026-09-09, fünfundzwanzigster" und
   „sechsundzwanzigster Lauf des Tages".

   **Zwischenstand 2026-09-09, siebenundzwanzigster Lauf des Tages.** Damit fehlt
   an `jumpProcess_isMPSolution` genau noch der Übergang von der unbedingten
   Erwartung zur **bedingten**, und dieser Lauf hat das Stück gebaut, das er
   braucht: die **Gestalt der Vergangenheit**, `IsPastFunctional`, in
   fünfundzwanzig Deklarationen, alle durch `lake env lean` gegen v4.33.1 und
   alle mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound`
   geprüft; die Zahl der `sorry` ist unverändert zehn. Bericht in
   `Facts/INVENTAR.md`, Läufe, „2026-09-09, siebenundzwanzigster Lauf des Tages".

   **Der im sechsundzwanzigsten Lauf angesagte Weg ist zweifach versperrt, und
   das ist der Befund.** Er lief über `isMPSolution_iff_forall_fdd`. (a) Dieser
   Satz trägt **selbst ein `sorry`** (`Suggested.lean:382`); ein darauf
   gestütztes `jumpProcess_isMPSolution` hinge an `sorryAx`. (b) Seine
   Voraussetzung ist `Clock.IsProgressive`, die der neunzehnte Lauf für den
   Sprungprozeß schon als vermutlich **nicht beweisbar** notiert hat. Die
   bedingte Erwartung wird darum direkt gerechnet, gegen die `𝓕 s`-meßbaren
   beschränkten Funktionale.

   **Und der Grund, aus dem die Meßbarkeit allein nicht die richtige Eigenschaft
   ist.** Die Identität `X r (jumpPrepend x a ω) = X (r - a / lam x) ω` ist
   jenseits der Explosionszeit von `ω` **falsch** — dort ist `stepIndex` der
   Sperrwert `0`, links steht `x` und rechts `ω.1 0` —, also startet ein bloß
   `𝓕 s`-meßbares Funktional nach dem ersten Sprung nicht wieder als eines.
   `IsPastFunctional` schneidet darum die Explosionsmenge weg, was eine
   Nullmenge kostet (`indicator_nonExplosive_ae_eq`) und was bei
   `StronglyAdapted` gerade **nicht** erlaubt war (neunzehnter Lauf).

   **Was jetzt noch fehlt**, ist die Induktion mit dem Faktor aus der
   Vergangenheit, `abs_integral_jumpMeasure_add_sub_le_past`; sie steht
   ausgeschrieben am Ende des Laufberichts, samt der Angabe, welcher vorhandene
   Satz jeden ihrer Schritte trägt.
3. `norm_apply_le` und `exists_unique_of_bounded`, die Picard-Iteration; nach der
   Roadmap „no analysis beyond `NormedSpace`".

   **`norm_apply_le` ist erledigt** (2026-09-09, achtzehnter Lauf des Tages), als
   `abs_jumpApply_le` in punktweiser Gestalt
   `(∀ x, |f x| ≤ C) → |jumpApply lam mu f x| ≤ 2 * L * C`. Es ist außer der
   Reihe gefallen, weil es beim Hinschreiben des Erzeugers ohnehin anfiel und
   vier Zeilen kostete; `exists_unique_of_bounded` steht unverändert offen und
   bleibt hinter Punkt 2.
4. **Erst danach das Akzeptanzbeispiel**, und dann wirklich als Beweis: `E = ℕ`,
   `lam ≡ 1`, `mu x = dirac (x+1)`, also `A f x = f (x+1) - f x` — der
   Poissonprozeß, mit den eindimensionalen Verteilungen gegen
   `ProbabilityTheory.poissonMeasure` geprüft. Es instanziiert jede Einzelheit
   des Meilensteins auf einmal; steht es nur als Prosa da, prüft es nichts (die
   Lehre des 2026-09-08). Bricht es, so ist der Befund wertvoller als der Satz
   darüber, und er gehört in den Bericht statt in eine Abschwächung.
5. Der lokale Fall und die pfadabhängige Variante zuletzt; sie liefern die
   Beispiele für die Meilensteine 7 und 9.

**Weitere Akzeptanzbeispiele, wenn die Konstruktion steht.** Alle drei sind
*Einsetzen von Daten*, kein neuer Beweis, und jedes prüft einen anderen Zweig:

* **M/M/1**, `b ≡ β`, `d x = δ * 1_{x ≥ 1}` auf `E = ℕ`. Beschränkt, also
  greifen `thm:jumpMP` und `exists_unique_of_bounded` unmittelbar.
* **Linearer Geburt-Tod**, `b x = β * x`, `d x = δ * x`. Hier ist
  `λ̄ = ∞`, der Satz greift **nicht**, und das Beispiel prüft als einziges den
  lokalen Zweig samt Nichtexplosionskriterium (`∑ 1/(β n)` divergiert). Der
  Yule-Prozeß `δ = 0` fällt als Sonderfall ab und hat geschlossene
  eindimensionale Verteilungen — geometrisch —, also eine unabhängige Kontrolle
  wie `poissonMeasure` beim Poissonprozeß.
* **Hawkes**, prädiktables `Λ(t, ω) = ν + ∫_0^{t-} h(t-s) dN_s`, das
  nicht-markovsche Beispiel und die Instanz von `ex:hawkes`. Es gehört zur
  pfadabhängigen Variante und kommt zuletzt.

In jedem Fall zuerst der Erzeuger als Rechnung: für Geburt-Tod kürzt sich `λ`
heraus und es muß `A f x = b x * (f (x+1) - f x) + d x * (f (x-1) - f x)`
herauskommen. Kommt dort etwas anderes heraus, ist die Form von `set:jumpdata`
unhandlich und das ist der Befund.

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
