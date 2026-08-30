# Inventar der `Fact`-Aussagen

Die 29 mit `\begin{fact}` ausgezeichneten Aussagen des Manuskripts sind seine
**Voraussetzungsfläche**: alles, was zitiert und nicht bewiesen wird. Eine
Formalisierung ist genau dann vollständig geplant, wenn zu jeder dieser Aussagen
feststeht, ob sie in Mathlib liegt, von einer der vier Roadmaps abgedeckt wird,
oder eine Lücke ist. Dieses Inventar hält das fest, eine Zeile je Fact.

Bis heute war diese Abdeckung von Hand zusammengetragen und **nachweislich
lückenhaft**: der Durchgang am 2026-08-29 fand in den Roadmaps drei falsche oder
veraltete Mathlib-Zitate und mehrere Punkte, die längst oben liegen. Das
Inventar ersetzt das Gedächtnis durch eine Liste.

## Spalten

* **tragend** — Zahl der Abschnitte, in denen der Fact außerhalb der
  Buchhaltungsabschnitte (§2.x „Where the prerequisites are used", §8, §9,
  Notation, Bündeltabelle) benutzt wird. Das ist die Prioritätsordnung: was
  nirgends tragend vorkommt, ist entweder implizit benutzt oder überflüssig, und
  beides will geklärt sein.
* **Status** — `Mathlib` (mit Deklaration), `Roadmap` (mit Meilenstein),
  `Lücke`, `bewusst` (zitiert, absichtlich nicht formalisiert), `?` (unbestimmt).
* **Beleg** — die Deklaration oder der Meilenstein. Ein Status ohne Beleg zählt
  als `?`.

## Regel

Ein Status wird nur eingetragen, wenn er **am Quelltext geprüft** wurde: die
Mathlib-Deklaration existiert unter diesem Namen und ist nicht `deprecated`, oder
der Meilenstein nennt die Aussage. Nicht aus dem Gedächtnis. Wer einen Status
setzt, nennt den Beleg.

## Tabelle

| Fact | tragend | Aussage | Status | Beleg |
|---|---|---|---|---|
| `fact:Dcountable` | 4 | EK, Lemma 3.7.7 | Roadmap | SkorokhodSpace M8, `SkorokhodSpace.exists_countable_dense_continuity`; Mathlib hat weder `cadlag` noch den Raum |
| `fact:monotoneclass` | 4 | Monotone class theorem; EK, Appendix 4 | Roadmap | WeakConvergence M5, `induction_on_mulSystem` — dort neu angelegt; Mathlib hat nur die Mengenfassung `induction_on_inter` |
| `fact:cmt` | 3 | Continuous mapping theorem; EK, Corollary 3.1.9 and Co | Roadmap | WeakConvergence M2 — der stetige Fall ist Mathlib (`FiniteMeasure.tendsto_map_of_tendsto_of_continuous`), die f.ü.-stetige Fassung fehlt |
| `fact:kolmogorov` | 3 | Kolmogorov extension; EK, Theorem 4.1.1; eqref{T0} + e | Roadmap | KolmogorovExtension M2 — Gerüst weitgehend in Mathlib, es fehlen σ-Subadditivität und `projectiveLimit` |
| `fact:stoneweierstrass` | 3 | Stone--Weierstrass for separating classes; EK, Theorem | Roadmap | WeakConvergence M1 — die separierende Hälfte ist Mathlib (`ext_of_forall_mem_subalgebra_integral_eq_of_polish`), die konvergenzbestimmende fehlt |
| `fact:bp` | 2 | EK, Lemma 3.4.1, Proposition 3.4.2, and Appendix 3, Pr | Roadmap | MartingaleProblems M2, `bpClosure` und `Submodule.bpClosure` — dort neu angelegt; Mathlib kennt bp-Konvergenz nicht, `seqClosure` ist der Abschluss unter Limiten einer Topologie |
| `fact:cadlagext` | 2 | Regularization along a dense set; EK, Lemma 2.2.8; eqr | Roadmap | MartingaleProblems M9; Vorarbeit in `brownian-motion` (Apache-2.0) |
| `fact:optsampl` | 2 | Optional sampling; EK, Theorem 2.2.13, Remark 2.2.14,  | Roadmap | MartingaleProblems M9, `Submartingale.stoppedValue_min_le_condExp` — dort neu angelegt; Mathlibs `Martingale.stoppedValue_min_ae_eq_condExp` ist der diskrete Fall und nur für Martingale |
| `fact:prohorov` | 2 | Prohorov; EK, Lemma 3.2.1 and Theorem 3.2.2 | Mathlib | `MeasureTheory/Measure/Prokhorov.lean`, `isCompact_closure_of_isTightMeasureSet` und Umkehrung |
| `fact:relcompact2` | 2 | Relative compactness, II; EK, Theorem 3.9.4 | Roadmap | MartingaleProblems M11, `isTight_map_postcomp_of_exists_martingale` — dort neu angelegt; `isRelativelyCompact_of_approx` nannte nur die Folgerung, nicht das Kriterium |
| `fact:sepcond` | 2 | Conditional determination by separating sets; EK, Chap | Roadmap | WeakConvergence M1, `IsSeparating.ae_eq_of_forall_condExp_eq` — dort neu angelegt; Mathlib liefert `Filter.EventuallyEq.of_forall_separating_preimage` als Schlussschritt |
| `fact:submgreg` | 2 | Submartingale regularization; EK, Proposition 2.2.9; e | Roadmap | MartingaleProblems M9; Vorarbeit in `brownian-motion` (Apache-2.0) |
| `fact:ui` | 2 | Uniform integrability; EK, Appendix 2 | Mathlib+ | `MeasureTheory.UniformIntegrable`, `uniformIntegrable_iff`; die Kopplung an Verteilungskonvergenz fehlt → WeakConvergence M4 |
| `fact:MZtight` | 1 | Tightness; MZ, Theorem~4, and Ku | Roadmap | MartingaleProblems M11 |
| `fact:PSpolish` | 1 | EK, Theorems 3.1.7 and 3.1.8 | Roadmap | WeakConvergence M3 — Skorokhod-Darstellung fehlt in Mathlib (dort nur `docs/1000.yaml`); dass 𝒫(S) polnisch ist, ungeprüft |
| `fact:convdet` | 1 | EK, Proposition 3.4.4 | Roadmap | WeakConvergence M1 |
| `fact:fddconv` | 1 | EK, Theorem 3.7.8 | Roadmap | SkorokhodSpace M8, `tendsto_finiteDimensional_of_tendsto` (a) und `tendsto_of_isTight_of_tendsto_finiteDimensional` (b); die Roadmap fixiert `E` polnisch, der Fact nur separabel |
| `fact:fullgenerator` | 1 | EK, Proposition 1.5.1 | Roadmap | MartingaleProblems M13 — dort neu angelegt; Mathlib hat keine Operatorhalbgruppen, `dissipative` kommt nicht vor, Hille--Yosida steht als `Q974405` ohne `decl` in `docs/1000.yaml` |
| `fact:jacodmemin` | 1 | Continuous mapping, Jacod--M'emin; CPS, Theorem 2.9 | bewusst | nicht formalisiert; `rem:augvsws` begründet, warum Augmentierung genügt |
| `fact:picard` | 1 | Picard--Lindel"of for SDEs | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:pseudopath` | 1 | Pseudo-paths; MZ, Section~1 and Lemma~1 | Roadmap | MartingaleProblems M11 |
| `fact:relcompact` | 1 | Relative compactness, I; EK, Theorem 3.9.1 | Roadmap | SkorokhodSpace M8, `isTightMeasureSet_iff_forall_postcomp` mit `continuous_postcomp` — dort neu angelegt |
| `fact:stoppingtimes` | 1 | EK, Propositions 2.1.2 and 2.1.4; eqref{T2b} | Mathlib | `MeasureTheory.IsStoppingTime` in `Probability/Process/Stopping.lean` |
| `fact:strookvaradhan` | 1 | Stroock--Varadhan; KA, Theorem 32.7 | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:yamadawatanabe` | 1 | Yamada--Watanabe | bewusst | SDE-Weg wird zitiert, nicht bewiesen (§7.5) |
| `fact:doob` | 0 | Doob's inequalities; EK, Corollary 2.2.17; eqref{T2b} | Roadmap | MartingaleProblems M9, `maximal_ineq_of_rightContinuous` und `Submartingale.eLpNorm_iSup_le` — dort neu angelegt; Mathlibs `MeasureTheory.maximal_ineq` ist `Filtration ℕ`, die `Lᵖ`-Ungleichung fehlt ganz |
| `fact:fdd` | 0 | EK, Proposition 3.4.6 and Proposition 3.7.1 | Roadmap | WeakConvergence M1 (Produktpunkt, am 2026-08-29 von endlichem auf beliebigen Index gebracht) und SkorokhodSpace M6, `borel_eq_iSup_comap_eval` |
| `fact:portmanteau` | 0 | Portmanteau; EK, Theorem 3.3.1 | Mathlib | `MeasureTheory/Measure/Portmanteau.lean` |
| `fact:stoppedlocalmg` | 0 | EK, Proposition 2.3.1 | Roadmap | MartingaleProblems M9, `isStable_martingale_rightContinuous` — dort neu angelegt; `MeasureTheory.Locally`, `IsStable` und `IsStable.locally` sind Mathlib, der Martingalfall ist es nicht |

## Offene Auffälligkeiten

* **Vier Facts ohne tragende Fundstelle** — `fact:doob`, `fact:fdd`,
  `fact:portmanteau`, `fact:stoppedlocalmg` werden nur in den
  Buchhaltungsabschnitten zitiert. Zu klären: implizit benutzt (dann die Stelle
  benennen) oder entbehrlich (dann aus §2 streichen). Für `fact:doob` ist die
  Antwort schon da: die Tabelle in §2 nennt selbst
  „Remark~`rem:EKrelcompact` (via Fact~`relcompact2`)", der Fact wird also
  mittelbar getragen und ist nicht entbehrlich. Die Spalte **tragend** zählt nur
  direkte `\ref`s und unterschätzt ihn deshalb; dasselbe ist für die anderen
  drei zu prüfen. Für `fact:stoppedlocalmg` am 2026-08-30 geprüft: die
  Lokalisierung setzt in `def:localizing`\ref{it:L1} die Martingaleigenschaft
  der gestoppten Prozesse voraus, statt sie herzuleiten; getragen wird der Fact
  erst bei der Verifikation eines konkreten lokalisierenden Systems. Offen
  bleiben `fact:fdd` und `fact:portmanteau`.
* **`fact:bp`** und **`fact:fullgenerator`** trägt §8 als „nur für optionalen
  Kontext". Am 2026-08-30 entschieden: solange `cor:bpclosure` und
  `rem:fullgenerator` im Manuskript stehen, gehören beide in die Roadmap, und
  sie stehen jetzt dort ohne das Wort „optional" (MartingaleProblems M2 und
  M13). Für `fact:bp` hält das Manuskript selbst fest, was der Unterschied
  kostet: `lem:closure` ist dominierte Konvergenz und gilt für unbeschränkte
  `f, g`, der bp-Abschluss verengt auf `Bdd(E) × Bdd(E)`. Die Roadmap nimmt
  beide auf und nennt `lem:closure` die benutzte Fassung.
* **`fact:sepcond`** wird im Manuskript selbst bewiesen (`rem:sepcondproof`,
  EK Kap. 3 Aufgabe 7); zitiert wird nichts. Es ist damit kein Fact im Sinne
  der Voraussetzungsfläche, wohl aber eine zu formalisierende Aussage, und
  steht seit dem 2026-08-30 als Punkt in `WeakConvergence` Meilenstein 1. Ob
  die `fact`-Umgebung im Manuskript die richtige ist, bleibt eine Frage an das
  Manuskript.
* **Der Beweis von `rem:sepcondproof` ist länger als nötig.** Schritt 2 und 3
  konstruieren eine reguläre bedingte Verteilung und zeigen die Messbarkeit der
  Diagonale. Beides entfällt: aus Schritt 1 folgt mit `G = {V ∈ B}` und dessen
  Komplement unmittelbar `P(U ∈ B, V ∉ B) = P(U ∉ B, V ∈ B) = 0` für jedes
  messbare `B`, und eine abzählbare trennende Familie schließt daraus
  `P{U = V} = 1`. Das ist genau
  `Filter.EventuallyEq.of_forall_separating_preimage`. Gebraucht wird davon nur
  \eqref{E1} in Gestalt von `CountablySeparated`; eine reguläre bedingte
  Verteilung kommt nicht vor. Fürs Manuskript wäre das eine Kürzung, nicht eine
  Korrektur.
* **Die Roadmap `MartingaleProblems` hat den Mathlib-Bestand an Martingaltheorie
  überschätzt** — sie führte „optional stopping, Doob's inequalities" unter dem,
  was nicht neu zu bauen ist. Alle diese Sätze sind in Mathlib auf `Filtration ℕ`
  (bzw. auf einen zu einer Teilmenge von `ℕ` ordnungsisomorphen Index)
  festgelegt, und Doobs `Lᵖ`-Ungleichung fehlt für jeden Index. Am 2026-08-29
  richtiggestellt und als Meilenstein 9 nachgetragen.
* **Eine falsche Begründung in `rem:atomicdual`, am 2026-08-30 korrigiert.** Zum
  kleinsten Index mit unvergleichbaren Atomen, `T = {0,a,b,t*}`, stand dort, die
  drei Relationen längs `[0,t*)`, `[a,t*)` und `[b,t*)` erzwängen
  `m_a γ(a,t) = m_b γ(b,t) = 0`. Sie erzwingen es nicht: alle drei Intervalle
  sind `{a,b}`, die drei Relationen sagen dasselbe. Das Argument benutzte
  nirgends die Positivität der Massen und hätte deshalb auch ein Gegenbeispiel
  mit `m_a + m_b = 0` decken müssen, das es gibt (`Task23/diamond.py`). Die
  Aussage selbst bleibt richtig; die Begründung ist im Manuskript ersetzt. Das
  ist die einzige Änderung dieses Laufs am Manuskript, und sie folgt der Regel
  von Task 23: erst wenn etwas vollständig und verifiziert ist.
* **Die Roadmaps kennen `E` nur polnisch.** `SkorokhodSpace` fixiert in
  Meilenstein 1 „`E` a Polish space", während `fact:fddconv`, `fact:cmt` und
  `fact:PSpolish` im Manuskript für separable metrische `E` gelten und
  `rem:MZcost` ausdrücklich festhält, dass der Pfadraum der Konvergenz nach Maß
  nicht polnisch ist. Zu klären, ob die Roadmaps auf separabel-metrisch
  umgestellt werden oder das Manuskript die Einschränkung notiert.

* **§4.3 von \EK{} ist nur zu einem Drittel ausgeschöpft.** Zitiert werden
  4.3.1, 4.3.5 und 4.3.6; die Sektion enthält danach noch Thm. 4.3.8,
  Prop. 4.3.9, Prop. 4.3.10, Thm. 4.3.12 und Cor. 4.3.13. Besonders
  **Thm. 4.3.12** ist der natürliche Begleiter von `thm:cadlag`: unter genau
  dessen Voraussetzungen ist jede Lösung **quasi-linksstetig**, also
  $P\{\lim_n X(\tau_n)=X(\tau),\ \tau<\infty\}=P\{\tau<\infty\}$ für
  aufsteigende Stoppzeiten, insbesondere $P\{X(t)=X(t-)\}=1$ für jedes $t>0$.
  Der Beweis ist optional sampling plus die Separiertheit von $\dom(A)$. Das ist
  eine Pfadeigenschaft, **in Termen des Martingalproblems** bewiesen — und damit
  das, was ein Stetigkeitssatz sein müsste und nicht ist: quasi-linksstetig heißt
  keine Sprünge zu vorhersehbaren Zeiten, der Poissonprozess erfüllt es. Echte
  Stetigkeit verlangt eine Bedingung an $A$ (kein Sprunganteil, für $\R^d$ die
  Lokalität nach Courrège) und steht bei \EK{} nicht in §4.3. Ob Thm. 4.3.12 in
  der abstrakten Sprache von `thm:absreg` formuliert werden soll, ist offen.

## Läufe

### 2026-08-29 — `fact:Dcountable`, `fact:monotoneclass`, `fact:optsampl`, `fact:doob`, `fact:fddconv`, `fact:relcompact`, `fact:relcompact2`, `fact:fdd`

Acht Zeilen von `?` auf `Roadmap` gebracht, jede am Quelltext belegt. Geprüft
wurde gegen `~/Code/lean/journal/.lake/packages/mathlib` (v4.33.1) und, wo es auf
**master** ankam, gegen `gh api`/`gh search code`; die Verzeichnisse
`Mathlib/Probability/Martingale/` und `Mathlib/Probability/Process/` sind auf
master identisch mit v4.33.1, die v4.33.1-Quelle ist für diesen Lauf also ein
tragfähiger Stellvertreter.

* **`fact:Dcountable`** (tragend 4). Mathlib hat den Skorokhod-Raum nicht:
  `gh search code` findet `cadlag` nirgends und `Skorokhod` nur in
  `docs/1000.yaml`. Die Aussage steht wörtlich in `SkorokhodSpace` Meilenstein 8
  als `SkorokhodSpace.exists_countable_dense_continuity`. Die Stellen 8471, 8474
  und 8511 des Manuskripts benutzen den Fact nur vergleichend (Pseudopfade,
  S-Topologie) und verlangen nichts über die Aussage hinaus.
* **`fact:monotoneclass`** (tragend 4). Lücke. Der Begriff „monotone class"
  kommt in Mathlib weder in v4.33.1 noch auf master vor; `docs/1000.yaml` führt
  den Satz als `Q242045` **ohne** `decl`. Vorhanden ist nur die Mengenfassung,
  Dynkins π–λ-Satz als `induction_on_inter` in
  `Mathlib/MeasureTheory/PiSystem.lean:692`. Die vier tragenden Stellen (2376,
  2630, 5468, 8862) brauchen sämtlich die **funktionale** Fassung. Neu angelegt
  als `WeakConvergence` Meilenstein 5 mit `IsMulSystem`, `generateFromFuns`,
  `induction_on_mulSystem` und den zwei benutzten Korollaren; die Produktaussage
  in Meilenstein 1 und `isDetermining_products` in `MartingaleProblems`
  Meilenstein 3 verweisen jetzt darauf statt auf „ein Monotone-Klassen-Argument".
* **`fact:optsampl`** (tragend 2). Lücke, und zugleich ein falsches Zitat in der
  Roadmap. Mathlibs Optional-Sampling-Satz ist
  `MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp`
  (`Probability/Martingale/OptionalSampling.lean:195`) und steht in der Sektion
  `SubsetOfNat` unter `[LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]` —
  ein zu einer Teilmenge von `ℕ` ordnungsisomorpher Index — und nur für
  `Martingale`. Die Submartingal-Fassung `Submartingale.expected_stoppedValue_mono`
  (`OptionalStopping.lean:44`) liegt auf `{𝒢 : Filtration ℕ m0}` und vergleicht
  nur Erwartungswerte, nicht bedingte. Das Manuskript braucht rechtsstetige
  Submartingale in stetiger Zeit mit `≥` unter `Filt_{τ₁}`. Nachgetragen als
  erste zwei Punkte von `MartingaleProblems` Meilenstein 9.
* **`fact:doob`** (tragend 0, aber über `fact:relcompact2` mittelbar getragen).
  Lücke. `MeasureTheory.maximal_ineq` (`OptionalStopping.lean:155`) ist Doobs
  Maximalungleichung für nichtnegative Submartingale über `Filtration ℕ`; der
  Modulkommentar `OptionalStopping.lean:153` sagt selbst, dass die
  `Lᵖ`-Ungleichung „will be proved in an upcoming PR" — auf master steht dieser
  Satz unverändert, die Ungleichung fehlt also weiterhin. Nachgetragen als
  dritter Punkt von `MartingaleProblems` Meilenstein 9
  (`maximal_ineq_of_rightContinuous`, `Submartingale.eLpNorm_iSup_le` und die
  Martingal-Korollare), zusammen mit der Messbarkeit des Supremums über einen
  überabzählbaren Index.
* **`fact:fddconv`** (tragend 1). Beide Hälften stehen in `SkorokhodSpace`
  Meilenstein 8: (a) `tendsto_finiteDimensional_of_tendsto`, (b)
  `tendsto_of_isTight_of_tendsto_finiteDimensional`. „Relativ kompakt" gegen
  „straff" ist über Prohorov dasselbe, aber nur auf polnischem `E`; der Fact
  verlangt nur separabel. Als Auffälligkeit notiert, nicht stillschweigend
  gleichgesetzt.
* **`fact:relcompact`** (tragend 1) und **`fact:relcompact2`** (tragend 2).
  Beides Lücken; Mathlib scheidet mit dem Skorokhod-Raum aus. `rem:EKrelcompact`
  des Manuskripts sagt selbst, woraus es besteht: „Facts `relcompact`,
  `relcompact2`, `fddconv` und `prohorov`". Die Roadmaps hatten davon nur die
  **Folgerung**: `MartingaleProblems` Meilenstein 11 nannte
  `isRelativelyCompact_of_approx` und als Beweisweg „Stone–Weierstrass plus das
  Straffheitskriterium von `SkorokhodSpace`" — aber das Kriterium von EK 3.9.1
  (Rückführung auf `D_ℝ` entlang einer kompakt-gleichmäßig dichten Teilmenge von
  `Cb(E)`) stand in `SkorokhodSpace` Meilenstein 7/8 nirgends, und das
  Martingalkriterium von EK 3.9.4 (der Banachraum `𝓛 n`, die Paare `𝓐 n`, die
  `Lᵖ`-Schranke an `Z n`) in Meilenstein 11 auch nicht. Beide sind jetzt als
  eigene Punkte benannt: `SkorokhodSpace.continuous_postcomp` und
  `SkorokhodSpace.isTightMeasureSet_iff_forall_postcomp` in Meilenstein 8,
  `isTight_map_postcomp_of_exists_martingale` in Meilenstein 11, und
  `isRelativelyCompact_of_approx` verweist jetzt auf beide statt auf eine
  Beweisskizze. EK 3.9.4 ist über `ℝ` formuliert; das Manuskript hält bei 2387
  fest, dass das nur an EK liegt, und die Roadmap notiert die `𝕂`-Fassung.
* **`fact:fdd`** (tragend 0). Die zweite Hälfte, `Bor(D_E) = σ(π_t)`, ist
  `SkorokhodSpace.borel_eq_iSup_comap_eval` in Meilenstein 6 und war schon da.
  Die erste war es nur halb: der Produktpunkt von `WeakConvergence`
  Meilenstein 1 stand für einen **endlichen** Index `S 1, …, S k`, der Fact
  verlangt `S = ∏_{k ≥ 1} S_k`. Für endlich-dimensionale Verteilungen eines
  Prozesses ist der Index die Zeitmenge, der endliche Fall genügt also nicht.
  Der Punkt ist auf einen beliebigen Index umgestellt, mit Produkten über
  `J : Finset ι` und Abzählbarkeit von `ι` nur für die konvergenzbestimmende
  Hälfte.

Nebenbefund, in die Roadmap eingetragen: die Liste „Mathlib supplies" von
`MartingaleProblems` nannte optional stopping, Doobs Ungleichungen, die
Upcrossing-Theorie und die Konvergenzsätze pauschal als vorhanden. Alle vier
sind auf `Filtration ℕ` festgelegt (`Convergence.lean:55`, `Upcrossing.lean:315`,
`OptionalStopping.lean:37`); nur die **Definitionen** `Martingale`,
`Supermartingale`, `Submartingale` (`Basic.lean:48,53,59,65`) gelten für
`[Preorder ι]`. Die Liste sagt das jetzt.

**Offen geblieben.** Nichts an diesen acht Zeilen; nicht angefasst wurden
`fact:bp`, `fact:sepcond`, `fact:fullgenerator` und `fact:stoppedlocalmg`.
Damit stehen noch vier `?` in der Tabelle, gegenüber zwölf zu Beginn des Laufs.
`fact:stoppedlocalmg` ist der nächste: die Notiz in der Tabelle vermutet
`MeasureTheory.Locally` und `stoppedProcess_localSeq` aus
`Probability/Process/LocalProperty.lean`, und diese Datei existiert auf master
wie in v4.33.1, aber ob sie EK Proposition 2.3.1 wirklich hergibt, ist
ungeprüft. `fact:bp` und `fact:fullgenerator` sind keine Suchaufgabe, sondern
die offene Entscheidung aus der Liste oben: „nur für optionalen Kontext" ist
kein Roadmap-Status.

**Als Nächstes zu formalisieren: `MeasureTheory.induction_on_mulSystem`**
(`WeakConvergence` Meilenstein 5). Es ruht auf nichts als
`MeasurableSpace.comap` (`MeasureTheory/MeasurableSpace/Basic.lean:82`), dem
Satz von der monotonen Konvergenz und `induction_on_inter`
(`MeasureTheory/PiSystem.lean:692`), das zugleich die Vorlage für Gestalt,
`@[elab_as_elim]`-Attribut und Beweisführung ist. Es ist jetzt dran, weil es die
einzige der acht heute geschlossenen Lücken ist, die von keiner anderen Roadmap
abhängt — `WeakConvergence` hängt nur an Mathlib —, und weil drei Punkte, die
schon in den Roadmaps stehen, unmittelbar darauf warten: die Produktaussage in
`WeakConvergence` Meilenstein 1, `isDetermining_products` in
`MartingaleProblems` Meilenstein 3 und `isMPSolutionFor_iff_forall_fdd`
ebenda. Ein Satz ohne Vorbedingungen, an dem drei wartende Punkte hängen, ist
der richtige erste.

### 2026-08-30 — `fact:bp`, `fact:sepcond`, `fact:fullgenerator`, `fact:stoppedlocalmg`

Die letzten vier `?` der Tabelle. Alle vier sind Lücken, alle vier stehen jetzt
als benannte Punkte in einer Roadmap. Damit ist **jede der 29 Zeilen belegt**.
Geprüft wurde gegen `~/Code/lean/journal/.lake/packages/mathlib` (v4.33.1) und
gegen master über `gh api`/`gh search code`.

* **`fact:sepcond`** (tragend 2). Kein zitierter Fact: das Manuskript beweist
  ihn in `rem:sepcondproof` selbst. Zu formalisieren ist er trotzdem, denn
  `thm:absreg` schließt mit ihm (Stelle 3167). Nachgetragen als letzter Punkt
  von `WeakConvergence` Meilenstein 1, wo `IsSeparating` definiert wird:
  `IsSeparating.ae_eq_of_forall_condExp_eq`. Der Beweis wird dabei kürzer als
  im Manuskript. Schritt 1 bleibt, braucht aber keine Normierung, weil
  `IsSeparating` für endliche Maße formuliert ist; Schritt 2 und 3 entfallen
  ganz. Mit `G = {V ∈ B} ∈ 𝒢` und dessen Komplement gibt Schritt 1 direkt
  `P(U ∈ B, V ∉ B) = P(U ∉ B, V ∈ B) = 0`, und
  `Filter.EventuallyEq.of_forall_separating_preimage`
  (`Mathlib/Order/Filter/CountableSeparatingOn.lean:257`) macht daraus
  `U =ᵐ V`. Dessen Instanzhypothese `HasCountableSeparatingOn E MeasurableSet
  univ` ist `MeasurableSpace.CountablySeparated`, geliefert von
  `CountablyGenerated` und `SeparatesPoints`
  (`MeasurableSpace/CountablyGenerated.lean:381`), und `CountablyGenerated`
  wiederum von `BorelSpace` mit `SecondCountableTopology`
  (`Constructions/BorelSpace/Basic.lean:210`). Reguläre bedingte Verteilungen
  werden nicht gebraucht, und das ist ein Glück: Mathlibs `condDistrib`
  (`Probability/Kernel/CondDistrib.lean:64`) bedingt auf eine **Abbildung**,
  nicht auf eine Teil-σ-Algebra, und `condExpKernel`
  (`Probability/Kernel/Condexp.lean:70`) verlangt `Ω` selbst standard-borelsch.
  Beides trifft hier nicht zu.
* **`fact:bp`** (tragend 2). Lücke. Mathlib kennt bp-Konvergenz nicht:
  `gh search code` findet weder „boundedly pointwise" noch „bp-closure", und
  `seqClosure`/`IsSeqClosed` (`Topology/Defs/Sequences.lean:55,61`) schließen
  unter den Limiten einer Topologie ab, was bp-Limiten nicht sind. Die
  Roadmaps hatten weder den bp-Abschluss noch `lem:closure`, die vom Manuskript
  als die eigentlich benutzte Fassung bezeichnete Aussage. Beides ist jetzt in
  `MartingaleProblems` Meilenstein 2: `mpProcess`, `MPSolutions.span`,
  `IsMPSolutionFor.insert_of_tendsto` (`lem:closure`, mit
  `MeasureTheory.eLpNorm_condExp_le_eLpNorm`,
  `ConditionalExpectation/Real.lean:288`, als einzigem analytischen Werkzeug)
  und darauf der bp-Block `BpTendsto`, `bpClosure`, `Submodule.bpClosure`,
  `isMPSolutionFor_bpClosure`. Der Befund, der die Größe der Lücke bestimmt:
  EKs transfinite Rekursion über die abzählbaren Ordinalzahlen wird in Lean
  durch eine **induktive Definition** von `bpClosure` ersetzt, und EK Appendix 3
  Proposition 3.1 ist dann eine doppelte Induktion über deren
  Induktionsprinzip, nach dem Muster von `induction_on_inter`. Der Fact ist
  damit kein schwerer Punkt mehr, sondern ein mittlerer.
* **`fact:fullgenerator`** (tragend 1). Die größte der vier Lücken, und die
  einzige, die außerhalb der Wahrscheinlichkeitstheorie liegt: Mathlib hat
  **keine Operatorhalbgruppen**. `dissipative` kommt in master nirgends vor
  (`gh search code`, null Treffer), eine stark stetige oder messbare
  Halbgruppe gibt es nicht, und Hille--Yosida steht in `docs/1000.yaml` als
  `Q974405` ohne `decl`. Vorhanden ist nur die Resolvente beschränkter
  Elemente einer Banachalgebra (`Analysis/Normed/Algebra/Spectrum.lean:285ff`),
  die hier nichts hilft. Da kein Meilenstein den Gegenstand hatte, ist
  `MartingaleProblems` Meilenstein 13 neu angelegt: `IsDissipative`,
  `MeasurableContractionSemigroup`, `fullGenerator`,
  `fullGenerator_isDissipative` mit der Resolventenformel (EK 1.5.1), die
  Darstellung `mpSolution_resolvent_repr` als eigener Punkt, und die beiden
  Richtungen `isDissipative_of_forall_exists_mpSolution` (EK 4.3.5) und
  `isMPSolutionFor_fullGenerator` (EK 4.1.7). Messbarkeit, nicht starke
  Stetigkeit: die Übergangshalbgruppe eines Markovprozesses auf `Bdd(E)` ist
  nicht stark stetig, und nichts im Meilenstein braucht es. Hille--Yosida,
  Cores und die Exponentialformel bleiben draußen, wie `rem:noch1` es sagt.
* **`fact:stoppedlocalmg`** (tragend 0). Lücke, aber die kleinste. Die Notiz
  des letzten Laufs war halb richtig: `MeasureTheory.Locally`, `IsStable` und
  `IsStable.locally` existieren (`Probability/Process/LocalProperty.lean:93,142,153`,
  auf master wie in v4.33.1), aber sie sind **abstrakt** — die Datei nennt
  Martingale nur im Modulkommentar, und `Locally` wird nirgends an einem
  Martingal instanziiert. Was fehlt, ist genau die Stabilität der
  Martingaleigenschaft unter Stoppen in stetiger Zeit;
  `Submartingale.stoppedProcess` (`OptionalStopping.lean:104`) ist auf
  `Filtration ℕ` und reellwertige Prozesse festgelegt. Nachgetragen als Punkt
  von `MartingaleProblems` Meilenstein 9, wo das dafür nötige Optional Sampling
  in stetiger Zeit schon steht: `isStable_martingale_rightContinuous`, als
  Eigenschaft die **Konjunktion** aus Martingal und Rechtsstetigkeit, denn nur
  sie ist stabil. `IsStable.locally` liefert dann EK 2.3.1 ohne weiteren
  Beweis. Der Fact ruht also auf `fact:optsampl`, und beide liegen jetzt im
  selben Meilenstein.

**Zur offenen Frage der vier Facts ohne tragende Fundstelle.** Für
`fact:stoppedlocalmg` nachgesehen und nichts gefunden: die Lokalisierung des
Manuskripts (`def:localizing`, Stelle 4385) setzt in \ref{it:L1} die
Martingaleigenschaft der gestoppten Prozesse **voraus** und leitet sie nicht
her. Mittelbar getragen wird der Fact damit erst dort, wo ein konkretes
lokalisierendes System verifiziert wird — in der Roadmap
`localizingSystem_of_boundedJumps`. Das ist eine schwächere Trägerschaft als
die von `fact:doob`, aber keine Entbehrlichkeit.

**Offen geblieben.** Nichts an diesen vier Zeilen. Das Inventar ist damit
vollständig: 29 Zeilen, kein `?`. Ungeprüft bleibt weiterhin die in den
Auffälligkeiten notierte Frage, ob die Roadmaps von polnischem auf
separabel-metrisches `E` umgestellt werden; sie betrifft `fact:fddconv`,
`fact:cmt` und `fact:PSpolish` und ist keine Suchaufgabe, sondern eine
Entscheidung.

**Als Nächstes zu formalisieren: `MeasureTheory.IsSeparating` samt
`IsSeparating.ae_eq_of_forall_condExp_eq`** (`WeakConvergence` Meilenstein 1).
Das Prädikat ruht auf `ext_of_forall_integral_eq_of_IsFiniteMeasure`
(`MeasureTheory/Measure/HasOuterApproxClosed.lean`), die bedingte Fassung
zusätzlich auf `Filter.EventuallyEq.of_forall_separating_preimage`
(`Order/Filter/CountableSeparatingOn.lean:257`) und der bestimmenden
Eigenschaft von `condExp`. Beides ist heute am Quelltext geprüft, beides liegt
in Mathlib fertig vor, und der Beweis ist der oben skizzierte Zweischritt --
also kein neuer Begriff außer dem Prädikat selbst. Es ist jetzt dran, weil
`IsSeparating` das einzige Prädikat ist, das **zwei** Roadmaps als Hypothese
führen: der Satz über die càdlàg-Modifikation in `MartingaleProblems`
Meilenstein 9 verlangt „`Φ` ist separierend", und `isDetermining_products` in
Meilenstein 3 baut darauf. Solange das Prädikat nicht existiert, greift jeder
dieser Punkte an den `ext_of_…`-Sätzen vorbei — und die bedingte Fassung
kostet, einmal das Prädikat da ist, zwanzig Zeilen. Sie schließt zugleich die
einzige Stelle des Manuskripts, an der eine trennende Klasse gegen eine
σ-Algebra statt gegen ein zweites Maß gespielt wird.

Damit sind es zwei benannte Ziele, die nebeneinander stehen dürfen, weil beide
nur an Mathlib hängen: `induction_on_mulSystem` (Meilenstein 5, vom
2026-08-29) und `IsSeparating` (Meilenstein 1). Reihenfolge: `IsSeparating`
zuerst, denn `isDetermining_products` braucht beide, und dieses ist das
kleinere.

### 2026-08-30, zweiter Lauf — Inventar vollständig, also Task 23

Die Tabelle hat kein `?` mehr; nach der stehenden Regel wechselt der Lauf zu
**Task 23**, dem Beweis der Dualitätsidentität für eine rein atomare Uhr. Am
Inventar wurde nichts geändert, an den Roadmaps eine Ergänzung, am Manuskript
der Eintrag, den Task 23 vorsieht. Der ausführliche Bericht steht in
`Task23/PROTOKOLL.md`; hier das Wesentliche.

**Stufe 1 und Stufe 2 sind bewiesen.** `rem:atomicdual` ist jetzt
`prop:atomicdual` mit Beweis, gestützt auf ein neues `lem:atomgrid`. Der Kern:
eliminiere `γ` durch Kreuzmultiplikation der beiden Zuwachsdarstellungen an
derselben Stelle, was
`m_j(Φ(i+1,j)-Φ(i,j)) = m_i(Φ(i,j+1)-Φ(i,j))` liefert; diese Relation ist linear
in `Φ` und invariant unter Transposition, also erfüllt der antisymmetrische
Anteil `w = Φ - Φᵀ` sie ebenfalls, und eine Induktion über den **Abstand zur
Diagonale**, die die Stufen `d` und `d-1` zugleich mitführt, gibt `w ≡ 0`.
Gebraucht wird nur `m_i ≠ 0`: keine Positivität, keine Integrabilität, keine
Regularität von `γ`. Die zweite Konvention `ι = o` ist nicht ein zweiter Beweis,
sondern dieselbe Aussage nach Spiegelung des Gitters und Umkehrung der
Massenliste.

Stufe 2 kostet danach nichts: sind die Atome unter `t` endlich viele und
paarweise vergleichbar, so ist die Kette `0, a₁, …, a_N, t` ein Gitter, und
abzählbar viele Atome insgesamt sind kein Hindernis. Genau das ist die stehende
Hypothese von `rem:atomicdual`.

**Verifiziert, nicht nur geglaubt.** `Task23/verify.py` (neu) baut das volle
homogene System, das \eqref{eq:incrementrep} den Unbekannten `Φ, γ` auferlegt,
nimmt dessen Kern und prüft an einer Kernbasis die Dualitätsidentität, die
Symmetrie von `Φ` auf dem ganzen Quadrat und die Symmetrie von `γ` im Inneren.
Exakte rationale Arithmetik, `N = 2..8`, drei Massenvektoren, beide
Konventionen: 42 Konfigurationen, alle drei Aussagen überall erfüllt. Das ist
stärker als `oracle.py`, das die Reduktion auf eine freie Zeile schon
voraussetzte. Danach meldet `python3 check.py` `clean` (123 Seiten, keine
undefinierten Referenzen).

**Ein Befund am Manuskript, und er ist eingetragen.** `rem:atomicdual` behauptete
bisher, das Argument brauche „no order structure beyond a preorder". Bewiesen
ist weniger: die Atome unter `t` müssen eine **Kette** bilden — unter
\eqref{T2a} automatisch, unter \eqref{T0} nicht. Die Statustabelle von
`rem:atomsnotchange` trennt jetzt beide Zeilen: „purely atomic, atoms a chain"
ist `proved`, „purely atomic, atoms incomparable" bleibt „verified symbolically;
not proved", und ordnungsdichte Atome stehen bei „open" statt stillschweigend
unter der bewiesenen Zeile. Ordnungsdichte Atommengen sind nämlich gar nicht
Stufe 2: sie verletzen die Hypothese „endlich viele Atome unter jedem `t`", und
der Grund ist scharf — liegen die Atome dicht, trägt kein Intervall `[s,s')`
genau ein Atom, die Gitterrelation hat kein Gegenstück, und es gibt kein Gitter,
an dem entlang induziert werden könnte.

**In die Roadmap eingetragen.** `MartingaleProblems` Meilenstein 8 hatte zur
atomaren Uhr keinen Punkt — er nannte `duality_of_atomless` und
`duality_discrete` und ließ dazwischen eine Lücke. Jetzt stehen dort
`atomGrid_symm`, `Clock.atomChain` und `duality_of_atomic`, und
`duality_discrete` ist als der Fall `m ≡ 1` von `duality_of_atomic` kenntlich.

**Ein zweiter Befund, der den nächsten Lauf spart.** `Task23/poset.py` (neu)
prüft den Fall unvergleichbarer Atome an `T = {0,1,2}²` mit der Produktordnung
nach, und zwar mit *allen* Relationen aus \eqref{eq:incrementrep} — für jedes
vergleichbare Paar, nicht nur für Einschrittintervalle. Zweierlei kommt heraus:
die Notiz des Manuskripts stimmt, `Φ(t,0) = Φ(0,t)` gilt dort für jedes `t`;
aber die **Symmetrie** `Φ(s,t) = Φ(t,s)` gilt nicht, sie fällt an den maximalen
und unvergleichbaren Punkten aus, etwa bei `((1,2),(2,1))`. Die Symmetrie ist
ein Phänomen der Kette, nicht der atomaren Uhr. Ein Beweis für den allgemeinen
Präordnungsfall kann also nicht über sie laufen — was die naheliegendste
Verallgemeinerung von `lem:atomgrid` ausschließt, bevor jemand sie versucht.
Auch das steht jetzt im Manuskript.

**Offen geblieben.** Der Fall unvergleichbarer Atome (der kleinste Fall geht von
Hand und steht im Protokoll; ein allgemeines Argument fehlt, und der Weg über
die Symmetrie ist nach dem eben Gesagten versperrt), ordnungsdichte Atommengen,
und Stufe 3, die gemischte Uhr. Ebenso unberührt die ältere Frage aus den
Auffälligkeiten, ob die Roadmaps von polnischem auf separabel-metrisches `E`
umgestellt werden.

**Als Nächstes zu formalisieren: `atomGrid_symm`** (`MartingaleProblems`
Meilenstein 8). Es ruht auf nichts — Körperarithmetik über `ℝ`, `ℕ` als einziger
Index, und eine Induktion, die zwei Stufen zugleich mitführt, also
`Nat.le_induction` auf der starken Form der Aussage. Kein Maß, keine Uhr, keine
Topologie, kein Import außer `Mathlib/Algebra/Order/`. Es ist jetzt dran, weil es
das kleinste vollständig bewiesene Objekt des ganzen Manuskripts ist, weil sein
Beweis seit heute Zeile für Zeile im Manuskript steht und symbolisch gegengeprüft
ist, und weil `duality_of_atomic` unmittelbar darauf wartet, ohne dass eine der
vier Roadmaps sonst etwas beisteuern müsste. Ein Satz ohne Vorbedingungen, dessen
Beweis schon geschrieben ist, ist der billigste erste Schritt, den dieses Projekt
gerade hat — und der einzige, bei dem die Formalisierung den Papierbeweis
tatsächlich prüfen kann, statt ihn nur nachzuzeichnen.

### 2026-08-30, dritter Lauf — Task 23, der Halbordnungsfall

Die Tabelle hat weiterhin kein `?`; der Lauf ging nach der stehenden Regel an
Task 23, und zwar an dessen ersten offenen Punkt, die **unvergleichbaren
Atome**. Ein Beweis kam nicht heraus. Zwei Dinge kamen heraus, die es wert sind,
und das Ausführliche steht in `Task23/PROTOKOLL.md`.

**Eine Reduktion, die `Φ` eliminiert.** Weil `T` ein kleinstes Element hat, ist
`T_{<0}` leer, und \eqref{eq:incrementrep} an `s = 0` bzw. `t = 0` löst `Φ` auf:
`Φ(s,t) = Φ(0,t) + Σ_{a<s} m_a γ(a,t)` und ebenso in der zweiten Variablen.
Beides zusammen ist mit \eqref{eq:incrementrep} gleichwertig, und übrig bleibt
eine Bedingung an `γ` allein. Diese zerfällt entlang `γ = (λ+κ)/2` in eine
Bedingung an den symmetrischen und eine an den antisymmetrischen Anteil, und der
Dualitätsdefekt `Φ(t,0) − Φ(0,t) = Σ_{a<t} m_a (γ(a,0) − γ(0,a))` hängt **nur an
`κ`**. Der symmetrische Anteil von `γ` kommt in der Dualität nicht vor. Auf einer
Kette erzwingt die `κ`-Bedingung sofort `κ ≡ 0` — das ist `lem:atomgrid` ohne
`Φ`. Als `duality_defect_eq_integral` in `MartingaleProblems` Meilenstein 8
eingetragen, vor `atomGrid_symm`, weil es unbedingt gilt und `duality_of_atomic`
kürzer macht.

**Ein Gegenbeispiel, das eine Begründung des Manuskripts widerlegt.** Auf dem
Diamanten `T = {0,a,b,t*}` mit `m_a = 1`, `m_b = −1` erfüllen
`γ(a,·) ≡ 1`, `γ` sonst `0`, und `Φ(t*,·) ≡ 0`, `Φ` sonst `≡ −1` beide
Darstellungen aus \eqref{eq:incrementrep} und haben `Φ(t*,0) − Φ(0,t*) = 1`.
Exakt gerechnet und die Relationen unabhängig nachgeprüft (`Task23/diamond.py`).
Damit steht fest: **`lem:atomgrid` kommt mit `m_i ≠ 0` aus, der Halbordnungsfall
nicht.** Die Positivität der Massen — also dass `q` ein Maß ist — ist dort
tragend. Siehe die Auffälligkeit oben.

**Und die Hypothese, die es stattdessen braucht, belegt statt geraten.** Über
alle Halbordnungen mit kleinstem Element auf vier und fünf Punkten und alle
Massenvektoren eines kleinen Gitters mit beiden Vorzeichen (18955
Konfigurationen, 624 Ausfälle) gilt ausnahmslos: fällt die Dualität, so gibt es
ein `s` mit `q(T_{<s}) = 0` bei nichtleerem `T_{<s}`. Für eine echte Uhr ist das
automatisch, und über dieselben Halbordnungen mit nichtnegativen Massen (58081
Konfigurationen) gab es keinen einzigen Ausfall. Die Vermutung lautet damit: für
jede Uhr auf einer Halbordnung mit kleinstem Element und endlich vielen Atomen
unter `t*` gilt `Φ(t*,0) = Φ(0,t*)`, ohne Vergleichbarkeit.

`python3 Journal/Blog/MartingaleProblem/check.py` meldet `clean` (123 Seiten).

**Offen geblieben.** Der Beweis des Halbordnungsfalls. Das Protokoll hält fest,
wo er hakt: unter der `κ`-Bedingung allein ist der Defekt durch *gewichtete*
Summen der Gleichungen unterhalb `t` nicht bestimmt — jede solche Kombination
wird zur Identität —, der Gehalt sitzt in den einzelnen Gleichungen an den
maximalen Elementen von `T_{<t}`. Unberührt: ordnungsdichte Atommengen, Stufe 3,
und die ältere Entscheidung, ob die Roadmaps von polnischem auf
separabel-metrisches `E` umgestellt werden.

**Als Nächstes zu formalisieren: `duality_defect_eq_integral`**
(`MartingaleProblems` Meilenstein 8). Es ruht auf nichts als
`MeasureTheory.setIntegral` über `Set.Iio` und der Beobachtung `Iio 0 = ∅` für
ein kleinstes Element — kein Gitter, keine Atome, keine Kette, keine
Vergleichbarkeit, und es gilt für jede Uhr, atomar oder nicht. Es ist jetzt dran,
weil es die einzige Aussage dieses Meilensteins ist, die *vor* der Fallunterteilung
in atomlos und atomar steht und beide Zweige trägt: `duality_of_atomless` und
`duality_of_atomic` beginnen beide damit, `Φ` aus `γ` aufzulösen, und beide
Beweise werden dadurch kürzer statt nur anders. Es ist zugleich die Aussage, die
den Beweisstand am schärfsten wiedergibt — sie sagt, dass Dualität eine Aussage
über den antisymmetrischen Anteil von `γ` ist und über sonst nichts —, und sie
ist noch kleiner als `atomGrid_symm`, das der Lauf vom 2026-08-30 vorgeschlagen
hat. Reihenfolge also: `duality_defect_eq_integral`, dann `atomGrid_symm`, dann
`duality_of_atomic`.
