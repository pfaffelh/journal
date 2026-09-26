### Derselbe Lauf, dritter Teil — B2 weiter offen; Aufgabe C, Schritt C2, Rest: **der Poissonprozeß von Hand mit `f = id`**, über `insert_of_tendsto`

**B2:** in diesem Lauf nicht angefaßt. Die Eingrenzung des Laufs 11:03 gilt unverändert (kein Zeuge
bei lokaler Äquivalenz, keiner bei einem einzigen Trennzeitpunkt); die erlaubte Nebenfassung unter
`[𝓕.IsRightContinuous]` über den Dichteprozeß ist weiter nicht gebaut. Nach der Regel „wer
steckenbleibt, geht zum nächsten Schritt, der nicht daran hängt“ weiter mit C.

**C2, neu** (`JumpProcesses/Suggested.lean`, Abschnitt `PoissonExample`, hinter
`jumpMeasure_map_jumpProcess_poisson`):

| Rolle | Lean-Name | Zeile |
| --- | --- | ---: |
| `n ↦ (n : ℝ)` integrierbar gegen `poissonMeasure r` (Mathlib hat kein Moment der Poissonverteilung) | `integrable_natCast_poissonMeasure` | 4842 |
| Erzeuger an der Stutzung: `A (min · n) = 1_{x < n}` | `jumpApply_poisson_min` | 4854 |
| **Akzeptanz: der Poissonprozeß löst das Problem mit `(id, 1)` dazu** | `poissonProcess_isMPSolutionFor_insert_id` | 4878 |

Aussage: `IsMPSolutionFor (insert (id, 1) (jumpOperator poissonRate poissonJumpKernel))` für den
konstruierten Poissonprozeß, seine Filtration und sein Gesetz; `N t - t` ist also Martingal. Der
Beweis benutzt **nur** `poissonProcess_isMPSolution` (beschränkte Paare) und
`IsMPSolutionFor.insert_of_tendsto` mit `f n = min · n`: punktweise Konvergenz der Testprozesse
(erster Term schließlich konstant, zweiter über dominierte Konvergenz auf dem Fenster), Majorante
`2 N t + 2 t`, Integrierbarkeit von `N t` über sein Gesetz `Po(t)`, und die Adaptiertheit von
`N t - t` als punktweiser Limes adaptierter Prozesse (`stronglyMeasurable_of_tendsto`), so daß über
die Filtration der Konstruktion nichts gesagt werden muß. `insert_of_forall_norm_le` greift hier
nicht (`id` unbeschränkt), das ist der Sinn des Beispiels. `#print axioms` für beide tragenden Sätze:
`propext`, `Classical.choice`, `Quot.sound`. Mathlib-Namen am Quelltext geprüft:
`integrable_poissonMeasure_iff` (`Probability/Distributions/Poisson/Basic.lean:76`),
`tendsto_lintegral_of_dominated_convergence'`
(`MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean:63`), `eLpNorm_one_eq_lintegral_enorm`
(`MeasureTheory/Function/LpSeminorm/Defs.lean:125`, verlangt die Meßbarkeit); dabei gefunden:
`ofReal_norm_eq_enorm` ist auf master veraltet, neu `ofReal_norm`.

`check_master.py` danach: 0 Fehler, 0 `sorry`, 0 Veraltungen, Warnungen 18 / 38 / 38 / 76.
**C2 ist damit bis auf `IsMPSolutionFor.map` längs Gleichheit der Gesetze vollständig.**

### Derselbe Lauf, Abschluß

`check_master.py` am Ende (Mathlib `94ef6b89544`): **0 Fehler, 0 `sorry`, 0 Veraltungen** in allen
vier Dateien, Warnungen 18 / 38 / 38 / 76 wie zu Beginn.

**Stand der drei Aufgaben nach diesem Lauf.**

* **A:** erledigt. A1–A4 vollständig; A5 mit allen im Auftrag benannten Akzeptanzbeispielen und
  jetzt auch „Doob's two inequalities computed“. Offen nur „cutting down to an open subset“, das die
  zwei nicht vorhandenen Sätze `IsMPSolutionFor.integral_comp_stoppedLim_eq` (EK 4.3.8) und
  `IsMPSolutionFor.ae_forall_mem_of_tendsto` (EK 4.3.9) verlangt; Bruchstelle: die Eintrittszeiten
  in `{infEdist < 1/m}` sind für die rohe Filtration keine Stoppzeiten.
* **B:** B1, B3 (**jetzt beide Hälften**), B4 stehen. **B2 offen**, unverändert eingegrenzt.
* **C:** C1 vollständig. **C2** bis auf `map` längs Gleichheit der Gesetze. C3 offen: die reelle
  Fassung über bloßem `[MeasurableSpace E]`, „meßbar zu jeder Zeit, progressiv zu keiner“. C4 global.
  C5 offen: beliebige f.s. endliche Stoppzeit, Chapman–Kolmogorov, klassische Instanz,
  Akzeptanzbeispiele.

**Befunde für den Nutzer (kein Manuskript, keine README angefaßt; nichts nach außen):**

1. `thm:localuniq`, Markov-Hälfte, auf beliebigem `Ω` braucht nicht „`𝓖` = natürliche Filtration“,
   sondern nur `𝓖 r ≤ σ(Φ)`-Vergangenheit bei `r`; sie ist nicht entbehrlich, weil die
   Lösungseigenschaft des Bildmaßes über `𝓖` nichts sagt.
2. Mathlib hat kein Moment der Poissonverteilung; `integrable_natCast_poissonMeasure` ist ein
   Kandidat für Mathlib (nicht eingereicht).

**Benanntes Ziel für den nächsten Lauf, der nächste offene Schritt der Liste: B2.** Kommt B2 nicht
voran, dann der Rest von C3 (die reelle Fassung `Clock.IsProgressiveComp` über bloßem
`[MeasurableSpace E]` durch Approximation von rechts), danach C5 (i), die starke Markoveigenschaft
an einer beliebigen f.s. endlichen Stoppzeit über dyadische Approximation von oben und
`isStrongMarkov_kernel_of_countable_range`.
