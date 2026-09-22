
### 2026-09-22, zweiter Lauf des Tages — der Akzeptanztest hat sein **erstes** Paar bekommen, und zugleich ist gemessen, warum das zweite nicht das Quadrat selbst sein kann: der Kompensator eines diskreten Quadrats ist eine **Treppe**, und die Klasse verlangt ein Integral

**Der Vorschlag des Vorlaufs lautete `isEventuallyApproximable_rescaledWalk`,
und er ist nicht eingelöst, aber er ist von einer Richtung in eine Rechnung
verwandelt worden.** Der Vorlauf hatte zwei Klemmstellen benannt: die Filtration
und die gleichmäßige Schranke `K` für den Kompensator des Quadrats. Die erste
ist keine mehr — `martingale_rescaledWalk` steht seit dem 2026-09-21 über
`floorFiltration`, und das ist dieselbe, die `isStronglyProgressive_rescaledWalk`
liest. Die zweite ist nicht die Stelle, an der es klemmt. Es klemmt eine Stufe
davor, und das ist der Befund dieses Laufs.

#### Der Befund: die beiden Paare sind ungleich teuer, und zwar aus einem Grund, der nicht die Irrfahrt betrifft

`MeasureTheory.IsApproximable` verlangt **zwei** Paare je Fehler: eines für den
Prozeß, eines für sein Quadrat.

* **Das erste ist umsonst.** Ein Martingal ist sein eigener Approximant — Fehler
  `0`, Kompensator `0`, Dichte `0`, Konstante `K = 0`.
* **Das zweite ist es nicht, und der Grund ist strukturell.** Zum Quadrat der
  Irrfahrt gehört der Kompensator `⟨V⟩ t = (n+1)⁻¹ ∑_{j < ⌊t(n+1)⌋} 𝔼[ξ_j²]`,
  und `V² − ⟨V⟩` ist ein Martingal. Aber `⟨V⟩` ist eine **Treppenfunktion der
  Zeit**, und das Feld `IsApproximatingPair.compensator_eq` verlangt
  `C t ω = ∫_{(0,t]} Z s ω` mit `Z` in `L^q`. **Keine Treppe ist ein solches
  Integral.**

Der Approximant des Quadrats ist deshalb nicht das kompensierte Quadrat,
sondern das kompensierte Quadrat **plus einen absolutstetigen Kompensator**, und
der Fehler ist der Abstand der beiden. Bei gemeinsamem zweitem Moment `σ` ist
der absolutstetige Kompensator `t · σ` mit der konstanten Dichte `σ`, und der
Abstand ist

```
(t − ⌊t (n+1)⌋ / (n+1)) · σ ≤ σ / (n+1),
```

gleichmäßig in `ω` **und** in `t`.

**Und das ist der Punkt.** Dieser Fehler geht gegen `0` *längs der Familie* und
ist bei festem `n` eine feste positive Zahl. Das ist dieselbe Aussage, die der
dreiundzwanzigste Lauf des 2026-09-21 als Unmöglichkeit gefunden hatte — eine
Irrfahrt ist bei festem Index durch nichts approximierbar —, hier aber von der
anderen Seite und mit einer Zahl daneben. `IsEventuallyApproximable` ist also
nicht bloß die Bedingung, unter der der Akzeptanztest durchgeht; sie ist die
Bedingung, unter der er **überhaupt formulierbar** ist, und der Betrag des
Fehlers ist `σ/(n+1)`.

#### Was gebaut ist — vier Deklarationen

| Deklaration | was sie sagt |
| --- | --- |
| `MeasureTheory.martingale_sq_partialSum_of_iIndepFun` | `(∑_{k<n} ξ k)² − ∑_{k<n} 𝔼[ξ k²]` ist ein Martingal für die natürliche Filtration der Summen |
| `MeasureTheory.martingale_sq_rescaledWalk` | dasselbe für die reskalierte Irrfahrt, längs der Abrundung umindiziert |
| `MeasureTheory.isApproximatingPair_rescaledWalk` | die Irrfahrt ist ihr eigener Approximant, mit `C = 0`, `Z = 0`, `K = 0` |
| `MeasureTheory.IsApproximatingPair.integrable_stoppedValue_of_dominated` | der gestoppte Wert ist integrierbar, wenn der Approximant bis `j` von einem **integrierbaren** `g` dominiert wird |

`check_master.py` nach dem Einbau: **0 Fehler, 0 `sorry`**, Warnungen unverändert
18 / 38 / 112, davon veraltet 0 — der Einbau erzeugt also keine einzige neue
Warnung. Alle vier mit `check_axioms_master.py` geprüft und auf `propext`,
`Classical.choice`, `Quot.sound` und nichts sonst; `…_of_bounded`, das jetzt
Instanz von `…_of_dominated` ist, mitgeprüft. Die Punkte stehen in
`MartingaleProblems/README.md`, Meilenstein 11.

#### Das kompensierte Quadrat: eine Lücke in Mathlib, am Quelltext belegt

**Mathlib hat es in keiner Fassung.** Gesucht am Quelltext von `master`
`09712d488fd` unter `Mathlib/Probability/` nach `QuadraticVariation`,
`predictableQuadratic` und `quadratic variation` — null Treffer; in
`Mathlib/Probability/Moments/Variance.lean` kommt `Martingale` **nicht ein
einziges Mal** vor, und die einzigen Treffer von `sq_sub` unter
`Mathlib/Probability/` sind `condVar_ae_eq_condExp_sq_sub_sq_condExp` und seine
Verbraucher, also die bedingte Varianz und nicht der Kompensator. Was Mathlib
hat, ist `ProbabilityTheory.IndepFun.variance_sum` — diese Aussage zu **einer**
Zeit und mit weggeworfener Bedingung. Das ist eine neue Lücke für `TODO.md`
Punkt 8.

**Der Kompensator ist die Summe der zweiten Momente und nicht der Varianzen.**
Unter der Zentriertheit sind beide gleich; die zweiten Momente sind, was der
Beweis erzeugt, denn `∫ ξ n ²` ist die bedingte Erwartung von `ξ n ²` unter der
Unabhängigkeit, und die Varianz müßte auf jeder Stufe zurückgerechnet werden.

**Wo die beiden Voraussetzungen an die Summanden verbraucht werden, je an einer
Stelle.** Die Zentriertheit tötet das Kreuzglied `2 · S n · ξ n` — über
`MeasureTheory.condExp_mul_of_stronglyMeasurable_left`
(`Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean:245`), deren
`m`-meßbarer Faktor die Summe und deren unabhängiger Faktor der Zuwachs ist —,
und die Quadratintegrierbarkeit kauft die Integrierbarkeit dieses Kreuzglieds
(`MeasureTheory.MemLp.integrable_mul` am Hölderpaar `(2,2)`,
`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1086`) und die des
Quadrats (`MeasureTheory.MemLp.integrable_sq`,
`Mathlib/MeasureTheory/Function/L2Space.lean:42`). Die Unabhängigkeit wird genau
dort gelesen, wo sie `martingale_partialSum_of_iIndepFun` liest, und **dieselbe**
Unabhängigkeit bedient den Zuwachs und sein Quadrat, weil `ξ n ²` für die
σ-Algebra von `ξ n` meßbar ist.

#### Zwei Kleinigkeiten, die Zeit gekostet haben und die aufzuschreiben sie spart

* **Die Konstante der *nächsten* Stufe bleibt beim adaptierten Summanden.** Die
  Zerlegung des Schrittes als
  `(S n ² − ∑_{k<n+1} 𝔼[ξ k²]) + (2 · S n · ξ n + ξ n ²)` läßt in dem Summanden,
  dessen bedingte Erwartung gerechnet wird, **keine Subtraktion** stehen, und
  `MeasureTheory.condExp_sub` muß mit `Pi.sub` gar nicht erst versöhnt werden.
  Mit der Konstanten auf der anderen Seite bleibt der Beweis an einem `rw`
  hängen, das `(f − g) ω` sieht, wo das Ziel `f ω − g ω` trägt —
  definitionsgleich, aber für `rw` kein Muster. Das ist dieselbe Falle wie die
  `ENNReal`/`WithTop`-Stelle des achtzehnten Laufs vom 2026-09-10: **nicht am
  Ziel rewriten, sondern die Aussage so hinschreiben, daß das Muster dasteht.**
* **`WithTop.untopA_le` ist durch `@[to_dual]` erzeugt.** Es entsteht aus
  `WithBot.le_unbotA` (`Mathlib/Order/WithBot.lean:658`) und steht in **keiner**
  `theorem`-Zeile; `Mathlib/Probability/Process/Stopping.lean:1019` benutzt es
  unqualifiziert. Das ist die vierte Instanz der stehenden Regel, nach
  `Set.indicator_of_notMem`, `frequently_lt_of_liminf_lt` und `IsCadlag.add`.

#### Warum die Integrierbarkeit des gestoppten Wertes eine Verallgemeinerung brauchte

`IsApproximatingPair.integrable_stoppedValue_of_bounded` verlangte eine
**konstante** Schranke an den Approximanten, und die Irrfahrt hat keine: ihr Wert
auf der Stufe `k` ist eine Summe unabhängiger Summanden. Auf einer beschränkten
Zeitstrecke wird sie aber von der Summe der endlich vielen Stufenwerte dominiert,
die dort vorkommen können, und die ist integrierbar. Die Verallgemeinerung auf
einen **integrierbaren Majoranten** kostet nichts — `Integrable.mono'` statt
`integrable_const` — und der bisherige Satz ist jetzt ihre Instanz am konstanten
Majoranten. Die Dominierung wird nur bis `j` verlangt, weil `WithTop.untopA_le`
die Lesestelle des gestoppten Wertes unter `j` legt; eine Schranke darüber wäre
eine Voraussetzung über Werte, die die Aussage nie ansieht.

**Ohne sie wäre der Akzeptanztest nicht erreichbar gewesen**, und das ist keine
Vermutung: `IsApproximable` fordert die vier Integrierbarkeiten von **jedem**
Paar, und mit konstantem Majoranten erreicht die Klasse keinen unbeschränkten
Approximanten.

#### Vorschlag für den nächsten Lauf, als benanntes Ziel

> `MeasureTheory.isApproximatingPair_sq_rescaledWalk` — das **zweite** Paar: für
> Zuwächse mit gemeinsamem zweitem Moment `σ` ist
> `Y' t ω = V t ω ² − ⟨V⟩ t ω + t σ` mit `C' t ω = t σ` und `Z' s ω = σ` ein Paar
> der Klasse, und `‖Y' t ω − V t ω ²‖ ≤ σ / (n+1)` gleichmäßig.

**Worauf es ruht, und das meiste steht.** Die Martingaleigenschaft von
`Y' − C' = V² − ⟨V⟩` ist `martingale_sq_rescaledWalk` dieses Laufs. Der
Kompensator ist `∫_{(0,t]} σ ds = t · σ`, also `setIntegral_const` und
`Real.volume_Ioc` und sonst nichts — **das ist der Grund, das gemeinsame zweite
Moment vorauszusetzen und nicht die allgemeine Treppendichte
`Z' s ω = 𝔼[ξ_{⌊s(n+1)⌋}²]`**: die allgemeine Fassung verlangt die Auswertung von
`∫_{(0,t]} f ⌊s c⌋₊ ds` als Teleskopsumme über die Zellen, eine Induktion über
`⌊t c⌋`, und sie ist der ganze Mehrpreis. Die Voraussetzung ist keine
Bequemlichkeit gegen die stehende Regel: Donsker verlangt identisch verteilte
Zuwächse ohnehin, und das gemeinsame zweite Moment ist genau das, was davon
gebraucht wird. **Die allgemeine Fassung gehört als eigener Punkt daneben, mit
der Treppendichte als Inhalt und der Zellinduktion als benanntem Preis.**

**Die Stelle, an der es klemmen kann, benannt.** Die Rechtsstetigkeit von
`Y' − C'` ist kein Problem — `Y' − C' = V² − ⟨V⟩`, beides Treppenpfade —, wohl
aber `ae_memLp` und `lintegral_eLpNorm_le` **für die konstante Dichte**: die sind
`eLpNorm` einer Konstanten auf `Set.Ioc 0 T`, also `σ · T^{1/q}`, und damit ist
`K = σ · T^{1/q}` **gleichmäßig in `n`** — der Punkt, an dem der Vorlauf die
Klemmstelle vermutet hatte, ist bei dieser Wahl der Dichte frei. Was bleibt, ist
die Buchhaltung des Fehlers: `⨆ t ∈ Set.Iic T` einer Schranke, die von `t` nicht
abhängt, und dann `lintegral_const` gegen ein Wahrscheinlichkeitsmaß — dieselbe
Rechnung wie `hstep` in `isEventuallyApproximable_scaledStep`.

**Und danach, und erst danach**, ist `isEventuallyApproximable_rescaledWalk` der
Zusammenbau: die beiden Paare mit `mono_K` auf ein gemeinsames `K` gehoben, die
vier Integrierbarkeiten über `integrable_stoppedValue_of_dominated` dieses Laufs,
und `isEventuallyApproximable_of_tendsto_zero_cofinite` mit dem Fehler
`e n = ofReal (σ/(n+1))`. Was dort noch zu tun bleibt und hier nicht erhoben
wurde, ist der **Majorant** der Irrfahrt auf `Set.Iic u`: die Summe der
`⌊u(n+1)⌋ + 1` Stufenwerte, integrierbar, aber als Aussage noch nicht
hingeschrieben.
