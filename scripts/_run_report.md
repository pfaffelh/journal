
### 2026-09-22, achter Lauf des Tages — das benannte Ziel steht, und mit ihm zwei weitere: die **Zelle** und der **Horizont** tragen die Schranke am Prozeß nicht mehr; was dabei an ihre Stelle tritt, ist an *einer* Stelle kein Tausch von Hypothesen, sondern ein **Parameter**, und der Grund dafür ist benennbar und heißt `lintegral_const_mul'`

**Das benannte Ziel des Vorlaufs war `lintegral_ofReal_dist_sq_le_of_isApproximatingPair_of_integrable_mul`**,
mit der Vorfrage nach der Additivität des gewichteten Summanden längs der Kette — die der Vorlauf
in seinem eigenen Nachtrag schon beantwortet hatte. Beides ist eingelöst, und der Lauf ist über
das Ziel hinausgegangen, weil die Antwort des Nachtrags trug.

#### Gebaut und übersetzt — drei Deklarationen

Alle in `TauCeti/MartingaleProblems/Suggested.lean`, Zeilen **nachher**:

* **`MeasureTheory.lintegral_ofReal_dist_sq_le_of_isApproximatingPair_of_integrable_mul`**
  (Z. 45270) — das benannte Ziel. Die Zelle von (9.26) ohne `hVb`, mit dem gewichteten Fehler
  `γ` und dem zweiten Summanden `2 * ∫⁻ ω, ‖stoppedValue V α ω‖ₑ * ‖ΔC‖ₑ ∂P`.
* **`MeasureTheory.IsApproximatingPair.sum_lintegral_mul_enorm_compensator_sub_le`**
  (Z. 43901) — die Kettensumme mit einem Gewicht, das **mit der Zelle wechselt**, gegen eine
  gemeinsame Majorante `M` und einen Parameter `Kw`.
* **`MeasureTheory.measure_setOf_oscHitSeq_lt_le_of_isApproximatingPair_of_integrable_mul`**
  (Z. 45472) — der Horizontterm, die beiden vorigen zusammengesetzt.

#### Was aus den sieben Verwendungen von `hVb` geworden ist, einzeln

Der Vorlauf hatte gezählt, daß `lintegral_ofReal_dist_sq_le_of_isApproximatingPair` die
Schranke **siebenmal** liest. Jede ist ersetzt, und keine durch eine Hypothese derselben Art:

| im beschränkten Nachbarn | hier |
| --- | --- |
| `hIVα`, `hIVβ` über `Integrable.mono'` gegen `c` | fallen **ganz weg** — nicht mehr gebraucht |
| `hIVα2`, `hIVβ2` gegen `c^2` | `MemLp.integrable_sq` (`MeasureTheory/Function/L2Space.lean:42`) |
| `hIVc`, `hIYc` über `Integrable.bdd_mul` | `MemLp.fun_mul` + `memLp_one_iff_integrable` |
| `hsq` gegen `(2c)^2` | `(hVβ.sub hVα).integrable_sq` |
| die Schranke am Gewicht der Kompensatoridentität | die vier Produktintegrierbarkeiten |

Die Cauchy–Schwarz-Stelle ist am Quelltext belegt und nicht geraten:
`MeasureTheory.MemLp.mul` (`MeasureTheory/Function/LpSeminorm/CompareExp.lean:537`) in seiner
`to_fun`-Gestalt `MemLp.fun_mul`, mit der Instanz `ENNReal.HolderTriple.instTwoTwo`
(`Mathlib/Basic/ENNReal/Holder.lean:133`), die `2⁻¹ + 2⁻¹ = 1⁻¹` liefert und `r := 1` als
`semiOutParam` bestimmt.

**Und die `L²`-Hypothesen fallen nicht nur auf `V`.** Sie fallen auf `V`, `Y` **und** `C`, weil
`enorm_integral_mul_stoppedValue_sub_le_lintegral_mul` vier Produkte des Gewichts mit den
gestoppten Werten von `Y` und von `C` verlangt und die Klasse nichts hat, was sie erzeugt. Im
Tausch fallen die beiden schlichten Integrierbarkeiten der gestoppten `Y`-Werte weg, die der
beschränkte Nachbar führt. Netto: zwei Hypothesen mehr, eine Schranke weniger — und die
Schranke ist die, die kein Verbraucher einlösen kann.

#### Der eine Punkt, an dem es **kein** Tausch von Hypothesen ist

Der Nachtrag des Vorlaufs hatte vorausgesagt, daß die Summation über die Kette pfadweise trägt
und daß `lintegral_const_mul'` die Stelle ist, an der es aufhört. **Beides bestätigt sich beim
Bauen, und zwar genau so.** Pfadweise ist

```
∑ₖ wₖ ω * ‖ΔCₖ ω‖ₑ ≤ M ω * ∑ₖ ‖ΔCₖ ω‖ₑ ≤ M ω * (ofReal u ^ (1-1/q) * eLpNorm (Z (·,ω)))
```

mit jeder Majorante `M` der Zellgewichte — das ist `sum_enorm_compensator_sub_le` unverändert
und kostet nichts. Danach läßt sich die **Konstante** `ofReal u ^ (1-1/q)` weiterhin
herausziehen (sie hängt nicht von `ω` ab), stehen bleibt aber `∫⁻ ω, M ω * eLpNorm (Z (·,ω))`,
und dafür gibt das einzige Feld der Klasse, `∫⁻ eLpNorm ≤ K`, **nichts** her.

Die Aussage trägt deshalb einen **Parameter** `Kw` dafür, in derselben Bauart wie das `S` von
`lintegral_ofReal_dist_le_sqrt_of_lintegral_mul_biSup_le`. Das ist kein Ausweichen: es benennt
die Forderung, statt sie zu verstecken, und sie ist in den beiden Fällen, die zählen, ohne neues
Feld eingelöst —

* **`Kw = 0`, wenn der Kompensator verschwindet.** `isApproximatingPair_rescaledWalk` hat
  `Z = fun _ _ ↦ 0`; die reskalierte Irrfahrt ist ihr eigenes Martingal. Das ist genau das Paar,
  dessen Gewicht im Kreuzterm die **unbeschränkte** Irrfahrt ist, und der gewichtete Summand ist
  dort null, wie groß das Gewicht auch sei.
* **`Kw = ‖Z‖ * ∫⁻ M`, wenn die Dichte deterministisch ist.** `isApproximatingPair_sq_rescaledWalk`
  hat `Z = fun _ _ ↦ σ`.

Ein **neues Feld** der Klasse — eine `L²`-Schranke an `eLpNorm (Z (·, ω))` — wird erst von einer
zufälligen Dichte gegen ein unbeschränktes Gewicht verlangt. Das ist eine Frage für allgemeine
Kerne und nicht für Donsker, und die Stelle steht benannt.

#### Die Majorante ist das **laufende Maximum**, und das ist die Quantorenentscheidung des Laufs

Jede Zelle fragt ihr eigenes Gewicht `‖V (σ k ω) ω‖ₑ` gegen ihren eigenen Fehler; eine Hypothese
je Stufe wäre unbrauchbar. Gewählt ist deshalb **eine** Hypothese über
`⨆ t ∈ Set.Iic u, ‖V t ω‖ₑ`, und sie trägt, weil die gekappten Trefferzeiten unter `u` bleiben
(`untopA_oscHitSeqCap_le`). Daß dieses Supremum unendlich sein darf, kostet nichts: die
Hypothesen sind Ungleichungen in `ℝ≥0∞`, und eingelöst wird das **Produkt**, nicht der Faktor.

#### Prüfung

`scripts/check_master.py` gegen `upstream/master`
(`94ef6b89544e58e90f119da869f3fb48d1da0f4c`, Lean `4.35.0-rc2`): **0 Fehler, 0 `sorry`** in
allen drei Dateien, Warnungen **18 / 38 / 112, davon 0 veraltet** — unverändert gegenüber dem
Vorlauf; die drei neuen Deklarationen erzeugen keine einzige Warnung.
`scripts/check_axioms_master.py` (mit `--build`; die Kettensumme mit, die beiden anderen ohne
`IsApproximatingPair`-Präfix): alle drei auf `propext`, `Classical.choice`, `Quot.sound`.
`check_cited_lines.py` meldet **445 gepaarte Fundstellen, 0 verschoben, 0 tot** (vorher 443; die
zwei neuen sind die Cauchy–Schwarz-Belege).
`check_own_names.py` zählt **443** statt 440 — die drei sind `Kw` und `hVb`, zwei Hypothesennamen
im Fließtext, und `MeasureTheory.MemLp.fun_mul`.

#### Zwei Befunde über das Werkzeug, beide gemessen

* **`check_own_names.py` ist blind für `@[to_fun]`.** `MemLp.fun_mul` steht dort als „ohne
  Deckung", **existiert aber**: die drei neuen Deklarationen übersetzen, und zwei von ihnen rufen
  ihn auf. Das ist dieselbe Familie falscher Negativbefunde wie bei `Set.indicator_of_notMem`
  (2026-09-13), `frequently_lt_of_liminf_lt` (2026-09-18) und `IsCadlag.add` (2026-09-21) — nur
  diesmal nicht von einem Grep, sondern vom Index. **Ein Eintrag in `own_names.md` ist kein
  Beleg, daß ein Name fehlt**, wenn über dem multiplikativen Nachbarn ein erzeugendes Attribut
  steht; er ist einer, wenn `example … := by exact?` gegen den master-Worktree scheitert.
* **Die Falle `mul_le_mul_left'` / `mul_le_mul_right'` stand längst in der README** — Meilenstein
  11, bei `mul_measure_setOf_lt_modulusBased_le_lintegral_dist`, Zeile 12199 —, und dieser Lauf
  ist trotzdem hineingelaufen und hat einen Übersetzungsdurchlauf dafür bezahlt. Der Eintrag ist
  richtig und vollständig (die primierten Namen gibt es auf `master` nicht, auch nicht als
  veraltete Aliase; die unprimierten tragen die primierte Bedeutung, und das Suffix benennt die
  Seite des **veränderlichen** Arguments). Die Notiz, die dieser Lauf zunächst ein zweites Mal
  hinschrieb, ist wieder entfernt worden. **Was fehlt, ist nicht der Eintrag, sondern daß er
  gefunden wird**; eine Notiz über einen Mathlib-Namen gehört an die Stelle, an der der Name
  gesucht wird, und nicht nur dorthin, wo er das erste Mal weh tat.

#### Die README ist nachgezogen

`MartingaleProblems/README.md`, Meilenstein 11, im Abschnitt über die Schranke: die drei neuen
Namen, die sieben ersetzten Verwendungen in Prosa, der Grund für `Kw` samt den beiden Fällen,
die ihn ohne neues Feld einlösen, die Wahl des laufenden Maximums, und die Zählung dessen, was
von den sechs noch `hVb` trägt.

#### Was von der Kette jetzt noch die Schranke trägt, und es sind vier

| Aussage | Zeile | liest `c` |
| --- | ---: | --- |
| `lintegral_ofReal_dist_le_sqrt_of_isApproximatingPair` | 45676 | **selbst** |
| `measure_setOf_oscHitSeq_lt_le_div_of_isApproximatingPair` | 45582 | durchgereicht |
| `sum_lintegral_ofReal_dist_oscHitSeqGap_le_of_isApproximatingPair` | 45774 | durchgereicht |
| `mul_measure_setOf_lt_modulusBased_le_of_isApproximatingPair` | 45934 | durchgereicht, in der Konklusion |

#### Vorschlag für den nächsten Lauf, als benanntes Ziel

**`lintegral_ofReal_dist_le_sqrt_of_isApproximatingPair_of_integrable_mul`** (Z. 45676 für den
beschränkten Nachbarn) — die **Lückenzelle**, dieselbe Aussage ohne `hVb`, mit dem gewichteten
Fehler `γ` und der Quadratintegrierbarkeit als Hypothese.

*Worauf sie ruht:* `lintegral_ofReal_dist_le_sqrt_of_lintegral_mul_biSup_le` (steht seit dem
siebten Lauf) und `IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le_lintegral_mul`
(ebenso), sowie dieselben `MemLp … 2`-Hypothesen, die heute bei der Horizontzelle getragen haben
— der Beweis ist der Beweis von heute an der anderen Zelle.

*Warum jetzt:* sie ist die **zweite und letzte** der beiden Aussagen, die die Schranke selbst
lesen; danach ist alles, was übrig ist, Durchreichen, und das ist Buchhaltung.

*Die eine Stelle, die vorher zu klären ist, und sie ist nicht dieselbe wie heute:* die Lückenzelle
ist **nicht** konsekutiv. Ihr rechtes Ende ist `min (τ (k+1)) (min (τ k) u + δ)`, und darum geht
die Summation über sie **nicht** über `sum_enorm_compensator_sub_le`, sondern über die
Hölder-Schranke `ofReal δ ^ (1-1/q) * K` je Zelle — das ist der Grund, warum der Meilenstein zwei
Blöcke hat. Zu prüfen ist deshalb, ob die gewichtete Fassung dort
`IsApproximatingPair.enorm_integral_mul_stoppedValue_sub_le` braucht (die Hölder-Gestalt, in der
`c` **vor** dem Produkt steht und die es in gewichteter Fassung noch nicht gibt) oder ob die
Lückenzelle mit der Lintegral-Gestalt auskommt, weil sie einzeln und nicht summiert gelesen wird.
**Diese Frage zu beantworten ist die halbe Arbeit jenes Laufs**, und sie ist am Quelltext von
`sum_lintegral_ofReal_dist_oscHitSeqGap_le_of_isApproximatingPair` zu entscheiden, nicht zu raten.
