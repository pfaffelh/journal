
### 2026-09-24, fünfter Lauf des Tages — Punkt 2 der Aufgabe ist bis auf **eine** Deklaration eingelöst, und beim Beweisen ist die Wegbeschreibung, die an ihr steht, **widerlegt**: das Maßargument über die schlechten Radien, das sie ansagt, wird nicht gebraucht — die Verschiebung des Fensters ist gegen `exp (-u) du` eine **Substitution**

*6 Deklarationen in `SkorokhodSpace/Suggested.lean`: fünf im Sprungfunktional-Block vor
`continuous_jumpFunctional` (neuer Unterabschnitt „Carrying the jump along a time change"),
eine in Meilenstein 6 vor `exists_dist_lt_of_intDist_lt`.
`scripts/check_master.py` gegen `upstream/master` (`94ef6b89544e58e90f119da869f3fb48d1da0f4c`,
Lean `4.35.0-rc2`): **0 Fehler, 0 veraltete Namen**, `sorry` unverändert **eins** (nämlich das
Ziel `continuous_jumpFunctional` selbst), Warnungen unverändert **18 / 39 / 36 / 76** — also
keine einzige neue. `check_axioms_master.py` über alle sechs: `propext`, `Classical.choice`,
`Quot.sound`, **kein `sorryAx`**. `check_duplicates.py` jetzt 1857 eigene Deklarationen,
43 Treffer, keiner auf einen neuen Namen.*

#### Stand der vier Punkte der Aufgabe vom 2026-09-24

Nachgesehen und nicht geschätzt: Punkt 1 ist im ersten Lauf des Tages erledigt, Punkt 3 im
dritten, Punkt 4 im zweiten. Von Punkt 2 standen `jumpFunctional`,
`jumpFunctional_eq_zero_iff`, `isClosed_setOf_continuous`, `isClosed_range_continuous` und die
Anwendung in `MartingaleProblems` (`jumpBdd`, und die f.s. Stetigkeit der Pfade im Limes,
`:30303`–`:30400`) schon da; offen war **allein** `continuous_jumpFunctional`, und es ist
zugleich das einzige `sorry` der ganzen Kette. Dieser Lauf hat es nicht geschlossen, aber
seine beiden Hälften gebaut und den Rest auf eine Integralrechnung zurückgeführt.

#### Was steht

| Name | Aussage |
| --- | --- |
| `OrderIso.map_nhdsLT` | `Filter.map e (𝓝[<] t) = 𝓝[<] (e t)` für einen Ordnungsisomorphismus |
| `SkorokhodSpace.dist_leftLim_le_of_eventually` | Linkslimiten erben eine Schranke, die auf `𝓝[≤] t` gilt |
| `min_one_le_min_one_add` | `a ≤ b + c`, `0 ≤ c` ⟹ `min 1 a ≤ min 1 b + c` |
| `SkorokhodSpace.jumpSize_le_of_forall_dist_le` | `jumpSize y t ≤ jumpSize x (e t) + 2ε` |
| `SkorokhodSpace.jumpWith_le_of_forall_dist_le` | `jumpWith u y ≤ jumpWith (u+η) x + 2ε` |
| `SkorokhodSpace.exists_orderIso_forall_dist_lt_of_intDist_lt` | die **gefensterte** Näherungsaussage, mit `e` **und** `e.symm` |

#### Der Befund, und er berichtigt den Doc-Kommentar, der seit dem Bau des Blocks an der Aussage stand

Dort stand, der Inhalt sei, „daß eine gleichmäßig kleine Störung `jumpWith` **an fast jedem
Radius** wenig bewegt — die Radien, an denen der Fensterrand einen Sprung von `x` trifft, sind
abzählbar viele, also Lebesgue-Null, und das Integral sieht sie nicht"; das sei „dasselbe
Argument, mit dem `ae_summable_min_one_distWith` die Metrik von Meilenstein 4 trägt".

**Das ist nicht der Weg, und die schlechten Radien kommen im Beweis überhaupt nicht vor.**
Die gebaute Abschätzung ist nicht `|jumpWith u y − jumpWith u x| ≤ …` an einem festen Radius,
sondern die **verschobene**

    jumpWith t₀ u y ≤ jumpWith t₀ (u + η) x + 2ε ,

und `η` ist die Verrückung des Zeitwechsels. Eine Verschiebung des Radius ist gegen das Gewicht
`exp (-u) du` aber **ein Faktor** — Translationsinvarianz des Lebesguemaßes:

    ∫_{u>0} exp (-u) · jumpWith (u+η) x du = exp η · ∫_{u>η} exp (-u) · jumpWith u x du
      ≤ exp η · jumpFunctional x .

Also `jumpFunctional y ≤ exp η · jumpFunctional x + 2ε + exp (−(R−η))`, und weil
`jumpFunctional x ≤ 1` ist (`jumpFunctional_le_one`), ist der erste Summand um höchstens
`exp η − 1` von `jumpFunctional x` entfernt. Kein Nullmengenargument, keine Stetigkeit von
`u ↦ jumpWith u x` an fast jedem Punkt, kein `Monotone.countable_not_continuousAt`. Die
Monotonie in `u` (`monotone_jumpWith`) wird an dieser Stelle **gar nicht** gelesen; sie trägt
weiterhin die Meßbarkeit und `jumpWith_eq_zero_of_jumpFunctional_eq_zero`, und sonst nichts.

**Damit ist gesagt, wofür das exponentielle Gewicht wirklich da ist.** Der Doc-Kommentar des
Blocks sagt, die Gestalt von `jumpFunctional` sei die der Metrik von Meilenstein 4, „und
absichtlich so". Das stimmt, aber der Grund ist ein anderer als der dort genannte: bei der
Metrik bezahlt das Gewicht die *Nichtmonotonie* von `distWith` im Radius (deshalb
`exists_radius_distWith_lt`, deshalb „ein Radius wird erzeugt, nicht gewählt"); beim
Sprungfunktional bezahlt es die *Verschiebung* des Fensters, und das ist eine Substitution und
keine Mittelwertaussage. Beide Male ist es dasselbe Gewicht und nicht dasselbe Argument.

Die Wegbeschreibung an `continuous_jumpFunctional` ist entsprechend neu geschrieben und nennt
jetzt die Konstantenwahl (`η` aus `exp η − 1 < ε/8`, dann `R` aus `exp (−(R−η)) < ε/8`, dann
`δ` aus der gefensterten Näherungsaussage zur Genauigkeit `min (ε/8) η`) samt beiden
Richtungen. Was noch fehlt, ist genau diese Rechnung.

#### Drei Einzelbefunde, damit sie kein Lauf neu erhebt

* **Die Voraussetzung des Linkslimes gehört auf `𝓝[≤] t` und nicht auf `𝓝[<] t`.** An einem von
  links isolierten Punkt ist `𝓝[<] t = ⊥`, jede Aussage darüber ist leer, und
  `Function.leftLim` ist dort der **Wert**. Auf `𝓝[≤] t` deckt eine Hypothese beide Fälle, weil
  dieser Filter `pure t` enthält (`Filter.Eventually.self_of_nhdsWithin`). Der Fallschnitt
  selbst braucht, daß der eine Filter genau dann `⊥` ist, wenn der andere es ist — und das ist
  `OrderIso.map_nhdsLT`.
* **Mathlib hat `OrderIso.map_nhdsLT` nicht.** Vorhanden sind `OrderIso.image_Iio`,
  `OrderIso.toHomeomorph` und `OrderIso.continuous`; eine Aussage über den *Filter* steht
  nirgends (gesucht am Quelltext von `upstream/master`, `Mathlib/Topology/Order/`). Die drei
  Zeilen sind hier ausgeschrieben; die Aussage ist elementar und gehört als Lücke zu
  `TODO.md` Punkt 8.
* **`leftLim_eq_of_eq_bot` steht im Wurzelnamensraum, nicht unter `Function`.** `Function.leftLim`
  ist die *Funktion*; die Lemmata darüber stehen nach einem `open Function` in
  `Mathlib/Topology/Order/LeftRightLim.lean` ohne Präfix. `Function.leftLim_eq_of_eq_bot` ist ein
  unbekannter Bezeichner und hat einen Durchlauf gekostet.

#### Und eine Stelle, an der die stehende Regel der minimalen Voraussetzungen etwas hergab

`exists_orderIso_forall_dist_lt_of_intDist_lt` ist die gefensterte Fassung von
`exists_orderIso_dist_lt_of_intDist_lt`, und sie ist **nicht teurer**: `TimeChange.dist_le_of_norm_le`
ist über dem ganzen Fenster ausgesprochen und `dist_le_distWith` ist ohnehin ein Supremum über
den Index. Die punktweise Fassung ist also nicht aus Not schwächer, sondern weil Meilenstein 6
nur einen Punkt verbraucht. Das steht so am Doc-Kommentar der neuen Aussage; die alte bleibt,
weil `continuous_eval_of_nhdsGT_eq_bot` und `lowerSemicontinuous_iSup_edist` sie in genau dieser
Gestalt lesen.

#### Das benannte Ziel für den nächsten Lauf

> **`SkorokhodSpace.continuous_jumpFunctional`** — die Integralrechnung, die die beiden
> gebauten Hälften zusammensetzt.

*Warum jetzt:* es ist das einzige `sorry` der ganzen Kette, der letzte offene Punkt der Aufgabe
vom 2026-09-24, und beide Eingaben stehen bewiesen da. Nach ihm trägt
`isClosed_range_continuous` — der einzige Punkt von `SkorokhodSpace` Meilenstein 5 ohne
Prototyp — kein `sorry` mehr, und dasselbe gilt für die Anwendung in `MartingaleProblems`
(`jumpBdd` und die f.s. Stetigkeit der Pfade im Limes), die heute darüber läuft.

*Worauf es ruht, und es ist alles gebaut:* `exists_orderIso_forall_dist_lt_of_intDist_lt` für
`e`, `η`, `ε`; `jumpWith_le_of_forall_dist_le` zweimal, einmal mit `e` und einmal mit `e.symm`;
`integrableOn_jumpFunctional` für beide Integrale; `jumpFunctional_le_one` für den Faktor
`exp η`; `SkorokhodSpace.dist_eq` für den Übergang von `Metric.continuous_iff` auf `intDist`.

*Die zwei Stellen, an denen ein Lauf danebengreifen wird.*

1. **Die Substitution.** `∫_{u>0} exp (-u) · W (u+η) du = exp η · ∫_{u>η} exp (-u) · W u du` ist
   in Lean die Translationsinvarianz des Lebesguemaßes (`MeasureTheory.integral_comp_add_right`
   auf `volume.restrict (Set.Ioi 0)`, mit `Measure.restrict` nachgeführt); der Faktor `exp η`
   kommt aus `exp (-(u-η)) = exp η · exp (-u)` und ist **vor** der Substitution aus dem
   Integranden zu ziehen, sonst steht er darunter und `integral_const_mul` findet ihn nicht.
2. **Die Rückrichtung ist nicht die Spiegelung der Hinrichtung.** Aus
   `dist (x (e t)) (y t) < ε` auf `exhaustion t₀ R` wird `dist (y (e.symm s)) (x s) < ε` erst
   nach der Substitution `s = e t`, und die verschiebt das Fenster um die Verrückung von
   `e.symm`. Deshalb trägt die Näherungsaussage die Klausel über `e.symm` eigens, und deshalb
   ist die Rückrichtung auf dem **kleineren** Fenster `exhaustion t₀ (R − η)` zu führen. Wer
   sie auf demselben `R` führt, bekommt eine Hypothese, die er nicht einlösen kann.
