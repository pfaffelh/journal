### 2026-09-26, Lauf 13:03 UTC — Aufgabe A, Schritt A5, Rest: **Doobs zwei Ungleichungen, an der Brownschen Bewegung gerechnet**; „cutting down to an open subset“ begründet offen

`check_master.py` zu Beginn (Mathlib `94ef6b89544`): 0 Fehler, 0 `sorry`, 0 Veraltungen;
Warnungen 18 / 38 / 38 / 76.

**Neu** (`MartingaleProblems/Suggested.lean`, Abschnitt `ContinuousTimeMartingales`, hinter
`integral_stoppedValue_hittingAfter_one_of_isBrownianReal`):

| README (Meilenstein 8, Akzeptanz) | Lean-Name | Zeile |
| --- | --- | ---: |
| (Hilfssatz) `∫⁻ ‖X T‖ₑ ^ 2 = T` für prä-Brownsche Bewegung | `lintegral_enorm_sq_eq_of_isPreBrownianReal` | 51341 |
| **Doobs `L²`-Ungleichung, gerechnet:** `∫⁻ (⨆ t ≤ T, ‖X t‖ₑ) ^ 2 ≤ 4 T` | `lintegral_biSup_enorm_sq_le_of_isBrownianReal` | 51367 |
| (Hilfssatz) `E|X T| ≤ √T` | `integral_norm_le_sqrt_of_isPreBrownianReal` | 51387 |
| **Doobs Maximalungleichung, gerechnet, Konstante `1`:** `ε · Q {ε ≤ ⨆ t ≤ T, ‖X t‖ₑ} ≤ √T` | `measure_biSup_enorm_le_of_isBrownianReal` | 51414 |

Beide sind die vorhandenen Sätze `Martingale.lintegral_biSup_enorm_rpow_le` (bei `r = 2`, Konstante
`(r/(r-1))^r = 4`) und `Martingale.measure_iSup_norm_le`, angewandt auf
`martingale_of_isPreBrownianReal` mit einer abzählbaren dichten Teilmenge von `ℝ≥0`
(`TopologicalSpace.exists_countable_dense`). Die rechte Seite ist die Varianz von
`gaussianReal 0 T` (`IsPreBrownianReal.hasLaw_eval`, `variance_id_gaussianReal`), in die untere
Integralform gebracht über `ofReal_integral_eq_lintegral_ofReal`; `E|X T| ≤ √T` aus
`Var |X T| ≥ 0` (`variance_eq_sub`). Der genaue Wert `E|X T| = √(2T/π)` ist nicht bewiesen und für
das Beispiel nicht nötig. Voraussetzung ist Stetigkeit **jedes** Pfades, weil die allgemeinen Sätze
die Rechtsstetigkeit an jedem Stichprobenpunkt lesen (wie bei den Treffzeitbeispielen daneben).
`#print axioms` für beide Akzeptanzsätze: `propext`, `Classical.choice`, `Quot.sound`.

**„Cutting down to an open subset“: nicht gebaut, mit Grund.** Das Akzeptanzbeispiel der README
(`E = ℝ`, `U = (-1, 1)`, Beulenfolge) prüft `IsMPSolutionFor.ae_forall_mem_of_tendsto`
(Ethier–Kurtz 4.3.9), und das ruht auf `IsMPSolutionFor.integral_comp_stoppedLim_eq`
(Ethier–Kurtz 4.3.8). **Beide Sätze stehen nicht in der Datei** (gesucht nach beiden Namen und
nach `stoppedLim`); das Beispiel ist also kein Abnahmetest für Vorhandenes, sondern verlangt zwei
neue Sätze. Die Stelle, an der der Bau Arbeit macht: die Stoppzeiten
`τ m = sInf {t | infEdist (X t) Uᶜ < 1/m}` sind Eintrittszeiten einer **offenen** Menge durch
einen càdlàg-Prozeß und damit für die **rohe** Filtration im allgemeinen keine Stoppzeiten (nur
für `𝓕_{t+}`); die Eintrittszeit der abgeschlossenen Menge `{infEdist ≤ 1/m}` ist es auch nicht,
weil der Pfad sie über einen linken Limes erreichen kann, ohne sie zu treffen. Der kürzere Weg
über `IsMPSolutionFor.submartingale_mpProcess_of_tendsto` (C2) gibt nur `X t ∈ U` f.s. für jedes
feste `t`, nicht für alle `t` zugleich und nicht für die linken Limiten. Das gehört in den Bericht,
nicht in diesen Lauf: die in Aufgabe A5 **benannten** Akzeptanzbeispiele (Submartingal ohne
càdlàg-Modifikation, optional sampling braucht die Beschränktheit, die Münze am Atom) stehen alle.

`check_master.py` danach: 0 Fehler, 0 `sorry`, 0 Veraltungen, Warnungen 18 / 38 / 38 / 76.

**Aufgabe A ist damit erledigt**, bis auf „cutting down to an open subset“, das zwei nicht
vorhandene Sätze (EK 4.3.8, 4.3.9) verlangt.
