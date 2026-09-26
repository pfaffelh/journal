### Derselbe Lauf, zweiter Teil — Aufgabe B, Schritt B3, Rest: **die Markov-Hälfte von `thm:localuniq` auf beliebigem `Ω`**

Die im Lauf 08:03 (fünfter Teil) offen gelassene Hälfte. **Neu** (`MartingaleProblems/Suggested.lean`,
Abschnitt `LocalOnAmbient`):

| Rolle | Lean-Name | Zeile |
| --- | --- | ---: |
| (Hilfssatz) `((g ∘ Φ) • P).map (θ ∘ Φ) = (g • P.map Φ).map θ` | `map_withDensity_comp_eq` | 49426 |
| **`thm:localuniq`, Markov-Hälfte, auf beliebigem `Ω`** | `isMarkov_of_unique_onedim_local_of_le_comap` | 49454 |

Aussage: `Φ : Ω → F` meßbar und adaptiert (`∀ i, Measurable[𝓖 i, 𝓕₀ i] Φ`), `P.map Φ` löst das
lokale Problem, und **`𝓖 r ≤ MeasurableSpace.comap Φ (𝓕₀ r)`**. Unter `eq:localonedim` bei `r`
gilt `P[g (π (r+t) ∘ Φ) | 𝓖 r] =ᵐ P[g (π (r+t) ∘ Φ) | σ(π r ∘ Φ)]`.

Beweis: `isMarkov_of_restart` mit `X := Φ`. Der verlangte Neustart ist `localRestart` **auf dem
Pfadraum**, nicht auf `Ω`: eine `𝓖 r`-meßbare Dichte `Z` faktorisiert als `Z' ∘ Φ` mit `Z'`
`𝓕₀ r`-meßbar (Mathlib `StronglyMeasurable.exists_eq_measurable_comp`,
`MeasureTheory/Function/FactorsThrough.lean:56`), auf dieselben Schranken abgeschnitten, und
`map_withDensity_comp_eq` schiebt die Dichte nach `P.map Φ`. `localRestart` auf `Ω` selbst wird
damit **nicht gebraucht**. `#print axioms` für beide Sätze: `propext`, `Classical.choice`,
`Quot.sound`.

**Befund: die Bedingung an `𝓖 r` ist die, die das Manuskript nicht nennt.** Im Lauf 08:03 war
vermutet, es brauche „`𝓖` = natürliche Filtration von `X`“. Gebraucht wird nur die eine
Inklusion zur Zeit `r`, und nur sie (die andere folgt aus der Adaptiertheit). Wegzulassen ist sie
nicht: `hP` spricht nur über das Gesetz, und für die Filtration, die zu jeder Zeit `m` ist, ist die
linke Seite `g (π (r+t) ∘ Φ)` selbst, im allgemeinen nicht `σ(X r)`-meßbar. Nicht erfaßt ist die
Vergrößerung um eine vom Pfad unabhängige σ-Algebra, die die Markoveigenschaft erhält; dafür wäre
die Unabhängigkeit zu tragen (wie in `Martingale.supConst`), und das ist nicht gebaut.

`check_master.py` danach: 0 Fehler, 0 `sorry`, 0 Veraltungen, Warnungen 18 / 38 / 38 / 76.
**B3 ist damit vollständig** (Eindeutigkeit und Markov-Eigenschaft auf beliebigem `Ω`).
