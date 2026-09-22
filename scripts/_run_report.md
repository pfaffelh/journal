
### 2026-09-22, siebzehnter Lauf des Tages — der Term **zweiter** Ordnung steht, und die angesagte Falle gibt es nicht: die beiden Schranken und `MemLp 2`, die der Vorschlag als Preis einer Identität mit nichtleerer rechter Seite ansetzte, werden **nicht gelesen**, weil Mathlibs Entkopplung eine **Produktformel** ist und keine Nullaussage. Dazu die **Randterme** und das **Restglied** — und damit ist die Zellenrechnung vollständig

*Sechs Deklarationen in `MartingaleProblems`, durch `check_master.py` mit 0 Fehlern und 0 `sorry`,
alle sechs mit `#print axioms` auf `propext`, `Classical.choice`, `Quot.sound` geprüft. Die
Warnungszahlen sind **unverändert** (18 / 38 / 112, davon 0 veraltet). Ein bestehender Satz ist
dabei zu einem Zweizeiler geworden.*

| Zeile | Name |
| ---: | --- |
| 51900 | `MeasureTheory.integral_mul_eq_mul_integral_of_indep_comap` |
| 51913 | `MeasureTheory.integral_mul_eq_zero_of_indep_comap` *(umgeschrieben)* |
| 53524 | `MeasureTheory.abs_sub_natCast_floor_div_le` |
| 53833 | `MeasureTheory.abs_mpTest_sub_rescaledWalk_sub_sum_le` |
| 53902 | `MeasureTheory.abs_sub_taylor_two_le` |
| 54037 | `MeasureTheory.integral_mul_comp_rescaledWalk_sq_mul_eq_smul` |

**Das benannte Ziel des Vorlaufs war `integral_mul_comp_rescaledWalk_sq_mul_eq_smul`.** Es steht,
und zwar mit **weniger** Voraussetzungen als angesagt. Weil es billiger war als veranschlagt,
sind im selben Lauf die beiden **Randterme** und das **Restglied** dazugekommen — die beiden
Posten, die der Vorlauf noch als offen führte.

#### Der Befund: die angesagte Falle gibt es nicht, und der Grund ist eine Formsache

Der Vorschlag hatte geschrieben:

> „`∫ W · ξ k ² = σ² · ∫ W` verlangt, daß `∫ W` selbst existiert […] Anders als heute sind die
> beiden Schranken hier also zu führen und nicht wegzulassen — die rechte Seite ist keine Null,
> und die Müllwerte der beiden Seiten stimmen nicht mehr überein. […] Ebenso ist `MemLp 2` an
> `ξ k` hier zum ersten Mal wirklich zu verlangen."

**Alle drei Voraussetzungen entfallen**, und es ist keine Schlauheit im Beweis, sondern die
Gestalt des Mathlib-Satzes. `ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral`
(`Mathlib/Probability/Independence/Integration.lean:423`) gibt nicht „`∫ W · X = 0`, wenn `X`
zentriert ist", sondern die **Produktformel** `∫ W · X = P[W] · P[X]`, und zwar aus bloßer
`AEStronglyMeasurable`. Ist das Produkt nicht integrierbar, so ist es nach
`IndepFun.integral_bilin'` (`:335`) auch einer der beiden Faktoren nicht, und dann sind **alle
drei** Integrale der Bochner-Müllwert `0`. Damit steht links `0` und rechts `v · 0` — die
Müllwerte stimmen also auch hier überein, und zwar aus demselben Grund wie beim Term erster
Ordnung, nicht aus dem schwächeren, daß beide Seiten Null wären.

Die Überlegung des Vorschlags war richtig für den Weg, den er vorsah — die Zentrierung
`∫ W · (ξ k ² − σ²) = 0`, ein Ausmultiplizieren, und dafür braucht man `∫ W` wirklich. Der Umweg
ist aber gar nicht nötig; die Produktformel liefert die Identität unmittelbar. **Das ist die
Lehre: wer eine Nullaussage als Bauteil hinschreibt, wo Mathlib eine Identität hat, zahlt die
Voraussetzungen, die die Nullaussage braucht.**

Entsprechend umgebaut: `integral_mul_eq_mul_integral_of_indep_comap` ist jetzt das Bauteil, und
`integral_mul_eq_zero_of_indep_comap` — das der Term erster Ordnung seit dem Vorlauf liest — ist
sein Korollar bei `∫ X = 0` und zwei Zeilen lang. Beide Verbraucher stehen damit auf **einer**
Voraussetzungsmenge.

#### Was der neue Satz liest, und was nicht

Von den drei Voraussetzungen des Akzeptanztests trägt er **`hind` allein**. `hcent` kommt nicht
vor — die Zentrierung wird für den Term zweiter Ordnung nicht gebraucht —, und `hsq` ist an einem
**einzigen** Index `k` verlangt statt an allen: die Zellen werden einzeln behandelt, und erst der
Verbraucher, der sie summiert, braucht die Übereinstimmung der Momente.

**Das zweite Moment ist ein nacktes reelles `v` und kein Quadrat.** Positivität wird nirgends
gelesen; ein `σ` in der Signatur hätte jedem Verbraucher ein Vorzeichen aufgebürdet, das die
Aussage nicht benutzt.

Die Unabhängigkeit ist die von `ξ k` und wird durch das Quadrat gezogen,
`comap (ξ k ²) ≤ comap (ξ k)` über `Measurable.comap_le` und
`ProbabilityTheory.indep_of_indep_of_le_left` (`Mathlib/Probability/Independence/Basic.lean:371`).
Das ist der ganze Zusatzaufwand gegenüber dem Term erster Ordnung: **drei Zeilen**, und der
Beweis ging im ersten Anlauf durch.

#### Der Zeuge gegen die falsche Filtration ist hier ein anderer als im Vorlauf

Über `Filtration.natural ξ` bei `k` ist auch diese Aussage falsch, aber der Zeuge des Vorlaufs
trägt **nicht**: mit `h = 1` und `Z = ξ k` steht links `∫ ξ k ³` und rechts `σ² · ∫ ξ k`, und für
einen **symmetrischen** Zuwachs sind beide `0`. Zu nehmen ist `Z = ξ k ²` — links `∫ ξ k ⁴`,
rechts `(∫ ξ k ²)²`, und die Differenz ist die Varianz von `ξ k ²`, die nur für einen Zuwachs mit
f.s. konstantem Quadrat verschwindet. Das steht so im Doc-Kommentar, samt der Warnung vor dem
untauglichen Zeugen.

#### Die beiden Randterme

`mpTest_sub_rescaledWalk_eq_sum` zerlegt die Lücke in die Zellensumme **plus zwei Randterme**.
Die Roadmap sagte von ihnen bisher bloß, sie seien „je höchstens `(n+1)⁻¹ ‖g‖`"; jetzt ist es
bewiesen, in der Gestalt, in der es der Verbraucher liest:

```
|(mpTest f g t − mpTest f g s)(walk n, ω) − ∑ Zellen| ≤ 2 · (n+1)⁻¹ · C   für |g| ≤ C
```

Zwei Deklarationen. `abs_sub_natCast_floor_div_le` ist die ganze Arithmetik — `Nat.floor_le` nach
unten, `Nat.lt_floor_add_one` nach oben — und `0 ≤ t` ist darin **gelesen und nicht
weglaßbar**: bei negativem `t` ist `Nat.floor` gleich `0`, der Rest ist `t` selbst, und die
Schranke bricht für jedes `t < −c⁻¹`. Das ist wieder eine Müllwert-Stelle, und die erste dieser
Arbeit, an der der Müllwert eine Aussage nicht still wahr macht, sondern kippt; sie steht im
Doc-Kommentar.

**Nur `g` wird beschränkt verlangt, `f` gar nichts** — `f` kürzt sich aus den beiden Randtermen
heraus, weil diese allein das Gewicht des Kompensators tragen. Das ist genau umgekehrt zu dem,
was die Zellensumme fragt, wo `f` entwickelt wird und `g` bloß `½ σ² f''` treffen muß.

Die Abschätzung ist **gleichmäßig in `ω`**. Das ist nicht Kosmetik: der Verbraucher zieht sie
damit unter das Integral gegen ein beschränktes Gewicht, ohne ein eigenes
Integrierbarkeitsargument.

Die Umrechnung von `⌊t · ((n : ℝ≥0)+1)⌋₊` auf `⌊(t : ℝ) · ((n : ℝ)+1)⌋₊` ist `norm_cast` allein —
ein `push_cast` davor tut nichts und wird vom Linter gemeldet.

#### Und das Restglied, das der Vorlauf als den teuersten Posten veranschlagt hatte

`abs_sub_taylor_two_le`:

```
|f (x + h) − f x − f' x · h − f'' x · h² / 2| ≤ M · |h|³ / 6   für |f'''| ≤ M
```

**Der Vorlauf hatte drei Zweige angesagt — `h = 0`, `h > 0`, `h < 0` — und „sie sind die
eigentliche Arbeit". Es ist einer.** Der Grund ist eine Fundstelle, die die Vorhersage nicht
kannte: `taylor_mean_remainder_lagrange_iteratedDeriv`
(`Mathlib/Analysis/Calculus/Taylor.lean:348`) steht über `Set.uIcc x₀ x` und nicht über einem
geordneten `Set.Icc`, verlangt also nur `x₀ ≠ x` und **kein Vorzeichen von `h`**. Der
Reflexionsschluß, den die Vorhersage für `h < 0` vorsah, entfällt ersatzlos.

**Und die zweite angesagte Falle gibt es ebenfalls nicht.** Der Vorschlag hatte gewarnt,
`iteratedDerivWithin` und `iteratedDeriv` stimmten am **Endpunkt** nicht überein, weil `Set.Icc`
dort keine Umgebung ist. Das ist wahr für Umgebungsargumente und falsch für den Satz, den man
dafür nimmt: `iteratedDerivWithin_eq_iteratedDeriv`
(`Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:70`) fragt `UniqueDiffOn` der Menge und
`ContDiffAt` der Funktion, **nicht** daß die Menge eine Umgebung sei — und `uniqueDiffOn_uIcc`
gibt das erste, Endpunkt hin oder her. Das ist die Stelle, an der die Vorhersage teuer und die
Rechnung billig war, und der Grund gehört aufgeschrieben: *eine Voraussetzung, die man sich
merkt, ist nicht die, die im Satz steht.*

Genommen ist die **Lagrange-Form** und nicht `taylor_mean_remainder_bound`; letztere gibt die
gröbere Konstante `M |h|³ / 2!` statt `/ 3!` und verlangt ein geordnetes Intervall. Für Donsker
wäre jede Konstante recht gewesen, aber die Lagrange-Form war ohnehin die billigere.

Der einzige eigene Fall ist `h = 0`, wo beide Seiten `0` sind und `simp` schließt. `0 ≤ M` ist
Folgerung und nicht Voraussetzung.

#### Prüfung

`scripts/check_master.py` gegen `upstream/master`
(`94ef6b89544e58e90f119da869f3fb48d1da0f4c`, Lean `4.35.0-rc2`): **0 Fehler, 0 `sorry`** in allen
drei Dateien, Warnungen **18 / 38 / 112, davon 0 veraltet** — unverändert gegenüber dem Vorlauf.
`scripts/check_axioms_master.py` über die sechs Deklarationen: `propext`, `Classical.choice`,
`Quot.sound`. `check_cited_lines.py`: **466 gepaarte Fundstellen, 0 verschoben, 0 tot** (vorher
463). `check_duplicates.py`: keiner der fünf neuen Namen trifft auf `master`.

#### Wo der Akzeptanztest damit steht — jeder Posten der Zellenrechnung ist bewiesen

```
mpTest_sub_rescaledWalk_eq_sum          (die Lücke, zellenweise, ohne Wahrscheinlichkeit)
  ↳ zwei Randterme:      abs_mpTest_sub_rescaledWalk_sub_sum_le        ← steht
  ↳ Erwartungswert der Zellensumme, Summand je Zelle:
      · Term erster Ordnung:  integral_mul_comp_rescaledWalk_mul_eq_zero   ← steht
      · Term zweiter Ordnung: integral_mul_comp_rescaledWalk_sq_mul_eq_smul ← steht
      · Restglied:            abs_sub_taylor_two_le                        ← steht
```

**Was noch fehlt, ist kein Posten mehr, sondern der Zusammenbau**: die vier Aussagen stehen
nebeneinander und nicht hintereinander. Keine von ihnen hat bisher eine andere als Eingabe.

#### Vorschlag für den nächsten Lauf, als benanntes Ziel

**`MeasureTheory.abs_integral_mpTest_sub_rescaledWalk_mul_le`** — der **Zusammenbau einer
Zelle unter dem Erwartungswert**, also der erste Satz, der die vier obigen hintereinanderschaltet.

*Die Aussage, in der Gestalt, in der sie der dritte Punkt der Kette liest:* unter `hind`, `hmeas`,
`hsq : ∀ k, ∫ ξ k ² = σ²`, für `f` mit `ContDiff ℝ 3 f` und `|iteratedDeriv 3 f| ≤ K`,
`g = fun y ↦ σ ^ 2 / 2 * iteratedDeriv 2 f y`, und `Z` beschränkt und meßbar für die skalierte
Vergangenheit bei `k`:

```
|∫ ω, (f (S n (k+1) ω) − f (S n k ω) − (n+1)⁻¹ · g (S n k ω)) · Z ω ∂P|
  ≤ K · ‖Z‖ · (n+1)^(−3/2) · 𝔼[|ξ k|³] / 6 .
```

*Warum sie jetzt dran ist.* Sie ist genau die Zusammenfügung: der Zuwachs wird nach
`abs_sub_taylor_two_le` entwickelt, der Term erster Ordnung fällt nach
`integral_mul_comp_rescaledWalk_mul_eq_zero` weg, der Term zweiter Ordnung trifft nach
`integral_mul_comp_rescaledWalk_sq_mul_eq_smul` den Kompensator **exakt** — das ist die Wahl
`g = ½ σ² f''` —, und stehen bleibt allein das Restglied. Jeder der drei Sätze wird dabei **genau
einmal** gelesen, und das ist die Probe darauf, ob sie in der richtigen Gestalt stehen.

*Worauf sie ruht.* Auf den drei genannten und auf `Integrable`-Argumenten, die hier zum ersten
Mal wirklich zu führen sind: das Restglied wird integriert, und `|ξ k|³` muß dafür integrierbar
sein. **Die Beschränktheit von `Z` wird hier gelesen** — anders als bei den beiden
Zellentermen, wo der Müllwert sie überflüssig machte.

*Die Entscheidung, die dabei ansteht, und sie ist keine Rechnung:* **ein drittes Moment hat
Donsker nicht.** Die Akzeptanzaussage gibt `MemLp 2`, nicht `MemLp 3`. Es gibt zwei Auswege, und
der Lauf hat einen zu wählen und die Wahl zu begründen:

* **Das dritte Moment in die Hypothese** — `hthird : ∀ k, ∫ |ξ k| ³ ∂P ≤ ρ`. Die Aussage ist dann
  schwächer als Donsker, aber der Beweis ist der obige und sonst nichts, und sie deckt jeden
  beschränkten Zuwachs, also insbesondere die Irrfahrt mit `±1`.
* **Lindeberg–Feller**, also das Abschneiden des Zuwachses bei `ε √(n+1)` und die Zerlegung des
  Restglieds in einen Teil mit drittem Moment auf dem kleinen Stück und einen mit zweitem auf dem
  großen. Das ist der Satz, den Donsker wirklich braucht, und es ist ein eigener Lauf.

*Empfehlung:* **den ersten Weg zuerst**, weil er den Zusammenbau prüft, ohne ihn mit der
Abschneidung zu vermengen; die Abschneidung setzt dann am fertigen Zusammenbau an und ersetzt
allein die Schranke am Restglied. Wer beides zugleich anfängt, hat bei einem Fehlschlag zwei
Verdächtige.
