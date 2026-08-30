# Was die Präordnung trägt

Angelegt am 2026-08-30 als Ergebnis der vorrangigen Aufgabe 2. Die Frage ist
dreiteilig und in allen drei Teilen eine **Vorlage an den Nutzer**: dieser Lauf
ändert weder die Uhr noch die Roadmaps noch das Manuskript.

1. Trägt die Präordnung, für die die Uhr ihr Intervall als Differenz von
   Abwärtsmengen definiert, außerhalb von §6 etwas?
2. Wie weit reicht \eqref{T3p}, getrennt nach Prädikat, Sprungtheorie und Raum —
   und was bräuchte die Gegenprobe, ein Stetigkeitssatz?
3. `AdditiveDist` als Typklasse oder \eqref{T3p} als Teilmenge von `ℝ`?

Alles unten ist am Manuskript (`MartingaleProblem.tex`, Zeilennummern), an
Mathlib v4.33.1 (`~/Code/lean/journal/.lake/packages/mathlib/Mathlib`), an
master (`gh api`) oder am Scan von \EK{} belegt. Wo nichts geprüft werden
konnte, steht das da.

---

## Teil 1: die Differenzform des Intervalls

### Zwei Vorbemerkungen, die die Liste halbieren

**(a) \eqref{T2b} enthält \eqref{T2a}.** Definition~`def:bundles` (Zeile 634)
liest: „\eqref{T2a}, $\T$ carries the order topology and admits a countable
dense subset $D$, …". Eine mit \eqref{T2b} annotierte Aussage hat also eine
**lineare** Ordnung, und auf einer linearen Ordnung ist
`Set.Iio t \ Set.Iio s = Set.Ico s t` (das ist `Clock.Ico_eq_setIco` der
Roadmap, `not_lt`). Die Aufgabenstellung nennt \eqref{T2b} in der Ausgangsliste;
für die Frage nach der Differenzform fällt die ganze Gruppe weg. Übrig bleiben
\eqref{T0} und \eqref{T1}.

**(b) Keine Aussage des Manuskripts ist mit \eqref{T1} annotiert.** `\eqref{T1}`
kommt an drei Stellen vor: in der Definition selbst (626), in der Diskussion von
\eqref{T1p} (665–674) und in `rem:chainonly` (4149, wo \eqref{T1} als *nicht
ausreichend* auftritt). §2 sagt es selbst (1856): \eqref{T1p} „does not occur at
all". Die Liste ist damit: die \eqref{T0}-Aussagen, mit oder ohne \eqref{T4}.

**(c) Bei $s = 0$ fallen beide Formen ohnehin zusammen.** Ist $0$ kleinstes
Element, so ist `Set.Ico 0 t = {x | 0 ≤ x ∧ x < t} = Set.Iio t` und
`Clock.Ico q 0 t = Set.Iio t \ Set.Iio 0 = Set.Iio t`, weil `Set.Iio 0 = ∅`;
ebenso für die optionale Konvention, wo `Set.Ioc 0 t` und
`Set.Iic t \ Set.Iic 0` beide `{x | ¬(x ≤ 0) ∧ x ≤ t}` sind. **Der Kompensator
selbst — `def:markovMP`, `eq:XXA`, Zeile 2428 — benutzt nur $\langle 0,t
\rangle_\iota$ und ist deshalb von der Wahl unabhängig.** Die Frage entscheidet
sich allein an den Stellen, an denen ein Intervall $\langle s,t \rangle_\iota$
mit $s \neq 0$ vorkommt, und dort an der Additivität `eq:clockadd`.

Die Stellen mit allgemeinem $s$ sind vollständig: 2517 und 2554
(`prop:fddchar`), 2680–2746 (`lem:closure`, `cor:bpclosure`), 3791
(`ex:shiftXA`), 4310–4317 und 5249 (§6, beide \eqref{T2b}), 5336–5353
(`lem:chain`), 5651 (`prop:atomicdual`), 6314–6317 (`lem:dualsemigroup`), 6433
(`thm:exduality`, \eqref{T2a}), 7951–8004 (`thm:clockchange`, \eqref{T3}).

### Die Tabelle

Eine Zeile je \eqref{T0}-Aussage. Spalten: kommt die Uhr vor; kommt ein
Intervall mit $s \neq 0$ vor; **bräche der Beweis unter `Set.Ico`**; ist die
Aussage auf einem wirklich nicht linearen Index instanziiert.

| Aussage | § | Uhr | $s \neq 0$ | bräche unter `Set.Ico` | nichtlinear instanziiert |
|---|---|---|---|---|---|
| `set:abstract`, `def:absMP`, `def:canonical` (2290–2330) | 4 | nein | — | — | — |
| `def:markovMP`, `eq:XXA` (2419) | 4 | ja | nein | **nein** (Vorbem. c) | `ex:clocks`(iv), $\T=\Rp^d$ (762) |
| `lem:compadapted` (2470) | 4 | ja | nein | **nein** (Vorbem. c) | dieselbe |
| `prop:fddchar`, `eq:fdd` (2505) | 4 | ja | **ja** (2517) | **ja** — der Beweis zieht `eq:clockadd` bei 2550 heran, um $Y_t-Y_s$ als ein Integral über $\langle s,t\rangle_\iota$ zu schreiben | **ja**, `rem:fddnochain` (2534) rechnet auf $\T=\Rp^2$ |
| `lem:closure` (2671) | 4 | ja | **ja** (2680) | **ja** — 2703 nennt `eq:clockadd` beim Namen | mittelbar, über `prop:fddchar` |
| `cor:bpclosure` (2725) | 4 | ja | **ja** (2740) | **ja**, wie `lem:closure` | dieselbe |
| `def:wellposed` (2778) | 4 | ja | nein | nein | — |
| `lem:mixture` (3320), `lem:disint` (3342), `lem:liftmarkov` (3454), `def:propagation` (3613) | 6 | nein | — | — | — |
| `ex:shiftXA` (3770) | 6 | ja | **ja** (3791) | **ja** — die Substitution $v = r+u$ bildet $\langle 0,t\rangle_\iota$ auf $\langle r,r+t\rangle_\iota$ ab, und dass die Bildmenge dieses Intervall *ist*, ist die Differenzform | $\Rp^d$ erfüllt \eqref{T4} und ist mit Lebesgue verschiebungsinvariant |
| `lem:restart` (3804), `lem:propagation` (3986), `thm:absuniq`\ref{it:absuniq_a} (4025) | 6 | nur über `ex:shiftXA` | nein | **nein** — die drei Aussagen sind rein abstrakt über Verschiebungssysteme; die Uhr-Spalte der §2-Tabelle bezieht sich auf die Instanz `ex:shiftXA`, nicht auf sie | $\Rp^d$, über `ex:shiftXA` |
| `lem:chain` (5328) | 7 | ja | **ja** (5336) | **nein** im Beweis — das Teleskop benutzt nur `eq:incrementrep`; **ja** in der Hypothese, denn `eq:incrementrep` wird vom Kompensator geliefert und dessen Zuwachs *ist* $\T_{<s'} \setminus \T_{<s}$ | nicht instanziiert; `rem:staircase` (5373) betont ausdrücklich die Präordnung |
| `prop:atomicdual` (5629) | 7 | ja | **ja** (5651) | **nein** — der Beweis läuft entlang einer Kette $u_0 \leq \dots \leq u_M$ von Atomen, und dort enthalten beide Formen dieselben Atome; die Differenzform steht nur in der Rechnung, die zeigt, dass $[u_i,u_{i+1})$ genau ein Atom trägt | nicht instanziiert |
| `lem:dualsemigroup` (6302), `prop:dualCK` (6337) | 8 | ja | **ja** (6314) | **ja** — Schritt 1 des Beweises ist wörtlich „By clock additivity \eqref{eq:clockadd}" | $\Rp^d$ mit Lebesgue ist \eqref{T4} und verschiebungsinvariant; 6507 nennt den Kernlayer als das, was ohne lineare Ordnung auskommt |
| `thm:absconv` (7622), `thm:absconvaug` (8218) | 8 | nein | — | — | 1847 zählt sie zu den Überlebenden |
| `fact:kolmogorov` (1547) | 2 | nein | — | — | — |

### Was daraus folgt

**Die Differenzform trägt, und zwar an vier Stellen.** `prop:fddchar` (mit
`lem:closure` und `cor:bpclosure` im Schlepptau), `ex:shiftXA` und
`lem:dualsemigroup` benutzen die Additivität bei allgemeinem $s$, und die
Additivität ist unter `Set.Ico` auf einer echten Halbordnung falsch. Das
Gegenbeispiel ist nicht der Diamant, sondern der Index, den das Manuskript
tatsächlich nennt: auf $\T = \Rp^2$ ist
`Set.Ico (0,0) (2,2) = [0,2)²`, aber
`Set.Ico (0,0) (1,1) ∪ Set.Ico (1,1) (2,2) = [0,1)² ∪ [1,2)²`, und der Streifen
$[0,1) \times [1,2)$ fehlt. Die Differenzform hat dieses Problem nicht, weil
$\T_{<s} \subset \T_{<t} \subset \T_{<u}$ die Zerlegung erzwingt.

**Und sie ist instanziiert, nicht nur zugelassen.** $\T = \Rp^d$ steht als
`ex:clocks`(iv) (762) mit dem Namen „the multiparameter martingale problem";
`rem:fddnochain` (2526–2538) *rechnet* auf $\Rp^2$ und benutzt die
Unvergleichbarkeit von $(1,0)$ und $(0,1)$, um zu zeigen, dass die Kettenform
von `eq:fdd` zu schwach ist; 749–751 begründet mit $\Rp^d$, warum die Uhr ein
Maß und keine additive Intervallfunktion sein muss; und 1847 fasst zusammen,
dass der halbgeordnete Fall „in Section~MP, in the Markov half of
Section~uniqueness, in the abstract convergence theorem and in the *kernel
layer*" überlebt. Das ist keine bloße Allgemeinheitsgeste.

**Die Präordnung trägt also weit außerhalb von §6:** in §4 (das ganze
Martingalproblem und seine Charakterisierung durch die endlichdimensionalen
Verteilungen), in §7 (`lem:chain`, `prop:atomicdual`) und in §8 (der Kernlayer
der Existenz über Dualität). §6 ist nicht die einzige und nicht einmal die
stärkste Fundstelle — die stärkste ist `prop:fddchar`, denn dort ist die
Halbordnung nicht nur zugelassen, sondern zwingt zu einer *anderen* Formulierung
der Hypothese (`rem:fddnochain`).

### Die Empfehlung

**Die Differenzform als Primitiv behalten.**

*Was das kostet.* Zwei Intervallfamilien statt einer, also `Clock.Ioc` und
`Clock.Ico` neben `Set.Ioc` und `Set.Ico`, mit den Brücken
`Clock.Ico_eq_setIco` und `Clock.Ioc_eq_setIoc` unter `[LinearOrder ι]`. Die
Roadmap `MartingaleProblems` Meilenstein 1 hat beide Brücken bereits als `@[simp]`
und schreibt die Uhrform *in* Mathlibs Form um; jeder konkrete Index landet
damit automatisch in Mathlibs Intervall-API. Der Preis ist eine Handvoll
Lemmata, keine Parallelbibliothek. Dazu kommt, dass Namen wie `Clock.Ico`
irreführend sein können — die Roadmap notiert das im Docstring und stellt die
Inklusion `Set.Ico s t ⊆ Clock.Ico q s t` als eigenes Lemma bereit, damit kein
Beweis eines für das andere hält.

*Was sie einspart.* Sie ist die Voraussetzung dafür, dass \eqref{T0} in §4, §7
und §8 überhaupt eine Aussage ist. Unter `[LinearOrder ι]` verlöre nicht nur §6
seine Halbordnungszeile, sondern es verlören:

* §4 die ganze Zeile — `prop:fddchar` ist die zentrale Aussage des Abschnitts
  und ist mit \eqref{T0} annotiert;
* §7 `lem:chain` und `prop:atomicdual`, und mit `prop:atomicdual` das
  einzige Ergebnis von Task 23, das dieses Jahr bewiesen wurde;
* §8 den Kernlayer `lem:dualsemigroup`/`prop:dualCK`, den 6507 ausdrücklich als
  die Schicht ohne lineare Ordnung benennt.

*Die Gegenrechnung.* Die Uhr auf `[LinearOrder ι]` festzulegen und direkt
`Set.Ico` zu nehmen spart genau die beiden Definitionen und die beiden
Brückenlemmata und macht `Set.Ico_union_Ico_eq_Ico` unmittelbar verfügbar. Sie
kostet vier der oben genannten Aussagen ihre Allgemeinheit und macht
`rem:fddnochain` gegenstandslos — eine Bemerkung, die das Manuskript als
Korrektur einer früheren Fassung führt. Das Verhältnis ist ungünstig.

---

## Teil 2: wie weit reicht \eqref{T3p}

\eqref{T3p} (1889–1896) ist: \eqref{T2a}, eine Metrik $\varrho$, die die
Ordnungstopologie induziert, längs der Ordnung additiv ist
($\varrho(s,u) = \varrho(s,t) + \varrho(t,u)$ für $s \leq t \leq u$) und
kompakte abgeschlossene Kugeln hat. `thm:T3sharp`(a) (2189) sagt: das ist
äquivalent zu „abgeschlossene Teilmenge von $\R$". Die Additivität längs der
Ordnung ist die **Menger-Zwischenrelation** — das Ordnungsintervall stimmt mit
dem metrischen Intervall $[a,b] = \{x : d(a,x)+d(x,b) = d(a,b)\}$ überein
(K. Menger, *Untersuchungen über allgemeine Metrik*, Math. Ann. 100 (1928),
75–163). Nicht Menger-*Konvexität*: die verlangt zu $a \neq b$ ein echtes
Zwischenglied und wird von $h\Z$ verletzt, das \eqref{T3p} erfüllt.

Drei Dinge sind zu trennen, und sie haben drei verschiedene schwächste
Indexhypothesen.

### (1) Das Prädikat càdlàg: `[Preorder ι] [TopologicalSpace ι]`

Belegt an der Quelle. `RemyDegenne/brownian-motion`,
`BrownianMotion/StochasticIntegral/Cadlag.lean` (Apache-2.0), deklariert
`variable {ι E : Type*} [TopologicalSpace ι]` und darunter

```
abbrev IsRightContinuous [TopologicalSpace E] [Preorder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

structure IsCadlag [TopologicalSpace E] [Preorder ι] (f : ι → E) : Prop where
  right_continuous : IsRightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)
```

Mehr braucht das Prädikat nicht, und die dort mitgelieferten Abschlusslemmata
(`Continuous.isCadlag`, `IsRightContinuous.continuous_comp`, `.mul`, `.div`)
kommen ebenfalls mit `[Preorder ι] [TopologicalSpace ι]` aus.

**Verlangt `SkorokhodSpace` Meilenstein 2 mehr, als das Prädikat braucht?** Der
Kopf des Meilensteins sagt „For `f : ι → E` with `[Preorder ι]
[TopologicalSpace ι] [TopologicalSpace E]`" — richtig. Aber Meilenstein 1 endet
mit dem Satz „Throughout the rest of this roadmap, `ι` denotes an index with
these instances", also mit vollem \eqref{T3p}, und **vier der Punkte von
Meilenstein 2 brauchen tatsächlich mehr**, ohne dass der Meilenstein sagt,
wieviel:

* `largeLeftJumpSet f ε` hat keinen Häufungspunkt, `leftJumpSet f` ist
  abzählbar — der Punkt sagt selbst „proved by the exhaustion";
* `IsCadlag.measurable` — „via approximation by the right continuous step
  functions of the exhaustion";
* „determined by a dense set";
* `IsCadlag.isBounded_image_of_isCompact`.

Das ist ein Befund an der Roadmap, nicht am Manuskript. **Auch das Manuskript
sagt es an einer Stelle falsch:** `rem:skorokhodform` (2236–2240) schreibt,
`brownian-motion` definiere `IsCadlag` auf `[TopologicalSpace ι] [Preorder ι]`,
„which is \eqref{T2b}". Das ist es nicht — \eqref{T2b} verlangt lineare Ordnung,
Ordnungstopologie, eine abzählbare dichte Teilmenge und Rechtsapproximierbarkeit
jedes nicht maximalen Punktes. `[Preorder ι] [TopologicalSpace ι]` ist echt
schwächer. Gehört unter „Offene Auffälligkeiten" des Inventars.

### (2) Die Sprungtheorie: Linearität und Zweitabzählbarkeit, nicht die Metrik

Was jeder der vier Punkte über (1) hinaus braucht, einzeln:

* **Lokale Endlichkeit von `largeLeftJumpSet f ε`.** Der Beweis widerlegt einen
  Häufungspunkt, indem er aus ihm eine monotone Folge zieht, die gegen ihn
  konvergiert, und den einseitigen Limes gegen die Sprunghöhe ausspielt. Die
  Monotonie der Folge braucht **Linearität**; die Ordnungstopologie braucht sie
  ebenfalls, damit „von links" und „von rechts" die einzigen Annäherungsweisen
  sind. Auf einer Halbordnung ist beides falsch, und `rem:skorokhodwalls`
  (2218) sagt genau das: càdlàg-Pfade brauchen, dass $\{s : s \leq t\}$ eine
  Kette ist.
* **Abzählbarkeit von `leftJumpSet f`.** Aus der lokalen Endlichkeit wird
  Abzählbarkeit durch eine abzählbare Ausschöpfung, also durch
  **σ-Kompaktheit** oder, gleichwertig genug, **Zweitabzählbarkeit** des Index.
  Die Metrik wird nicht gebraucht, die Ausschöpfung schon.
  Mathlibs `Monotone.countable_not_continuousAt`
  (`Mathlib/Topology/Order/LeftRightLim.lean`) ist der monotone Spezialfall und
  ist, wie der Meilenstein richtig sagt, kein Ersatz.
* **`IsCadlag.measurable`.** Approximation durch rechtsstetige Treppenfunktionen
  längs einer abzählbaren dichten Menge: **Linearität** (damit Treppen
  definierbar sind) und eine **abzählbare dichte Teilmenge**. Das ist genau
  \eqref{T2b}, nicht mehr.
* **Bestimmtheit durch eine dichte Menge.** Zwei càdlàg-Funktionen, die auf
  dichtem $D$ übereinstimmen, sind gleich: das ist Rechtsstetigkeit plus die
  Forderung von \eqref{T2b}, dass jeder nicht maximale Punkt von rechts
  erreichbar ist. **\eqref{T2b}, wörtlich.**
* **`isBounded_image_of_isCompact`.** Hier ist die Metrik auf **$E$**, nicht auf
  $\iota$; der Index braucht Kompaktheit des Urbildbereichs und sonst nichts
  über (1) hinaus.

**Fazit für (2): \eqref{T2b} genügt der ganzen Sprungtheorie.** Die Metrik auf
dem Index kommt nirgends vor. Auch `largeLeftJumpSet` misst mit `dist` auf $E$.

### (3) Der Raum $D(\T,E)$ mit $J_1$: \eqref{T3p}, und es geht nicht weniger

Hier greift `thm:T3sharp`(b) (2193–2210): ohne Additivität längs der Ordnung
kann `lem:tccontrol` fallen, und dann ist $d$ von `def:dcirc` keine Metrik — es
gibt $\T$ und $f \neq g$ mit $d(f,g) = 0$. Das Gegenbeispiel ist ein
gewurzelter Baum mit der Baummetrik, deren Additivität längs der Ordnung
ausdrücklich nachgerechnet wird; was fehlt, ist die Linearität, und eine
wurzelfixierende Isometrie, die zwei isomorphe Äste vertauscht, hat
$\gamma(\lambda)=0$ bei Verschiebung in der Größenordnung des Durchmessers.
`rem:additivityused` (2028) sagt zusätzlich, dass die Additivität **genau
einmal** benutzt wird, in `lem:tccontrol`, und alles danach nur deren Schluss.
Das ist die schärfste denkbare Buchhaltung, und sie lässt keinen Spielraum: der
Raum braucht \eqref{T3p}.

### Die Gegenprobe: stetige Pfade

**Mathlibs Ausgangslage, am Quelltext geprüft.**
`Mathlib/Probability/Process/Kolmogorov.lean` deklariert
`variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
[PseudoEMetricSpace E]` und darauf

```
structure IsKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop where
  measurablePair : ∀ s t : T, Measurable[_, borel (E × E)] fun ω ↦ (X s ω, X t ω)
  kolmogorovCondition : ∀ s t : T, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q
  p_pos : 0 < p
  q_pos : 0 < q
```

**Der Index trägt keine Ordnung.** Kein `Preorder`, kein `LinearOrder`, keine
Teilmenge von $\R$ — nur ein Pseudo-EMetrikraum. Und die Bedingung ist ein
**Momentenkriterium**: eine Schranke an $\int\lVert X_s - X_t\rVert^p$ durch
$\mathrm{d}(s,t)^q$, punktweise in $(s,t)$, ohne Filtration, ohne bedingte
Erwartung, ohne Stoppzeit. Das ist der Grund, warum der Index so allgemein sein
darf: der Mechanismus vergleicht zwei Zeitpunkte metrisch und nie einen
Zeitpunkt mit seiner Vergangenheit. Die càdlàg-Modifikation von `thm:absreg`
und `fact:submgreg` läuft dagegen über die Doobsche Upcrossing-Ungleichung, also
über eine Filtration und die Ordnung des Index — dort ist die lineare Ordnung
konstitutiv, hier nicht.

**Was Mathlib nicht hat.** `Probability/Process/Kolmogorov.lean` enthält nur die
*Bedingung* und deren API (`IsAEKolmogorovProcess`, `mk`, `ae_eq_mk`,
`mk_of_secondCountableTopology`, `measurable_edist`, `edist_eq_zero` …). Der
**Satz von Kolmogorov--Chentsov steht nicht darin**: die einzige Erwähnung von
„Chentsov" ist der Modulkommentar Zeile 21, „This condition is the main
assumption of the Kolmogorov-Chentsov theorem". Auf master ist es dasselbe —
`gh api search/code` für „Chentsov repo:leanprover-community/mathlib4" liefert
genau zwei Dateien, `Probability/Process/Kolmogorov.lean` und
`Topology/EMetricSpace/PairReduction.lean` (letztere die Hilfsaussage
`pair_reduction` nach Krätschmer--Urusov). **Das ist eine Korrektur an der
Roadmap `MartingaleProblems`**, die in der Liste „Mathlib supplies" schreibt:
„`Mathlib/Probability/Process/Kolmogorov.lean`: the Kolmogorov–Chentsov
continuous modification". Vorhanden ist die Hypothesenklasse, nicht der Satz.

**Wo der Satz liegt.** `RemyDegenne/brownian-motion`, Verzeichnis
`BrownianMotion/Continuity/`, mit den Dateien `CoveringNumber.lean`,
`HasBoundedInternalCoveringNumber.lean`, `IsKolmogorovProcess.lean`,
`KolmogorovChentsov.lean`, `KolmogorovChentsovInequality.lean`, `Chaining.lean`
und `LimitModification.lean`. `KolmogorovChentsov.lean` arbeitet unter
`[PseudoEMetricSpace T] [PseudoEMetricSpace E]` und führt zusätzlich die
Hypothese `HasBoundedCoveringNumber U c d` mit; die Kette
`holderOnWith_of_mem_holderSet` → `holderModification` →
`exists_modification_holder''` ist die Kettenkonstruktion. Die
Überdeckungszahlschranke ist die eine Hypothese, die über den Pseudo-EMetrikraum
hinausgeht, und sie ersetzt genau das, was auf $\Rp$ die Dimension leistet.

**Was das Manuskript dazu hat: nichts.** `\CE` kommt zehnmal vor (Zeilen 50 und
518 als Notation, 2342 in `def:canonical`, 2784–2786 in `def:wellposed`,
5264–5274 in `thm:uniqueness` und ihrer lokalen Fassung) — und zwar **nicht** in
§3, dem Skorokhod-Abschnitt, sondern durchweg als Alternative zu $\DE$ in §4
und §6, also als Pfadraum, in dem eine Lösung leben *darf*. Ein Stetigkeitssatz
im Sinne von `thm:absreg` — Hypothesen an eine Klasse von Testfunktionen, Schluss
auf eine Modifikation mit stetigen Pfaden — existiert im Manuskript nicht. Der
Suchbegriff „Kolmogorov--Chentsov" kommt gar nicht vor.

**Was ein solcher Satz bräuchte, wo er stünde und wohin er gehört.**

*Hypothesen.* (i) Index: ein Pseudo-EMetrikraum mit beschränkter innerer
Überdeckungszahl — **keine Ordnung**, also weder \eqref{T0} noch \eqref{T2a}
noch \eqref{T3p}. Das ist die einzige Stelle des ganzen Manuskripts, an der die
Graduation von `def:bundles` nicht greift, weil sie mit \eqref{T0} beginnt und
\eqref{T0} eine Ordnung ist. (ii) Zustand: ein vollständiger metrischer Raum,
also \eqref{E3} ohne Separabilität, oder \eqref{E2} plus Vollständigkeit; die
`brownian-motion`-Kette verlangt `[CompleteSpace E] [Nonempty E]`. (iii) Uhr:
keine. (iv) Die Momentenschranke selbst.

*Ort.* Nach §3 gehört er nicht, denn er hat mit $J_1$ nichts zu tun; nach §5
(„Sample path regularity: existence of a càdlàg modification") gehört er als
zweiter Abschnitt, als Gegenstück zu `thm:absreg` — und die richtige Überschrift
wäre, dass §5 zwei Regularisierungssätze mit *unvergleichbaren* Voraussetzungen
enthält: einen martingaltheoretischen, der eine lineare Ordnung braucht und
Sprünge zulässt, und einen momententheoretischen, der keine Ordnung braucht und
Sprünge ausschließt.

*Roadmap.* Er gehört **nicht** in `MartingaleProblems`. Die dortige Vorgabe ist
`[Preorder ι]` mit `Filtration`, und der Satz braucht weder das eine noch das
andere; ihn dorthin zu setzen hieße, eine Filtration als Hypothese zu führen,
die im Beweis nicht vorkommt, und das verstößt gegen die stehende Regel der
minimalen Voraussetzungen. Er gehört auch nicht in `SkorokhodSpace`, dessen
Meilenstein 1 den Index auf \eqref{T3p} festlegt. Der richtige Ort ist ein
eigener, fünfter Roadmap-Gegenstand — oder, näherliegend, eine direkte
Mathlib-Einreichung neben `Probability/Process/Kolmogorov.lean`, wo die
Hypothesenklasse schon liegt und der Satz fehlt. `brownian-motion` hat den
Beweis unter Apache-2.0; die Arbeit ist Zuschnitt und Einreichung, nicht
Neubeweis.

Solange das Manuskript keinen solchen Satz führt, ist das ein Vorschlag und kein
Befund: die Formalisierung des Manuskripts geht auch ohne ihn auf.

---

## Teil 3: Typklasse oder Teilmenge

`thm:T3sharp`(a) sagt, \eqref{T3p} sei dasselbe wie „abgeschlossene Teilmenge von
$\R$". Damit ist `AdditiveDist` mathematisch verzichtbar. Die Frage ist eine
nach Lean-Kosten, und das Experiment des Nutzers,
`~/Code/lean/journal/scratch/AdditiveDistTest.lean`, hat sie zum Teil schon
beantwortet. Es deklariert die Klasse, die Instanzen für `ℝ` und `ℤ` (je vier
Zeilen, wie `rem:skorokhodform` sagt) und die Subtyp-Instanz

```
instance instSubtype {α : Type*} [LinearOrder α] [PseudoMetricSpace α] [AdditiveDist α]
    (s : Set α) : AdditiveDist s where
  dist_add {a b c} hab hbc := AdditiveDist.dist_add (α := α) hab hbc
```

und prüft danach die vier gewünschten Zeitmengen durch. Zwei Lücken sind
gemessen und im Experiment als „LUECKE 1" und „LUECKE 2" markiert:

1. **Die Subtyp-Instanz greift nicht durch die `SetLike`-Hülle.**
   `AdditiveDist (AddSubgroup.zmultiples h)` löst nicht auf,
   `AdditiveDist ((AddSubgroup.zmultiples h : Set ℝ))` schon.
2. **`OrderTopology` fehlt dem Gitter als Teiltyp.** $h\Z$ ist nicht
   ordnungszusammenhängend, also greift `orderTopology_of_ordConnected` nicht,
   und `OrderTopology.of_discreteTopology` verlangt `PredOrder` und `SuccOrder`,
   die der Teiltyp nicht trägt. Als eigener Typ hat `ℤ` alle fünf Instanzen.
   `ProperSpace` dagegen kommt für das Gitter durch
   `AddSubgroup.isClosed_of_discrete` und `ProperSpace.of_isClosed` durch.

### Weg A: `AdditiveDist` als Typklasse behalten

*Kosten.* Eine neue Klasse (vier Zeilen), zwei Basisinstanzen (je vier Zeilen),
die Subtyp-Instanz (definitional), und die beiden gemessenen Lücken: eine
`SetLike`-Instanz und `PredOrder`/`SuccOrder` (oder `OrderTopology` direkt) für
einen diskreten `AdditiveDist`-Teiltyp. `SkorokhodSpace` Meilenstein 1 führt
beide bereits als eigene Punkte. Dazu kommt der Einbettungssatz
`AdditiveDist.orderIso_isometry_real`, den man unter Weg B nicht bräuchte.

*Ersparnis.* Jeder Index bleibt ein **Typ**, und `ℝ`, `ℤ`, `ℕ` und `NNReal`
sind Instanzen ohne Umweg. Kein `↥`-Kalkül, keine Koerzionslemmata, keine
`Subtype.val`-Schicht in jedem Beweis; die vier Fälle `ℝ`, `[0,∞)`, `[0,T]`,
$h\Z$ und jede abgeschlossene Teilmenge sind Instanzen *einer* Entwicklung. Das
ist das Argument, das `rem:T3primeis` (1917–1922) macht und das das Experiment
für drei der vier Fälle bestätigt.

### Weg B: \eqref{T3p} als abgeschlossene Teilmenge von $\R$

*Kosten.* Der Index wird zu `(T : Set ℝ) (hT : IsClosed T)` und gearbeitet wird
in `↥T`. Damit ist **jeder** Index ein Teiltyp, und die beiden gemessenen Lücken
treten nicht mehr in einem Sonderfall auf, sondern immer: `OrderTopology (↥T)`
ist für nicht ordnungszusammenhängendes `T` — also für jedes Gitter, jede
Sprungmenge, jeden abgeschlossenen Wertebereich eines Subordinators — nicht
automatisch, und `orderTopology_of_ordConnected` hilft dort nie. Dazu verliert
man `ℝ` und `ℤ` als bare Typen: sie müssten als `↥(Set.univ)` bzw. über eine
Koerzionsschicht auftreten, oder jede Aussage wird doppelt geführt. Der
Einbettungssatz entfällt, das ist der einzige echte Gewinn.

*Ersparnis.* Keine neue Klasse, kein Einbettungssatz, und man hat die reelle
Struktur unmittelbar zur Hand, wo ein Beweis sie braucht.

### Empfehlung

**Weg A.** Die beiden gemessenen Lücken sind unter Weg A zwei einmalige
Instanzbeweise; unter Weg B sind sie die Grundsituation. Genau das ist die
Begründung, die `rem:skorokhodform` schon gibt (2278: „That gap is the concrete
reason to state \eqref{T3p} as a typeclass rather than to define $\T$ as a
subset of $\R$"), und das Experiment stützt sie, statt sie nur zu illustrieren:
`ProperSpace` kommt für $h\Z$ durch, `OrderTopology` nicht, und der Unterschied
liegt daran, dass für `ProperSpace` eine Instanz über die Abgeschlossenheit
existiert und für `OrderTopology` keine über die Diskretheit eines Teiltyps.
Diese Asymmetrie verschwindet unter Weg B nicht, sie wird allgemein.

**Was hier nicht geprüft wurde.** Ob für eine *abgeschlossene* Teilmenge von $\R$
die Teilraumtopologie stets die Ordnungstopologie ist — mathematisch die
Voraussetzung dafür, dass Weg B überhaupt geht — ist nicht nachgeschlagen
worden, und ob Mathlib ein solches Lemma führt, ebensowenig. Solange das offen
ist, hat Weg B eine unbezifferte Zusatzposition.

---

## Was dieser Lauf nicht geprüft hat

* Ob `Set.Ico` in den §6-Aussagen (\eqref{T2b}) irgendwo *bequemer* wäre als die
  Uhrform. Die Frage stellt sich nicht für die Allgemeinheit, wohl aber für die
  Lesbarkeit; die `@[simp]`-Brücken der Roadmap sollten sie erledigen, aber das
  ist nicht am Lean-Code getestet, weil es den Code noch nicht gibt.
* Der Zusammenhang zwischen der Menger-Zwischenrelation und dem, was Mathlib
  unter `Wbtw` und `Sbtw` (Zwischenrelation in affinen Räumen) führt. Der Name
  legt eine Verbindung nahe; ob eine der beiden die andere impliziert, ist nicht
  nachgesehen.
* Ob es in `RemyDegenne/brownian-motion` außerhalb von `Continuity/` und
  `StochasticIntegral/Cadlag.lean` weiteres gibt, das \eqref{T3p} betrifft.
