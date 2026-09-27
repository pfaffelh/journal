# Befundliste am Manuskript (Stand 2026-09-27, nachts)

Gesammelt aus `Facts/INVENTAR.md` (Branch `facts-inventory`, Stand `a7faaaf`), in
fünf zeitlichen Ausschnitten, je Befund gegen das heutige Manuskript geprüft.
Zeilen „INV“ zählen im jeweiligen Ausschnitt, Zeilen „MS“ im Manuskript vom
2026-09-27 00:30 (nach der Streichung von `lem:localmix`(a)).

**Zusammengeführt, noch nicht entschieden.** Nächster Schritt: Entscheidung
durch den Nutzer, Punkt für Punkt, dann Korrektur am Manuskript.

## Stand der Sitzung

- Die stündlichen Läufe sind **angehalten**: `~/bin/facts_gate.sh`,
  `NOT_BEFORE='2099-01-01 00:00'` (seit 2026-09-27 00:37).
- **Nicht committet** im Arbeitsbaum von `master`:
  - `MartingaleProblem.tex`: `lem:localmix`(a) mit Beweisteil und
    `rem:convexfree` gestrichen, Satz „only genuinely new proofs“ angepaßt
    (Gegenbeispiel `LocalMixWitness.not_convex`); PDF neu gebaut.
  - `Talks/20260926Arbeitsweise/Ratchet.tex`/`.pdf`: englische Fassung.
  - diese Datei.
- Zusätzlich von Hand gefunden: `thm:duality`, Satzbruch nach `eq:dual1`
  („…they are automatic.“ gefolgt von „and“ vor `eq:dual2`).



## Zusammenführung: die offenen Befunde, nach Schwere

Aus 72 Einträgen der fünf Ausschnitte (28 erledigt, 41 offen, 3 unklar), Doppelte
zusammengelegt. „✓ selbst geprüft“ heißt: in der Sitzung am heutigen Text
nachgerechnet. Alles andere ist der Befund der Läufe, von einem Agenten gegen
den heutigen Text gelesen, aber nicht nachgerechnet.

### A. Aussagen, die falsch sind

1. **`def:dcirc` ist keine $J_1$-Metrik** (✓ selbst geprüft). Abschneiden
   $\tau_m(t)=t\wedge m$ und Reihe über ganzzahlige $m$: für
   $f=1_{[1,\infty)}$, $g=1_{[1+\varepsilon,\infty)}$ ist $d(f,g)\ge\frac12$ für
   jedes $\varepsilon$. Betroffen `rem:dcirccases` (die Gleichsetzung mit EK §3.5),
   und `thm:DEmetric`, `thm:DEpolish` stehen auf dieser Metrik; laut Lauf fällt
   auch die Vollständigkeit. Lean: `dist_exhaustionMax_le_distOn`,
   `exists_jump_continuousAt_eval`. (Ausschnitt 1)
2. **`thm:DEcompact`, „nur wenn“** (✓ selbst geprüft): `def:modulus` nagelt die
   Unterteilung bei $\max B_m$ fest; $f_n=1_{[m-1/n,\infty)}$ ist relativkompakt
   mit $w'_m=1$. EK (3.6.2) erlauben $t_n\ge T$. Lean:
   `not_tendsto_iSup_modulusPinned`. (Ausschnitt 1)
3. **`thm:DEpolish` unter (T3′)**: Die Cantormenge ist zulässiger Index, $D$ dort
   nicht separabel (Lean `not_separableSpace_of_rigid`, die Starrheit nur in
   Prosa). Dazu „(T2b), which (T3′) implies“: falsch, Gegenbeispiel $h\mathbb Z$.
   (Ausschnitt 1)
4. **Explodierende Sprungprozesse sind keine lokalen Lösungen** im Sinn von
   `def:absMP`/`def:localizing`: $\tau_n\uparrow\zeta$, nicht $\uparrow\infty$.
   Lean: `not_isLocalMPSolution_explode`; die Ersatzdefinition
   `IsLocalMPSolutionUpTo`. Stellen: Einleitung (MS 360), `rem:jumpexplosion`,
   `rem:jumppoint`, `thm:pathjumpMP`. (Ausschnitt 5)
5. **Sprungzeiten sind keine Pfadfunktionale**, wenn $\mu(x,\{x\})>0$ oder die
   Diagonale nicht meßbar ist: `def:jumpconstruction`, `thm:jumpMP` Schritt 4,
   `rem:jumpexplosion`, `rem:jumppoint`, `thm:pathjumpMP`(a). Lean:
   `not_isStoppingTime_min_jumpTimeE`,
   `not_isStoppingTime_hawkesJumpTime_pathFiltration`. (Ausschnitt 2)
6. **(L1) verlangt eine gemeinsame Folge**, `lem:L1auto` liefert eine je
   Testprozeß: `def:localizing`(L1), `rem:localhyp`, `lem:L1auto`. Umstellen auf
   „je Testprozeß eine Folge in $\Sigma$“; `lem:localmix`, `lem:localrestart`,
   `thm:localuniq` bleiben dann richtig (Lean: `IsLocalizationForEach`,
   `LocalizingSystemEach`). (Ausschnitt 5)
7. **`ex:hawkes`, „never explodes“**: aus „$m$ löst die Erneuerungsgleichung“
   folgt in $[0,\infty]$ keine Endlichkeit, die Resolventenlösung ist nur die
   kleinste (`renewal_le_of_eq`, `renewal_ae_eq_of_eq`). (Ausschnitt 4)

### B. Fehlende Voraussetzungen und Lücken im Beweis

8. `lem:restart`: $\tilde\kappa\in L^1(P)$ benutzt, nicht vorausgesetzt. (3)
9. `thm:localuniqueness`: die Integrabilitätsbedingung von `lem:pasting` fehlt. (5)
10. `lem:pasting`: „adapted, so a function of $a_T$“ braucht Progressivität;
    ebenso die Kernmeßbarkeit in `cor:pastingmarkov`. (5)
11. `cor:pastingmarkov`: $a_T\gamma(\alpha,\beta)=a_T\alpha$ nur bei
    $\beta_0=\alpha_{T(\alpha)}$, also nur fast sicher. (5)
12. `eq:countabletest`: die Integrierbarkeit gehört in die Testbedingung. (5)
13. `lem:disint`: $\pi_0$ $\mathcal F^\circ_0$-meßbar stillschweigend benutzt. (5)
14. `cor:atomless`: `lem:calculus` auf $[0,L]^2$ angewandt, auf $[0,\infty)^2$
    ausgesprochen; der Beweis endet am Endpunkt; „$Q$-almost every“ statt $q$;
    nach Ausschnitt 1 gilt die Identität sogar überall. (1, 5)
15. `thm:jumpMP`, Schluß: Progressivität unter (E0) falsch begründet
    („right continuous X“ ohne Topologie); die Aussage stimmt über $h(X)$. (2)
16. Absatz vor `thm:pathjumpMP`: Überlebensfunktion $e^{-A_n(u)}$ nur für
    $u\ge\tau_n$. (2)
17. „Relatively compact“ nirgends definiert; `fact:fddconv`(b) nur unter
    Separabilität, Straffheit und Relativkompaktheit fallen erst polnisch
    zusammen. (1)
18. `prop:hawkesduality`(D2): „Laplace-Funktionale bestimmen einen
    Punktprozeß“ steht in keinem Fact. (1)
19. `rem:ccverify`: schließt bei $D_{E^\Delta}$, der Rückweg nach $D_E$ fehlt
    (EK 4.3.8 mit 4.3.9/4.3.10). (1)
20. `def:separating` nur für $C_b(S)$ erklärt, auf $\mathrm{Bdd}(E)$ angewandt
    (MS 7575, 8750). (1)
21. `thm:absstrongmarkov`, Kernform: die Integrierbarkeit aus `lem:mixture`
    für $\int P_x\mu(dx)$ nicht ausdrücklich genannt — **unklar**, Lesart. (5)

### C. Überflüssige Voraussetzungen, Präzisierungen

22. `lem:propagation`, `thm:absuniq`(b): „$\mathcal Z^\circ$ determining“ wird
    nicht gebraucht. (3)
23. `def:restartkernel`: (E1) nicht gebraucht, erst in `cor:pastingmarkov`. (5)
24. `lem:localrestart`: „By (L1)“ → „by the definition of a local martingale“. (5)
25. `fact:sepcond` ist im Manuskript bewiesen, also kein Fact;
    `rem:sepcondproof` Schritte 2–3 entbehrlich. (1)
26. `rem:absuniqgain`(ii): „For $\XX_A$ it never fails“ → „under (T2a)“. (1, 3)
27. `rem:modulusborel`: der meßbare Ausweg über den Rechtslimes im Radius
    (Lean `measurable_iInf_modulusBased`) fehlt. (4)
28. `rem:dualnonmarkov`: $\Lambda_{s,t,y}$ nicht definiert, duale Zeit $T$ mit
    $Q(T)=Q(t)-Q(s)$. (4)
29. `rem:absreggain`(ii): Grenze der Atomtoleranz (EK 4.3.12 scheitert bei
    $q=\delta_u$). (1)
30. `fact:pseudopath`: Injektivität gilt auf $M_E$; „that compact space“
    mehrdeutig. (1)
31. `def:cc`: allenfalls Halbsatz zur Meßbarkeit. (3)
32. `eq:pathgen`: $\omega(t-)$ gegen $X_t$, Nullmenge; allenfalls Halbsatz. (2)

### D. Buchhaltung

33. Tabelle „Where the prerequisites are used“: Zeile portmanteau falsch (nur
    `fact:cmt`), `fact:fdd` fehlt, bei `fact:PSpolish` fehlt `thm:MZconv`. (1)
34. Nicht tragend: `fact:portmanteau`, Produkthälfte von `fact:fdd`;
    `fact:bp`/`cor:bpclosure` sind nicht „optional“, sondern unbenutzt. (1)
35. Bündeltabelle: Zeilen für `thm:absconvws`, `thm:MZconv`,
    `rem:EKrelcompact` fehlen. (1)

### E. Kleinkram

36. `thm:duality`: Satzbruch nach `eq:dual1` („…are automatic.“ dann „and“). (✓)

---

# Rohlisten der fünf Ausschnitte

---

## Ausschnitt 1

# Befunde am Manuskript aus INV_slice1.md

Zeilen: „Inv. Z." = Zeile in `INV_slice1.md`, „MS Z." = Zeile in `MS_current.tex` (heutiger Stand).
Einträge mit (*) sind Befunde, die der Lauf nur an der Lean-Roadmap festgestellt hat. Er hat nicht gesagt, dass sie das Manuskript treffen. Ich habe die Übertragung aufs Manuskript selbst am heutigen Text geprüft: Die Definition oder Aussage im Manuskript ist dieselbe wie die widerlegte Lean-Fassung.

---

## A. Skorokhod-Raum (§3)

### def:dcirc / rem:dcirccases / thm:DEpolish — die Reihenmetrik ist keine $J_1$-Metrik (*)
- Lauf: 2026-09-08, achtzehnter Lauf (Inv. Z. 11073–11245)
- Befund: Die Summe über ganzzahlige Radien $d=\sum_m 2^{-m}\min(1,d_m)$ mit einseitiger Clampung liest den Abstand am Fensterrand $\max B_m$ ungedämpft ab, für jeden Zeitwechsel. Konvergenz in $d$ erzwingt deshalb punktweise Konvergenz an allen Fensterrändern. $J_1$ tut das nicht. Beispiel: $\mathbf 1_{[1,\infty)}$ und $\mathbf 1_{[1+\varepsilon,\infty)}$ haben Abstand $\ge 1/2$ für jedes $\varepsilon$. Die Vollständigkeit fällt ebenfalls: Auf $\R$ ist $x_n=\mathbf 1_{(-\infty,1+1/(n+1))}$ eine Cauchy-Folge ohne Grenzwert. \EK{} integrieren über einen reellen Radius $u$, gerade damit die abzählbar vielen schlechten Radien nicht zählen.
- Lean-Beleg: `SkorokhodSpace.dist_exhaustionMax_le_distOn`, `continuous_eval_exhaustionMax`, `exists_jump_continuousAt_eval`. Die Cauchy-Folge ist von Hand gerechnet. Reparatur: `metricSpaceInt` / `intDist` (Inv. Z. 11409ff., 11536ff.).
- Heute: OFFEN. MS Z. 2085–2097: `def:dcirc` definiert genau diese Reihe. MS Z. 2104 (`rem:dcirccases`): „the metric of \EK, Section 3.5, with the integral over the truncation level replaced by a series“, und das ist falsch. `thm:DEmetric`/`thm:DEpolish` (Z. 2114, 2126) stehen auf dieser Metrik.
- Vorschlag: $d$ als $\int_0^\infty e^{-u}\,(1\wedge d_u)\,\mathrm du$ über reelle Radien definieren, wie \EK{} §3.5 und `intDist`. Den Satz in `rem:dcirccases` streichen. Die Vollständigkeitsskizze von `thm:DEpolish` neu begründen.

### thm:DEcompact / def:modulus — gepinnte Unterteilung macht das Kriterium falsch (*)
- Lauf: 2026-09-09, sechster Lauf (Inv. Z. 12921–12960)
- Befund: Die Unterteilung muss am kleinsten Punkt des Fensters beginnen und am größten enden. Dann ist die „nur wenn“-Richtung falsch: Sprünge, die von innen gegen einen Fensterrand laufen, halten $w'_m\ge1$ für jedes $\delta$, obwohl die Menge kompakt ist. Beispiel in $D(\R,\R)$: `stepAt (1/(n+2)-1) 1 0` konvergiert gegen `stepAt (-1) 1 0`. \EK{} (3.6.2), S. 122, lassen den letzten Knoten über $T$ hinausragen, $t_{n-1}<T\le t_n$.
- Lean-Beleg: `SkorokhodSpace.not_tendsto_iSup_modulusPinned`, `modulus_le_modulusPinned`
- Heute: OFFEN. MS Z. 2196–2213: `def:modulus` verlangt „$\min B_m = t_0<\dots<t_n=\max B_m$“, und `thm:DEcompact` steht darauf. Auf $[0,\infty)$ bleibt der rechte Rand $m$ betroffen.
- Vorschlag: $t_0\le\min B_m$ und $\max B_m\le t_n$ zulassen, wie \EK. Auf $\Rp$ genügt es, rechts über $\max B_m$ hinauszuragen.

### thm:DEpolish — unter (T3′) nicht separabel (Cantormenge) (*)
- Lauf: 2026-09-09, erster Lauf (Inv. Z. 12195–12296)
- Befund: (T3′) lässt jede abgeschlossene Teilmenge von $\R$ zu, also auch die Cantormenge. Dort ist jeder Zeitwechsel mit Norm $<\log 3$ die Identität. Damit ist die überabzählbare Familie der Einheitsstufen paarweise gleichmäßig getrennt, und $D(\T,\R)$ ist nicht separabel. Die Beweisskizze („step paths with jump times in a countable dense $D$“) trägt dort nicht. Der Lauf hat die Aussage unter die Zusatzklasse `HasCountableCore ι` gestellt. $\R$ erfüllt sie mit $C=\Q$ (Inv. Z. 12352ff.).
- Lean-Beleg: `SkorokhodSpace.not_separableSpace_of_rigid`. Die Starrheit der Cantormenge ist Prosa, kein Lean. Ersatz: `HasCountableCore`, `instSeparableSpace`.
- Heute: OFFEN. MS Z. 2124–2135: „Assume (T3′) … Then $(\DT,d)$ is Polish“. `rem:T3primeis` (Z. ~1955) zählt ausdrücklich jede abgeschlossene Teilmenge als Modell.
- Vorschlag: Die Hypothese um die Verschiebbarkeit der Sprungzeiten ergänzen (`HasCountableCore`) oder den Satz auf $\R,\Rp,[0,T],h\Z$ beschränken. Das Cantor-Beispiel als Bemerkung aufnehmen.

### Absatz nach thm:DEpolish — „(T2b), which (T3′) implies“ stimmt nicht
- Lauf: 2026-09-06, fünfter Lauf (Inv. Z. 220–232, 5511–5513). Auch 2026-08-30, fünfter Lauf (Inv. Z. 1410–1421): (T2b) und (T3′) sind unvergleichbar.
- Befund: (T2b) verlangt $D\cap(t,u)\ne\emptyset$ für alle nicht maximalen $t<u$. $h\Z$ erfüllt (T3′) und verletzt das an jedem Punkt. An der Stelle selbst ist das folgenlos, weil nur die Separabilität gebraucht wird.
- Lean-Beleg: keiner (Zeuge `AddSubgroup.zmultiples h`)
- Heute: OFFEN. MS Z. 2131–2132: „available by \eqref{T2b}, which \eqref{T3p} implies“.
- Vorschlag: „available because a closed subset of $\R$ is separable“. Andere Stellen, die (T2b) aus (T3′) ziehen, gegenlesen.

### thm:fdd — $D$ muss das größte Element (und rechtsisolierte Punkte) enthalten
- Lauf: 2026-09-06, fünfter Lauf (Inv. Z. 178–218, 5487–5513)
- Befund: Bloße Dichtheit von $D$ reicht nicht. Gegenbeispiele: $[0,1]$ mit $D=[0,1)\cap\Q$ und $[0,1]\cup\{2\}$.
- Lean-Beleg: `IsCadlag.eq_of_eqOn_dense`, `SkorokhodSpace.measurableEmbedding_piDense`, `exists_countable_rightDense`
- Heute: ERLEDIGT. MS Z. 2144–2150 verlangt „containing every maximal element … and every right-isolated point that is not isolated“, und `rem:fdddense` (Z. 2170ff.) bringt beide Beispiele. Commit 1bc5106, 2026-09-14.
- Vorschlag: —

### rem:skorokhodform — `[Preorder ι] [TopologicalSpace ι]` als „(T2b)“ bezeichnet
- Lauf: 2026-08-30, vierter Lauf (Inv. Z. 523–529, 1260–1262)
- Befund: Die Hypothesen von `IsCadlag` bei RemyDegenne sind echt schwächer als (T2b).
- Lean-Beleg: keiner
- Heute: ERLEDIGT. MS Z. ~2302–2305: „that is (T0) together with a topology, which is strictly weaker than (T2b)“. Commit ba3f8f0, 2026-08-31.
- Vorschlag: —

---

## B. Voraussetzungen (§2), Buchhaltung

### fact:convdet — Separabilität für die erste Hälfte unnötig
- Lauf: 2026-09-07, fünfzehnter Lauf (Inv. Z. 157–176, 7738–7748)
- Befund: Der Beweis braucht keine abzählbare dichte Menge. Das ist eine Verallgemeinerung, keine Korrektur.
- Lean-Beleg: `isConvergenceDetermining_setOf_uniformContinuous_isBounded_support`
- Heute: ERLEDIGT. Der Nachsatz in MS Z. 1455–1465 („Separability is not needed for the first half …“). Commit ce2516e, 2026-09-07.
- Vorschlag: —

### def:separating — nur für $M\subset\Cb(S)$ definiert, aber für $\Bdd(E)$-Familien benutzt
- Lauf: 2026-09-06, dritter Lauf (Inv. Z. 5185–5197)
- Befund: `cor:uniqviadual`(i) und `prop:jumpwellposed` nennen Teilmengen von $\Bdd(E)$ „separating“. Die Definition deckt das nicht ab.
- Lean-Beleg: `IsSeparating (Γ : Set (E → ℝ))`. Das ist schon die allgemeine Fassung.
- Heute: OFFEN. MS Z. 1437: „$M \subset \Cb(S)$ is separating if …“. Die Gebrauchsstellen stehen unverändert in Z. 7575 („$\subset\Bdd(E)$ is separating for $\Prob(E)$“) und Z. 8750 („since $\Bdd(E)$ is separating“).
- Vorschlag: Die Definition auf beschränkte messbare $M\subset\Bdd(S)$ erweitern, mit „convergence determining“ weiter nur für $\Cb$.

### fact:sepcond — ein Fact, den das Manuskript selbst beweist
- Lauf: 2026-08-30 (Inv. Z. 481–486, 885–887)
- Befund: Es wird nichts zitiert, der Beweis steht in `rem:sepcondproof`. Offen ist, ob die `fact`-Umgebung die richtige ist, da sie die Voraussetzungsfläche verfälscht.
- Lean-Beleg: `IsSeparating.ae_eq_of_forall_condExp_eq`
- Heute: OFFEN. MS Z. 1620–1626: weiterhin `\begin{fact}`.
- Vorschlag: In eine `lemma`/`proposition` umwandeln, mit Beweis statt `rem:sepcondproof`.

### rem:sepcondproof — Schritte 2 und 3 sind unnötig
- Lauf: 2026-08-30 (Inv. Z. 487–496, 889–906)
- Befund: Aus Schritt 1 mit $G=\{V\in B\}$ und seinem Komplement folgt $P(U\in B,V\notin B)=P(U\notin B,V\in B)=0$, und eine abzählbare trennende Familie gibt $P\{U=V\}=1$. Reguläre bedingte Verteilung und Messbarkeit der Diagonale entfallen. Das ist eine Kürzung, keine Korrektur.
- Lean-Beleg: `Filter.EventuallyEq.of_forall_separating_preimage` (Mathlib), `IsSeparating.ae_eq_of_forall_condExp_eq`
- Heute: OFFEN. MS Z. 1654–1672: Schritte 2 und 3 mit regulärer bedingter Verteilung stehen unverändert.
- Vorschlag: Schritte 2 und 3 durch das Zwei-Zeilen-Argument ersetzen. Dann wird aus (E1) nur „countably separated“ gebraucht.

### Tabelle „Where the prerequisites are used“ — Zeile portmanteau falsch
- Lauf: 2026-08-31, erster Lauf (Inv. Z. 598–606, 1475–1488)
- Befund: `lem:EKconv` und `thm:CPSconv` prüfen nur (C1)–(C3) von `thm:absconv`, und dieser benutzt nur `fact:cmt`, `fact:ui` und `fact:Dcountable`. Portmanteau kommt in keinem der drei Beweise vor.
- Lean-Beleg: keiner
- Heute: OFFEN. MS Z. 1700–1701: „Fact portmanteau, cmt & Lemma EKconv, Theorem CPSconv“.
- Vorschlag: Die Zeile auf `fact:cmt` beschränken.

### Tabelle „Where the prerequisites are used“ — `fact:fdd` fehlt
- Lauf: 2026-08-31, erster Lauf (Inv. Z. 606–608, 1540–1548)
- Befund: Die Tabelle führt nur `thm:fdd`, nicht den Fact. Dessen zweite Hälfte trägt mittelbar an `thm:absuniq`, `cor:DEuniqueness` und `ex:determining`.
- Lean-Beleg: keiner
- Heute: OFFEN. MS Z. 1680–1732: keine Zeile `Fact~\ref{fact:fdd}`.
- Vorschlag: Eine Zeile ergänzen, getrennt nach Produkthälfte (kein Abnehmer, nur §9) und Hälfte „fdd bestimmen das Gesetz“.

### Tabelle „Where the prerequisites are used“ — `fact:PSpolish` nennt nur den ersten Abnehmer
- Lauf: 2026-09-08, neunter Lauf (Inv. Z. 9432–9445)
- Befund: `fact:PSpolish` (Skorokhod-Darstellung) wird auch in Schritt 1 von `thm:MZconv` verbraucht, nicht nur in `rem:EKrelcompact`.
- Lean-Beleg: keiner
- Heute: OFFEN. MS Z. 1702–1703: „Fact PSpolish, prohorov & Remark EKrelcompact“.
- Vorschlag: `Theorem~\ref{thm:MZconv}` ergänzen. Nach dem neuen `rem:MZcost` genügt dort die polnische Fassung über $M_E$.

### fact:portmanteau und die Produkthälfte von fact:fdd — kein Beweis benutzt sie
- Lauf: 2026-08-29 bis 2026-08-31 (Inv. Z. 392–415, 1515–1548, 1649–1687)
- Befund: `fact:portmanteau` wird von keinem Beweis getragen. Höchstens (a)⇒(b) bei metrischer Lesart von „relativ kompakt“, (c)–(f) nie. Die Produkthälfte \eqref{eq:prodsep} von `fact:fdd` hat keinen Abnehmer. Die Wege von fdd zum Gesetz laufen über Monotone-Klasse bzw. Dynkin, und \EK{} Cor. 3.9.2, die einzige Stelle, an der sie arbeiten würde, zitiert das Manuskript nicht. Nur §9 verlangt sie.
- Lean-Beleg: keiner
- Heute: OFFEN. Beide stehen unverändert (MS Z. 1365, 1479–1492).
- Vorschlag: Nutzerentscheidung: entweder als „nicht tragend, nur für §9“ kennzeichnen oder `fact:portmanteau` auf (a)⇒(b) kürzen.

### fact:bp / cor:bpclosure — unbenutzt, nicht bloß „optional“
- Lauf: 2026-08-30, vierter Lauf (Inv. Z. 469–480, 1148–1221)
- Befund: Kein Beweis benutzt `cor:bpclosure` oder `fact:bp`. Getragen wird `lem:closure`, und \EK{} Prop. 4.3.1 trägt im Manuskript nichts. §8 und `rem:bpunused` sagen nur „optional“.
- Lean-Beleg: bp-Block gestrichen, ersetzt durch `IsMPSolutionFor.insert_of_tendsto_of_forall_norm_le`, `submartingale_mpProcess_of_tendsto`
- Heute: OFFEN. MS Z. 1430–1432 („see Remark bpscope for why even that is optional“) und Z. 10654 („cor:bpclosure, which is itself optional“).
- Vorschlag: In §8 und `rem:bpunused` „unused by any proof“ schreiben, oder `cor:bpclosure`/`fact:bp` in eine Bemerkung verschieben.

### „relativ kompakt“ — nirgends definiert, und in fact:fddconv(b) nur unter Separabilität
- Lauf: 2026-08-29 (Inv. Z. 812–817) und 2026-08-31 (Inv. Z. 609–627, 1490–1513)
- Befund: „Relatively compact“ steht in `fact:fddconv`(b), `fact:relcompact`, `fact:relcompact2`, `fact:prohorov` und `rem:EKrelcompact` ohne Definition (schwache Topologie oder Prohorov-Metrik?). Gleichheit mit „straff“ gilt über Prohorov nur für polnisches $E$, `fact:fddconv` verlangt aber nur separabel.
- Lean-Beleg: `isCompact_closure_of_isTightMeasureSet` (Mathlib), `SkorokhodSpace.tendsto_of_isCompact_closure_of_tendsto_finiteDimensional`
- Heute: OFFEN. Keine Definition gefunden (grep „relatively compact“: Z. 1405, 1508, 1526ff., 9150). `fact:prohorov` (Z. 1404) benutzt das Wort ebenfalls undefiniert.
- Vorschlag: Einen Satz in §2 ergänzen: „relatively compact in the topology of weak convergence“. Bei `fact:fddconv` vermerken, dass „tight“ dort erst unter Vollständigkeit äquivalent ist.

### Bündeltabelle — drei Aussagen von §7 fehlen
- Lauf: 2026-08-31, erster Lauf (Inv. Z. 703–712, 1596–1600)
- Befund: `thm:absconvws`, `thm:MZconv` und `rem:EKrelcompact` haben keine Zeile. Bei `thm:MZconv` ist der Pfadraum nicht polnisch, eine Abweichung von (E3), die die Tabelle markieren soll.
- Lean-Beleg: keiner
- Heute: OFFEN. MS Z. 1875–1885: die Tabelle endet mit `lem:EKconv`/`thm:CPSconv` und hat keine Zeile für die drei.
- Vorschlag: Drei Zeilen ergänzen. Für `thm:MZconv`: $\T=\Rp$, Pfadraum separabel metrisch (nicht polnisch), Lebesgue.

### prop:hawkesduality(D2) — zitiert eine Aussage ohne `\begin{fact}`
- Lauf: 2026-09-06, dritter Lauf (Inv. Z. 5198–5206, 5133–5151)
- Befund: Dass ein Punktprozess durch sein Laplace-Funktional bestimmt ist, wird benutzt und nicht bewiesen. Die Aussage steht in keinem Fact und fehlt damit in der Voraussetzungsfläche. Mathlib hat sie nicht.
- Lean-Beleg: keiner
- Heute: OFFEN. MS Z. 8430–8432: „Laplace functionals determining the law of a point process“, ohne Fact. Z. 8236 nennt sie „available“.
- Vorschlag: Einen Fact „Laplace functionals determine point processes“ mit Zitat anlegen und in die Tabellen aufnehmen.

---

## C. Martingalproblem, Regularität, Eindeutigkeit (§4–§6)

### ex:shiftXA — braucht (T2a); rem:absuniqgain(ii), thm:absuniq
- Lauf: 2026-09-14, zweiter Lauf (Inv. Z. 114–155)
- Befund: Die Substitution $v=r+u$ braucht $r+\langle0,t\rangle_\iota=\langle r,r+t\rangle_\iota$, und das ist Totalität. Zeuge ist `ex:clocks`(iv) auf $\Rp^2$: $\kappa=r_1t_2+t_1r_2$ hängt von $t$ ab. Damit gilt „For $\XX_A$ it never fails“ nur unter (T2a).
- Lean-Beleg: keiner (Roadmap: `Clock.interval_add`)
- Heute: ERLEDIGT. Die Überschrift von MS Z. 3854 trägt „+ (T2a)“, `rem:shiftXAtotal` (Z. 3890–3923) bringt Zeugen und Einschränkung von `rem:absuniqgain`(ii). Commit 1bc5106, 2026-09-14. Rest: Der Wortlaut in `rem:absuniqgain`(ii), MS Z. 4592 („For $\XX_A$ it never fails: whatever the clock …“), ist unverändert; die Einschränkung steht nur in `rem:shiftXAtotal`.
- Vorschlag: In Z. 4592 „(under (T2a); see Remark~\ref{rem:shiftXAtotal})“ einfügen.

### rem:ccverify — endet bei $D_{E^\Delta}$
- Lauf: 2026-08-30, fünfter Lauf (Inv. Z. 591–597, 1386–1391)
- Befund: Die Bemerkung liefert, was \EK{} Cor. 4.3.7 hergibt: Pfade in $D_{E^\Delta}$. Der Rückweg nach $D_E$ (\EK{} Thm. 4.3.8 mit Prop. 4.3.9/4.3.10) fehlt, die Bemerkung schließt also weniger, als der Leser erwartet.
- Lean-Beleg: keiner (Roadmap M9: `integral_comp_stoppedLim_eq`, `ae_forall_mem_of_tendsto`, `ae_forall_mem_iInter_of_tendsto`)
- Heute: OFFEN. MS Z. 3338–3347: schließt mit „paths in $D_{E^\Delta}[0,\infty)$; see \EK, Corollary 4.3.7“.
- Vorschlag: Einen Satz ergänzen: „returning to $D_E$ is \EK, Theorem 4.3.8 with Propositions 4.3.9/4.3.10“.

### rem:absreggain(ii) — „Atoms are harmless“ endet an der Quasi-Linksstetigkeit
- Lauf: 2026-08-30, fünfter Lauf (Inv. Z. 569–590, 1326–1350, 1433–1437)
- Befund: Die Aussage selbst ist richtig und kein Fehler. Aber \EK{} Thm. 4.3.12 ist bei einer Uhr mit Atomen falsch: $q=\delta_u$ mit fairem Münzwurf bei $u$ löst ein MP und ist nicht quasi-linksstetig. Das ist die scharfe Grenze der Atomtoleranz und fehlt im Manuskript. Offen ist auch, ob Thm. 4.3.12 hinter `thm:cadlag` aufgenommen wird.
- Lean-Beleg: `not_isQuasiLeftContinuous_of_atom` (Roadmap), `IsQuasiLeftContinuous.ae_eq_leftLim` (bewiesen, Inv. Z. 5470ff.)
- Heute: OFFEN. MS Z. 3269–3275: unverändert. „quasi-left“ und „4.3.12“ kommen im Manuskript nicht vor.
- Vorschlag: Einen Satz in (ii) ergänzen: „but quasi-left continuity (\EK, Thm. 4.3.12) fails at atoms; example $q=\delta_u$“. Gegebenenfalls eine abstrakte Fassung von Thm. 4.3.12 unter $q(\{u\})=0$.

---

## D. Dualität, Uhren mit Atomen (§6, Task 23)

### rem:atomicdual — falsche Begründung am Diamanten
- Lauf: 2026-08-30, dritter Lauf (Inv. Z. 503–512, 1104–1111)
- Befund: Auf $\{0,a,b,t^*\}$ sind die drei Relationen dieselbe. Sie erzwingen $m_a\gamma(a,t)=m_b\gamma(b,t)=0$ nicht, und bei $m_a+m_b=0$ gibt es ein Gegenbeispiel.
- Lean-Beleg: keiner (`Task23/diamond.py`)
- Heute: ERLEDIGT. Vom Lauf selbst ersetzt, heute durch `lem:selfadjoint`/`prop:atomicposet` und `rem:atomicposet` (MS Z. 6139ff., 6258ff.) mit dem Diamanten $m_a=1$, $m_b=-1$.
- Vorschlag: —

### rem:atomicdual — „no order structure beyond a preorder“
- Lauf: 2026-08-30, zweiter Lauf (Inv. Z. 1033–1044)
- Befund: Bewiesen war nur der Fall, dass die Atome eine Kette bilden.
- Lean-Beleg: `atomGrid_symm` (Roadmap)
- Heute: ERLEDIGT. Die Formulierung fehlt in `rem:atomicdual` (MS Z. 5983ff.), die Statustabelle trennt „atoms a chain“ (MS Z. 5795).
- Vorschlag: —

### Statuszeile „purely atomic, atoms incomparable“ und die o-Konvention
- Lauf: 2026-08-31, siebter und achter Lauf (Inv. Z. 661–702, 2236–2265, 2376–2395)
- Befund: Die Zeile „verified …; not proved“ war falsch, denn der Fall ist für $\iota=\mathrm p$ bewiesen. Die o-Fassung ist falsch, mit dem Diamanten $m_a=1,m_b=4,m_c=2$ als Zeugen.
- Lean-Beleg: keiner (Matrixlemmata der Roadmap M8)
- Heute: ERLEDIGT. MS Z. 5796–5797 („proved, Proposition atomicposet ($\iota=\mathrm p$)“ und „the same for $\iota=\mathrm o$: false“). Das Gegenbeispiel steht in Z. 6280–6300, die Bedingung „maximal order“ in Z. 6264/6303.
- Vorschlag: —

### prop:mixeddual — die Hypothese stetiger Masse zwischen Atomen
- Lauf: 2026-09-01, erster und zweiter Lauf (Inv. Z. 2466–2471, 2531–2548)
- Befund: $c_j>0$ (\eqref{eq:separated}) war eine Hypothese des Beweises, nicht der Aussage.
- Lean-Beleg: `duality_of_mixed` (Roadmap)
- Heute: ERLEDIGT. `eq:separated` fehlt im Manuskript, der Beweis unterscheidet die Fälle $c_j>0$ und $c_j=0$ (MS Z. 6424ff., 6474, 6497).
- Vorschlag: —

### prop:atomicposet — die Endlichkeit ist scharf
- Lauf: 2026-09-04, zweiter Lauf (Inv. Z. 726–762, 3951ff.)
- Befund: Der Schlusssatz legt nahe, die Endlichkeit sei Bequemlichkeit. Eine abzählbare Antikette gibt ein Gegenbeispiel.
- Lean-Beleg: keiner (`Task23/poset_infinite.py`)
- Heute: ERLEDIGT. `ex:antichain` (MS Z. 6695–6720) und die Statuszeile „countable, without (F): false“ (Z. 5802). Commit 153ebdf, 2026-09-04. Der Satz in Z. 6147 („No hypothesis is made on the mutual position …“) steht noch, das Beispiel ist aber verknüpft.
- Vorschlag: —

### rem:atomsnotchange, Statustabelle — bewiesene Erweiterungen fehlten
- Lauf: 2026-09-01, neunter Lauf, bis 2026-09-04 (Inv. Z. 3350–3361, 3819–3829, 3928–3938)
- Befund: Die Tabelle kannte nur endlich viele Atome in einer Kette und „order-dense: open“. Bewiesen waren schon intervallendliche Ketten, diskrete Ketten mit beschränktem $\Phi$ und beliebige Ketten mit Integrierbarkeit, womit „order-dense: open“ falsch wurde.
- Lean-Beleg: `atomGrid_symm_int`, `duality_of_atomic_intervalFinite` (Roadmap)
- Heute: ERLEDIGT. MS Z. 5800–5810: „countable chain, any order type, with (F): proved, thm:densechain“ und weitere Zeilen. Offen sind nur noch Fälle ohne (F).
- Vorschlag: —

### cor:atomless — schließt nur $Q$-f.ü., obwohl der Beweis „überall“ hergibt
- Lauf: 2026-09-01 (Inv. Z. 713–724)
- Befund: Die Einschränkung „$Q$-almost every $t$“ ist ein Artefakt des Umwegs über `lem:calculus`. `lem:rectangle` gibt auf demselben Paar $\Psi=f(x+y)$ überall. Damit ist auch die Bemerkung „the conclusion is genuinely $Q$-almost every $t$“ fraglich.
- Lean-Beleg: keiner
- Heute: OFFEN. MS Z. 5710–5711 („for $Q$-almost every $t$“), Z. 5835–5837 („genuinely $Q$-almost every $t$“). `lem:rectangle` (Z. 6334) wäre verfügbar.
- Vorschlag: Im Beweis `lem:rectangle` statt `lem:calculus` einsetzen, die Konklusion auf „every $t\le t^*$“ heben und die Bemerkung in Z. 5835 prüfen oder streichen.

---

## E. Konvergenz (§7)

### rem:MZcost, zweiter Absatz — „CMT und Skorokhod in nicht-polnischer Allgemeinheit nötig“
- Lauf: 2026-09-08, elfter Lauf (Inv. Z. 9701–9931, 10015–10023)
- Befund: Falsch in beiden Hälften. Der Beweis von `thm:MZconv` benutzt `fact:cmt` nicht, und Schritt 1 läuft über den polnischen Raum $M_E$ (Kurtz 1991).
- Lean-Beleg: `measurableSet_of_measurable_injective`, `measurableSet_of_continuous_injective`, `AEEqFun.distInMeasure`; $M_E$ polnisch (Meilenstein 6, Inv. Z. 10187ff.)
- Heute: ERLEDIGT. MS Z. 10213ff. („It does not follow that a formalization needs either of them at that generality …“, mit $d_m$ und $M_E$). Commit f2531eb, 2026-09-08.
- Vorschlag: —

### fact:pseudopath — Injektivität nur auf $\DE$ gefolgert; „that compact space“ mehrdeutig
- Lauf: 2026-09-08, elfter Lauf (Inv. Z. 102, 9762–9766, 10036–10044)
- Befund: Der Fact sagt selbst, dass die Abbildung genau die $\lambda$-f.ü. gleichen Pfade identifiziert, also auf ganz $M_E$ injektiv ist. Das Manuskript folgert nur „injective on $\DE$“. „That compact space“ in (ii) muss der Raum der Gesetze $\Prob([0,\infty]\times\hat E)$ sein. Die neue Argumentation von `rem:MZcost` hängt an dieser Lesart. Das ist Präzisierung, kein Fehler.
- Lean-Beleg: keiner
- Heute: OFFEN. MS Z. 10064 („so it is injective on $\DE$“) und Z. 10072–10073 („$\DE$ being merely Borel in that compact space“) sind unverändert.
- Vorschlag: „injective on $M_E$, in particular on $\DE$“ schreiben und „in $\Prob([0,\infty]\times\hat E)$“ ausschreiben.

---

Gesamt: 31 Befunde / erledigt: 12 / offen: 19 / unklar: 0
(Davon sind 3 offene Befunde (*) von mir aus Lean-Widerlegungen aufs Manuskript übertragen: `def:dcirc`, `thm:DEcompact`, `thm:DEpolish`/Cantor.)

---

## Ausschnitt 2

# Befunde am Manuskript — Inventar-Ausschnitt 2 (Läufe 2026-09-09, elfter Lauf, bis 2026-09-13, siebter Lauf)

Zeilenangaben „INV“ beziehen sich auf `INV_slice2.md`, „MS“ auf `MS_current.tex` (heutiger Stand).
Alle betroffenen MS-Stellen sind laut `git log -S` seit dem 2026-08-25 (bbda4b4) unverändert.

### def:jumpconstruction / thm:jumpMP (Schritt 4) / rem:jumpexplosion / rem:jumppoint — Sprungzeiten sind im Allgemeinen keine Funktionale des Pfades
- Lauf: 2026-09-10, zehnter Lauf (INV 3763–3920, v.a. 3780–3830); bestätigt und verschärft 2026-09-11, zehnter Lauf (INV 7561–7590), 2026-09-12, sechster Lauf (INV 10640–10730), 2026-09-12, achter Lauf (INV 10954–10980), 2026-09-12, neunter Lauf (INV 11143–11160)
- Befund: Die Konstruktion zählt einen Sprung von $x$ nach $x$ mit, der Pfad zeigt ihn aber nicht. Ist $\mu(x,\{x\})>0$, dann lassen sich die $\tau_n$ nicht aus dem Pfad ablesen und sind für keine Filtration des Prozesses Stoppzeiten, auch nicht für die rechtsstetige. Das bleibt auch f.s. falsch: bei einpunktigem $E$ oder $\mu=$ Identität tritt es mit Wahrscheinlichkeit 1 ein. Außerdem braucht „der Pfad hat den Wert gewechselt“ eine meßbare Diagonale von $E\times E$, und die fehlt unter (E0). Die Pfad- und die Sprungzeitfiltration stimmen nur überein, wenn vier Bedingungen gelten: die Kette bewegt sich bei jedem Schritt, die Sprungzeiten wachsen streng, $T_0=0$ und die Diagonale ist meßbar. Damit sind die Aussagen „$\tau_n$ is a functional of the path“, die Beschreibung von $\Gilt_s$ in Schritt 4 und „$(\tau_n)$ localizing system, L1–L3“ in dieser Allgemeinheit falsch.
- Lean-Beleg: `not_isStoppingTime_min_jumpTimeE`, `eq_of_measurable_jumpFiltrationE_of_subsingleton`, `eq_of_measurable_jumpFiltrationE_const_chain`, `exists_not_pointFiltrationE_le_stepPathFiltrationE_of_const_chain`, `…_of_coincident_times`, `…_of_not_measurableEq`, `pointFiltrationE_eq_stepPathFiltrationE` (positive Fassung unter den vier Bedingungen), `ae_move_jumpMeasure_of_ne`
- Heute: OFFEN. MS 8624–8626 „each $\tau_n$ is a functional of the path --- the time of its $n$-th jump --- which is what will make it a legitimate localizing sequence“. MS 8710–8713 (Schritt 4) „On $\{N_s=n\}$ the σ-field $\Gilt_s$ is generated by $Y_0,\dots,Y_n$, $\tau_1,\dots,\tau_n$ and $\{\tau_{n+1}>s\}$“. MS 8842–8846 (rem:jumpexplosion) „$\tau_n$ is a functional of the path … hence $(\tau_n)$ is a localizing system“. MS 8873–8874 (rem:jumppoint) „a genuine instance of L1–L3“. Das Beispiel $\mu(n,\cdot)=\delta_{n+1}$ in rem:jumpexplosion selbst ist nicht betroffen, weil die Kette dort bei jedem Schritt wächst.
- Vorschlag: Für die Aussage über die Sprungzeiten $\mu(x,\{x\})=0$ und eine meßbare Diagonale (z.B. (E1)) voraussetzen. Oder $\tau_n$ durch die echten Sprungzeiten des Pfades bzw. durch Trefferzeiten des laufenden Supremums $\sup_{s\le t}\lambda(X_s)$ ersetzen; das ist die Reparatur aus dem Lauf, `rateTime`. Schritt 4 entsprechend umformulieren, etwa über die Punktfiltration $\sigma(Y_k,\tau_k)$ statt $\Gilt_s$, und dann den Übergang zu $\Gilt_s$ getrennt begründen.

### thm:pathjumpMP (Beweis von (a)) — „strict stopping time, being the $m$-th jump time“ gilt nur, wenn die Kette sich bewegt
- Lauf: 2026-09-11, zehnter Lauf (INV 7561–7590); 2026-09-12, sechster Lauf (INV 10710–10730); 2026-09-12, neunter Lauf (INV 11143–11160)
- Befund: Derselbe Defekt in der pfadabhängigen Fassung. In Setting set:pathjump ist $\mu(t,\omega,\cdot)$ beliebig in $\Prob(E)$ und darf ein Atom in $\omega(t-)$ haben. Dann ist $\tau_m$ keine Pfadfunktion und keine strikte Stoppzeit der Pfadfiltration. Für Hawkes gibt es das Problem nicht, weil dort $\mu=\delta_{\omega(t-)+1}$ ist und die Kette bei jedem Schritt springt.
- Lean-Beleg: `not_isStoppingTime_hawkesJumpTime_pathFiltration` (Zeuge mit konstanter Kette), `not_hawkesFiltration_le_hawkesPathFiltration`, `ae_ne_poissonKernel`
- Heute: OFFEN. MS 10432–10434 „each $\tau_m$ is a functional of the path --- indeed a strict stopping time, being the $m$-th jump time of a right continuous piecewise constant path“. Setting set:pathjump (MS 10301–10321) schließt Atome in $\omega(t-)$ nicht aus.
- Vorschlag: In set:pathjump $\mu(t,\omega,\{\omega(t-)\})=0$ fordern, dazu eine meßbare Diagonale. Oder im Beweis die Lokalisierung über Pfadfunktionale führen, etwa über die Trefferzeiten der kumulierten Rate.

### Notation für Prozesse / thm:jumpMP (Schluß des Beweises) — Progressivität unter (E0) ist nicht belegt
- Lauf: 2026-09-09, neunzehnter Lauf (INV 1323–1350)
- Befund: Ein Limes $E$-wertiger meßbarer Abbildungen ist nur meßbar, wenn die Diagonale von $E$ meßbar ist. Unter (E0) ist daher die Progressivität des $E$-wertigen Sprungprozesses laut Lauf „mutmaßlich falsch“. Ohne Topologie auf $E$ ist auch „right continuous $X$“ gar nicht definiert. Gebraucht wird nur die reelle Fassung: $(s,\omega)\mapsto h(X_s(\omega))$ ist gemeinsam meßbar, weil jeder Pfad rechts lokal konstant ist. Daraus folgt ${}^{*}\Filt^X_t=\Filt^X_t$ trotzdem. Die Schlußfolgerung stimmt also, die Begründung im Manuskript trägt unter (E0) aber nicht.
- Lean-Beleg: `measurable_uncurry_min_of_eventuallyEq`, `eventuallyEq_nhdsGE_stepPath`, `stronglyAdapted_mpFamily_jumpProcess`
- Heute: OFFEN. MS 892–893 „If $X$ is progressively measurable --- in particular if $\T$ satisfies (T2b) and $X$ is right continuous --- then ${}^{*}\Filt^X_t=\Filt^X_t$“ (Topologie auf $E$ stillschweigend). MS 8732–8734: „since ${}^{*}\Filt^X_t=\Filt^X_t=\Gilt_t$ for the right continuous $X$“, im Rahmen von thm:jumpMP unter (T3)+(E0) und rem:jumppoint „needs only (E0) … no topology“.
- Vorschlag: In MS 8732 statt „right continuous“ begründen: die Pfade sind rechts lokal konstant, also ist $h(X)$ für jedes $h\in\Bdd(E)$ reell rechtsstetig und progressiv, und daher liegen die Integrale in (eq:starfilt) schon in $\Filt^X_t$. Bei MS 892 die Voraussetzung „$E$ topologisch/metrisierbar“ ausdrücklich nennen.

### thm:pathjumpMP (a) — $(\tau_n)$ als lokalisierendes System wegen unbeschränkter kumulierter Rate
- Lauf: 2026-09-11, siebzehnter Lauf (INV 8860–8870); zurückgenommen und präzisiert im achtzehnten Lauf, zweiter Teil (INV 9133–9157)
- Befund: Der siebzehnte Lauf hatte als „Abweichung vom Manuskript“ vermerkt: Auf $[0,\tau_n]$ ist die kumulierte Rate $\sum_{k<n}\xi_k$ in $\omega$ unbeschränkt, also taugen die Sprungzeiten nicht als lokalisierendes System. Der achtzehnte Lauf stellt klar, daß $\sum_{k<n}\xi_k$ eine integrierbare Majorante ist. Nur Leans `martingale_stoppedProcess` verlangt eine konstante Schranke. Das ist eine Eigenheit der Lean-Werkzeuge und kein Fehler des Manuskripts, das eq:compensatorexp genau so benutzt.
- Lean-Beleg: `cumulativeRateF_min_jumpTimeF_le`, `rateInverse_sum_eq_jumpTimeF`, `cumulativeRateF_jumpTimeF_sub` (= eq:compensatorexp)
- Heute: ERLEDIGT (durch den Folgelauf zurückgenommen; MS 10345–10360 und 10363–10381 brauchen deswegen keine Änderung. Der davon unabhängige Punkt „Sprungzeiten als Pfadfunktionale“ steht oben.)
- Vorschlag: keiner.

### eq:pathgen — der Erzeuger liest $f(\omega(t-))$, die Formalisierung $f(X_t)$
- Lauf: 2026-09-11, elfter Lauf (INV 7822–7830, „Eine Auffälligkeit am Manuskript“)
- Befund: eq:pathgen setzt den Zuwachs bei $\omega(t-)$ an. Die beiden Integranden unterscheiden sich nur auf den abzählbar vielen Sprungzeiten, also auf einer Lebesgue-Nullmenge. Die Kompensatorintegrale stimmen daher überein, und der Lauf sagt ausdrücklich, daß „keine Aussage über einen Testprozeß betroffen“ ist. Er hält den Unterschied nur fest, damit er nicht stillschweigend geglättet wird.
- Lean-Beleg: `jumpApplyF`, `jumpOperatorF`
- Heute: UNKLAR (kein Fehler im Manuskript, nur ein Hinweis; MS 10314–10318 unverändert)
- Vorschlag: allenfalls ein Halbsatz, daß man $\omega(t-)$ durch $\omega(t)$ ersetzen kann, ohne $\XX^\circ$ zu ändern.

### Absatz nach def:pathjumpconstruction (ex:hawkes-Umfeld) — Überlebensfunktion $e^{-A_n(u)}$ gilt nur für $u\ge\tau_n$
- Lauf: 2026-09-13, vierter Lauf (INV 12722–12744)
- Befund: Die bedingte Überlebensfunktion $P(\tau_{n+1}>u\mid\mathcal H_n)$ ist nur auf $\{\tau_n\le u\}$ gleich $\exp(-(\Lambda_u-\Lambda_{\tau_n}))$. Für $u<\tau_n$ ist der Exponent negativ, $e^{-A_n(u)}>1$ „und damit gar keine Wahrscheinlichkeit“, richtig ist dort $1$. Der Lauf schreibt die Formel `ex:hawkes` zu, sie steht heute aber im Absatz vor thm:pathjumpMP.
- Lean-Beleg: `condExp_lt_jumpTimeFE_hawkesSelfRateH_block_exp` (mit Voraussetzung $\tau_n\le t$), `condExp_lt_jumpTimeFE_hawkesSelfRateH_block` (`expMeasure`-Gestalt, überall gültig)
- Heute: OFFEN. MS 10338–10341 „the survival function $P(\tau_{n+1}>u\mid\mathcal H_n)=e^{-A_n(u)}$ and the jump-time density …“, ohne „$u\ge\tau_n$“. Im Beweis (MS 10398–10407) wird die Formel nur für $u\ge\tau_n$ benutzt.
- Vorschlag: „for $u\ge\tau_n$“ ergänzen oder $e^{-A_n(u)\vee 0}$ schreiben. Die Dichte entsprechend auf $(\tau_n,\infty)$ einschränken.

---

Ausdrücklich keine Befunde (Läufe bestätigen das Manuskript, nicht gezählt):
- ex:hawkes, Nichtexplosion ohne $\lVert\phi\rVert_1<1$ (INV 6995–7004): „keine Auffälligkeit gegen das Manuskript, sondern Übereinstimmung“.
- eq:compensatorexp „by the very definition“ (INV 9124–9131): in Lean wörtlich wahr.
- set:jumpdata, Form des Erzeugers (INV 3681–3693, Geburt-Tod): „kein Befund gegen `set:jumpdata`“.
- Rate $\lambda=0$ und absorbierende Zustände (INV 976–985, 3695–3710): betrifft nur Lean ($x/0=0$) und Kerne aus der Roadmap. Das Manuskript hat die Konvention $1/0=\infty$ (MS 8613) und die Lesart „$\lambda=0$ … read as $0$“ (MS 8683–8684).
- $\mathcal H_n$ muß bei $Y_n$ aufhören (INV 12661–12720): das Manuskript definiert $\mathcal H_n=\sigma(Y_0,\dots,Y_n,\tau_1,\dots,\tau_n)$ bereits so.

Zahlen: gesamt 6 / erledigt 1 / offen 4 / unklar 1

---

## Ausschnitt 3

# Befunde am Manuskript, Inventar-Ausschnitt 3 (2026-09-13, 8. Lauf, bis 2026-09-19, 4. Lauf)

Vorbemerkung: Der Ausschnitt ist fast ganz Lean-/Roadmap-Arbeit (Meilensteine 4–10, Skorokhod, Teil D). Befunde, die das Manuskript wirklich betreffen, gibt es nur in den Läufen vom 2026-09-14 (erster bis vierter) und am 2026-09-15 (fünfter). Nach 2026-09-18 sagt jeder Lauf ausdrücklich „keine Zeile des Manuskripts angefaßt“ und meldet keinen Befund am Manuskript. Zeilen „Inv.“ beziehen sich auf INV_slice3.md, Zeilen „MS“ auf MS_current.tex.

### ex:shiftXA — Substitution v = r+u braucht (T2a)
- Lauf: 2026-09-14, zweiter Lauf, Inv. Z. 1496–1539 (erneut aufgegriffen Inv. Z. 1633–1638)
- Befund: Der Beweis setzt r + ⟨0,t⟩ = ⟨r, r+t⟩. Das ist eine Totalitätsbedingung, die aus (T4) nicht folgt. Die Überschrift von ex:shiftXA führte (T2a) nicht. Zeuge ist ex:clocks(iv) (ℝ₊², Lebesgue, f=0, g≡1): κ = r₁t₂ + t₁r₂ hängt von t ab.
- Lean-Beleg: `isShiftSystem_mpFamily`, `Clock.IsShiftInvariant` (Totalität in `map_interval` eingeschlossen)
- Heute: ERLEDIGT (MS Z. 3854: Kopf „(T0)+(T4)+(T2a)“, Hinweis im Beweis; neue rem:shiftXAtotal ab MS Z. 3890 mit dem Zeugen; Commit 1bc5106 vom 2026-09-14)
- Vorschlag: —

### rem:absuniqgain(ii) — „For 𝕏_A it never fails“ gilt nur unter (T2a)
- Lauf: 2026-09-14, zweiter Lauf, Inv. Z. 1526–1531
- Befund: rem:absuniqgain(ii) folgert, für 𝕏_A versage das Schiftsystem nie. Das stimmt unter (T2a), über einer Halbordnung nicht.
- Lean-Beleg: wie oben
- Heute: OFFEN (Rest). rem:shiftXAtotal (MS Z. ~3913) schränkt die Behauptung ausdrücklich ein, und rem:absuniqoner (MS Z. 4209) sagt es auch. Die Bemerkung selbst sagt in MS Z. 4592 aber weiter ohne Einschränkung „For $\XX_A$ it never fails: whatever the clock $q$ …“.
- Vorschlag: In (ii) „under \eqref{T2a} (Remark~\ref{rem:shiftXAtotal})“ einfügen.

### thm:absuniq(a) — eq:absonedim wird an nur einem r gebraucht; Markov-Teil ruht über das Schiftsystem auf Totalität
- Lauf: 2026-09-14, vierter Lauf, Inv. Z. 1913–1935; dritter Lauf, Inv. Z. 1633–1638
- Befund: Teil (a) verbraucht eq:absonedim nur an dem einen r, an dem die Markoveigenschaft behauptet wird (beide Restarts sitzen am selben Shift). Das Manuskript verlangte es für jedes r. Außerdem führt (a) kein (T2a), sein Standardbeispiel 𝕏_A braucht es aber über ex:shiftXA.
- Lean-Beleg: `isMarkov_of_unique_onedim`
- Heute: ERLEDIGT (MS Z. 4180ff.: „let r be *one* time for which eq:absonedim holds“; neue rem:absuniqoner ab MS Z. 4197, einschließlich des Absatzes zu (T2a) im Standardbeispiel; die bestimmende Menge ist nach (b) verschoben; Commit 1bc5106)
- Vorschlag: —

### lem:restart — vier fehlende Voraussetzungen, zwei überflüssige
- Lauf: 2026-09-14, erster Lauf, Inv. Z. 1131–1187 (vorbereitet 2026-09-13, zwölfter Lauf, Inv. Z. 1076–1081)
- Befund: Der Beweis braucht (1) die Adaptiertheit von X, (2) r ≤ r+u, (3) die Integrierbarkeit der Grundfamilie längs X und (4) θ_r-Meßbarkeit bzw. eine Schranke an κ. Das Manuskript nannte davon drei nur in Prosa. Die Normierung E[Z]=1 und die bestimmende Menge 𝓩° werden dagegen nicht gebraucht, wenn man gegen jede Menge von 𝓕°_s testet.
- Lean-Beleg: `restart`, `restart_canonical`, `integral_smul_martingale_eq`, `isProbabilityMeasure_map_withDensity_ofReal`
- Heute: ERLEDIGT (MS Z. 3926–3942: adapted, $Y^\circ_u(X)\in L^1$, „$r \le r+u$ for all $u$“, keine Normierung, „R is a probability measure precisely when E[Z]=1“; neue rem:restarthyp ab MS Z. 3946; im Beweis wird gegen alle $B\in\Filt^\circ_s$ getestet; Commit 1bc5106). Den κ-Teil siehe nächster Eintrag.
- Vorschlag: — (Hinweis: lem:localrestart, MS Z. 4835–4840, trägt noch die alte Gestalt mit $\ZZ^\circ$, $E^P[Z]=1$ und ohne Adaptiertheit bzw. $r\le r+u$. Das Inventar prüft diese lokale Fassung nicht; es wäre eigens nachzusehen.)

### lem:restart — Integrierbarkeit von κ̃ wird benutzt, aber nicht vorausgesetzt
- Lauf: 2026-09-14, erster Lauf, Inv. Z. 1159–1165
- Befund: Das Inventar liest die letzte Beweiszeile als Forderung κ̃ ∈ L¹(P). Lean verlangt dafür eine Schranke an κ als Feld von `IsShiftSystem`, weil die Struktur kein Maß kennt. Im Manuskript steht κ̃ ∈ L¹ aber nur im Beweis. Weder die Aussage des Lemmas noch def:shiftstable (κ nur $\Filt^\circ_r$-meßbar) fordern es, und aus den übrigen Voraussetzungen folgt es nicht: κ = Ŷ°₀∘θ_r, und über 𝕏°_r ist keine Integrierbarkeit angenommen.
- Lean-Beleg: Feld „Schranke an κ“ in `IsShiftSystem` (von `restart` verbraucht)
- Heute: OFFEN. MS Z. 3931–3933 nennt nur „$Y^\circ_u(X)\in L^1(P)$ for every $Y^\circ\in\XX^\circ$“. MS Z. 4006 benutzt „$\tilde\kappa \in L^1(P)$“. rem:restarthyp (MS Z. 3946ff.) erwähnt κ nicht.
- Vorschlag: In lem:restart „and $\kappa(X)\in L^1(P)$ for the $\kappa$ of \eqref{eq:shiftstable}“ ergänzen, oder in def:shiftstable κ beschränkt verlangen. In ex:shiftXA ist das mit κ = f(π_r) und beschränktem f ohnehin erfüllt. Einen Satz dazu in rem:restarthyp aufnehmen.

### lem:propagation / thm:absuniq(b) — die bestimmende Menge 𝓩° wird nicht gebraucht
- Lauf: 2026-09-14, erster Lauf, Inv. Z. 1178–1187; bestätigt im zweiten Lauf, Inv. Z. 1409–1411 (`subsingleton_mpSolutions_of_unique_onedim` ist genau `propagatesAgreement_of_unique_onedim` gefolgt von `subsingleton_of_propagatesAgreement`, dazwischen nichts)
- Befund: Weil lem:restart ohne 𝓩° auskommt, fällt 𝓩° auch aus den Voraussetzungen von lem:propagation, und damit aus thm:absuniq(b). prop:uniqfromprop braucht es ohnehin nicht.
- Lean-Beleg: `propagatesAgreement_of_unique_onedim`, `subsingleton_mpSolutions_of_unique_onedim`
- Heute: OFFEN. MS Z. 4136–4137: lem:propagation fordert „with $\ZZ^\circ$ determining for each $\XX^\circ_r$“, obwohl der Beweis (MS Z. 4146–4171) es nirgends benutzt. MS Z. 4190: thm:absuniq(b) fordert „if $\ZZ^\circ$ is determining for every $\XX^\circ_r$“. Commit 1bc5106 hat 𝓩° bewußt nach (b) verschoben („where it belongs“), dort ist es nach dem Lean-Beleg aber ebenfalls überflüssig.
- Vorschlag: Die 𝓩°-Voraussetzung in lem:propagation und thm:absuniq(b) streichen oder als „nicht gebraucht“ kennzeichnen. Ob die lokalen Fassungen (lem:localrestart Z. 4837, thm:localuniq Z. 4923) sie brauchen, deckt das Inventar nicht.

### def:cc — Meßbarkeit des Ereignisses in eq:cc
- Lauf: 2026-09-15, fünfter Lauf, Inv. Z. 3714–3721
- Befund: def:cc schreibt P{X(t) ∈ K für alle t ∈ 𝕋_{≤T} ∩ D} und setzt stillschweigend voraus, daß das ein Ereignis ist. Vorgeschlagen war nur eine Bemerkung bei def:cc, keine Änderung der Aussage.
- Lean-Beleg: keiner (Entwurf der Fassungen (a)/(c) von `CompactContainment`; Meßbarkeitsschritt in `CompactContainment.ae_exists_isCompact`)
- Heute: OFFEN, aber inhaltlich gegenstandslos. def:cc (MS Z. 3002–3013) ist seit 2026-08-24 unverändert, eine Bemerkung gibt es nicht. Im Manuskript ist D abzählbar, E ist unter (E2) metrisierbar, also ist K abgeschlossen, und X(t) ist meßbar. Das Ereignis ist dann ein abzählbarer Durchschnitt meßbarer Mengen und damit meßbar. Das Problem gibt es nur in der Lean-Fassung.
- Vorschlag: Höchstens einen Halbsatz „(an event, since D is countable and K closed)“ ergänzen. Sonst nichts.

## Randnotizen (keine Fehler, nicht gezählt)
- thm:absuniq(a) / rem:chainonly (MS Z. 4304ff.): Laut Lean braucht (a) den Subtraktionsteil von (T4) (`hsub`) nicht, nur ⊥ = 0 und r ≤ r+u (Inv. Z. 1924–1929). rem:chainonly sagt „(T0) and (T4)“. Das ließe sich verschärfen, falsch ist es nicht.
- thm:absreg (MS Z. 3145): Der Lean-Beweis kommt ohne Hypothese (b) „Φ separating“ aus. Er verlangt statt dessen Beschränktheit und |f|² ∈ Φ für die abzählbare Teilklasse (Inv. Z. 4888–4905). Das Manuskript benutzt (b) in Schritt 4 über fact:sepcond und ist damit korrekt. Es ist eine alternative Hypothesenwahl.
- thm:absconv: Der Pfadraum muß weder separabel noch metrisch sein (Inv. Z. 7683–7692). Das Manuskript (E3) ist ein Spezialfall. Es wäre eine Verallgemeinerung, kein Fehler.
- def:Pcont: Ausdrücklich als richtig bestätigt, nur die Roadmap war mehrdeutig (Inv. Z. 7706–7710).
- fact:fddconv(b) = EK 3.7.8(b): Die Bruchstelle liegt in der Beweisskizze der Roadmap, nicht im Satz. Der Lauf sagt ausdrücklich, er habe nicht gezeigt, daß EK 3.7.8(b) falsch wäre (Inv. Z. 11138–11150, 11491).
- Ethier–Kurtz 4.3.12 ohne Atomlosigkeit (Inv. Z. 6631ff.): Das Manuskript enthält keine Quasi-Linksstetigkeit, also ist es nicht betroffen.

Zahlen: gesamt 7 / erledigt 3 / offen 4 (davon 1 inhaltlich gegenstandslos: def:cc; 1 Restkorrektur: rem:absuniqgain(ii)) / unklar 0

---

## Ausschnitt 4

# Befunde am Manuskript: Inventar-Ausschnitt 4 (Läufe 2026-09-19, 5. Lauf, bis 2026-09-21, 20. Lauf)

Vorbemerkung: Fast alle Läufe dieses Ausschnitts arbeiten an den TauCeti-Roadmaps
(`SkorokhodSpace`, `MartingaleProblems`, Meilensteine 8, 11, 14). Ihre „Befunde“
betreffen meist Roadmap-Aussagen, Lean-Formulierungen oder Mathlib. Nur der vom
Nutzer eingeschobene Lauf 2026-09-20/9 richtet sich ausdrücklich gegen das
Manuskript. Zwei weitere Einträge (Nr. 6 und 7) sind Lean-Ergebnisse, die eine
heutige Aussage des Manuskripts überholen oder eine Lücke darin aufdecken.
Heutige Zeilen beziehen sich auf MS_current.tex.

### ex:volterra / rem:dualnonmarkov — falscher Grund, warum die Dualität Volterra nicht erreicht
- Lauf: 2026-09-20, 9. Lauf (eingeschoben), Inventar Z. 6072–6099 und 6218–6235
- Befund: Das Manuskript begründete, dass Abschnitt sec:duality Volterra-Prozesse nicht erreicht, mit dem Schiftsystem. Der wahre Grund: Ein zustandsbasierter Dualer erzwingt die Markoveigenschaft, und ein pfadabhängiger Prozess hat sie nicht. Das Schiftsystem ist dagegen entbehrlich.
- Lean-Beleg: `integral_smul_martingale_eq`, `propagatesAgreement_of_transfer` (Roadmap: `isMarkov_of_duality`)
- Heute: ERLEDIGT (Z. 5309–5315 in ex:volterra: „the reason given here is the wrong one, and Remark rem:dualnonmarkov replaces it“; Z. 7608–7647 rem:dualnonmarkov; Commit 51c443b, 2026-09-20)
- Vorschlag: —

### cor:uniqviadual — Umweg über thm:absuniq unnötig, nur Hypothese (i) überlebt
- Lauf: 2026-09-20, 9. Lauf, Inventar Z. 6087–6092, 6204–6210, 6225–6230
- Befund: Die gewichtete Dualität liefert `PropagatesAgreement` direkt. Damit folgt die Eindeutigkeit über prop:uniqfromprop, ohne Schiftsystem, ohne bestimmende Menge und ohne thm:absuniq. Von cor:uniqviadual überlebt nur (i), die trennende Familie. Die Markoveigenschaft fällt in einer Zeile aus der Identität, auf kürzerem Weg als im Manuskript.
- Lean-Beleg: `propagatesAgreement_of_transfer`, `isFiniteMeasure_weightedLaw`, `weightedLaw_univ`
- Heute: ERLEDIGT (Z. 7613–7628 „The shift is dispensable … Of Corollary cor:uniqviadual only hypothesis (i) … survives“; Z. 5392–5397). Der Beweis des Korollars selbst (Z. 7570 ff.) geht weiter über Theorem thm:uniqueness. Das Manuskript vermerkt das bewusst (Z. 3463–3465, rem:disintkall).
- Vorschlag: allenfalls im Korollar selbst auf rem:dualnonmarkov verweisen

### rem:dualnonmarkov — zwei Preise der gewichteten Fassung (Martingaleigenschaft; Messbarkeit nur bezüglich 𝓕^X)
- Lauf: 2026-09-20, 9. Lauf, Inventar Z. 6112–6117 und 6166–6178
- Befund: Die gewichtete Dualität braucht in der X-Richtung die volle Martingaleigenschaft. Die ungewichtete braucht nur die Konstanz des Mittelwerts. Außerdem muss das Gewicht 𝓕^X_{s₀}-messbar sein und nicht 𝓕_{s₀}-messbar. Die Bedingung ist scharf: Zeuge mit E₁ = Unit, f(x,y) = y, Z = 1 + Y₁.
- Lean-Beleg: `not_secondIncrement_of_weight_on_dual` (Roadmap)
- Heute: ERLEDIGT (Z. 7630–7637, einschließlich des Zeugen)
- Vorschlag: —

### rem:dualnonmarkov — Spielraum außerhalb der Markov-Welt: bedingte Bilanz, keine Instanz bekannt
- Lauf: 2026-09-20, 9. Lauf, Inventar Z. 6237–6244
- Befund: Übrig bleibt nur die bedingte Bilanz E[g_r(X,·) − h(X_r,·) | 𝓕^X_{s₀}] = 0, die ein pfadabhängiges g zulässt. Keine Instanz ist bekannt, und das Manuskript liefert keine.
- Lean-Beleg: keiner (Roadmap: `duality_weighted_of_condExp`, offen)
- Heute: ERLEDIGT (Z. 7649–7655 „no instance of it is known … the question this remark leaves open“; Status Z. 7657–7662)
- Vorschlag: —

### rem:dualnonmarkov — Λ undefiniert; duale Zeit ist „gleiche Uhrmasse“, nicht s′ − s₀
- Lauf: 2026-09-20, 9. Lauf, Inventar Z. 6150–6165 und 6182–6190
- Befund: Bei verschobenem Fußpunkt s₀ lautet die Folgerung Φ^Z(s′,⊥) = Φ^Z(s₀,T). Sie gilt genau dann, wenn Q(s′) − Q(s₀) = Q(T), also wenn beide Fenster dieselbe q-Masse tragen. Nur unter Lebesgue ist T = s′ − s₀. Der Transferoperator ist Λ_{s,t,y}(x) = E[f(x, Y^y_T)] und hängt nicht von P ab. Genau das trägt `PropagatesAgreement`.
- Lean-Beleg: `propagatesAgreement_of_transfer`
- Heute: OFFEN (Z. 5402 und Z. 7642 benutzen Λ_{s,t,y} ohne Definition. Z. 7618–7625 sagen nicht, zu welcher dualen Zeit die gewichtete Identität gelesen wird. rem:haarrole, Z. 5822 ff., behandelt nur den Fußpunkt ⊥.)
- Vorschlag: In rem:dualnonmarkov einen Satz ergänzen: „Λ_{s,t,y}(x) := E[f(x, Y^y(T))] mit Q(T) = Q(t) − Q(s); für s₀ = ⊥ ist T = t, unter Lebesgue T = t − s₀; Λ hängt nicht von der Lösung ab.“

### rem:modulusborel — „open point“ ist teilweise überholt
- Lauf: 2026-09-21, 6. Lauf, Inventar Z. 10451–10475 und 10562–10590
- Befund: Die Lean-Entwicklung hat die eigene Negativaussage „no argument is available that they are Borel“ widerrufen. Der Rechtslimes im Fensterradius, f ↦ inf_{u′>u} w′(f,δ,u′), ist oberhalbstetig und damit Borel-messbar. Er klemmt {w′_m ≥ η} zwischen die Modulmengen zu m und m+1 ein, und ein Verbraucher, der über alle m quantifiziert, bekommt so eine messbare Bedingung ohne Kosten. Offen bleibt nur die Messbarkeit des Moduls bei festem Radius. Er ist dort nicht oberhalbstetig, und der Weg über abzählbar viele Knoten ist nachweislich verschlossen.
- Lean-Beleg: `SkorokhodSpace.upperSemicontinuous_iInf_modulusBased`, `SkorokhodSpace.measurable_iInf_modulusBased`, `SkorokhodSpace.setOf_le_iInf_modulusBased_subset`, `SkorokhodSpace.modulusBased_mono_window`
- Heute: OFFEN (Z. 2215–2241: „Is the modulus Borel? An open point … no Borel witness is produced by that route … A formalization should take that route and leave the measurability question aside“; laut `git log -S` seit 2026-08-29 unverändert)
- Vorschlag: Der Bemerkung einen Absatz anfügen: Die Regularisierung im Radius ist oberhalbstetig, also Borel, und sie klemmt w′_m zwischen m und m+1 ein. Damit gibt es neben der Außenmaß-Route einen zweiten, messbaren Ausweg. Offen bleibt nur der feste Radius.

### ex:hawkes (Absatz „A linear Hawkes process never explodes“) — aus der Erneuerungsgleichung folgt Endlichkeit nur mit Minimalität
- Lauf: 2026-09-20, 6. Lauf, Inventar Z. 5486–5497 und 5645–5648; 2026-09-20, 8. Lauf, Inventar Z. 5962–5984 (dazu Z. 5868–5902)
- Befund: Die Resolvente gibt E[N_t] < ∞ erst, wenn gezeigt ist, dass die mittlere Intensität die Erneuerungsgleichung erfüllt. Das ist eine Aussage über die Konstruktion, keine über die Faltung, und im Bestand fehlt sie für den linearen Fall. Zudem liefert die Resolventenlösung in [0,∞] nur eine untere Schranke für jede Lösung (`renewal_le_of_eq`). Eindeutigkeit gilt nur unter fensterweiser Endlichkeit (`renewal_ae_eq_of_eq`), und auch m ≡ ∞ kann die Gleichung lösen. Der Schluss „m löst m = μ₀ + φ∗m, die Resolvente existiert, also ist m endlich“ braucht deshalb eine Minimalitäts- oder Abschneideüberlegung.
- Lean-Beleg: `renewal_le_of_eq`, `renewal_ae_eq_of_eq`, `setLIntegral_volterraResolvent_lt_top_of_ne_top`; die Naht `lintegral_hawkesSelfRate_eq_add_lconvolution` / `lintegral_stepIndex_hawkesJumpTime_lt_top` ist offen
- Heute: OFFEN (Z. 10479–10485: „The mean intensity m(t) = E[Λ_t] satisfies the renewal equation … So E[N_t] = ∫₀ᵗ m < ∞ for every t“. Die Clusterdarstellung im Beweis zu lem:hawkesflow, Z. 8498–8505, trägt das Argument richtig, weil sie die minimale Lösung Σ‖φ^{∗n}‖ direkt konstruiert. Der Absatz in ex:hawkes verweist aber nicht darauf.)
- Vorschlag: In ex:hawkes entweder abschneiden (m_n bis zur n-ten Sprungzeit ist endlich und eine Sub-Lösung, also höchstens gleich der Resolventenlösung; dann n → ∞) oder auf die Clusterdarstellung verweisen. Hinweis: Die Inventarstelle ist als Roadmap-Naht formuliert, nicht ausdrücklich als Kritik am Manuskript.

Keine Befunde am Manuskript (geprüft und verworfen):
- Z. 829 („das Manuskript und fact:relcompact reden von Straffheit, EK von Relativkompaktheit“): fact:fddconv(b) spricht heute (Z. 1510) wie EK von Relativkompaktheit. Die Brücke fact:prohorov wird in rem:EKrelcompact (Z. 9153) ausdrücklich benutzt. Das ist nur eine Lean-Brücke.
- Z. 917–925 und 690–718: Die Lean-Fassung von EK 3.7.8(b) braucht CompleteSpace/SecondCountable über dem Vorgänger, fact:fddconv verlangt nur „E separable“. Keine Folge, denn der einzige Verbraucher, rem:EKrelcompact, setzt E polnisch voraus.
- Z. 11955–11966: Dichtheit in der Supremumsnorm ist zu stark. fact:relcompact verlangt schon „dense in the topology of uniform convergence on compact sets“ (Z. 1523).
- Z. 8224 und 8372: q = 1 genügt nicht (EK Bem. 9.5(a)). eq:relcompact2 verlangt schon p ∈ (1,∞] (Z. 1546).
- Z. 12189–12213: Der Kompensator ist an jedem Pfad stetig. lem:EKconv sagt das schon (Z. 8998, Teil C3a: „The integral term is continuous at every ω“).
- Hawkes-Resolvente ohne ‖φ‖ < 1 (Z. 5868–5902): Das Manuskript (Z. 10480–10487) sagt ebenfalls „whatever its mass“. Der Weg per exponentieller Dämpfung ist nur eine Beweisvariante.
- Alle übrigen „Befund“-Abschnitte (Aldous-Faktor, Randterm am Basispunkt, twoJump-Zeuge, Fensterrand bei IsApproximable, ℝ-Supremum usw.) betreffen die Roadmap oder Lean-Aussagen. Das Manuskript formuliert diese Aussagen nicht.

Zahlen: gesamt 7 / erledigt 4 / offen 3 / unklar 0

---

## Ausschnitt 5

# Befunde am Manuskript aus INV_slice5.md

Ausschnitt: Läufe vom 2026-09-21 bis 2026-09-27. Die Donsker-, Brown- und Anwendungsläufe (Inventar-Z. 1–8363) enthalten keine Befunde am Manuskript, nur Befunde an Lean, Mathlib und den READMEs. Die Befunde beginnen mit den Dualitätsläufen vom 25.09. (Z. 8364 ff.). „Heute“ meint Zeilen in MS_current.tex.

---

### lem:calculus / eq:calcint — gemeinsame Meßbarkeit von γᵢ
- Lauf: 2026-09-25, fünfzehnter Lauf, Inventar-Z. 8468–8471
- Befund: `eq:calcint` sagt nichts über die gemeinsame Meßbarkeit von γᵢ, und Fubini braucht sie. Aus der absoluten Stetigkeit in jeder Variablen folgt sie nicht ohne weiteres.
- Lean-Beleg: `ae_sub_eq_integral_antidiagonal` (dort steckt sie in `IntegrableOn`)
- Heute: ERLEDIGT (Z. 7245: „set (γ₁,γ₂) = ∇Φ, jointly measurable“; Commit c5d60fc)
- Vorschlag: —

### thm:duality / eq:dual1 — Schranken beim eingefrorenen Wert des anderen Prozesses
- Lauf: 2026-09-25, siebzehnter Lauf, Befund 2, Inventar-Z. 8655–8667 (auch 8681–8682)
- Befund: Schritt 1 friert Y(t) = y ein und braucht die Integrierbarkeit bei festem y. `eq:dual1` gab die Majorante aber nur längs der Diagonale y = Y(t). Also gehören die Schranken in eingefrorener Form formuliert, oder Schritt 1 muß die Übertragung ausführen.
- Lean-Beleg: `duality`, `duality_augment` (Schranken `∀ y`, `∀ x`)
- Heute: ERLEDIGT (Z. 7284–7296: sup über y ∈ E₂ bzw. x ∈ E₁, „asked at a frozen value“; Schritt 1 in Z. 7340–7341). Nebenbei: Z. 7296–7297 hat einen Satzbruch („are automatic.“ gefolgt von „and“ vor `eq:dual2`).
- Vorschlag: nur den Satzbruch glätten.

### cor:atomless / eq:quantile — Atomlosigkeit für die Quantilformel nicht nötig
- Lauf: 2026-09-25, achtzehnter Lauf, vierter Teil, Befunde 1–2, Inventar-Z. 8900–8913
- Befund: `eq:quantile` gilt für jede Uhr (Monotonie, Stetigkeit von unten). Die Atomlosigkeit wird nur für Q(Q^←(z)) = z gebraucht, nicht vorab, wie der Beweis es anordnete.
- Lean-Beleg: `setIntegral_interval_eq_clockQuantile`, `le_clockQuantile_iff`, `clockTime_clockQuantile`
- Heute: ERLEDIGT (Z. 5716–5728: „For every clock, Q is nondecreasing and continuous from below … Atomlessness has not been used so far; it enters only now.“)
- Vorschlag: —

### cor:atomless / lem:calculus — lem:calculus wird auf [0,L]² angewandt, ist aber für den ganzen Quadranten ausgesprochen
- Lauf: 2026-09-26, Lauf 22:03 UTC (vom 25.), Inventar-Z. 9248–9259 (Vorgeschichte: Z. 8946–8954, dort als Lean-Voraussetzung „unendliche Masse“, später in Lean beseitigt)
- Befund: `lem:calculus` verlangt Φ auf [0,∞)² und `eq:calcint` für jedes T > 0. Der Beweis von `cor:atomless` wendet es „on [0,L]²“ an, wo Ψ nur dort erklärt ist. Das ist richtig, weil der Beweis bei jedem T nur [0,T]² liest, wird aber nicht gesagt. Die naheliegende Fortsetzung von Ψ jenseits L bricht (ein einzelner Randschnitt müßte integrierbar sein).
- Lean-Beleg: `integral_sub_eq_integral_antidiagonal_Icc`, `ae_sub_eq_integral_antidiagonal_Icc`, `duality_of_atomless` (ohne `hunb`)
- Heute: OFFEN (Z. 7242–7255 unverändert für [0,∞)²; Z. 5741: „So Ψ satisfies the hypotheses of Lemma lem:calculus on [0,L]²“)
- Vorschlag: an `lem:calculus` anhängen: „The proof reads Φ only on [0,T]²; so for Φ given on [0,L]² with eq:calcint at T = L, eq:calcconc holds for almost every t ∈ [0,L].“

### cor:atomless — Rückübersetzung auf q-fast jedes t fehlt
- Lauf: 2026-09-25, achtzehnter Lauf, fünfter Teil, Befund 2, Inventar-Z. 8955–8957; bekräftigt im Lauf 22:03 UTC, Inventar-Z. 9216–9221 (Befund 3) und 9257–9259
- Befund: Der Schluß „Ψ(L,0) = Φ(t*,0), Ψ(0,L) = Φ(0,t*)“ gibt die Aussage nur am Endpunkt t*. Die Behauptung „für fast jedes t“ braucht einen eigenen Schritt: Die Ausnahmemenge ist das Urbild einer Lebesgue-Nullmenge (samt Randpunkt Q(b)) unter Q und hat q-Maß 0, weil q|[0,b) das Bild von Lebesgue unter Q^← ist und Q∘Q^← = id gilt.
- Lean-Beleg: `duality_of_atomless`, `restrict_Iio_eq_map_clockQuantile`, `clockTime_clockQuantile_of_le`
- Heute: OFFEN (Z. 5741–5744 unverändert. Die Aussage in Z. 5711 lautet zudem „for Q-almost every t“, Lean hat `∀ᵐ t ∂q`.)
- Vorschlag: den Schluß des Beweises durch die Rückübersetzung ersetzen (Nullmenge N_b ∪ {Q b} unter Q zurückziehen, dann ℝ≥0 = ⋃ₙ[0,n)); in der Aussage „q-almost every t“ statt „Q-almost every t“ prüfen.

### lem:localmix(a) / rem:convexfree — Konvexität „ohne Voraussetzung“
- Lauf: 2026-09-25, Lauf 21:03 UTC, Inventar-Z. 9131–9141 (auch „(T2b), nicht ‚keine Voraussetzung‘“, Z. 9139–9141); 2026-09-26, Lauf 23:03 UTC, Befunde 1–2, Z. 9406–9431 und 9637; Lauf 18:03 UTC, Z. 11518–11535 (Zeuge), 11795
- Befund: (a) „M_loc ist konvex, keine Voraussetzung“ ist falsch, sogar bei rechtsstetiger Filtration. Der Beweisschritt „σₙ → ∞ Q-f.s.“ trägt nicht, und rem:convexfree zieht die Grenze an der falschen Stelle. Die Stelle Z. 10803 alt („only genuinely new proofs“) nannte (a).
- Lean-Beleg: `LocalMixWitness.not_convex`; Wahres: `isLocalMPSolution_add_of_isUniformLocalization`, `isLocalMPSolution_add_of_boundedJumps`
- Heute: ERLEDIGT (Vorgabe; nachgelesen: `lem:localmix` Z. 4703–4718 hat nur noch Mischungen unter (L1) und die Disintegration, `rem:convexfree` fehlt, Z. 10778 nennt nur noch `lem:L1auto` als „only genuinely new proof“)
- Vorschlag: —

### def:localizing (L1) / lem:L1auto — „eine Folge für alle Testprozesse“ vs. „je Testprozeß eine Folge“
- Lauf: 2026-09-26, Lauf 22:03 UTC, zweiter Teil, Befund 2, Inventar-Z. 9310–9326; Lauf 08:03 UTC, dritter Teil, Z. 10144–10147 (Vorschlag an den Nutzer)
- Befund: (L1) verlangt eine Folge τₙ ∈ Σ für alle Y° ∈ 𝓧°. `lem:L1auto` liefert aber mit Σ₀ = {τ^Y_n} je Testprozeß eine eigene Folge. Für unendliche Familien trägt kein Infimum, und das endliche Minimum liegt nicht in Σ₀. Die Behauptung „Σ₀ satisfies (L1)“ ist deshalb in der Fassung von (L1) nicht bewiesen. Die Fassung „je Testprozeß“ genügt allen Verbrauchern (`lem:localmix`, `lem:localrestart`, `thm:localuniq`).
- Lean-Beleg: `IsLocalizationForEach`, `isLocalizationForEach_of_boundedJumps` (beliebige Familien), `LocalizingSystemEach`; gleichmäßig nur endlich: `isUniformLocalization_of_boundedJumps`
- Heute: OFFEN (Vorgabe; nachgelesen: Z. 4644–4650 „Σ contains a sequence τ₁ ≤ τ₂ ≤ … with … for all Y° ∈ 𝓧°“; Z. 4747–4749 „Σ₀ … satisfies (L1)“; ebenso rem:localhyp Z. 4674–4676 „one sequence localizes every test process“)
- Vorschlag: (L1) auf „für jedes Y° ∈ 𝓧° eine Folge τ^{Y°}_n ∈ Σ mit …“ umstellen und rem:localhyp mitziehen. Dann ist `lem:L1auto` wörtlich richtig.

### lem:disint / eq:countabletest — Integrierbarkeit gehört in die Testbedingung
- Lauf: 2026-09-26, Lauf 23:03 UTC, Befunde 3–4, Inventar-Z. 9432–9441 und 9638
- Befund: Für ein Q, das noch nicht als Lösung bekannt ist, ist E^Q[(Y_t − Y_s) Z_s] nicht erklärt. Die Charakterisierung `eq:countabletest` muß also die Integrierbarkeit von Y_s, Y_t für die abzählbar vielen Daten enthalten. Nur diese Integrierbarkeit vererbt sich mit einer Nullmenge auf P(·|π₀ = x). Gebraucht wird außerdem nur die Richtung „⟸“.
- Lean-Beleg: `ae_isMPSolution_of_countableTest`, `ae_isLocalMPSolution_of_countableTest(_each)`
- Heute: OFFEN (Z. 3431–3437: „P ∈ Msol iff E^P[(Y_t − Y_s) Z_s] = 0 for all …“, ohne Integrierbarkeit; ebenso in `lem:localmix`(b), Z. 4712–4714)
- Vorschlag: „… if and only if Y°_s, Y°_t ∈ L¹(P) and eq:countabletest holds for all …“, oder nur „if“ fordern.

### lem:disint — π₀ muß 𝓕°₀-meßbar sein
- Lauf: 2026-09-26, Lauf 23:03 UTC, Befund 5, Inventar-Z. 9442–9444
- Befund: Der Beweis braucht, daß Z°_s h(π₀) 𝓕°_s-meßbar ist, also π₀ ∈ 𝓕°₀. Das wird stillschweigend benutzt. Auf dem Pfadraum ist es wahr.
- Lean-Beleg: `ae_isMPSolution_of_countableTest` (Hypothese `∀ i, Measurable[𝓕₀ i] π₀`)
- Heute: OFFEN (Z. 3446–3447: „the variable Z°_s h(π₀) is bounded and 𝓕°_s-measurable“, ohne Begründung)
- Vorschlag: Halbsatz „(π₀ is 𝓕°_0-measurable)“ einfügen.

### lem:localrestart — „By (L1)“ braucht (L1) für 𝓧°_r, gebraucht wird nur die Folge
- Lauf: 2026-09-26, Lauf 23:03 UTC, zweiter Teil, Befund 2, Inventar-Z. 9489–9495 und 9639
- Befund: Der Beweis beginnt mit „By (L1) it suffices …“. Das Lokalisierungssystem ist aber für 𝓧° gegeben, nicht für 𝓧°_r. Es genügt die Definition des lokalen Martingals: τₙ ↑ ∞ punktweise, Stoppzeiten, und Ŷ^{τₙ} ist ein R-Martingal.
- Lean-Beleg: `localRestart` (τ als eigenes Datum, ohne `IsUniformLocalization`)
- Heute: OFFEN (Z. 4853: „By (L1) it suffices to show that Ŷ^{°,τₙ} is an R-martingale …“)
- Vorschlag: „By the definition of a local martingale (τₙ ↑ ∞ pointwise), it suffices …“ statt „By (L1)“.

### def:restartkernel / cor:pastingmarkov — (E1) steht an der falschen Stelle; Meßbarkeit des Kerns in α
- Lauf: 2026-09-26, Lauf 23:03 UTC, vierter Teil, Befunde 1–2, Inventar-Z. 9595–9600 und 9640; präzisiert im Lauf 01:03 UTC, Befund 1, Z. 9697–9705 und 9832
- Befund: Für (R1) in der Fassung „Q_α-f.s. a_Tβ = a_Tα“ braucht die Definition (E1) nicht. Gebraucht wird (E1) erst in `cor:pastingmarkov`: Das Bildmaß überträgt eine f.s.-Aussage nur für ein meßbares Ereignis, und dafür braucht es meßbare Punkte. Auch die 𝓕°_T-Meßbarkeit des Kerns in α wird von `lem:pasting` nicht gebraucht, ein Kern auf (F, 𝓢) genügt. Das ist kein Fehler, nur eine überflüssige bzw. falsch plazierte Voraussetzung.
- Lean-Beleg: `IsRestartKernel`, `comp_apply_eq_of_isRestartKernel`, `isRestartKernel_concatKernel` (`[MeasurableSingletonClass F]`)
- Heute: OFFEN (Z. 5076–5077 „kernel … from (F, 𝓕°_T)“; Z. 5091–5093 „the diagonal is measurable because 𝓢 is countably generated and separating — which is (E1)“; `cor:pastingmarkov` nennt (E1) nicht)
- Vorschlag: (R1) als „Q_α-a.s.“ lesen und den (E1)-Satz von `def:restartkernel` nach `cor:pastingmarkov` verlegen. Optional: „kernel from (F, 𝓢)“ genügt.

### thm:localuniqueness — die Integrabilitätsbedingung von lem:pasting fehlt
- Lauf: 2026-09-26, Lauf 23:03 UTC, vierter Teil, Befund 3, Inventar-Z. 9601–9606
- Befund: Der Beweis wendet `lem:pasting` auf jedes P ∈ M(𝓧^{°,T}) an. Dafür braucht es ∫ E^{Q_α}|Y°_t| P(dα) < ∞ für eben dieses P, und der Satz nennt das nicht.
- Lean-Beleg: `hasLocalUniqueness_of_restartKernel` (Bedingung in `hkernel`)
- Heute: OFFEN (Z. 5171–5174: „Suppose that a restart kernel exists at every strict stopping time, and that …“)
- Vorschlag: „Suppose that at every strict stopping time there is a restart kernel satisfying the integrability of Lemma lem:pasting for every P ∈ M(𝓧^{°,T}).“

### lem:pasting (und cor:pastingmarkov) — „adapted, so a function of a_T“ braucht Progressivität
- Lauf: 2026-09-26, Lauf 23:03 UTC, vierter Teil, Befund 4, Inventar-Z. 9607–9610 und 9641; dazu Lauf 01:03 UTC, Befund 3, Z. 9718–9722
- Befund: Daß Y°_{u∧T} eine Funktion des gestoppten Pfades ist, ist die 𝓕°_T-Meßbarkeit des gestoppten Wertes. Die gibt die Progressivität (unter T2b), nicht die Adaptiertheit allein. Dieselbe Progressivität braucht `cor:pastingmarkov`, damit α ↦ (α_{T(α)}, T(α)) 𝓕°_T-meßbar ist und α ↦ P_{α_{T(α)},T(α)} ein Kern wird.
- Lean-Beleg: `isMPSolution_comp_of_isRestartKernel` (Hypothese `hYT`)
- Heute: OFFEN (Z. 5144–5146: „because Y° is adapted, so Y°_{u∧T} is a function of the path on T_{≤T}“)
- Vorschlag: „because Y° is progressively measurable (by (T2b), being càdlàg adapted), so Y°_{u∧T} is 𝓕°_T-measurable, i.e. a function of a_T“. In `cor:pastingmarkov` die Meßbarkeit von α ↦ (α_{T(α)}, T(α)) begründen.

### cor:pastingmarkov — a_T γ(α,β) = a_T α gilt nur bei β₀ = α_{T(α)}
- Lauf: 2026-09-26, Lauf 01:03 UTC, Befund 2, Inventar-Z. 9706–9713 und 9831
- Befund: Die Konkatenation auf dem càdlàg-Raum stimmt mit α auf [0,T(α)) überein. Den Wert bei T(α) liefert β₀. Also gilt a_Tγ(α,β) = a_Tα nur bei β₀ = α_{T(α)}, d.h. nur P_{α_r,r}-fast sicher. Wörtlich genommen ist der Beweis von (R1) falsch, sobald β₀ ≠ α_r.
- Lean-Beleg: `isRestartKernel_concatKernel` (Voraussetzung `hkeep`)
- Heute: OFFEN (Z. 5195: „agreeing with α before T(α)“; Z. 5205: „(R1) holds because a_Tγ(α,β) = a_Tα“)
- Vorschlag: Z. 5195 „agreeing with α on [0,T(α)) and, when β₀ = α_{T(α)}, on [0,T(α)]“, und in Z. 5205 „… = a_Tα for P_{α_r,r}-a.e. β, since β₀ = α_r a.s.“

### rem:jumpexplosion / thm:pathjumpMP(a) / Einleitung / rem:jumppoint — explosive Sprungprozesse sind keine lokalen Lösungen im Sinn von def:absMP und def:localizing
- Lauf: 2026-09-26, Lauf 01:03 UTC, zweiter Teil, Befunde 1, 2 und 4, Inventar-Z. 9777–9815 und 9828–9830; Lauf 08:03 UTC, vierter Teil, Z. 10186–10212 (Wortlautvorschläge, Definition auf [0,ζ))
- Befund: `def:absMP` und (L1) verlangen τₙ ↑ ∞ (bei (L1) punktweise), die Sprungzeiten wachsen aber gegen ζ, und ζ < ∞ hat positive Wahrscheinlichkeit. Für λ(n) = 2ⁿ gibt es nachweislich keine lokale Lösung, auch mit keiner anderen Folge. „localizing system in the sense of def:localizing“, „ssec:localmp applies verbatim“ und „genuine instance of (L1)–(L3)“ sind deshalb falsch. Ein lokales Problem auf [0,ζ) definiert das Manuskript nirgends. Wahr ist die Stufenaussage, und τₙ ↑ ζ gilt nur fast sicher. Nebenpunkt: In der Lean-Konstruktion sind die Sprungzeiten keine Stoppzeiten der rohen Filtration, `rateTime` schon.
- Lean-Beleg: `not_isLocalMPSolution_explode`, `not_isMPSolution_explode`, `martingale_stoppedProcess_rateTime_jumpProcessE`, `not_ae_mem_nonExplosiveE_explode`; neu: `IsLocalMPSolutionUpTo`, `jumpProcessE_isLocalMPSolutionUpTo`, `explode_isLocalMPSolutionUpTo`, `ae_tendsto_rateTime_explosionTimeE`; Nebenpunkt `not_isStoppingTime_min_jumpTimeE`
- Heute: OFFEN (Z. 8843–8851: „τₙ ↑ ζ; hence (τₙ) is a localizing system in the sense of def:localizing … Section ssec:localmp applies verbatim“; Z. 8874: „a genuine instance of (L1)–(L3)“; Z. 359–361: „the jump times are a localizing sequence by construction“; Z. 10351–10353 (`thm:pathjumpMP`(a)) und Beweis Z. 10432–10436: „(τ_m) is a localizing system, with (L1) holding by construction“)
- Vorschlag: In `ssec:localmp` eine Definition „lokales Problem auf [0,ζ)“ mit τₙ ↑ ζ f.s. ergänzen, parallel zu `def:absMP`. Z. 8843–8851 umschreiben, etwa: „There is then no solution of the global martingale problem, and none of the local one either: with f(n) = 1 − 2^{−n} one has Af ≡ 1/2 … What survives is the stopped statement: M^{τₙ} is a martingale for every n, i.e. X solves the martingale problem on [0,ζ).“ „applies verbatim“ streichen, Z. 8874 auf den nicht explodierenden Fall beschränken, Z. 360 und `thm:pathjumpMP`(a) entsprechend umstellen. UNKLAR bleibt, ob der Nebenpunkt zu den Sprungzeiten auch den kanonischen Pfadraum von `thm:pathjumpMP` trifft; das Manuskript argumentiert dort mit Rechtsstetigkeit auf dem Pfadraum, der Lean-Zeuge lebt auf dem Stichprobenraum.

### thm:localuniq auf beliebigem Ω — Voraussetzungen der Übertragung
- Lauf: 2026-09-26, Lauf 08:03 UTC, fünfter Teil, Inventar-Z. 10231–10247; Lauf 13:03 UTC, zweiter Teil, Z. 10894–10900 und 10935–10937
- Befund: Die Übertragung auf eine Lösung auf (Ω, 𝓖, P) braucht (1) die Adaptiertheit und Meßbarkeit der Pfadabbildung (laut Lauf „stillschweigend mit ‚X adaptiert‘“), (2) (L1) auf Ω gelesen und (3) für die Markov-Hälfte 𝓖_r ≤ Φ⁻¹𝓕°_r.
- Lean-Beleg: `map_eq_of_martingale_comp_localizingSystemEach`, `isMarkov_of_unique_onedim_local_of_le_comap`, `martingale_comp_stoppedProcess_supHittingTime`
- Heute: UNKLAR. (2) ist gedeckt: `def:localizing` Z. 4637–4641 sagt ausdrücklich, daß auf einem Umgebungsraum 𝓕° durch 𝔾 und Y° durch Y°(X) zu ersetzen ist, und das steht seit August (Commit bbda4b4). (3) ist nach Lage der Dinge ein Artefakt des Lean-Weges: Lean nimmt `localRestart` auf dem Pfadraum. `lem:localrestart` im Manuskript ist auf dem Umgebungsraum ausgesprochen (Z. 4836–4849), und dann braucht der Manuskriptbeweis die Bedingung nicht. (1) ist höchstens eine Formulierungsfrage.
- Vorschlag: allenfalls in `thm:localuniq` einen Halbsatz, daß auf einem Umgebungsraum (L1)–(L3) im Sinn von `def:localizing` gelesen werden und `lem:localrestart` in der Umgebungsfassung benutzt wird. Sonst nichts.

### thm:absstrongmarkov — erste Aussage im inhomogenen Fall falsch
- Lauf: 2026-09-26, Lauf 11:03 UTC, Inventar-Z. 10659–10670 und 10811–10814
- Befund: E[f(X(τ+t))|𝓖_τ] = E[f(X(τ+t))|X(τ)] ist im zeitinhomogenen Fall falsch, und diesen Fall ließ der Satz zu. Richtig ist das Bedingen auf (τ, X(τ)).
- Lean-Beleg: `StrongMarkovWitness.not_condExp_eq_state`, `isStrongMarkov_of_countable_range`
- Heute: ERLEDIGT (Teilung in (a) homogen, Z. 4400–4428, und (b) allgemein an abzählbarwertigen Stoppzeiten, Z. 4429–4447, „function of the pair (τ, X(τ))“; der Zeuge steht in `rem:strongmarkovscope`, Z. 4519–4531; Commit 1b552cb)
- Vorschlag: —

### thm:absstrongmarkov — abzählbarwertiger Fall braucht weder optional sampling noch Pfadregularität
- Lauf: 2026-09-26, Lauf 11:03 UTC, Befund 2, Inventar-Z. 10815–10817 (auch 10652–10654)
- Befund: Schritt 3 hängt nicht an den Schritten 1–2. Die Voraussetzungen „F ⊂ D_E“, „rechtsstetige Pfade“ und `eq:optafterint` gehören nur zur Aussage für allgemeines τ.
- Lean-Beleg: `isStrongMarkov_of_countable_range`
- Heute: ERLEDIGT (Pfadvoraussetzungen nur noch in (a), Z. 4403–4415; Z. 4491–4492: „neither optional sampling nor path regularity is used“)
- Vorschlag: —

### thm:absstrongmarkov — Chapman–Kolmogorov im inhomogenen Fall braucht die Verträglichkeit der Schiftsysteme
- Lauf: 2026-09-26, Lauf 14:03 UTC, zweiter Teil, Inventar-Z. 11046–11053 und 11078–11079
- Befund: „follows by applying the first assertion twice“ trägt im inhomogenen Fall nicht. `IsShiftSystem` bezieht jedes 𝓧°_r nur auf 𝓧°₀, und es fehlt die Konsistenz: (𝓧°_{r+u})_u muß ein Schiftsystem für 𝓧°_r sein.
- Lean-Beleg: `chapmanKolmogorov_of_unique_onedim` (homogen); später `IsShiftSystem.IsConsistent`, `chapmanKolmogorov_of_isConsistent`, `isConsistent_mpFamilyTime`
- Heute: ERLEDIGT (Z. 4442–4446: „If in addition the shift system is consistent …“; Beweis Z. 4500–4508; Begründung für `ex:shiftXA` in Z. 4533–4540. Der spätere Lauf 21:03 UTC vom 26., Z. 11989–11994, bestätigt: „Kein Befund am Manuskript“.)
- Vorschlag: —

### thm:absstrongmarkov — Adaptiertheit des verschobenen Pfades folgt nicht aus der Meßbarkeit von θ
- Lauf: 2026-09-26, Lauf 15:03 UTC, Inventar-Z. 11135–11143 und 11194–11197
- Befund: Der Beweis liest die 𝓖_{τ+s}-Meßbarkeit von X(τ+·). Die gemeinsame Meßbarkeit von (ω,r) ↦ θ_rω gibt nur die Meßbarkeit, nicht diese Adaptiertheit, und das Manuskript nannte sie nicht eigens.
- Lean-Beleg: Hypothese `hψadapt`; eingelöst durch `measurable_cadlagShift_stoppingTime`, `measurable_cadlag_eval_stoppingTime`
- Heute: ERLEDIGT (`eq:shiftadapt`, Z. 4409–4413; Beweis Z. 4467–4476; `rem:strongmarkovscope` Z. 4549–4555)
- Vorschlag: —

### thm:absstrongmarkov — Kernform braucht die Integrierbarkeit von lem:mixture für ∫P_x μ(dx)
- Lauf: 2026-09-26, Lauf 18:03 UTC, zweiter Teil (Tabelle E1), Inventar-Z. 11593 und 11608
- Befund: Die Kernform (in (a) und (b)) bildet R₂ = ∫ P_x μ_{F₀}(dx) und beruft sich auf `lem:mixture`. Das verlangt ∫ E^{P_x}|Y°_t| μ(dx) < ∞, und (a) nennt die Bedingung nicht. Für beschränkte Operatoren ist sie frei.
- Lean-Beleg: `isStrongMarkov_kernel_of_unique_onedim`, `isStrongMarkov_kernel_of_countable_range_of_bounded` (Hypothese `hKint`)
- Heute: UNKLAR (Z. 4398: „In the situation of Theorem thm:absuniq“, und `thm:absuniq` Z. 4176–4177 steht „subject to the integrability provisos of Lemmas lem:mixture and lem:restart“. Das deckt es sinngemäß, aber nicht ausdrücklich für die Familie (P_x) bzw. (P_{x,r}). Der Lauf 18:03 UTC las schon die geteilte Fassung (Commit 1b552cb, 17:36 UTC) und hielt den Punkt trotzdem für offen.)
- Vorschlag: in (a) und (b) beim Kern ergänzen: „with ∫ E^{P_x}|Y°_t| μ(dx) < ∞ for every μ ∈ Prob(E), Y° ∈ 𝓧°, t (automatic for bounded test processes)“.

---

Nicht aufgenommen, weil die Läufe sie selbst als Beobachtung ohne Fehler einstufen oder weil sie Lean, Mathlib oder READMEs betreffen:
- `cor:dualdiscrete`: Der Beweis nutzt nur die Erwartung (Z. 8427–8431).
- `thm:duality`, Schritt 1: Das Bedingen ist bei α = β = 0 mehr als nötig (Z. 8554–8557).
- T₂/T₄-Partitionen entbehrlich (Z. 8647–8653).
- `rem:dualnonmarkov`: Filtration des Zeugen, „all integrals assumed to exist“, Status (Z. 8737–8761, 8872–8874).
- „Uhr unendlicher Masse“ (Z. 8946): eine Lean-Voraussetzung, später in Lean beseitigt.
- `lem:localmix`, Halbsatz zur Progressivität unter (L1) entbehrlich (Z. 9449–9452).
- `T ∘ a_T = T` (Z. 9611–9614).
- Transport punktweise statt f.s. (Z. 9723–9727).
- `thm:uniqueness`-Instanz: E polnisch, `A ⊆ Cb × Cb` (Z. 11704–11718). (E2) verlangt ohnehin „separabel metrisierbar“.
- README-Befunde: „closed subset of ℝ“, `span`, `map`, `isDetermining_products` „jedes dichte D“, „progressiv zu keiner“.

Zahlen: gesamt 21 / erledigt 8 / offen 11 / unklar 2
