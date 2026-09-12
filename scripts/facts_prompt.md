Du arbeitest autonom und unbeaufsichtigt am **Formalisierungs-Inventar** des
Manuskripts `Journal/Blog/MartingaleProblem/MartingaleProblem.tex`. Du bist in
einem git-Worktree auf dem Branch `facts-inventory`. Zeitbudget: 120 Minuten.

## Vorrangige Aufgaben

*Erledigte Aufgaben stehen in `scripts/facts_prompt_archiv.md` und sind **nicht**
zu lesen; sie sind ausgelagert, damit dieser Auftrag der Auftrag bleibt und nicht
die Aktenlage. Die Ergebnisse stehen ohnehin in `Facts/INVENTAR.md`.*

### Aufgabe: `SkorokhodSpace` fertig, dann Meilenstein 4 von `MartingaleProblems` *(gestellt 2026-09-08 vom Nutzer)*

**Reihenfolge, vom Nutzer am 2026-09-10 abends neu festgelegt:**

> **D → F → C → E**

Ein Teil wird **nicht** angefangen, solange ein früherer offen ist. Teil D ist
ein einzelner Lauf und wird mit jedem Tag riskanter, deshalb steht er vorn; Teil
C, die pfadabhängige Variante, ist eine Kette und läuft danach ungestört.
(Die Teile A und B sind erledigt, siehe unten.)

~~**Teil B — `WeakConvergence` fertigmachen.**~~ *(erledigt 2026-09-09; die Datei
trägt kein `sorry` mehr, nur noch die eine bewußt gegen `upstream/master`
geschriebene Aussage. Einzelheiten im Archiv.)*

~~**Hinweis zu `martingale_stoppedProcess` in stetiger Zeit**~~ *(vom Nutzer,
2026-09-10; **eingelöst 2026-09-10, fünfzehnter Lauf des Tages** — der Satz steht,
über die dyadische Diskretisierung wie angesagt, aber **ohne** gleichgradige
Integrierbarkeit: die Fensterschranke des beschränkten Erzeugers macht den
Grenzübergang zu einer dominierten Konvergenz mit konstanter Majorante. Bericht in
`Facts/INVENTAR.md`, Läufe, „2026-09-10, fünfzehnter Lauf des Tages".)*

Der Beweis läuft über die **Approximation der Stoppzeit durch Stoppzeiten mit
abzählbarem Wertebereich**, also die dyadische Diskretisierung

$$\tau_n = 2^{-n}\lceil 2^n \tau\rceil,$$

die selbst Stoppzeiten sind, von oben gegen `τ` fallen, und für die das optionale
Sampling schon gilt (`Probability/Process/Stopping/OptionalSampling.lean:121`
und `:90` — sie stehen über beliebigem `[LinearOrder ι] [OrderTopology ι]`, also
über `ℝ≥0`). Dann Grenzübergang: die Rechtsstetigkeit der Pfade gibt
`X (τ n) → X τ` punktweise, die gleichgradige Integrierbarkeit macht daraus
$L^1$-Konvergenz, und die bedingten Erwartungen ziehen mit.

**Zwei Fundstellen, die den Weg stützen** — im Repo `RemyDegenne/brownian-motion`
(lokal unter `~/Code/lean/brownian-motion`, Lizenz geklärt, aber **kein Verweis
darauf in einer Roadmap**; lies und schreibe eigenen Beweis):

* `Martingale.ae_eq_condExp_of_isStoppingTime`
  (`BrownianMotion/StochasticIntegral/UniformIntegrable.lean:121`) —
  `stoppedValue X τ =ᵐ μ[X n | hτ.measurableSpace]` für `τ ≤ n`, über
  `[LinearOrder ι] [OrderBot ι] [OrderTopology ι] [FirstCountableTopology ι]`.
  Das ist der Baustein, aus dem die Stabilität folgt; dort ist er nicht
  ausgewertet.
* `Martingale.uniformIntegrable_stoppedValue_of_countable_range` (`:147`) mit
  einem ausdrücklichen `omit [Countable ι]` davor — also **abzählbarer
  Wertebereich der Stoppzeit** statt abzählbarem Index. Genau die Bauart, die
  hier gebraucht wird, und der Beleg, daß der Weg gangbar ist.

Die Aussage selbst — `Martingale (stoppedProcess X τ) 𝓕 P` in stetiger Zeit —
steht dort in **keiner** Fassung; ich habe danach gesucht. Sie bleibt also unsere
Arbeit und ist der fünfte Eintrag für `TODO.md` Punkt 8, sobald sie steht.

**Teil F — der Yule-Prozeß, und ein gemessener Vergleich zweier Wege.** Nach
Teil E. *(Vom Nutzer am 2026-09-10 vorgeschlagen; er darf vorgezogen werden, wenn
ein Lauf an Teil D oder E nicht weiterkommt.)*

Der lineare Geburt-Tod-Prozeß ist am 2026-09-10 über die **Reihe längs der
eingebetteten Kette** erledigt (`ae_mem_nonExplosiveE`,
`ae_mem_nonExplosiveE_linear`). Der Nutzer hatte einen anderen Weg genannt: nach
oben abschätzen durch den **reinen Geburtsprozeß** (Yule, `d ≡ 0`), dessen Wert
zu fester Zeit geometrisch verteilt und damit f.s. endlich ist. Auf Papier ist
das ein Einzeiler. Diese Aufgabe fragt, **was er in Lean kostet** — und sie fragt
es, weil die Roadmap derzeit bloß *behauptet*, die Reihe sei billiger.

**Es sind drei Wege, nicht zwei** *(vom Nutzer am 2026-09-10 ergänzt)*, und der
dritte ist vermutlich der beste:

> **Die Mastergleichung.** Setzt man in der schon bewiesenen
> Erwartungswertidentität
> `jumpMeasure_integral_sub_eq_intervalIntegral` die Testfunktion
> `h = indicator {n}`, so ist `p n t = 𝔼[h (X t)]` und
> `A h x = β (n−1) · 1_{n−1} x − β n · 1_{n} x`, also steht dort die
> Mastergleichung in integrierter Gestalt:
> `p n t = p n 0 + ∫₀ᵗ (β (n−1) · p (n−1) r − β n · p n r) dr`.
> Der Erzeuger bildet einen **Indikator auf eine endlich getragene und damit
> beschränkte** Funktion ab, obwohl `lam` unbeschränkt ist — dieselbe
> Beobachtung wie in der Bemerkung zur Domäne mit kompaktem Träger in
> `MartingaleProblems/README.md`. Der vorhandene Satz verlangt noch global
> beschränktes `lam`; die Abschwächung ist der erste Schritt und sollte über die
> lokalisierende Folge und die Dominierung durch `1` gehen.
>
> Gelöst wird induktiv über `n` mit dem integrierenden Faktor `exp (β n t)` —
> jeder Schritt eine skalare lineare ODE erster Ordnung — und heraus kommt
> `p n t = exp (−β t) · (1 − exp (−β t))^(n−1)`.
>
> **Und hier verschwindet die Zirkularität:** `∑ n, p n t = 1` ist dann eine
> geometrische Reihe, und *diese Gleichung ist die Nichtexplosion*. Man setzt sie
> nicht voraus, man erhält sie. Dieser Weg liefert also Verteilung **und**
> Nichtexplosion in einem, während der Kopplungsweg die Nichtexplosion braucht,
> um überhaupt von `X t` sprechen zu dürfen.

**Ein vierter Weg, und nach dem Befund des 150. Laufs der aussichtsreichste**
*(vom Nutzer am 2026-09-11 vorgeschlagen)*: **Momentenschranke und Grönwall.**

Der 150. Lauf hat gezeigt, daß `∑ k, p k t = 1` auf dieser Konstruktion
**voraussetzungslos** gilt — jenseits der Explosionszeit gibt `stepIndex` den
Müllwert, der Pfad sitzt an einem Zustand von `E`, und die entweichende Masse
wird mitgezählt. Jede Aussage über `X t` *selbst* ist deshalb blind für die
Explosion. Der Ausweg ist, nicht über `X t` zu reden, sondern über die
**Stoppzeiten**, die aus dem Pfad *vor* der Explosion gebildet sind — und die
gibt es schon: `rateTime lam n`, die Trefferzeiten des laufenden
Ratensupremums.

Der Weg, für den Yule-Prozeß `lam x = β * x`:

1. **Abschneiden der Testfunktion**, nicht der Rate: `h N x = min x N` ist
   **beschränkt**, also greift die vorhandene Erwartungswertidentität.
2. **Die Lyapunov-Ungleichung** `A (h N) x ≤ β * h N x` — nachrechnen, sie ist
   der ganze Inhalt: `β x (h N (x+1) − h N x) ≤ β x · 1_{x<N} ≤ β · h N x`.
3. **Grönwall** auf `m N t = 𝔼[h N (X t)]` gibt `m N t ≤ exp (β t)`,
   **gleichmäßig in `N`**. Mathlib hat es als `gronwallBound` und
   `norm_le_gronwallBound_of_norm_deriv_right_le`
   (`Analysis/ODE/Gronwall.lean`), also in der Ableitungsform — die
   Differentialform der Mastergleichung (`hasDerivWithinAt_jumpLaw`) ist damit
   der Anschluß.
4. **Markov auf dem gestoppten Prozeß** — und *das* ist der Schritt, der dem
   Müllwert entkommt:
   `P (rateTime lam N ≤ t) ≤ 𝔼[X (t ⊓ rateTime lam N)] / N ≤ exp (β t) / N → 0`.
   Weil `rateTime lam N` aus dem Pfad **vor** der Explosion gebildet ist, sieht
   diese Aussage die Explosion, anders als `tsum_jumpLaw_eq_one`.
   `mul_meas_ge_le_lintegral` steht in
   `MeasureTheory/Integral/Lebesgue/Markov.lean:50`.
5. Also `rateTime lam N → ∞` f.s., und das **ist** die Nichtexplosion.

**Warum das mehr ist als ein vierter Meßwert.** Der Reihenweg ruht darauf, daß
die Kette Nachbarschritte macht; dieser hier ruht auf `A f ≤ C · f` für *eine*
geeignete Funktion `f`, also auf einer Lyapunov-Bedingung. Das ist das
allgemeine Nichtexplosionskriterium und überlebt beliebige Sprungkerne. Wenn er
trägt, gehört er in den Meilenstein, nicht nur in den Vergleich.

**Zu prüfen, ehe gebaut wird:** die Erwartungswertidentität verlangt derzeit eine
globale Schranke an `lam`, die Yule nicht hat. Ob der Weg über den gestoppten
Prozeß oder über `truncRate` und einen Grenzübergang geht, ist die erste
Entscheidung — und sie ist zu begründen, nicht zu raten.

**Und der Satz, um den es dabei wirklich geht** *(Nutzer, 2026-09-11)*: nicht
Yule, sondern das **Lyapunov-Kriterium**. Trage es als eigenen Punkt in
Meilenstein 4 ein und beweise es *vor* den Instanzen:

> `isNonExplosive_of_lyapunov` — gibt es `f : E → ℝ≥0` meßbar, deren
> Subniveaumengen `{f ≤ N}` ausschöpfen, mit `A f ≤ C • f`, so explodiert der
> Prozeß f.s. nicht.

Der Beweis ist der oben beschriebene, aber **ohne Abschneiden von `f`**: mit
`τ N` = Trefferzeit von `{f ≥ N}` ist `f (X (t ⊓ τ N)) * exp (−C * (t ⊓ τ N))`
ein Supermartingal, also `𝔼[f (X (t ⊓ τ N))] ≤ f x₀ * exp (C t)`, und Markov gibt
`N * P (τ N ≤ t) ≤ f x₀ * exp (C t)`. Das Abschneiden `f ⊓ N` ist eine Abkürzung,
die nur bei **Nachbarschritten** trägt; bei weiten Sprüngen ist `f ⊓ N` nicht
mehr kontrolliert, und dann braucht man den gestoppten Prozeß.

**Die Instanzen fallen dann heraus**, jede in wenigen Zeilen:

* **Allgemeiner Geburt-Tod-Prozeß:** mit `f x = x` ist
  `A (f ⊓ N) x ≤ b x * 1_{x<N}`, denn der Todesterm ist **immer ≤ 0**. Die
  Bedingung ist also `b x ≤ C * x` — *die Geburtsrate wächst höchstens linear,
  die Sterberate ist frei*. Sie ist scharf: `b x = x^(1+ε)` explodiert.
* **Yule** (`b x = β * x`, `d ≡ 0`) ist der schlechteste Fall dieser Klasse,
  weil ohne Todesterm — und damit die richtige Probe.
* **Linear** (`b x = β * x`, `d x = δ * x`) ebenso.
* Und `rateSup`/`rateTime` aus dem lokalen Fall sind der Spezialfall `f = lam`;
  prüfe, ob sie sich als Instanz lesen lassen oder ob die Trefferzeiten anders
  gebildet sind.

**Was das für den bestehenden Reihenweg heißt:** `ae_mem_nonExplosiveE` ruht
darauf, daß die Kette Nachbarschritte macht. Er bleibt als Abkürzung stehen und
ist nicht falsch — aber im Vergleich am Ende gehört gesagt, daß er ein
Sonderfall des Lyapunov-Kriteriums ist und nicht ein gleichrangiger Weg.

Zu bauen, in dieser Reihenfolge — **Lyapunov, dann die Instanzen, dann
Mastergleichung, dann Kopplung**:

1. **Yule als Instanz:** `b x = β * x`, `d ≡ 0`, mit `jumpApply_yule` und
   `yule_isLocalMPSolution` als Spezialfall des schon bewiesenen
   `linearBirthDeath_isLocalMPSolution`. Das ist Buchhaltung und sollte billig
   sein; kostet es mehr als erwartet, ist das der erste Meßwert.
2. **Die Mastergleichung** wie oben, und daraus die eindimensionale Verteilung
   als Kontrolle gegen Bekanntes: von `1` gestartet ist `X t` geometrisch mit
   Parameter `exp (−β t)`. Das ist der Prüfstein wie `poissonMeasure` beim
   Poissonprozeß — ein Leser rechnet das Ergebnis gegen etwas nach, das nicht aus
   unserer Konstruktion stammt. Nimm die Nichtexplosion als Korollar mit.
3. **Die Kopplung**: eine gemeinsame Konstruktion, unter der der
   Geburt-Tod-Prozeß pfadweise vom Yule-Prozeß dominiert wird, und daraus die
   Nichtexplosion des ersten aus der des zweiten.

**Die Falle, und sie ist der Grund, warum das interessant ist.** „Zu fester Zeit
geometrisch verteilt, also f.s. endlich, also keine Explosion" ist **zirkulär**:
um von `X t` zu sprechen, muß der Prozeß bei `t` schon definiert sein. Sauber ist
erst `∑ k, P (X t = k) = 1` für den *minimalen* Prozeß — und das **ist** die
Nichtexplosion. Auf Papier sieht man das kaum; hier bricht ein Beweis genau
daran. Wenn Du auf die Zirkularität stößt, ist das kein Scheitern, sondern ein
Ergebnis, und es gehört so in den Bericht.

**Was gemessen und berichtet wird** — das ist der Zweck der Aufgabe, nicht der
Satz:

* Deklarationen und Zeilen je Weg (Reihe / Mastergleichung / Kopplung),
  getrennt gezählt;
* welche Mathlib-Bausteine jeder Weg brauchte und welche fehlten;
* an welcher Stelle der Kopplungsweg am teuersten war;
* und ein Satz Urteil: welcher Weg ist für **eine allgemeinere** Ratenfunktion
  der bessere, nicht nur für diese eine.

**Was nicht zählt:** den Kopplungsweg abzubrechen, weil der Reihenweg schon
dasteht. Der Vergleich ist die Aufgabe. Bleibt er stecken, dann mit benannter
Bruchstelle.

**Teil D — die Roadmaps gegen Mathlib `master` prüfen.** Nach Teil C, vor allem
anderen. Das ist Rückstaupunkt 5, vom Nutzer am 2026-09-10 vorgezogen.

Unsere vier `README.md` und die drei `Suggested.lean` zitieren Mathlib-Namen mit
**Datei und Zeile**. Die letzte Prüfung ist vom 2026-09-06; seither sind vier
Tage vergangen, und die Bibliothek bewegt sich. Eine Roadmap, die auf einen
Namen zeigt, den es nicht mehr gibt, ist schlimmer als eine, die schweigt.

Zu tun, in dieser Reihenfolge:

1. Frisches `upstream/master` holen und den Commit im Bericht **nennen**.
2. Jeden zitierten Namen prüfen: existiert er noch, heißt er noch so, steht er
   noch in der genannten Datei? Zeilennummern sind nachrangig — falsch ist ein
   verschwundener oder umbenannter *Name*, nicht eine verschobene Zeile.
3. Jede **Negativaussage** nachprüfen — „Mathlib hat X nicht". Davon stehen
   inzwischen viele in den Roadmaps und in `TODO.md` Punkt 8, und jede ist ein
   Versprechen an einen Leser. Ist eine inzwischen falsch, ist das der wertvollste
   Fund des Laufs.
4. Die drei `Suggested.lean` gegen v4.33.1 übersetzen (das ist unsere Bindung),
   und **zusätzlich** melden, welche Deklarationen auf `master` brechen würden,
   soweit das ohne Umbau erkennbar ist.

Was **nicht** zu tun ist: auf `master` umstellen. Wir sind an v4.33.1 gebunden,
und die eine bewußt gegen `master` geschriebene Aussage in
`WeakConvergence/Suggested.lean` bleibt, wie sie ist.

**Die Richtung, nach dem Baum des 24. Laufs** *(vom Nutzer am 2026-09-12
festgelegt; sie ersetzt die Suche nach der nächsten Eingabe)*

> **Ein so elementarer Prozeß braucht genau *eine* Filtration.**

**Präzisierung des Nutzers, 2026-09-12** — und sie berichtigt die erste Fassung
dieses Satzes: die Filtration der *Konstruktion* kann **nicht** die des Prozesses
selbst sein, weil er dabei noch nicht existiert. Sie ist notwendig die des
zugrundeliegenden Materials: `hawkesFiltration`, die Punktfiltration der
Sprungzeiten, die die Rekursion zurückgibt. Die ist hint-frei und existiert
immer.

**Was statt dessen zu zeigen ist, und zwar *nach* der Konstruktion:**

> `hawkesFiltration = naturalFiltration hawkesProcess`,
> also `⨆ s ≤ t, σ(X s) = 𝓕 t` — die **kanonische** Filtration des
> konstruierten Prozesses ist dieselbe.

Das ist der Satz, der die Sache in Ordnung bringt: er sagt, daß die Aufzeichnung
(welcher Sprung wann, und wohin) genau dieselbe Information trägt wie der Pfad.
Der Baustein dafür ist bewiesen — `hawkesProcess_eq_stepPath` —, denn ein
Treppenpfad bestimmt seine Sprungzeiten und umgekehrt. Trage ihn als eigenen
Punkt in Meilenstein 4 ein.

*Zum Zusammenhang mit dem Manuskript:* `ssec:notation` hält für rechtsstetige `X`
fest, daß `*𝓕^X_t = 𝓕^X_t = 𝓖_t`; Schritt 5 des Beweises von `thm:jumpMP` hat
genau davon Gebrauch gemacht. Im markovschen Fall stand es also schon da, im
pfadabhängigen fehlt es noch.

Das ist die Vorgabe, und alles Weitere richtet sich danach. Zwei Filtrationen
sind kein Entwurf, sondern ein Symptom: `hawkesJumpFiltration` trägt `hint` im
Argument seiner **Definition**, und `hint` ist nach dem Zeugen des 24. Laufs
(`φ = 1_(0,1]`, `T n = 1 − 1/n`) unerfüllbar. Die Zielaussage stünde über einer
leeren Voraussetzung.

**Der Weg:**

1. **Heben nach `ℝ≥0∞`.** `cumulativeRateF` wird `ℝ≥0∞`-wertig, so daß `Λ = ⊤`
   an einem explosiven Stichprobenpunkt **zulässig** ist. Dann verschwindet
   `hint` aus jeder *Definition*; `rateInverseE` ist schon `ℝ≥0∞`-wertig und
   braucht nichts dazu.
2. **Damit fallen die beiden Filtrationen zusammen** — nicht bloß vergleichbar,
   sondern gleich, wenn der Fixpunkt `jumpTimeFE_hawkesSelfRate` ohne `hint`
   gilt. Prüfe das zuerst; trägt es, so ist die Unvergleichbarkeit des 23. Laufs
   gegenstandslos und der Schnitt geht über der einen Filtration.
3. **Erst danach, und als Satz statt als Voraussetzung: die Rate ist fast sicher
   endlich.** `{ω : ∀ r, Λ r ω < ⊤}` ist genau die Nichtexplosionsmenge, und für
   die gibt es bereits `ae_mem_nonExplosiveE`-artige Kriterien. Was dort nicht
   reicht, bleibt getragene Hypothese (Volterra, siehe unten) — aber es steht
   dann *neben* der Aussage und nicht *in* einer Definition.

**Und der Punkt, auf den dabei zu achten ist** *(Nutzer, wörtlich: „auf die
Müllwerte muß man schon aufpassen")*: `⊤` in `ℝ≥0∞` ist **kein** Müllwert. Die
Müllwerte dieser Arbeit — `sInf ∅ = 0`, `x / 0 = 0`, `∫ f = 0` für
nichtintegrierbares `f`, `stepIndex = 0` jenseits der Explosion — **lügen**: sie
geben eine plausible Zahl, wo keine Antwort existiert, und haben sechsmal eine
Aussage still wahr gemacht. `Λ = ⊤` sagt die Wahrheit. Genau deshalb hat die
Hebung jedesmal getragen: sie ersetzt eine lügende Vorgabe durch eine ehrliche.

Beim Heben ist daher **jede** Stelle zu prüfen, an der bisher ein `0` für
„undefiniert" stand — sie ist entweder durch `⊤` zu ersetzen oder als bewußte
Wahl zu begründen. Stillschweigend darf keine bleiben.

**VORRANGIG, vor allem anderen in Teil C: den Abhängigkeitsbaum von
`hawkes_isLocalMPSolution` von unten aufschreiben** *(vom Nutzer am 2026-09-12
angeordnet)*

Seit dem 2026-09-11 haben **fünf Läufe hintereinander** gemeldet, es fehle „genau
eine Eingabe" — die Läufe 169, 171, 172, 173 und 177. Jede Meldung war im
Augenblick richtig, und jedesmal hat die letzte Eingabe eine neue erzeugt. Das
ist kein Vorwurf: die neuen Eingaben wurden beim Beweisen entdeckt, nicht
übersehen. Aber es heißt, daß der Baum tiefer ist, als er von oben aussieht, und
daß wir ihn von oben abarbeiten, statt ihn zu kennen.

**Also zuerst, und ehe irgendetwas weiterbewiesen wird:**

1. Schreibe den Abhängigkeitsbaum von `hawkes_isLocalMPSolution` **vollständig
   und von unten** auf — jede Aussage, die gebraucht wird, mit ihrem Status
   (bewiesen / offen / nicht formulierbar) und ihren eigenen Voraussetzungen.
   Nicht die, die Du als nächstes angehen willst, sondern **alle**.
2. Markiere bei jeder offenen, **woran** sie hängt: an einer Rechnung, an einer
   Entscheidung (welche Filtration, welche Stoppzeit), oder an der
   Nichtexplosion. Die Nichtexplosion ist bisher an **vier** Stellen aufgetreten
   — Rechtsstetigkeit des Testprozesses, Übertragung des ersten
   Sprungzeitgesetzes, Formulierbarkeit von `hawkesJumpFiltration`, und jetzt der
   Gültigkeitsbereich der Formel für die kumulierte Rate. Sammle sie an einer
   Stelle.
3. Sag am Schluß **eine Zahl**: wie viele Aussagen sind noch offen. Ist es eine,
   so beweise sie im selben Lauf. Sind es mehr, so ist die Liste das Ergebnis des
   Laufs, und der nächste arbeitet sie ab.

Der Baum gehört in `MartingaleProblems/README.md`, Meilenstein 4, als eigener
Abschnitt, **nicht** in den Laufbericht allein — er soll beim nächsten Mal
dastehen, statt neu erschlossen zu werden.

**Erst danach** gilt wieder, was unten steht.

**Zum Abschluß von Teil C — was bewiesen wird und was Voraussetzung bleibt**
*(vom Nutzer am 2026-09-11 festgelegt)*

Ziel ist `thm:pathjumpMP`**(a)**, der **lokale** Satz: der Prozeß löst das lokale
Martingalproblem auf `[0, ζ)`. Das Manuskript sagt dazu „No hypothesis beyond
Setting~\ref{set:pathjump} is needed", und das ist der billigere der beiden
Teile.

Teil **(b)**, der globale Satz, verlangt `𝔼[N t] < ∞`. **Diese Bedingung wird
getragen, nicht bewiesen** — als Hypothese der Aussage. Der Grund ist geprüft:
das Manuskript beweist sie für den linearen Hawkes-Prozeß über die
Erneuerungsgleichung `m = μ₀ + φ * m` und die **Volterra-Resolvente** eines
Kerns in `L¹_loc`, und davon hat Mathlib nichts — „volterra", „renewal",
„resolvent kernel", „Neumann series" geben **null Treffer**. Vorhanden ist die
Faltung (`Analysis/Convolution.lean`, 65 Sätze) und die Neumann-Reihe in einer
**normierten Algebra** (`NormedRing.inverse_one_sub`), die `‖φ‖ < 1` verlangt.
Der Volterra-Trick braucht das gerade nicht: man arbeitet auf `[0,δ]` kurz genug,
daß `∫₀^δ φ < 1`, und schreitet fort. Das ist eine Aussage über die
**Kausalität** des Kerns, nicht über eine Banachalgebra, und die Faltungsalgebra
der kausalen Kerne auf `[0,∞)` gibt es in Mathlib nicht.

**Also:** `hawkes_isLocalMPSolution` beweisen; die globale Fassung mit
`(hN : ∀ t, 𝔼[N t] < ∞)` als Hypothese hinschreiben und dabei im Doc-Kommentar
sagen, daß diese Hypothese für den linearen Fall wahr ist und woran ihr Beweis
hängt. **Keine** Volterra-Theorie anfangen — das wäre ein eigener Meilenstein.

**Und die Lokalisierung geht an der kumulierten Rate**, nicht an der Rate: mit
`σ N = rateInverse N` ist `{σ N ≤ t} = {Λ t ≥ N}` (`setOf_rateInverse_le`, schon
bewiesen), also eine Stoppzeit, und auf `[0, σ N]` ist
`|∫₀^(t ⊓ σ N) 𝒜ₛ f ds| ≤ 2‖f‖ N` **gleichmäßig in ω** — genau die Schranke,
die `martingale_stoppedProcess` verlangt und die die Rate selbst nicht hergibt,
weil `φ` nur lokal integrierbar und nicht beschränkt ist. Die Rate springt, die
kumulierte Rate ist stetig; deshalb trägt `rateTime` nicht und `rateInverse`
schon.

*Vermerke dabei die Abweichung:* `thm:pathjumpMP`(a) nennt die **Sprungzeiten**
`(τ n)` als lokalisierendes System. Die geben keine gleichmäßige Schranke — auf
`[0, τ n]` ist die kumulierte Rate `∑_{k<n} ξ k`, in `ω` unbeschränkt. Entweder
weicht die Formalisierung hier ab und nimmt `σ N`, oder es braucht eine Fassung
des gestoppten Martingalsatzes mit **gleichgradiger Integrierbarkeit** statt
gleichmäßiger Beschränktheit. Ersteres ist billiger und liegt fertig da; sag im
Bericht, was Du genommen hast.

**Teil E — Meilenstein 6 von `MartingaleProblems`.** Nach Teil D.

Der abstrakte Eindeutigkeitssatz `thm:absuniq`, und er hat in Lean **keine
einzige Deklaration**, während sein Unterbau — Meilenstein 5, `restart` — bewiesen
dasteht. Fünf Aussagen sind im `README.md` ausformuliert:
`isMarkov_of_unique_onedim`, `subsingleton_mpSolutions_of_unique_onedim`,
`eq_of_forall_onedim`, die klassische Fassung als Instanz, und `isStrongMarkov`.

Zwei Dinge, die dabei nicht verlorengehen dürfen:

* **Markov ist die Konklusion, nicht die Voraussetzung.** Ethier--Kurtz 4.4.1
  läuft andersherum und sitzt auf Hille--Yosida; das ist ausdrücklich nicht
  unsere Richtung (`rem:noch1`). Wer die Aussage so hinschreibt, daß sie Markov
  voraussetzt, hat einen anderen Satz.
* **Die Eindeutigkeit der eindimensionalen Verteilungen muß für *jeden* Shift
  `r` gelten**, nicht nur bei `r = 0` — die endlichdimensionalen Verteilungen
  werden über `restart` aus den geshifteten Problemen gebaut. Das
  Akzeptanzbeispiel dazu steht im Meilenstein und ist der Prüfstein.

**Teil C — Meilenstein 4 von `MartingaleProblems`, die Sprungprozesse.** Teil A
und Teil B sind beide durch (2026-09-09, dreizehnter und sechzehnter Lauf), also
gilt dieser Teil. Er ist damit der laufende Auftrag.

Der Grund, und er ist kein ästhetischer: **die Existenztheorie hat sonst keinen
Boden.** §`sec:Existence` des Manuskripts hat drei Zweige, und zwei davon sind
relativ — aus einem dualen Prozeß (`thm:exduality`; Meilenstein 12 ist
ausdrücklich *not to be attempted as stated*, weil Kolmogorov für überabzählbaren
Index fehlt) und aus Konvergenz (`thm:absconv`, das die Approximanten schon
voraussetzt). Der dritte, die Übergangshalbgruppe, ist durch `rem:noch1`
ausgeschlossen: kein Hille--Yosida, kein Kapitel 1 von Ethier--Kurtz. Bleibt
`thm:jumpMP`, und das ist die **einzige Konstruktion von Hand**. Ohne sie steht
in keiner der drei Dateien ein Prozeß, von dem in Lean bewiesen wäre, daß er ein
Martingalproblem *löst* — die Münze aus `AtomWitness` ist ein Gegenbeispiel, kein
Beispiel.

Der Meilenstein steht ausformuliert in `TauCeti/MartingaleProblems/README.md`.
Reihenfolge:

*Reihenfolge, auf Wunsch des Nutzers: erst das eigentliche Ziel, die Beispiele
danach.*

5. Der lokale Fall und die pfadabhängige Variante zuletzt; sie liefern die
   Beispiele für die Meilensteine 7 und 9. **Die Punkte 0 bis 4 sind durch, also
   ist dies der laufende Auftrag** (seit dem sechsten Lauf des 2026-09-10).
   ~~Der Befund des siebzehnten Laufs des 2026-09-09 gilt weiter und ist die
   erste Hürde: `x / 0 = 0` in Lean, also verläßt der Pfad einen Zustand mit
   `lam x = 0` sofort; der absorbierende Fall verlangt Sprungzeiten in
   `ℝ≥0∞`.~~ *(die Hürde ist genommen, 2026-09-10, siebter Lauf des Tages.)*
   Die drei Akzeptanzbeispiele darunter — M/M/1, linearer Geburt-Tod, Hawkes —
   gehören zu diesem Punkt, und der lineare Geburt-Tod ist das einzige, das den
   lokalen Zweig prüft.

   *(Die Zwischenstände des siebten bis sechzehnten Laufs vom 2026-09-10 stehen
   in `scripts/facts_prompt_archiv.md`. Was von ihnen noch gilt, ist in die
   beiden folgenden eingearbeitet; sie sind hier ausgelagert, damit dieser
   Auftrag nicht länger ist als die Arbeit.)*

   **Zwischenstand 2026-09-10, siebzehnter Lauf des Tages. Beide angesagten
   Schritte stehen, und die Identifikation ist stärker als angesagt.** Acht
   Deklarationen im neuen Abschnitt `LocalAssembly` von
   `TauCeti/MartingaleProblems/Suggested.lean`, die ganze Datei ohne einen Fehler
   durch `lake env lean` gegen v4.33.1, alle acht mit `#print axioms` auf
   `propext`, `Classical.choice`, `Quot.sound` geprüft, die Zahl der `sorry`
   bleibt bei neun. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-10,
   siebzehnter Lauf des Tages"; die Punkte stehen in
   `MartingaleProblems/README.md`, Meilenstein 4.

   `stoppedProcess_mpFamily_truncRate_eq` sagt, daß der gestoppte Testprozeß des
   lokalen und der des gestutzten Problems **dieselbe Funktion** sind — an *jedem*
   Stichprobenpunkt und nicht bloß fast sicher.
   `martingale_of_martingale_of_stopped` ist der Turmschluß, ohne jeden Bezug auf
   die Sprungkonstruktion, und `martingale_indicator_bot` zieht den Indikator, den
   `Locally` verlangt, durch ein Martingal hindurch.

   **Drei Befunde für den nächsten Lauf.**

   * **Die Nichtexplosion in `jumpProcessE_eq_truncRate_of_le_rateTime` wird nicht
     gebraucht** (`jumpProcessE_truncRate_eq_of_rate_le`,
     `jumpProcessE_eq_truncRate_of_le_rateTime'`). Sie benannte nur ein Fenster;
     wo es keines gibt, liegt jede Sprungzeit unter `t` und beide Stufenindizes
     werden aus derselben Folge gerechnet. Das ist es, was die Identifikation der
     gestoppten Testprozesse zu einer Gleichheit von **Funktionen** macht — und
     `StronglyAdapted` wie `IsStoppingTime` sind keine f.s.-Aussagen.
   * **Die Zusage „die Adaptiertheit ist kein eigener Schritt" ist falsch, und der
     Grund ist kein Formfehler.**
     `isStronglyProgressive_mpFamily_jumpProcessE` trägt die Schranke
     `∀ x, lam x ≤ L`, die der lokale Fall nicht hat, und die Schranke ist dort
     keine Bequemlichkeit: für unbeschränkte Rate ist der **ungestoppte**
     Testprozeß an einem explosiven Stichprobenpunkt nicht rechtsstetig, weil
     `∫_0^{T_∞} lam(X_u) du = ∑_k ξ_k = ∞` ist und Bochner den Müllwert `0`
     zurückgibt. Der **gestoppte** hat den Defekt nicht — unter `rateTime lam n`
     ist die Rate längs des Pfades unter `n` —, also ist die Aussage über ihn zu
     führen: `stronglyAdapted_stoppedProcess_mpFamily_jumpProcessE`, und sie ist
     die **einzige** noch fehlende Eingabe von `jumpProcess_isLocalMPSolution`.
     Der Weg steht ausgeschrieben im Laufbericht und in
     `MartingaleProblems/README.md`, Meilenstein 4: der erste Summand über
     `measurable_uncurry_jumpProcessE` und `IsStoppingTime.measurable_of_le`, der
     Kompensator über den abgeschnittenen Integranden
     `g(u, ω) = {ofReal u < τ ω}.indicator (fun _ ↦ p.2 (X_u ω))`, der durch
     `2·n·C` beschränkt ist.
   * **`Clock` trägt seinen `MeasurableSpace` als Feld und nicht als Instanz.**
     `measurableSet_Ioc` scheitert gegen `lebesgueClock.q` an
     `OpensMeasurableSpace ℝ≥0`, weil die Instanzensuche syntaktisch ist; zu
     nehmen ist `Clock.measurableSet_interval`, und das Fenster erst *danach* in
     ein `Set.Ioc` umzuschreiben.

   **Zwischenstand 2026-09-10, achtzehnter Lauf des Tages.
   `jumpProcess_isLocalMPSolution` steht** — die erste in Lean bewiesene
   **lokale** Lösung eines Martingalproblems, und es ist Mathlibs `Locally` und
   kein eigener Begriff. Vier Deklarationen im neuen Abschnitt `LocalSolution`
   von `TauCeti/MartingaleProblems/Suggested.lean`, die ganze Datei ohne einen
   Fehler durch `lake env lean` gegen v4.33.1, alle vier mit `#print axioms` auf
   `propext`, `Classical.choice`, `Quot.sound` geprüft, die Zahl der `sorry`
   bleibt bei neun. Bericht in `Facts/INVENTAR.md`, Läufe, „2026-09-10,
   achtzehnter Lauf des Tages"; die Punkte stehen berichtigt in
   `MartingaleProblems/README.md`, Meilenstein 4. Voraussetzungen:
   `Measurable lam`, `∀ x, 0 < lam x`, und f.s. Nichtexplosion unter
   `jumpMeasure mu nu`; über `E` steht nichts als `[MeasurableSpace E]`.

   **Drei Befunde.**

   * **Die angesagte Schranke `2·n·C` wird nicht gebraucht, und das ist der
     Grund, aus dem der Satz geht.** `stronglyMeasurable_integral_comp` fragt
     nach **gemeinsamer Meßbarkeit** und nach nichts sonst. Zu leisten ist statt
     dessen die Umschreibung „ein Fenster mit **zufälligem oberen Ende** ist ein
     Fenster **fester Länge** mit abgeschnittenem Integranden": eine Zeile
     Mengenalgebra (`Set.Ioc ⊥ i ∩ Set.Iic (σ ω) = Set.Ioc ⊥ (σ ω)` für
     `σ ω = (min i (τ ω)).untopA ≤ i`) und `setIntegral_indicator`. Die
     Abschneidemenge liegt in `Borel ℝ≥0 ⊗ 𝓕 i` genau deshalb, weil `min i τ` —
     anders als `τ` — für die Vergangenheit bei `i` meßbar ist. Das ist die ganze
     Rolle der Stoppzeit im Beweis, und deshalb steht über der Rate nichts als
     ihre Meßbarkeit.
   * **`ENNReal` und `WithTop ℝ≥0` sind für `rw` nicht dasselbe.**
     `stoppedProcess` und `Locally` leben über `WithTop ι`; schreibt man
     `(⊥ : ENNReal)`, so ist die Aussage definitionsgleich, aber `rw` und `simp`
     finden das Muster nicht („not type-correct under the `implicit`
     transparency level"). `exact` findet es. **Nicht am Ziel rewriten, sondern
     das Ziel mit `exact` treffen**; hier fiel dabei
     `stoppedProcess_indicator_comm` ganz weg, weil
     `stoppedProcess (fun i ↦ S.indicator (Y i)) τ` und
     `fun i ↦ S.indicator (stoppedProcess Y τ i)` definitionsgleich sind.
   * **Die Stufe `n = 0` ist billiger zu umgehen als zu behandeln.** Genommen ist
     die **verschobene** Folge `fun n ↦ rateTime lam (n + 1)`; eine Teilfolge
     einer lokalisierenden Folge ist eine (drei Zeilen), und die Stufe, an der
     `truncRate lam 0 = 0` jeden beschränkten Satz aussperrt, kommt nicht vor.

   **Die Leerheitsprobe ist mitgemacht** (`poissonProcess_isLocalMPSolution`,
   `ae_mem_nonExplosiveE_poisson`): jede der drei Voraussetzungen auf Daten
   eingelöst, die Nichtexplosion an *jeder* Kette, weil die Rate konstant ist und
   das Kriterium die Divergenz von `∑ 1` wird. Was sie **nicht** vorführt, ist
   eine **unbeschränkte** Rate — der Fall, für den der lokale Zweig existiert.
   Sie ist ein Beleg gegen Leerheit und keiner für Schärfe; das steht so an der
   Deklaration.

   **Was von Punkt 5 jetzt noch fehlt, und es ist eine einzige benannte Aussage:
   `jumpProcessE_isMPSolution` unter `0 ≤ lam ≤ L` statt `0 < lam ≤ L`.** Die
   **lineare Geburt-Tod-Kette**, das einzige Akzeptanzbeispiel, das den lokalen
   Zweig prüft, wird von `jumpProcess_isLocalMPSolution` **nicht** erreicht: ihre
   Rate `b x + d x` ist am absorbierenden Zustand `0` gleich `0`
   (`birthDeathRate_linear_zero`), und der Satz verlangt `∀ x, 0 < lam x`. Das
   ist genau der Defekt, für den `jumpProcessE` gebaut wurde; die Konstruktion
   trägt ihn, der Satz noch nicht.

   Die Voraussetzung wird **an einer einzigen Stelle** geerbt:
   `jumpProcessE_isMPSolution` ist über `clipWait` vom alten Prozeß übertragen,
   und `jumpProcessE_eq_jumpProcess_clipWait` identifiziert die beiden
   Konstruktionen nur bei durchweg positiven Haltezeiten; über `truncRate_pos`
   und `martingale_stoppedProcess_mpFamily_jumpProcessE` wandert `0 < lam` von
   dort bis in den Zusammenbau. Alles andere — die Adaptiertheit, der
   Turmschluß, `jumpFiltrationE_inter_lt_rateTime`,
   `stoppedProcess_mpFamily_truncRate_eq`, `isLocalizingSequence_rateTime` —
   verlangt sie **nicht**. Der neue Beweis ist darum von vorn zu führen und nicht
   noch einmal zu übertragen: der absorbierende Zustand ist gerade der Punkt, an
   dem die beiden Konstruktionen auseinandergehen. Die Stelle, an der der alte
   Beweis seine Positivität verbraucht, ist die Erneuerungszerlegung am ersten
   Sprung (`jumpMeasure_integral_eq_of_firstJump`): dort ist die erste Sprungzeit
   `ofReal (xi 0) / ofReal (lam x)`, bei Rate `0` also `⊤` statt einer reellen
   Zahl. Der Erzeuger ist dort ebenfalls `0`, die zu zeigende Martingalgleichung
   an einem absorbierenden Zustand also `E[f (X t)] = f (X 0)` — richtig, aber
   eigens zu zeigen. Danach fällt die lineare Kette durch Einsetzen:
   `jumpApply_birthDeath`, `isMarkovKernel_birthDeathKernel` und
   `ae_mem_nonExplosiveE_linear` stehen alle schon.

**Weitere Akzeptanzbeispiele, wenn die Konstruktion steht.** Alle drei sind
*Einsetzen von Daten*, kein neuer Beweis, und jedes prüft einen anderen Zweig:

* ~~**M/M/1**, `b ≡ β`, `d x = δ * 1_{x ≥ 1}` auf `E = ℕ`. Beschränkt, also
  greifen `thm:jumpMP` und `exists_unique_of_bounded` unmittelbar.~~ *(erledigt
  2026-09-10, neunter Lauf des Tages: `jumpApply_mm1`, `mm1_isMPSolution`,
  `martingale_compensated_mm1` — die erste Lösung mit zustandsabhängigem
  Erzeuger.)*
* **Linearer Geburt-Tod**, `b x = β * x`, `d x = δ * x`. Hier ist
  `λ̄ = ∞`, der Satz greift **nicht**, und das Beispiel prüft als einziges den
  lokalen Zweig samt Nichtexplosionskriterium (`∑ 1/(β n)` divergiert). Der
  Yule-Prozeß `δ = 0` fällt als Sonderfall ab und hat geschlossene
  eindimensionale Verteilungen — geometrisch —, also eine unabhängige Kontrolle
  wie `poissonMeasure` beim Poissonprozeß.
* **Hawkes**, prädiktables `Λ(t, ω) = ν + ∫_0^{t-} h(t-s) dN_s`, das
  nicht-markovsche Beispiel und die Instanz von `ex:hawkes`. Es gehört zur
  pfadabhängigen Variante und kommt zuletzt.

~~In jedem Fall zuerst der Erzeuger als Rechnung: für Geburt-Tod kürzt sich `λ`
heraus und es muß `A f x = b x * (f (x+1) - f x) + d x * (f (x-1) - f x)`
herauskommen.~~ *(gerechnet 2026-09-10, neunter Lauf des Tages,
`jumpApply_birthDeath`: es kommt heraus, wie es soll, also kein Befund gegen
`set:jumpdata` — wohl aber einer über den Kern am absorbierenden Zustand, siehe
den Zwischenstand zu Punkt 5.)*

**Was zählt:** eine in Lean bewiesene Lösung eines Martingalproblems. **Was nicht
zählt:** ein Prädikat, das sagt, was eine Lösung wäre.

## Worum es geht

Die 29 mit `\begin{fact}` ausgezeichneten Aussagen des Manuskripts sind seine
Voraussetzungsfläche — alles, was zitiert und nicht bewiesen wird. Sie müssen
alle formalisiert sein, damit die Formalisierung des Manuskripts überhaupt
aufgeht. `Journal/Blog/MartingaleProblem/Facts/INVENTAR.md` hält je Fact fest,
ob er in Mathlib liegt, von einer der vier Roadmaps unter
`Journal/Blog/MartingaleProblem/TauCeti/` abgedeckt wird, oder eine Lücke ist.

## Zuerst

Lies `Facts/INVENTAR.md` ganz, dann `git log --oneline -15`. Nimm dir die
Zeilen mit Status `?` vor, in der Reihenfolge der Spalte **tragend**
(absteigend). Ein Lauf schafft vielleicht zwei bis vier Facts gründlich — das
ist besser als zehn oberflächlich.

## Je Fact

1. Lies die Aussage im Manuskript nach, ganz. Nicht den Titel, den Wortlaut.
2. Stelle fest, ob Mathlib sie hat. Der Worktree hat kein `.lake`; die
   Mathlib-Quellen sind über `--add-dir` erreichbar, unter
   `~/Code/lean/journal/.lake/packages/mathlib/Mathlib` (v4.33.1) und
   `~/Code/lean/mathlib4` — dort aber **nicht der Arbeitsbaum**. Die
   Rangfolge der Quellen, und sie ist wichtig:

   * **`git show upstream/master:Mathlib/...`** in `~/Code/lean/mathlib4`.
     `upstream` zeigt auf `leanprover-community/mathlib4` und ist aktuell.
     Das ist die maßgebliche Quelle für Aussagen über master, worauf Tau Ceti
     aufsetzt. `git grep <Begriff> upstream/master -- Mathlib/` sucht darin,
     ohne etwas auszuchecken.
   * `~/Code/lean/journal/.lake/packages/mathlib/Mathlib` — Release v4.33.1,
     ein brauchbarer Stellvertreter und bequem zu durchsuchen, aber ein
     Release und nicht master.
   * **Nicht benutzen: der Arbeitsbaum von `~/Code/lean/mathlib4`.** Er steht
     auf dem PR-Branch des Nutzers, ist vom März 2026 und über fünftausend
     Commits hinter master — älter als der `.lake`-Release. `origin` dort ist
     der Fork des Nutzers und ebenfalls veraltet; `origin/master` ist **nicht**
     master.

   `gh api`/`gh search code` bleibt zulässig, ist aber langsamer als
   `git show upstream/master:` und nur nötig, wenn `upstream` nicht frisch
   geholt ist (`git fetch upstream master`). Suche
   **nach der Aussage, nicht nach unserer Vokabel**: Mathlib nennt Dinge oft anders, als das Manuskript sie nennt.
   Am 2026-08-29 kostete genau das drei Fehler — `Locally` statt „local
   martingale", `IsStronglyProgressive` statt `ProgMeasurable`,
   `upcrossingsBefore` statt `upcrossing`. Prüfe für jeden gefundenen Namen,
   dass er als Deklaration existiert und **nicht `deprecated`** ist.
3. Trage den Status mit Beleg ein. Ohne Beleg gilt `?`, nicht `Mathlib`.
4. Ist es eine **Lücke**, so trage sie als benannten Punkt in den passenden
   Meilenstein der passenden Roadmap ein — mit der Aussage, worauf sie ruht,
   und in Mathlibs Namenskonventionen. Passt sie in keinen Meilenstein, lege
   einen neuen an. Halte die Formatregeln von Tau Ceti ein: keine Lücken, keine
   konditionale Sprache („optional", „später", „blockiert durch"), zeitlos,
   vollständige Grundtheorie je Objekt.
5. Deckt eine Roadmap den Fact schon ab, nenne den Meilenstein in der Spalte
   Beleg — und prüfe bei der Gelegenheit, ob das dortige Zitat noch stimmt.

## Stehende Regel: minimale Voraussetzungen

Eine Roadmap-Aussage trägt **die schwächsten Hypothesen, unter denen sie gilt**,
nicht die bequemsten. Reicht separabel metrisch, steht dort nicht polnisch;
reicht messbar, steht dort keine Topologie. Der Maßstab ist das Manuskript: es
führt in §2 die Bündel \eqref{E0}–\eqref{E3} und \eqref{T0}–\eqref{T4} genau
dafür, und jede Aussage dort ist mit dem Bündel annotiert, das sie wirklich
braucht. Übernimm diese Annotation, statt sie neu zu erraten.

Wo eine Roadmap heute mehr verlangt als das Manuskript, ist das ein Befund und
gehört korrigiert. Wo das Manuskript selbst mehr verlangt, als der Beweis
braucht, gehört es unter „Offene Auffälligkeiten" — das Manuskript wird von
diesen Läufen nicht geändert.

Umgekehrt gilt: eine Abschwächung wird **belegt**, nicht vermutet. Wer
„polnisch" durch „separabel metrisch" ersetzt, nennt die Stelle, an der die
Vollständigkeit im Beweis nicht mehr vorkommt. Prohorovs Satz zum Beispiel
braucht sie in der Rückrichtung; der Satz von der stetigen Abbildung nicht.

## Wie geschrieben wird, damit ein Abbruch nichts kaputt macht

Ein Lauf kann jederzeit abgeschnitten werden — von der Nutzungsgrenze, vom
Zeitlimit. Zwei Vorkehrungen, beide aus echten Ausfällen gelernt:

1. **Schreibe in Dateien, nicht in lange Antworten.** Am 2026-09-03 starb ein
   Lauf an `Claude's response exceeded the 64000 output token maximum` und
   hinterließ nichts. Halte einzelne Antworten kurz und lege Ergebnisse
   fortlaufend in `Task23/PROTOKOLL.md`, `Facts/INVENTAR.md` oder eigenen
   Dateien ab, sobald sie feststehen. Eine Abschlusszusammenfassung am Ende ist
   ein Absatz, kein Bericht — der Bericht steht in den Dateien.

2. **Hinterlasse nichts, was auf Ungeschriebenes verweist.** Derselbe Ausfall
   hinterließ ein Prüfskript, das sich auf einen „Beweis des zwanzigsten Laufs"
   berief, den es nicht gab, und das wegen einer toten Platzhalterzeile nicht
   einmal startete. Die Reihenfolge ist daher: erst der Protokolleintrag mit
   dem Ergebnis, dann das Skript, das darauf zeigt. Ein Skript muss allein
   lauffähig sein; ein Zwischenstand, der abbricht, soll lieber weniger
   dastehen lassen als etwas Widersprüchliches.

## Lean übersetzen — das geht, entgegen dem, was frühere Läufe notiert haben

Mehrere Läufe haben Rückstaupunkte mit „wartet auf `.lake`" liegen lassen. Der
Worktree hat wirklich kein `.lake`, aber das ist keine Blockade: der
Hauptcheckout hat ein **fertig gebautes Mathlib** (v4.33.1), und

```
lake env lean <absoluter Pfad zur Datei>
```

typprüft **jede** Datei dagegen — auch eine im Worktree. Es schreibt nichts,
weder in den Worktree noch in den Hauptcheckout, und braucht keinen Build. Am
2026-09-05 geprüft; ein Durchlauf über
`TauCeti/WeakConvergence/Suggested.lean` meldete echte Fehler (fehlende
`TopologicalSpace (ProbabilityMeasure E)`-Instanz, fehlender Import für die
`→ᵇ`-Notation, eine Universenbedingung).

Der Hauptcheckout `~/Code/lean/journal` ist dafür über `--add-dir` erreichbar
und `lake`, `lean`, `elan` sind freigegeben. **Dort wird nur gelesen und
übersetzt, niemals geschrieben** — er steht auf `master`, und eine Änderung dort
landet außerhalb Deines Branches. Geht `lake env lean` in Deinem Lauf trotzdem
nicht, so prüfe das mit `lean --version` als erstes, halte es im Bericht fest
und arbeite mit Signaturprüfung am Quelltext weiter, statt Übersetztes zu
behaupten.

Damit gilt: **wer Lean schreibt, übersetzt es auch.** Eine Deklaration, die
nicht durch `lake env lean` geht, ist kein Ergebnis, sondern ein Entwurf, und
gehört als solcher gekennzeichnet. `sorry` ist erlaubt, wo die Aussage die
Arbeit ist; ein Fehler in der *Aussage* ist es nicht. Der erste Durchlauf einer
großen Datei dauert einige Minuten, weil Mathlib geladen wird — das ist normal
und im Zeitbudget vorgesehen.

## Regeln, die nicht verhandelbar sind

1. **Nichts aus dem Gedächtnis.** Jeder Mathlib-Name wird am Quelltext belegt.
2. **Das Manuskript wird nicht verändert.** Du arbeitest an `Facts/INVENTAR.md`
   und an den Roadmaps. Fällt Dir am Manuskript etwas auf, schreibe es unter
   „Offene Auffälligkeiten" ins Inventar.
3. **Nur dieser Branch.** Kein Wechsel auf `master`, kein Force-Push. Der
   Runner committet und pusht selbst, und er zieht zu Beginn jedes Laufs
   `origin/master` nach — Du arbeitest also immer auf aktuellem Stand.
   **Ob der Branch nach `master` wandert, entscheidet der Nutzer, nicht der
   Lauf.** Das ist die Stelle, an der ein Mensch die Vorschläge prüft, und sie
   wird nicht wegautomatisiert.
4. **Kein Vortäuschen.** Ein Fact, dessen Lage Du nicht klären konntest, bleibt
   `?` mit einer Notiz, woran es lag. Das ist ein gutes Ergebnis.

## Am Ende jedes Laufs, verpflichtend

Hänge an `Facts/INVENTAR.md` unter „Läufe" einen Abschnitt mit Datum an:
welche Facts bearbeitet wurden, was der Befund war, was offen blieb. Und
**mindestens ein konkreter Vorschlag, was als Nächstes formalisiert werden
soll** — als benanntes Ziel, nicht als Richtung: eine Aussage, worauf sie ruht,
warum sie jetzt dran ist. Ist der Vorschlag reif, trage ihn direkt in die
betreffende Roadmap oder in `PLAN.md` ein, auf diesem Branch.

## Es gibt immer Arbeit

Ein Lauf endet **nie** mit „nichts zu tun". Die Reihenfolge:

1. die vorrangigen Aufgaben oben, falls welche dastehen;
2. Zeilen mit Status `?` im Inventar;
3. `Journal/Blog/MartingaleProblem/Facts/BACKLOG.md`, von oben nach unten;
4. Task 23, siehe unten.

Kommst Du bei einem Punkt nicht weiter, gehst Du zum nächsten und schreibst in
den Bericht, woran es lag. Ist der Rückstau leer, hänge selbst einen Punkt an —
etwas, das Dir beim Lesen als reif aufgefallen ist, mit derselben Begründung,
die auch ein Vorschlag am Ende eines Laufs tragen muss.

## Wenn das Inventar vollständig ist

Sind alle 29 Zeilen belegt, wechselst Du zu **Task 23** — dem Beweis der
Dualitätsidentität für eine rein atomare Uhr. Auftrag, Modell, Stand und
Sackgassen stehen in `Journal/Blog/MartingaleProblem/Task23/PROTOKOLL.md`, das
Orakel in `Task23/oracle.py`. Dieselben Regeln gelten; das Manuskript darf
dann angefasst werden, aber erst wenn ein Beweis vollständig und verifiziert
ist, und danach muss `python3 Journal/Blog/MartingaleProblem/check.py` `clean`
melden.
