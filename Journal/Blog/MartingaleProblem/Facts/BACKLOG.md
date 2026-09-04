# Rückstau

Damit nie ein Lauf ohne Arbeit dasteht. Der Prompt schickt einen Lauf hierher,
wenn die vorrangigen Aufgaben leer sind, das Inventar geschlossen ist und Task 23
gerade nicht weiterkommt. **Von oben nach unten**; wer einen Punkt erledigt,
streicht ihn hier und berichtet im Inventar unter „Läufe".

Wer einen Punkt für erledigt hält, ohne ihn erledigt zu haben, schadet mehr als
ein Lauf, der nichts tut. Im Zweifel: Punkt stehen lassen, Zwischenstand
anhängen.

**Der \EK{}-Scan ist erreichbar**, entgegen einer Notiz vom 2026-08-31. Er liegt
nicht im Worktree, sondern unter
`/home/pfaffelh/Code/lean/journal/references/EthierKurtz1986.pdf`, und das
`Read`-Werkzeug liest ihn mit `pages`. Der Seitenversatz ist **+10**:
Buchseite $n$ ist PDF-Seite $n+10$. Am 2026-08-31 geprüft an den Buchseiten
102--104, 111--116, 126--133 und 142--145.

## Offen

1. **Task 23, was sonst offen bleibt.** **Stufe 3, die gemischte Uhr,** ist
   erledigt, und seit dem zehnten Lauf des 2026-09-01 ohne jede Bedingung an die
   stetige Masse: `prop:mixeddual` samt `lem:rectangle` steht im Manuskript, der
   Beweis im PROTOKOLL, das Orakel in `Task23/mixed.py`. Der zweite Rest — zwei
   benachbarte Atome ohne stetige Masse dazwischen — ist damit gestrichen; die
   beiden Mechanismen sind verschränkt, und zwar als die zwei Fälle **einer**
   Induktion, nicht als zwei Beweise nebeneinander.

   Offen bleibt allein die **ordnungsdichte Atommenge**. Der Grund ist scharf
   und unverändert: es gibt keine Aufzählung $a_1<a_2<\dots$, entlang der
   induziert werden könnte, und unter einem Punkt liegen dann unendlich viele
   Atome. Beide bisherigen Wege — die Induktion über $d=i-j$ und die
   Nilpotenz der Matrix $V$ in `prop:atomicposet` — brauchen Endlichkeit an
   einer benannten Stelle.

   *Zwischenstand 2026-09-01, elfter Lauf: die Ausschöpfung ist durchgerechnet
   und scheitert, aber an einer anderen Stelle als vermutet.* Der Beweis des
   sechsten Laufs ist störungsweise gelesen worden und liefert die **Identität**
   $\langle\delta,T\mathbb 1\rangle=-\frac12\operatorname{tr}(TE)$, wenn (S) nur
   bis auf einen Rest $E$ gilt. Damit hängt die ganze Ausschöpfung an einer
   berechenbaren Zahl, $C(V,t)=\|T\|_F$ für $T=T^{\mathsf T}$,
   $TV=V^{\mathsf T}T$, $T\mathbb 1=e_t$: der Defekt verschwindet, sobald
   $|F|C_F\varepsilon_F\to0$ für eine Folge endlicher $F$ gilt. `Task23/dense.py`
   misst $C$ exakt in Brüchen. Befund, und er ist scharf: $C$ ist
   skaleninvariant, hängt also nur an der *Gestalt* des Massenvektors, und eine
   kleine Masse $\varepsilon$ an Stelle $k$ einer Kette aus $n$ Atomen kostet
   $C\sim\varepsilon^{-\max(n-2k,0)}$ — geprüft für $n=4,6,8,10$ an jeder
   Stelle, ohne Abweichung. Kleine Massen **oben** sind gratis, kleine Massen
   **unten** ruinieren die Schranke. Fallende Massenprofile geben $C\approx1.6$
   gleichmäßig, steigende $C\sim\rho^{n^2/2}$. Eine ordnungsdichte Menge erzwingt
   das teure Profil, weil unter jedem Punkt unendlich viele Atome liegen.
   Wer den Punkt aufnimmt, fängt deshalb **nicht** mehr bei der Ausschöpfung an,
   sondern bei der Frage, ob die Cauchy--Schwarz-Ungleichung in
   $|\operatorname{tr}(TE)|\le\|T\|_F\|E\|_F$ durch eine Paarung ersetzt werden
   kann, die die Struktur von $E$ als Schwanzbeitrag benutzt statt sie
   wegzuwerfen. Widerlegt ist die grobe Ausschöpfung, nicht die Aussage; ein
   Gegenbeispiel ist nicht gesucht und nicht gefunden. Einzelheiten im
   `Task23/PROTOKOLL.md`, Abschnitt „Die ordnungsdichte Atommenge, 2026-09-01
   (elfter Lauf)", Sackgassen im zehnten Nachtrag.

   *Zwischenstand 2026-09-01, zwölfter Lauf: die Frage nach der feineren
   Paarung ist beantwortet — linear gibt es sie nicht, quadratisch sitzt die
   Numerik exakt auf ihr.* Das Problem ist auf drei Bedingungen an den
   verschobenen antisymmetrischen Anteil $h(a,t)=\kappa(a,t)-\kappa(a,0)$
   reduziert, die Behauptung ist äquivalent zu $h(a,a)=0$ je Atom, und die
   Reduktion trägt in beide Richtungen — wer ein Gegenbeispiel sucht, sucht
   eine Lösung mit nichtverschwindender Diagonale. Auf Level-Trunkierungen der
   dyadischen Uhr ist das ein LP (`Task23/lp_dense.py`; Kontrolle $\eta=0$
   reproduziert den endlichen Satz exakt). Befund: der maximale Defekt fällt
   für alle drei gemessenen Massenprofile gegen $0$ — **kein beschränktes
   Gegenbeispiel auf der dyadischen Uhr** —, die beste lineare
   Zertifikatskonstante ist exakt $n+\frac12$ (linear in der Atomzahl, darum
   scheiterte der elfte Lauf), und alles sitzt auf dem Zwei-Regime-Gesetz
   $v\approx\min(\kappa\eta,\,0.85\sqrt{BM\eta})$ mit Übergang bei
   $BM/\kappa^2$. Wer den Punkt aufnimmt, beweist die **Energieschranke**
   $\Delta(t)^2\le C\,B\,M\,\eta$ ($C\le1$) für endliche Kettensysteme mit
   Residuum $\eta$ und $|h|\le B$ — sie schließt per Ausschöpfung jede rein
   atomare Uhr endlicher Masse mit beschränktem $\kappa$, ordnungsdicht
   eingeschlossen. Der erste Paarungsschritt und die Sackgassen stehen im
   PROTOKOLL, zwölfter Lauf; dort auch die noch zu prüfende Skizze, dass
   Nachbaratome ohne Bodenatom (Typ $\omega^*$, $\mathbb Z$-Ketten) schon der
   bisherigen Induktion zugänglich sind.

   *Zwischenstand 2026-09-01, dreizehnter Lauf: die Energieschranke ist
   **falsch**, in jeder Konstante.* Der kleinste Zeuge hat zwei Atome
   (Massen $(\mu,1)$, $\eta=2\mu^2/3$, Verhältnis $\to 3/2$, analytisch und in
   exakter Bruchrechnung), und entlang aufsteigend-geometrischer Ketten ist
   $\Delta^2/(BM\eta)$ unbeschränkt — zertifizierte Instanzen bis $27588$
   (`Task23/energy_counterexample.py`). Auch masse-lokale Residuenbudgets
   retten nichts. Damit ist der Ausschöpfungsweg über eine profilfreie
   Schranke dreifach zu (Frobenius, linear, quadratisch) und im Ganzen zu:
   die Relaxation „endliches System plus Slack" ist echt schwächer als
   „Trunkierung eines exakten Systems". Wer den Punkt aufnimmt, hat zwei
   Wege: die $\omega^*$-Skizze des zwölften Laufs nachrechnen (unverändert
   offen), oder die **Gestalt** des Trunkierungsresiduums benutzen — es ist
   selbst $\sum_{\text{fehlend}}m_ah(a,\cdot)$ mit global gebundenem $h$,
   und ordnungsdichte Uhren mit durchweg aufsteigenden Massen existieren
   nicht (Summierbarkeit). Einzelheiten in `Task23/PROTOKOLL.md`,
   dreizehnter Lauf.

   *Zwischenstand 2026-09-01, vierzehnter Lauf: die $\omega^*$-Skizze ist
   nachgerechnet und **Satz**.* Für jede rein atomare Uhr, deren Atome unter
   $t^*$ eine **intervallendliche** Kette bilden — je zwei Atome schließen nur
   endlich viele ein; das erfasst $\omega$, $\omega^*$ und $\mathbb Z$-Ketten
   und enthält `prop:atomicdual` —, gilt die Dualität in beiden Konventionen,
   ohne Schranke an $\kappa$: die Zwei-Diagonalen-Induktion braucht weder
   Boden noch Deckel (`Task23/neighbor.py`, Test R), und die Ränder kommen als
   Schwänze der absolut konvergenten Atomsummen, die \eqref{eq:incrementrep}
   ohnehin voraussetzt — die $B$-Hypothese des zwölften Laufs ist damit für
   den Kettenfall vom Tisch. Zwei Korrekturen an der Skizze: ihre wörtliche
   Hypothese „beidseits ein Nachbaratom" ist echt schwächer als die
   Intervallendlichkeit (zwei $\zeta$-Ketten übereinander trennen beide, und
   Test X zeigt, dass die lokalen Relationen die Kreuzpaare dort nicht
   erzwingen), und ihre Schritte über $\kappa$ sind nur für die volle
   Symmetrie nötig. Beweis und Befunde in `Task23/PROTOKOLL.md`, vierzehnter
   Lauf; Roadmap-Einträge `atomGrid_symm_int` und
   `duality_of_atomic_intervalFinite` in `MartingaleProblems` Meilenstein 8.
   Offen am ordnungsdichten Kern: unverändert die in sich dichte Atommenge
   und neu benannt die diskrete, nicht intervallendliche Kette; beide hängen
   am Überqueren eines Häufungspunkts.

   *Zwischenstand 2026-09-02, fünfzehnter bis siebzehnter Lauf: die
   LP-Schiene ist ausgeschöpft, und zwar beweisbar.* Der fünfzehnte Lauf
   maß auf geschachtelten summierbaren Uhren den Kollaps
   $v_J\approx c\sqrt{M\varepsilon_J}$, der sechzehnte baute die
   hierarchische Motor-Uhr, auf der $v_J$ bis Stufe 14 bei $\tfrac1{24}$
   klebt, und erklärte deshalb „(S) ist falsch"; der siebzehnte hat das
   **zurückgenommen und die Kollision entschieden**: das exakte $h$-System
   1–3 ist auf jeder intervallendlichen Kette starr —
   $\widehat w(s,t):=H(s,t)+\Delta(t)-\Delta(s)$ erfüllt exakt die
   Kreuzrelation $(\ast)$, $h$- und $\Phi$-System sind im antisymmetrischen
   Sektor **isomorph** —, also gilt dort $v_J\to0$ (Fensterschranke
   $v_i\le2B\,M_{<u_l}+(K_l+2B)E_i$), nur mit Konstanten $K_l$, die als
   Produkte von Massenverhältnissen jede Messung überdauern. Endliche
   LP-Werte sagen über den Limes nichts; wer den ordnungsdichten Kern
   aufnimmt, arbeite mit dem $\widehat w$-Isomorphismus an den
   Schwanzrelationen über Häufungspunkte (kleinste Instanz: zwei
   $\zeta$-Ketten) und lasse die LPs liegen. `Task23/PROTOKOLL.md`,
   fünfzehnter bis siebzehnter Lauf.

   *Zwischenstand 2026-09-02, achtzehnter Lauf: die Viertelgitterfrage (V)
   der zwei $\zeta$-Ketten ist strukturiert, teilbeantwortet und scharf
   lokalisiert.* Normalform: eine kommutierende Evolution
   $F(\cdot,j{+}1)=(I+\nu_jL)F(\cdot,j)$ mit einem einzigen Operator $L$;
   (V) ist die Injektivität des Geschlecht-0-Produkts $\Pi_j(L)$ auf
   westabfallenden Zeilen — eine Quasianalytizitätsfrage. Bewiesen: ohne
   Summierbarkeit ist (V) **falsch** (Buckel bei Massen $\equiv1$); mit
   Summierbarkeit sterben endliche Modensuperpositionen (Momentenschritt
   plus Vandermonde), endlich getragene $x$, jeder einzelne Schritt
   (injektiv), und jedes reelle Spektralmaß mit exponentiellem
   Abfallspielraum (Streifenanalytizität). Sackgasse mit Beleg: die exakte
   Energieidentität ist indefinit, mit demselben Faktor
   $\mu_i\nu_j(\nu_j-\mu_i)$ wie der Dispersionsdefekt des
   charakteristischen Ansatzes. Offen ist genau der quasipolynomiale
   Bereich: zulässige Spektralmaße müssen nur $e^{\Phi_\mu+\Phi_\nu}$
   integrieren ($O((\log r)^2)$ bei geometrischen Massen), dort existieren
   Maße mit lauter Nullmomenten, und ob eines die ganze
   $\{\lambda_j\}$-Familie annihiliert, ist eine Vollständigkeitsfrage, in
   die die Massen über ihre Zählfunktion eingehen — möglicherweise die
   erste echt massenabhängige Stelle von Task 23. Wer den Punkt aufnimmt:
   Weg (α) Spektraldarstellung westabfallender Lösungen bzw.
   Carleman-Argument an der Evolution, Weg (β) Gegenbeispielsuche bei stark
   lakunären Massen; beides präzise in `Task23/PROTOKOLL.md`, achtzehnter
   Lauf, mit `Task23/zeta_cross.py` (Proben (a)–(f), exakt, rc=0) als
   mechanischer Verifikation der Beweisalgebra.

   *Zwischenstand 2026-09-02, neunzehnter Lauf: Weg (β) ist zu, durch
   Beweis.* Die „Vollständigkeitsfrage" des achtzehnten Laufs war keine:
   die Geschlecht-0-Produkte haben nichtnegative Taylorkoeffizienten, und
   die Zulässigkeitsschranke $e^{\Phi_\mu+\Phi_\nu}$ ist genau ihre
   Koeffizienten-Majorante — also paart die Taylorreihe jeder Mode gegen
   jedes zulässige $\sigma$ absolut, und **die Momente entscheiden alles**
   (Theorem 6: Nullmomente ⟺ Annihilation aller $\lambda_j$ ⟺ aller
   $\beta_i$ ⟺ jeder ganzen Funktion mit zulässiger Majorante; die
   Polynomgewichte der Zulässigkeit von Proposition 5 sind dabei
   entbehrlich). Folgen: jeder zulässige reelle Spektralkandidat, der (Q)
   löst, ist identisch null — ohne den Exponentialspielraum von
   Proposition 5.2 —, die drei (β)-Bedingungen sind äquivalent zu den
   Nullmomenten und von jedem Stieltjes-Maß erfüllt, das aber nur die
   Null darstellt; die Denjoy–Carleman-Spekulation (Massenzählfunktion)
   ist zurückgenommen. Mechanisch verifiziert in
   `Task23/spectral_closed.py` (mpmath, 50 Stellen, rc=0): alle
   $\mathcal E$-Paarungen $<10^{-47}$ relativ bei $\|\sigma\|_{TV}=0.94$,
   Kontrollfunktion $e^{-3c}$ außerhalb der Klasse bei $5\cdot10^{-13}$ —
   37 Größenordnungen Trennung. Wer (V) aufnimmt, hat nur noch Weg (α),
   und der ist leichter geworden: es genügt, jeder westabfallenden Lösung
   **irgendeine** zulässige reelle Spektraldarstellung zu verschaffen
   (quasipolynomialer Abfall reicht), oder Carleman direkt an der
   Evolution. `Task23/PROTOKOLL.md`, neunzehnter Lauf.

   *Zwischenstand 2026-09-03, zwanzigster Lauf: Weg (α) trägt — (V) ist
   bewiesen für quadrantensummierbare Lösungen, insbesondere für alle
   beschränkten.* Der Transformationsbeweis: $G_j(c)=\sum_i\mu_iF(i,j)
   W^c_i$ mit den Geschlecht-0-Schwänzen $W^c_i=\prod_{i'>i}(1+c\mu_{i'})$
   ist ganz vom Typ 0, erfüllt exakt die Nordrekursion
   $G_{j+1}=(1+c\nu_j)G_j+\nu_jR_j$, ist rechts beschränkt und fällt
   reell — Phragmén–Lindelöf (Titchmarsh §5.62) plus Liouville geben
   $G_j\equiv0$, und die **unbedingte** Injektivität der W-Transformation
   auf $\ell^1$ (Theorem 9: Fußpunktzerlegung, noch einmal PL) holt
   $x\equiv0$ zurück. Die Hypothese (H)
   $\sum_{j\ge j_0}\nu_j\sum_i\mu_i|x_{ij}|<\infty$ steht genau am
   Nordlimes und an der Reihe der Identität I; beschränktes $x$ erfüllt
   sie. **Damit sind die zwei $\zeta$-Ketten in der Klasse $|h|\le B$
   geschlossen** — der Klasse aller LPs und Messungen des zwölften bis
   siebzehnten Laufs; die Identität I ist das erste Argument von Task 23,
   das einen Häufungspunkt überquert. Offen: (V) in der nackten Klasse
   (nur zeilen-/spaltenweise absolute Konvergenz) — beide Seiten der
   Transformationsmethode brauchen dieselbe gemeinsame Summe, (H) ist
   ihre Grenze; benannte Angriffe: Bootstrap ((H) aus (Q) selbst) oder
   eine Paarung ohne gemeinsame Summe. Und jenseits der zwei Ketten der
   Cantor–Bendixson-Weg. `Task23/PROTOKOLL.md`, zwanzigster Lauf;
   `Task23/quarter_transform.py` (exakt, rc=0; der abgeschnittene Lauf
   08:23 hatte es mit Syntaxfehler hinterlassen).

   *Zwischenstand 2026-09-03, einundzwanzigster Lauf: „(H) ist die Grenze
   der Methode" ist zurückgenommen — (V) gilt, sobald der Fluss nach Norden
   beschränkt ist, und das ist die Manuskriptklasse.* Der Beweis von
   Theorem 10 benutzt (H) an genau drei Stellen und dort nur durch zwei
   Folgerungen; abgezogen ergibt das **(U)** = Straffheit nach Norden
   ($\sup_{j\ge j_0}\sum_{|i|>N}\mu_i|F(i,j)|\to0$) plus
   $\sum_{j\ge j_0}\nu_j|R_j|<\infty$, und **Theorem 12** schließt daraus
   $x\equiv0$. (U) hat zwei unvergleichbare hinreichende Kriterien: (H) —
   Theorem 10 ist damit Korollar — und
   $\sup_{i,\,j\ge j_0}|F(i,j)|<\infty$, die Beschränktheit des
   **Dualitätsdefekts** $\Phi(s,t)-\Phi(t,s)$. Das zweite ist die
   Hypothesengestalt, die `thm:duality` (\EK{} 4.4.11) in
   \eqref{eq:dual1}+\eqref{eq:dual2} ohnehin trägt: die Dominante $\Gamma_T$
   gibt $|\Phi|\le e^{C_T}E[\Gamma_T]$ auf $[0,T]^2$. Mitgefallen: die
   Identität I des zwanzigsten Laufs ist entbehrlich (Koeffizientenvergleich
   in (B$\infty$)), und die Fortsetzung nach Süden ist ein eigener,
   hypothesenfreier Schritt. Jedes Gegenbeispiel hat jetzt eine scharfe
   Gestalt (Proposition 15): unbeschränkter Defekt auf **jedem**
   Nordquadranten, $\sup_j\rho_j=\infty$, und $|x|$ zeilen- und
   spaltenweise integrierbar, aber auf keinem Nordquadranten
   $\mu\otimes\nu$-integrierbar. **Und Theorem 12 iteriert** (Korollar 16):
   ist die Atomkette diskret — jedes Atom hat Nachbarn — und ist die Ordnung
   ihrer Blöcke (Klassen der Relation „nur endlich viele Atome dazwischen",
   sämtlich vom Typ $\zeta$) intervallendlich, so gilt die Dualität bei
   beschränktem $\Phi$; die Induktion läuft über den Blockabstand, die zwei
   Abfälle stehen an den einander zugewandten Rändern und kommen aus der
   Induktionsvoraussetzung. Damit sind abzählbar viele Häufungspunkte
   erfaßt, nicht nur einer. Offen bleibt (V) bei unbeschränktem Defekt —
   der Bootstrap richtet sich jetzt auf die **Straffheit** statt auf die
   Summierbarkeit —, die nicht intervallendliche Blockordnung (dieselbe
   Frage eine Cantor–Bendixson-Stufe höher) und die nichtdiskrete, in sich
   dichte Atommenge, wo es keine Einschrittrelationen gibt.
   `Task23/PROTOKOLL.md`, einundzwanzigster Lauf;
   `Task23/naked_class.py` (Proben (A)–(F), exakt, rc=0); Roadmapeinträge
   `tailProduct`, `norm_le_of_bddOn_imAxis_of_subexponential`,
   `tailProduct_pairing_eq_zero`, `crossGrid_eq_zero_of_bddFlux`,
   `duality_of_atomic_twoChains_of_bounded`, `Clock.atomBlocks` und
   `duality_of_atomic_blockStack_of_bounded` in `MartingaleProblems`
   Meilenstein 8.

   *Zwischenstand 2026-09-04, zweiundzwanzigster Lauf: der ordnungsdichte
   Kern ist gefallen — die Einschrittrelation war nie nötig.* Der
   einundzwanzigste Lauf hatte den Rest als „die Algebra der
   Einschrittrelation" diagnostiziert; das war, wie „(H) ist die Grenze der
   Methode" davor, eine Prämisse aus der Rechnung statt aus dem Beweisbedarf.
   Die Abelsche Summation von Theorem 12 ist in Wahrheit eine
   **Stieltjes-Produktregel** (Lemma 17.1: haben $f$ und $V$
   Zuwachsdarstellungen mit $\ell^1$-Sprüngen, so hat es $fV$ mit den
   Produktsprüngen), und die kennt keine Nachbarn — sie gilt auf **jeder**
   abzählbaren Kette. Damit läuft die ganze Transformationsmethode auf einer
   beliebigen Atomkette: die Gewichte $W^c(a)=\prod_{a'>a}(1+cm_{a'})$, die
   Identität $K(t;c)-cG(t;c)=\psi(t)-\Delta(t)V_0(c)$, und aus ihr an
   $t=b\in A$, $t=0$ und $t=t^*$ die drei Gleichungen $P=V_0Q$,
   $R=\Delta(t^*)+cQ$ und $S=R(1-V_0)$. Die letzte macht $R$ auf $\Re c\ge0$
   beschränkt (denn $|V_0(c)|\ge\prod(1+m_a^2|c|^2)^{1/2}\to\infty$), also
   nach Phragmén–Lindelöf und Liouville konstant, also $Q\equiv0$, also
   $\Delta\equiv0$ auf den Atomen: **Theorem 17**, $h(a,a)=0$ für jedes Atom
   einer beliebigen Kette, ordnungsdicht eingeschlossen. Einzige
   Zusatzhypothese ist **(F)** $\sum_{a,b}m_am_b|h(a,b)|<\infty$ — die
   $m\otimes m$-Integrierbarkeit der Dichte auf Atompaaren, hinreichend dafür
   $|\gamma|$ beschränkt auf $A\times A$; sie steht an genau zwei Stellen
   (Fubini in $P=V_0Q$, Existenz von $P$). Mitgefallen: der Blockstapel des
   einundzwanzigsten Laufs braucht in dieser Klasse weder Diskretheit noch
   intervallendliche Blockordnung, und die Bemerkung des zwölften Laufs, der
   Mechanismus brauche einen Punkt echt zwischen Atom und Nachfolger, ist
   widerlegt (Probe (E): die lückenfreie Bedingungsmenge erzwingt die
   Diagonale bis $n=7$). Offen bleiben nur noch zwei benannte Dinge: die
   **nackte Klasse** (weder (F) noch $\Phi$ beschränkt — dieselbe Lücke wie
   „(V) bei unbeschränktem Defekt", jetzt für beliebige Ketten; jedes
   Gegenbeispiel hat nach Proposition 15 unbeschränkten Defekt *und*
   $\sum_{a,b}m_am_b|\kappa(a,b)|=\infty$) und die **unendliche
   Halbordnung**, die von keinem der Sätze erfaßt ist.
   `Task23/PROTOKOLL.md`, zweiundzwanzigster Lauf; `Task23/dense_chain.py`
   (Proben (A)–(G), exakt, rc=0); Roadmapeinträge `HasAtomIncrements`,
   `HasAtomIncrements.mul`, `chainTailProduct`,
   `chainTailProduct_pairing_eq_zero`, `atomDiag_eq_zero_of_integrable` und
   `duality_of_atomic_chain_of_integrable` in `MartingaleProblems`
   Meilenstein 8.

   *Zwischenstand 2026-09-04, dreiundzwanzigster Lauf: die zweite der beiden
   Restfragen ist entschieden — die unendliche Halbordnung ist **falsch**.*
   Auf der abzählbaren Antikette $\T=\{0\}\cup A\cup\{t^*\}$ mit positiven
   summierbaren Massen $m_i$, Schwänzen $\sigma_i$ und
   $\kappa(a_i,a_j)=\operatorname{sgn}(i-j)/(\sigma_n\sigma_{n+1})$,
   $n=\min(i,j)$, teleskopiert $m_jf(j)=1/\sigma_{j+1}-1/\sigma_j$ die
   Zeilensummen zu $\sum_jm_j\kappa(a_j,a_i)=1/M$ — konstant und von Null
   verschieden, jede Zeile absolut konvergent ($r_i=2/\sigma_i-1/M$). Das löst
   alle Relationen und gibt $\Phi(t^*,0)-\Phi(0,t^*)=1/M$ (Theorem 19).
   Die Endlichkeit in `prop:atomicposet` ist damit unentbehrlich, und (F) ist
   im Halbordnungsfall scharf: unter Integrierbarkeit schließt auf der
   Antikette schon Fubini (Proposition 19.1). Zwei Befunde, die die
   Hypothesenwahl künftiger Läufe festlegen: das Gegenbeispiel hat
   **beschränktes $\Phi$** (drei Werte) — Korollar 14 ist ein Kettenphänomen
   und außerhalb von Ketten wertlos —, und es braucht $q(\{0\})=0$
   (Proposition 19.2), also genau die Bedingung, die `sharp.py` im dritten
   Lauf im Endlichen als notwendig gefunden hat; die Unendlichkeit kauft hier,
   was dort die negativen Massen kauften. Offen bleiben jetzt drei benannte
   Dinge: die Halbordnung **unter (F)**, die nackte Klasse auf Ketten
   (unverändert), und ob ein Gegenbeispiel mit durchweg positiven
   Abwärtsmassen existiert. Für das erste steht der Weg schon da: unter (F)
   trägt die Ausschöpfung wieder, aber mit der massegewichteten Supremumsnorm
   $\|T\|_m=\sup_{s,t}|T_{st}|/(m_sm_t)$ statt der Frobeniusnorm, an der der
   elfte Lauf gescheitert ist — $|\operatorname{tr}(TE)|\le4M\|T\|_m
   \varepsilon_F$ mit $\varepsilon_F=\sum_{a\notin F}m_a\sum_tm_t|\kappa(a,t)|
   \to0$, und das ist (F) (Proposition 19.3). Wer den Punkt aufnimmt, mißt
   zuerst $\|T\|_m$ für das explizite Zertifikat des sechsten Laufs auf den
   Familien von `Task23/dense.py`. `Task23/PROTOKOLL.md`, dreiundzwanzigster Lauf;
   `Task23/poset_infinite.py` (Proben (A)–(H), exakt, rc=0); Roadmapeinträge
   `duality_of_atomic_antichain_of_integrable` und
   `exists_atomic_antichain_duality_ne` in `MartingaleProblems`
   Meilenstein 8.

   *Zwischenstand 2026-09-04, vierundzwanzigster Lauf: die Ausschöpfung ist
   gemessen und erledigt; dafür fällt die Halbordnung unter (F), sobald ihre
   Unvergleichbarkeit transitiv ist.* Die vom dreiundzwanzigsten Lauf
   aufgegebene Rechnung — $\|T\|_m$ für das explizite Zertifikat des sechsten
   Laufs — steht in `Task23/certificate_m.py` (exakt, Konstruktion an
   $70\,956$ Fällen geprüft). Befund dreifach: auf der Antikette ist
   $\|T\|_m$ **gleichmäßig $1$** mit geschlossener Formel (Theorem 20), also
   schließt Proposition 19.3 dort und liefert Proposition 19.1 ohne Fubini;
   auf der dyadischen ordnungsdichten Uhr ist $\|T\|_m=1/m_{\min}^2$ exakt und
   $\varepsilon_F\|T\|_m\sim8^n\to\infty$ — und das auf einer **Kette**, wo
   Theorem 17 die Konklusion längst gibt, die Ausschöpfung ist damit als
   Methode erledigt (vierte Norm nach Frobenius, linear, quadratisch); und die
   „freie Wahl innerhalb von $\mathcal L$" ist ausgenutzt und wertlos — 37
   lineare Programme geben als Minimum von $\|\cdot\|_m$ durchweg genau den
   Wert des expliziten Zertifikats. Der Ertrag steht daneben: die gemessene
   **Breiteninvarianz** gestufter Halbordnungen ist eine Mittelung der Daten,
   nicht der Zertifikate, und gibt **Theorem 21** — auf jeder abzählbaren
   *schwachen Ordnung* (totale Präordnung, äquivalent: transitive
   Unvergleichbarkeit, äquivalent: Stapel von Antiketten) gilt die Dualität
   unter (F), mit Theorem 17 auf der Stufenkette. Das enthält Theorem 17 und
   Proposition 19.1 als die beiden Extremfälle und erlaubt unendlich breite
   Stufen. Offen bleibt jetzt die Halbordnung mit **nicht** transitiver
   Unvergleichbarkeit (kleinste Gestalt: ein unendliches „N"), dazu
   unverändert die nackte Klasse auf Ketten und das Gegenbeispiel mit
   durchweg positiven Abwärtsmassen. `Task23/PROTOKOLL.md`,
   vierundzwanzigster Lauf; `Task23/weakorder.py` (Proben (A)–(E), exakt,
   rc=0) und `Task23/certificate_m.py`; Roadmapeinträge `Clock.atomLayers`,
   `Clock.atomLayerKernel`, `atomLayerKernel_increment_eq`,
   `atomLayerKernel_rel` und `duality_of_atomic_weakOrder_of_integrable` in
   `MartingaleProblems` Meilenstein 8.

2. **Prüfen, ob die Roadmaps noch zu Mathlib master passen.** Alle zitierten
   Deklarationen gegen master, auf Existenz und `deprecated`. Am 2026-08-29
   fanden sich so drei Fehler. Sinnvoll etwa alle zwei Wochen. *Am 2026-08-31,
   dritter Lauf, ist die Liste „What Mathlib already has" von `WeakConvergence`
   erledigt: elf Deklarationen, alle vorhanden, keine `deprecated`. Am
   2026-09-01, zweiter Lauf, die Liste „Mathlib supplies" von
   `MartingaleProblems`: 38 Namen aus elf Dateien, gegen master geprüft, alle
   vorhanden. Ein Fehler, und ein systematischer — vier Namen standen in
   `MeasureTheory` statt in `ProbabilityTheory`, siehe die Auffälligkeit im
   Inventar. Mitgeprüft und weiterhin richtig: `ProgMeasurable` ist ein
   `@[deprecated (since := "2026-04-24")]`-Alias von `IsStronglyProgressive`
   (`Process/Adapted.lean:381`), Doobs `Lᵖ`-Ungleichung fehlt weiterhin für jeden
   Index (`OptionalStopping.lean:143` sagt es selbst), und `IsStable` ist für
   keine hier interessierende Eigenschaft bewiesen (`gh search code`: der
   Bezeichner kommt in genau einer Wahrscheinlichkeitsdatei vor).*

   *Am 2026-09-01, vierter Lauf, sind `KolmogorovExtension` und `SkorokhodSpace`
   erledigt, und zwar vollständig — Kopfliste **und** Meilensteine; bei
   `SkorokhodSpace` zitieren nur die Meilensteine 1, 2, 3 und 8 überhaupt
   Mathlib. Sieben Fehler, alle berichtigt: zwei Namensräume in
   `KolmogorovExtension` (`MeasureTheory.Measure.isProjectiveLimit_infinitePi`,
   `ProbabilityTheory.isProjectiveLimit_map`), ein Meilensteinpunkt, den Mathlib
   längst hat (`MeasureTheory.IsProjectiveLimit.unique`,
   `Constructions/Projective.lean:150`), eine zu schwach angegebene Hypothese
   (`innerRegular_isCompact_isClosed_measurableSet_of_finite` braucht neben
   `IsCompletelyPseudoMetrizableSpace` auch `SecondCountableTopology` und
   `BorelSpace`), und in `SkorokhodSpace` die sechs `Monotone.`-Sätze, die die
   Kopfliste als „die ganze Einseitiglimes-API" führte, der Selbstwiderspruch um
   `Monotone.countable_not_continuousAt` und der Typfehler `LipschitzWith.const`
   in der Definition von `TimeChange.norm`. Zwei Funde in die andere Richtung
   sind mit eingetragen: `isCompactSystem_isCompact_isClosed`
   (`Topology/Compactness/CompactSystem.lean:163`) und
   `OrderTopology.of_linearLocallyFinite` (`Instances/Discrete.lean:63`).
   Einzelheiten im Inventar unter „Läufe" und bei den Auffälligkeiten.*

   *Am 2026-09-01, fünfter Lauf, sind die Meilensteine von `WeakConvergence`
   erledigt — fünf Befunde, darunter der größte des ganzen Rückstaupunktes:
   `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` mit
   `MeasureTheory.TendstoInDistribution` war der Roadmap unbekannt, und vier
   Punkte der Meilensteine 2 und 3 verlangten, was darin steht. Dazu
   `measurableSet_of_continuousAt`, das Meilenstein 2 unter einem erfundenen
   Namen suchte, und vier Zeilennummern aus v4.33.1. Von `MartingaleProblems`
   sind die Meilensteinstellen mit ausgeschriebenem Mathlib-Pfad erledigt (ein
   Namensraumfehler, zwei Zeilennummern, eine verschwiegene Hypothese, ein
   präzisiertes Zitat); es fehlen die Nennungen **ohne** Pfad, und das sind die
   meisten. Einzelheiten im Inventar unter „Läufe".*

   *Werkzeug, und es spart den halben Aufwand: `~/Code/lean/mathlib4` hat neben
   `origin` (Fork des Nutzers, master vom 2026-03-23, untauglich) das Remote
   `upstream` auf `leanprover-community/mathlib4`. Nach
   `git -C ~/Code/lean/mathlib4 fetch --no-tags upstream master` beantwortet
   `git grep -n <muster> upstream/master -- Mathlib` in einem Aufruf, wofür
   `gh api` ein Dutzend braucht, und liefert Zeilennummern, Namensraumgrenzen
   und Variablenblöcke mit. So ist dieser Lauf gegen `981fa8f5` geprüft.*

   *Am 2026-09-01, sechster Lauf, ist die Restmenge erledigt — die
   Meilensteinnennungen von `MartingaleProblems` **ohne** Pfad, rund dreißig aus
   den Meilensteinen 1, 2, 8, 9, 12 und 13, geprüft gegen `e076e1ca8f3`. Damit
   ist dieser Punkt für alle vier Roadmaps einmal durchgelaufen; die nächste
   Runde ist in etwa zwei Wochen fällig und fängt wieder bei
   `KolmogorovExtension` an. Drei Befunde, alle in der Lokalisierungs- und
   Stoppzeitschicht: Meilenstein 2 stand auf `[Preorder ι]` und benutzte
   `ProbabilityTheory.Locally`, das `[LinearOrder ι] [OrderBot ι]
   [TopologicalSpace ι] [OrderTopology ι] [Zero E]` verlangt; Meilenstein 9
   nannte `⊥` ohne `[OrderBot ι]`; und `IsQuasiLeftContinuous` typisierte
   Stoppzeiten als `Ω → ι`, während Mathlibs `IsStoppingTime` `Ω → WithTop ι`
   ist. Alle drei berichtigt, `Suggested.lean` mit. Einzelheiten im Inventar.*

   *Die Lehre dieses Laufs, neben der des fünften: die drei Fehler waren keine
   Versionsdrift — jede der Deklarationen steht in v4.33.1 wortgleich da. Was
   ungeprüft blieb, war nicht der **Name**, sondern die **Signatur**: der
   Variablenblock, in dem eine Deklaration steht, und der Typ ihrer Argumente.
   Wer den Punkt fortsetzt, lese zu jedem zitierten Namen die `variable`-Zeilen
   des umgebenden `section` mit, nicht nur die Zeile der Deklaration.*

   *Die Lehre aus dem Hauptbefund, für den nächsten Durchgang: die Datei stand
   in v4.33.1 wortgleich da. Der Fehler war keine Versionsdrift, sondern eine
   nie gestellte Suche — nach dem Wort des Manuskripts („weak convergence")
   statt nach Mathlibs Begriff („convergence in distribution"). Wer den Punkt
   fortsetzt, sehe zu jedem Meilensteinpunkt zuerst das **Verzeichnis** durch,
   in dem er läge, und lese dessen Dateinamen, bevor er nach Deklarationen
   sucht.*

3. **Die Grundtheorie von `ProbabilityMeasure E` als metrischem Raum
   formalisieren.** Am 2026-08-31 als Lücke belegt und als Block an den Kopf von
   `WeakConvergence` Meilenstein 3 eingetragen: Mathlib hat die Metrisierbarkeit
   (`MeasureTheory.instMetrizableSpaceProbabilityMeasure`,
   `Measure/LevyProkhorovMetric.lean:695`) und weder die Separabilität noch die
   Vollständigkeit — `SeparableSpace (ProbabilityMeasure`,
   `PolishSpace (ProbabilityMeasure` und `CompleteSpace (ProbabilityMeasure`
   haben in v4.33.1, im Arbeitsbranch und auf master (`gh search code`) null
   Treffer. Das ist die erste Hälfte von `fact:PSpolish`, und sie ist der
   Untergrund jedes Teilfolgenarguments des Konvergenzteils.

   *Zwischenstand 2026-08-31, dritter Lauf: der Block war so, wie er dastand,
   nicht formalisierbar, und beide Gründe sind behoben. `CompleteSpace
   (ProbabilityMeasure E)` ist ein Typfehler — die Metrik sitzt auf der Struktur
   `LevyProkhorov (ProbabilityMeasure E)`, `ProbabilityMeasure E` trägt keine
   Uniformität —, und der angegebene Beweisweg der Vollständigkeit war zirkulär,
   weil er `isTightMeasureSet_of_isCompact_closure` für einen Schritt nannte, der
   den kompakten Abschluss erst herstellen soll. Der Meilenstein führt jetzt vier
   Punkte, den Weg über Ulam (`isTightMeasureSet_singleton`) und, als eigene
   Aussage, die Herauslösung des Straffheitsskeletts aus `Measure/Prokhorov.lean`
   (`isTightMeasureSet_of_forall_exists_finite_iUnion_ball`). Übersetzt ist
   nichts: der Worktree hat kein `.lake`. Der Punkt bleibt deshalb offen, und der
   erste Schritt ist jetzt benannt — siehe den Laufbericht im Inventar.*
