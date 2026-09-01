# Task 23 — Protokoll

Anhängend, nie umschreiben. Das Gedächtnis der Läufe liegt hier und in den
Commits auf `task23-atomic-duality`. Wer einen Weg als Sackgasse erkennt,
schreibt das hierher, damit kein späterer Lauf ihn erneut geht.

## Auftrag

`rem:atomicdual` im Manuskript sagt für eine rein atomare Uhr
$q=\sum_k m_k\delta_{a_k}$: die Relationen aus \eqref{eq:incrementrep} erzwingen
$\Phi(t,0)=\Phi(0,t)$ — „verified symbolically … **not proved**". Ziel ist ein
Beweis, in dieser Reihenfolge:

1. **endlich viele Atome** — als eigenständige Proposition;
2. **abzählbar viele Atome**, insbesondere ordnungsdichte Atommengen;
3. **gemischte Uhr** (atomarer plus diffuser Anteil).

Danach wandert die Zeile „purely atomic" in der Statustabelle von
`rem:atomsnotchange` von „not proved" auf „proved", und `rem:atomicdual` wird
eine Proposition mit Beweis.

## Das Modell, festgeschrieben

$\T=\{0,1,\dots,N\}$, Atome $a_k=k$ für $k=1..N$ mit Massen $m_k$, Konvention
$\iota=\mathrm{p}$, also $[s,s')=\T_{<s'}\setminus\T_{<s}$. Damit ist
$[s,s+1)=\{s\}$, und $\{s\}$ ist genau für $s\ge1$ ein Atom. Aus
\eqref{eq:incrementrep} mit $\gamma_1=\gamma_2=\gamma$:

$$\Phi(s{+}1,t)-\Phi(s,t)=m_s\gamma(s,t)\ (s\ge1),\qquad
  \Phi(s,t{+}1)-\Phi(s,t)=m_t\gamma(s,t)\ (t\ge1),$$

und $0$ für $s=0$ bzw. $t=0$. Also $\Phi(1,t)=\Phi(0,t)$ und
$\Phi(s,1)=\Phi(s,0)$, und die Behauptung $\Phi(N,0)=\Phi(0,N)$ ist
gleichwertig zu $\Phi(N,1)=\Phi(1,N)$ — einer Aussage über das Innere. Dort gilt

$$\Phi(s{+}1,t)=\Phi(s,t)+\frac{m_s}{m_t}\bigl(\Phi(s,t{+}1)-\Phi(s,t)\bigr),$$

Zeile $s+1$ ist also aus Zeile $s$ bestimmt; freie Daten sind $\Phi(1,1..N)$.

## Stand

**2026-08-29, Einrichtung.** `oracle.py` prüft den Defekt $\Phi(N,1)-\Phi(1,N)$
symbolisch. Ergebnis für $N=2,\dots,6$ mit **vollständig symbolischen Massen**
$m_1,\dots,m_N$ und freier Zeile $\Phi(1,\cdot)$: der Defekt ist identisch $0$.
Das ist stärker als die im Manuskript vermerkte Verifikation (dort: bis fünf
Atome). Ein Beweis fehlt weiterhin.

## Sackgassen

* **Induktion über die Atome** scheitert an ordnungsdichten Atommengen (PLAN,
  Task 23). Für den endlichen Fall ist sie brauchbar, für Stufe 2 nicht.
* **Interpolation über ein Atom hinweg** ist unmöglich, mit Gegenbeispiel:
  `rem:atomsnotchange`, $\T=[0,2]$, $q=\delta_1$. Ein Paar $\Psi,\psi$ mit
  \eqref{eq:rectrepinline} ist automatisch Funktion von $x+y$ und hat die
  Konklusion eingebaut — der Weg setzt voraus, was zu zeigen ist.
* **Ein zu grobes Randmodell** (freie $\gamma(s,0)$ in der Spalte $t=0$) liefert
  einen scheinbar nicht verschwindenden Defekt. Falsch: $\gamma(s,0)$ ist durch
  $\Phi(s,1)=\Phi(s,0)$ mitbestimmt, nicht frei. Wer das Orakel umbaut, prüfe
  zuerst, ob es für gleiche Massen die bekannte Aussage „$\Phi$ konstant auf
  Antidiagonalen" reproduziert.

## Vermutung, noch ungeprüft

Bei gleichen Massen sagen die Relationen genau „$\Phi$ konstant auf
Antidiagonalen", was die Konklusion schon ist; der Gehalt sitzt also in
**ungleichen Massen**. Naheliegend: die Invariante ist dort $Q(s)+Q(t)$ mit
$Q(s)=q(\T_{<s})$. Das würde `cor:atomless` subsumieren, wo die Konklusion genau
„Funktion von $Q(s)+Q(t)$" lautet, und beide Zeilen der Statustabelle
vereinheitlichen.

**2026-08-30 erledigt, und anders als vermutet.** Die Invariante ist nicht
$Q(s)+Q(t)$, sondern schlicht die **Symmetrie** $\Phi(s,t)=\Phi(t,s)$. Auf einem
Gitter mit paarweise verschiedenen Massen sind die Niveaumengen von $Q(s)+Q(t)$
generisch nur die Paare $\{(s,t),(t,s)\}$; „konstant auf den Niveaumengen von
$Q(s)+Q(t)$" *ist* dort die Symmetrie, und diese gilt. Siehe unten.

## Stufe 1 und Stufe 2 (lokal endlich): bewiesen, 2026-08-30

`rem:atomicdual` ist jetzt `prop:atomicdual` mit Beweis, gestützt auf ein neues
`lem:atomgrid`. Beide Konventionen. Der Beweis steht im Manuskript; hier das
Gerüst und warum er funktioniert, damit spätere Läufe ihn nicht neu suchen.

**Der Kern.** Eliminiere $\gamma$. Aus \eqref{eq:incrementrep} an derselben
Stelle $(i,j)$ folgt durch Kreuzmultiplikation

$$m_j\bigl(\Phi(i{+}1,j)-\Phi(i,j)\bigr)=m_i\bigl(\Phi(i,j{+}1)-\Phi(i,j)\bigr)
\qquad (\ast)$$

und $\gamma$ kommt nicht mehr vor. $(\ast)$ ist **linear** in $\Phi$ und
**invariant unter Transposition**: schreibt man $(\ast)$ an der Stelle $(j,i)$,
so ist das genau $(\ast)$ an $(i,j)$ für $\Phi^{\mathsf T}$. Also erfüllt
$w(i,j)\coloneqq\Phi(i,j)-\Phi(j,i)$ ebenfalls $(\ast)$, ist antisymmetrisch, und
zu zeigen bleibt $w\equiv0$.

**Die Induktion.** Über den Abstand $d=|i-j|$ zur Diagonale, mit den Stufen $d$
und $d-1$ **gleichzeitig**:

* $d=0$: $w(i,i)=0$ aus der Antisymmetrie.
* $d=1$: $(\ast)$ an $(j,j)$ gibt $w(j{+}1,j)=w(j,j{+}1)=-w(j{+}1,j)$, also $0$.
* $d\to d+1$: $(\ast)$ an $(j{+}d,\,j)$ gibt
  $m_j\,w(j{+}d{+}1,j)=m_{j+d}\,w(j{+}d,j{+}1)-\,(m_{j+d}-m_j)\,w(j{+}d,j)$.
  Rechts steht $w$ an den Abständen $d-1$ und $d$, beides $0$; $m_j\neq0$
  schließt.

Das ist der Grund, warum keine Treppe in `lem:chain` die Kürzung sichtbar macht:
gefegt werden die **Diagonalen** $i-j=d$, nicht die Antidiagonalen, und es
braucht zwei aufeinanderfolgende Stufen auf einmal. Eine Treppe sieht immer nur
eine Antidiagonale.

**Was gebraucht wird.** Nur $m_i\neq0$ für $1\le i\le M-1$. Keine Positivität,
keine Integrabilität, keine Regularität von $\gamma$, $m_M$ kommt nie vor.

**Die Reduktion (Stufe 2, lokal endlich).** Sind die Atome in $\T_{\le t^*}$
endlich viele und paarweise vergleichbar, so ordne sie zu $a_1,\dots,a_N$ und
setze $u_0=0$, $u_i=a_i$, $u_{N+1}=t^*$. Dann trägt $[u_i,u_{i+1})$ genau das
Atom $a_i$ ($i\ge1$) und $[u_0,u_1)$ keines, und $\widehat\Phi(i,j)=\Phi(u_i,u_j)$
ist das endliche Gitter mit $\widehat m_0=0$. Stufe 1 und Stufe 2 fallen also
zusammen: **abzählbar viele Atome kosten nichts**, solange unter jedem Punkt nur
endlich viele liegen — und genau das ist die stehende Hypothese von
`rem:atomicdual`.

**Die zweite Konvention.** $\iota=\mathrm o$ ist nicht ein zweiter Beweis,
sondern **dieselbe** Aussage nach der Spiegelung $(i,j)\mapsto(M{-}i,M{-}j)$ bei
umgekehrter Massenliste: $(\ast)$ ist darunter invariant. Das ersetzt die frühere
Begründung („die Relationen erzwingen $\gamma(t,0)=\gamma(0,t)$"), die die
Konklusion nur verschob.

**Verifikation.** `verify.py` (neu). Anders als `oracle.py` setzt es über die
Gestalt der Lösung nichts voraus: es baut das volle homogene System, das
\eqref{eq:incrementrep} den $2(N{+}1)^2$ Unbekannten $\Phi,\gamma$ auferlegt,
nimmt dessen Kern und prüft an einer Kernbasis drei Aussagen — die
Dualitätsidentität, die Symmetrie von $\Phi$ auf dem **ganzen** Quadrat und die
Symmetrie von $\gamma$ im Inneren. Exakte rationale Arithmetik, $N=2..8$, drei
Massenvektoren (gleich / ganzzahlig verschieden / Stammbrüche), beide
Konventionen: 42 Konfigurationen, alle drei Aussagen überall erfüllt.
`verify.py --symbolic` wiederholt das mit **vollständig symbolischen** Massen
(Nullraum über `Q(m_1,…,m_N)`, deshalb nur bis `N=5`); die Dimensionen der
Lösungsräume stimmen mit denen der rationalen Läufe überein — 7, 9, 11, 13 für
`ι=p` —, keine der Spezialisierungen war also entartet. `oracle.py` bleibt
liegen, ist aber durch `verify.py` überholt: es setzte die Reduktion auf eine
freie Zeile bereits voraus.

## Was offen bleibt

> **Überholt, 2026-08-31 (sechster Lauf).** Der erste Punkt dieser Liste — Atome,
> die keine Kette bilden — ist bewiesen, für jede endliche Halbordnung und
> nichtnegative Massen. Siehe den Abschnitt „Der Halbordnungsfall, 2026-08-31
> (sechster Lauf)" ganz unten. Die Liste bleibt stehen, weil sie den Weg dorthin
> festhält, und weil ihre beiden anderen Punkte offen sind.

* **Atome, die keine Kette bilden.** `prop:atomicdual` verlangt, dass die Atome
  unter $t^*$ paarweise vergleichbar sind; unter \eqref{T2a} ist das
  automatisch, unter \eqref{T0} nicht. Das Manuskript behauptete bisher mehr
  („uses no order structure beyond a preorder", gestützt auf die symbolische
  Prüfung von $\{0,1,2\}^2$); die Statustabelle trennt jetzt beide Zeilen. Der
  kleinste Fall ist $\T=\{0,a,b,t^*\}$ mit $a,b$ unvergleichbar, Atome bei
  beiden. **Der hier zuerst notierte Grund war falsch** — er lautete, die drei
  Relationen längs $[0,t^*)$, $[a,t^*)$ und $[b,t^*)$ gäben
  $\Phi(t^*,t)-\Phi(0,t)$ dreimal, einmal als $m_a\gamma(a,t)$, einmal als
  $m_b\gamma(b,t)$ und einmal als deren Summe, also seien beide Null. Die drei
  Intervalle sind aber alle drei $\{a,b\}$; siehe den Lauf vom 2026-08-30 unten.
  Ein allgemeines Argument fehlt.

  **Und der Weg über die Symmetrie ist versperrt.** `poset.py` (neu) stellt für
  $\T=\{0,1,2\}^2$ mit der Produktordnung *alle* Relationen aus
  \eqref{eq:incrementrep} auf — für jedes vergleichbare Paar $s\le s'$, nicht nur
  für Einschrittintervalle, denn in einem Verband folgen die übrigen nicht durch
  Teleskopieren entlang einer Kette — und prüft den Kern. Befund für drei
  Massenwahlen: $\Phi(t,0)=\Phi(0,t)$ gilt für **jedes** $t$, die Notiz des
  Manuskripts stimmt also; aber $\Phi(s,t)=\Phi(t,s)$ gilt **nicht**, sie fällt
  an den maximalen und den unvergleichbaren Punkten aus, etwa beim Paar
  $((1,2),(2,1))$. Die Symmetrie ist ein Phänomen der Kette, nicht der atomaren
  Uhr. Wer den Präordnungsfall angeht, braucht eine schwächere Invariante als
  `lem:atomgrid` sie liefert; die Induktion über die Höhe des Atomverbands mit
  dem Kettenfall als Basis müsste das mittragen.
* **Ordnungsdichte Atommengen** fallen aus der Hypothese heraus (unter einem
  Punkt liegen dann unendlich viele Atome) und sind **nicht** Stufe 2, sondern
  eine eigene Frage. Der Grund ist scharf: liegen die Atome dicht, so trägt kein
  Intervall $[s,s')$ genau ein Atom, $(\ast)$ hat kein diskretes Gegenstück, und
  es gibt kein Gitter, an dem entlang induziert werden könnte. Das ist dieselbe
  Sperre wie im gemischten Fall, von der atomaren Seite gesehen.
* **Stufe 3, gemischte Uhr,** unberührt.

## Sackgassen, Nachtrag

* **„Die Invariante ist $Q(s)+Q(t)$"** (Vermutung vom 2026-08-29) führt in die
  Irre. Bei paarweise verschiedenen Massen sind die Niveaumengen von $Q(s)+Q(t)$
  auf dem Atomgitter generisch zweielementig, die Aussage ist dort also nichts
  anderes als die Symmetrie — und der Umweg über eine „Zeitvariable" $Q$
  verdeckt, dass der Beweis rein kombinatorisch ist und $Q$ nirgends braucht.
* **Symmetrie über die freie Zeile beweisen** ist zirkulär. Der Lösungsraum wird
  von der Zeile $\Phi(1,\cdot)$ aufgespannt; die Zuordnung Zeile $\mapsto$ Spalte
  ist eine untere Dreiecksmatrix $R$ mit $R^2=I$ und $R\mathbf 1=\mathbf 1$, aber
  daraus folgt $R=I$ nicht — und $R=I$ *ist* die Behauptung. Der Ausweg ist
  gerade, $\Phi$ nicht aus der Zeile aufzubauen, sondern $(\ast)$ auf die
  antisymmetrische Differenz anzuwenden.

## Der Halbordnungsfall, 2026-08-30 (dritter Lauf): eine Reduktion, ein Gegenbeispiel

Angegangen wurde der erste offene Punkt oben, die unvergleichbaren Atome. Ein
Beweis kam nicht heraus, wohl aber zweierlei, das jeder spätere Lauf braucht:
eine Reduktion, die $\Phi$ ganz eliminiert, und ein Gegenbeispiel, das die im
Manuskript genannte Begründung des kleinsten Falles widerlegt und zugleich
festlegt, welche Hypothese der Fall wirklich braucht.

**Die Reduktion.** $\T$ hat ein kleinstes Element, also ist $\T_{<0}$ leer, und
\eqref{eq:incrementrep} mit $s=0$ bzw. $t=0$ *löst $\Phi$ auf*:

$$\Phi(s,t)=\Phi(0,t)+\sum_{a<s}m_a\gamma(a,t),\qquad
  \Phi(s,t)=\Phi(s,0)+\sum_{b<t}m_b\gamma(s,b).$$

Beides zusammen ist mit \eqref{eq:incrementrep} gleichwertig — für $s\le s'$ ist
$\T_{<s}\subseteq\T_{<s'}$, und die Differenz der beiden Formeln ist genau die
Relation über $[s,s')$. Übrig bleibt eine Bedingung an $\gamma$ allein:

$$\sum_{a<s}m_a\bigl(\gamma(a,t)-\gamma(a,0)\bigr)
  =\sum_{b<t}m_b\bigl(\gamma(s,b)-\gamma(0,b)\bigr)\quad\text{für alle }s,t,
  \qquad(\ast\ast)$$

und der zu zeigende Defekt ist
$\Phi(t,0)-\Phi(0,t)=\sum_{a<t}m_a(\gamma(a,0)-\gamma(0,a))=:\delta(t)$.

**Und $(\ast\ast)$ zerfällt.** Schreibt man $\gamma=(\lambda+\kappa)/2$ mit
$\lambda$ symmetrisch und $\kappa$ antisymmetrisch, so ist $(\ast\ast)$
äquivalent zum Paar

$$\Psi(s,t)+\Psi(t,s)=\Psi(s,s)+\Psi(t,t),\qquad \Psi(s,t):=\sum_{a<s}m_a\kappa(a,t),
  \qquad(\diamondsuit)$$

und „$\Lambda(s,t)-\Lambda(s,0)$ symmetrisch in $(s,t)$" für
$\Lambda(s,t):=\sum_{a<s}m_a\lambda(a,t)$. Die beiden Hälften sind entkoppelt,
und der Defekt ist $\delta(t)=\Psi(t,0)$, hängt also **nur an $\kappa$**: der
symmetrische Anteil von $\gamma$ kommt in der Dualität überhaupt nicht vor. Auf
einer Kette erzwingt $(\diamondsuit)$ sofort $\kappa\equiv0$: mit $t=s+1$ geben
$\Psi(s{+}1,s)=\Psi(s,s)$ und $\Psi(s{+}1,s{+}1)=\Psi(s,s{+}1)+m_s\kappa(s,s{+}1)$
zusammen $\kappa(s,s{+}1)=0$, und dieselbe Rechnung an $t=s+d+1$ trägt die
Induktion über den Abstand. Das ist `lem:atomgrid` noch einmal, ohne $\Phi$.

**Das Gegenbeispiel** (`diamond.py`; exakte Arithmetik, und die Relationen am
Ende Zeile für Zeile unabhängig von der linearen Algebra nachgerechnet, die den
Zeugen geliefert hat). Diamant $\T=\{0,a,b,t^*\}$ mit $a,b$ unvergleichbar,
$m_a=1$, $m_b=-1$, $m_0=0$:

$$\gamma(a,\cdot)\equiv1,\ \gamma \text{ sonst } 0;\qquad
  \Phi(t^*,\cdot)\equiv0,\ \Phi \text{ sonst }\equiv-1$$

erfüllt beide Darstellungen aus \eqref{eq:incrementrep} und hat
$\Phi(t^*,0)-\Phi(0,t^*)=1$. Also: **im Halbordnungsfall genügt $m_i\neq0$
nicht.** `lem:atomgrid` kommt mit $m_i\neq0$ aus, der Fall unvergleichbarer
Atome nicht — das ist der scharfe Unterschied zwischen beiden.

**Was am Manuskript dadurch falsch war, und jetzt korrigiert ist.**
`rem:atomicdual` behauptete zum kleinsten Fall, „the three relations along
$[0,t^*)$, $[a,t^*)$ and $[b,t^*)$ force $m_a\gamma(a,t)=m_b\gamma(b,t)=0$".
Das trifft nicht zu, und zwar aus einem Grund, der den ganzen Fall erklärt: auf
dem Diamanten ist $[0,t^*)=[a,t^*)=[b,t^*)=\{a,b\}$, die drei Relationen sagen
also dasselbe und binden kein einzelnes $\gamma(a,t)$. Bei $m_a=1$, $m_b=2$ gibt
es Lösungen mit $\gamma(a,0)=-2\neq0$ (`diamond.py`, Teil 1) — die Dualität gilt
dort trotzdem, aber aus einem anderen Grund. Das Argument benutzte nirgends die
Positivität und hätte deshalb auch das Gegenbeispiel decken müssen. Im
Manuskript ersetzt.

Der strukturelle Grund: **das Intervall $[s,s')$ einer Halbordnung ist auch dann
keine Einpunktmenge, wenn $s'$ das Element $s$ überdeckt.** Auf $\{0,1,2\}^2$
ist $[(1,0),(1,1))=\{(1,0),(0,1)\}$. Genau darauf ruht das Gitter von
`lem:atomgrid`, und genau das fällt weg.

**Die Hypothese, die es stattdessen braucht** (`sharp.py`). Über alle
Halbordnungen mit kleinstem Element auf vier und fünf Punkten und alle
Massenvektoren aus einem kleinen Gitter mit beiden Vorzeichen — $1216+17739$
Konfigurationen, $48+576$ Ausfälle — gilt ausnahmslos: **fällt die Dualität, so
gibt es ein $s$ mit $q(\T_{<s})=0$ bei nichtleerem $\T_{<s}$.** Kein einziger
Ausfall bei durchweg nicht verschwindenden Abwärtsmassen. Die Umkehrung gilt
nicht; das Verschwinden ist notwendig und nicht hinreichend. Für eine *echte*
Uhr ist die Bedingung automatisch: $q$ ist ein Maß, $q(\T_{<s})=0$ heißt, unter
$s$ liegt kein Atom, und dann ist der Defekt ohnehin $0$. Entsprechend fand
`posetsearch.py --clocks` über dieselben Halbordnungen mit **nichtnegativen**
Massen — auch am kleinsten Punkt, also alle Massenvektoren aus dem Gitter:
$4864+53217$ Konfigurationen — **keinen einzigen Ausfall**, und auf Ketten
fällt die Dualität auch bei gemischten Vorzeichen nie, wie `lem:atomgrid` es
sagt.

**Vermutung, damit belegt und nicht geraten.** Für jede Uhr auf einer
Halbordnung mit kleinstem Element, deren Atome unter $t^*$ endlich viele sind,
gilt $\Phi(t^*,0)=\Phi(0,t^*)$; die Vergleichbarkeit ist entbehrlich, die
Positivität der Massen nicht.

**Wo der Beweis hakt.** Unter $(\diamondsuit)$ allein ist $\delta(t)$ durch
*gewichtete* Summen der Gleichungen an Paaren unterhalb $t$ nicht bestimmt:
multipliziert man $(\diamondsuit)$ an $(a,t)$ mit $m_a$ und summiert über
$a<t$, so kommt mit der Antisymmetrie von $\kappa$ nur die Tautologie
$\Theta(t,t)=\mu(t)\delta(t)$ heraus, $\mu(t)=q(\T_{<t})$. Der Gehalt sitzt in
den **einzelnen** Gleichungen. Am Diamanten liefern die beiden an $(a,t^*)$ und
$(b,t^*)$ getrennt $m_b\kappa(b,a)=\delta(t^*)$ und
$-m_a\kappa(b,a)=\delta(t^*)$, deren Differenz $(m_a+m_b)\kappa(b,a)=0$ ist —
dort steht die Positivität, und dort steht auch das $q(\T_{<t^*})$ des
Suchbefunds. Ein allgemeines Argument müsste diese Rechnung über die maximalen
Elemente von $\T_{<t^*}$ führen, deren Antikette die Rolle von $\{a,b\}$ spielt.

**Die Skripte.** `poset2.py` prüft die Reduktion, indem es jede Konfiguration
auf zwei Wegen rechnet — volles System in $(\Phi,\gamma)$ und reduziertes System
$(\ast\ast)$ in $\gamma$ — und die Antworten vergleicht; sie stimmen überall
überein. `posetsearch.py` zählt alle Halbordnungen mit kleinstem Element auf bis
zu fünf Punkten auf und entscheidet die Dualität durch einen Rangvergleich
(liegt das Funktional $\delta(t)$ im Zeilenraum?), exakt in Brüchen und ohne
Kernbasis. `sharp.py` setzt darauf die Suche nach der scharfen Bedingung auf,
`diamond.py` hält den Zeugen fest.

## Sackgassen, zweiter Nachtrag

* **Den Halbordnungsfall über eine Induktion „von unten" führen**, also
  $\delta(a)=0$ für alle $a<t$ voraussetzen und $\delta(t)$ folgern, geht mit
  gewichteten Summen nicht: unter dieser Hypothese wird jede Linearkombination
  von $(\diamondsuit)$ über $a<t$ zur Identität $0=0$. Wer es versucht, muss die
  Gleichungen einzeln halten.
* **Positivität für entbehrlich halten**, weil `lem:atomgrid` sie nicht braucht.
  Widerlegt durch das Gegenbeispiel oben.

## Der Halbordnungsfall, 2026-08-31 (vierter Lauf): die Idealreduktion

Wieder angegangen wurde der erste offene Punkt, die unvergleichbaren Atome. Ein
Beweis kam wieder nicht heraus. Herausgekommen sind eine **Reduktion, die den
Fall auf beschränkte Halbordnungen einschränkt und dort auf einen einzigen
Defekt**, eine schärfere Gestalt dieses Defekts, und eine Vermutung, die den
Rest schließen würde und deren Gültigkeitsbereich vermessen ist. Alles Folgende
steht in der $\kappa$-Gestalt des dritten Laufs — $\gamma$ zerfällt in
symmetrischen und antisymmetrischen Anteil, der Defekt hängt nur am
antisymmetrischen, und mit

$$\Psi(s,t)=\sum_{a<s}m_a\kappa(a,t),\qquad \delta(t)=\Psi(t,t)$$

lautet die Bedingung $(\diamondsuit)$: $\Psi(s,t)+\Psi(t,s)=\Psi(s,s)+\Psi(t,t)$
für alle $s,t$; zu zeigen ist $\delta\equiv0$.

**Die Kontrolle zuerst.** `antisym.py` (neu) stellt das System allein in
$\kappa$ auf — $\binom n2$ Unbekannte statt $n^2$ — und reproduziert die
bekannten Antworten: auf Ketten fällt die Dualität für keinen Massenvektor aus
$\{-2,-1,0,1,3\}$ bis $n=5$, am Diamanten mit $m_a=1$, $m_b=-1$, $m_0=0$ fällt
sie, mit $m_a=m_b=1$ nicht, und über alle Halbordnungen mit kleinstem Element
auf vier und fünf Punkten mit nichtnegativen Massen aus einem Gitter
($4864+53217$ Fälle) gibt es keinen Ausfall. Die $\kappa$-Gestalt ist damit
gegen `posetsearch.py` geeicht.

**Die Idealreduktion, bewiesen.** Ist $I$ eine abwärtsabgeschlossene Teilmenge
von $\T$, die das kleinste Element enthält, so ist für $s\in I$ auch
$\T_{<s}\subseteq I$, also $\Psi_I(s,t)=\Psi(s,t)$ für $s,t\in I$, und die
Relationen $(\diamondsuit)$ an Paaren aus $I$ sind eine Teilmenge derer auf
$\T$. Eine Lösung auf $\T$ schränkt sich also zu einer Lösung auf $I$ mit
demselben $\delta$ ein. Daraus:

> $\delta(t)=0$ ist auf $\T$ erzwungen, sobald es auf $\T_{\le t}$ erzwungen
> ist — und $\T_{\le t}$ hat kleinstes Element $0$ **und** größtes Element $t$.

Die Induktion über $|\T|$ gibt damit $\delta(s)=0$ für jedes $s$, dessen
Hauptideal $\T_{\le s}$ echt kleiner als $\T$ ist, also für jedes $s$ außer
einem größten Element. Offen bleibt genau:

> **(R)** $\T$ endlich mit kleinstem Element $0$ und größtem Element $z$,
> $m\ge0$, $\kappa$ antisymmetrisch mit $(\diamondsuit)$. Dann ist
> $\Psi(z,z)=0$.

Hat $\T$ zwei maximale Elemente, so ist nichts mehr zu zeigen: $\T$ ohne das
eine und $\T$ ohne das andere sind zwei echte Ideale, die $\T$ überdecken.
`reduction.py` (neu) prüft die Richtung, die der Beweis behauptet, an $3513$
Paaren $(\T,t)$ mit zufälligen Massen beider Vorzeichen auf vier und fünf
Punkten: **null Abweichungen**. Verlustfrei ist die Reduktion nicht — in vier
dieser Fälle ist $\delta(t)$ auf $\T_{\le t}$ frei und auf $\T$ erzwungen, die
Aussage (R) ist also echt stärker als nötig. Für nichtnegative Massen, um die
es geht, kostet das nichts, weil dort ohnehin kein Ausfall vorkommt.

**Nullmassen fallen weg.** Ist $m_c=0$ für ein $c\neq0$, so ändert das Streichen
von $c$ aus $\T$ kein einziges $\Psi(s,t)$, lässt $0$ kleinstes Element und
nimmt dem System nur Relationen. Was auf $\T$ ohne $c$ erzwungen ist, ist es auf
$\T$ erst recht. Man darf also **alle Massen außer $m_0$ als strikt positiv
annehmen**.

**Die scharfe Gestalt des Restdefekts.** Unter (R) ist $\delta(s)=0$ für alle
$s$ in $W:=\T$ ohne $z$, und die Relationen an den Paaren $(0,a)$ und $(0,z)$
geben unmittelbar $\Psi(a,0)=\delta(a)=0$ für $a\in W$ und
$\Psi(z,0)=\delta(z)$. Setzt man $g(c):=m_c\,\kappa(c,0)$, so heißt das: $g$
summiert sich über **jedes** Hauptideal $\T_{<a}$, $a\in W$, zu null, und der
ganze Defekt ist die Summe über das eine verbleibende Ideal,

$$\delta(z)=\sum_{c\in W}g(c),\qquad
  \sum_{c\in\T_{<a}}g(c)=0\ \text{ für alle } a\in W.$$

Die Vereinigung der $\T_{<a}$, $a\in W$, ist $W$ ohne die maximalen Elemente von
$W$ — der Defekt sitzt also genau auf der Antikette der maximalen Elemente von
$\T_{<z}$, und das ist dieselbe Stelle, an der schon der dritte Lauf hakte, nur
ohne $\Phi$, ohne $\gamma$ und ohne das obere Ende. `reduction.py` prüft diese
drei Identitäten über alle beschränkten Halbordnungen auf vier und fünf Punkten
mit positiven Massen nach: $243+608$ Fälle, keine Abweichung.

**Was den Rest schließen würde, und wo es gilt.** Gilt

> **(C4)** $\Psi(a,x)=0$, sobald $a<x$

am Paar $(a,z)$ für alle $a<z$, so folgt (R) in vier Zeilen: multipliziert man
$(\diamondsuit)$ an $(a,z)$ mit $m_a$ und summiert über $a<z$, so verschwindet
$\sum_a m_a\Psi(z,a)=\sum_{a,b<z}m_am_b\kappa(b,a)$ durch Antisymmetrie und es
bleibt $q(\T_{<z})\,\delta(z)=\sum_{a<z}m_a\Psi(a,z)=0$; ist $q(\T_{<z})>0$, so
ist $\delta(z)=0$, und ist $q(\T_{<z})=0$, so sind bei $m\ge0$ alle Massen unter
$z$ null und $\Psi(z,\cdot)$ verschwindet ohnehin. Gleichwertig lautet (C4) am
Paar $(a,z)$: **$\Psi(z,\cdot)$ ist auf $\T_{<z}$ konstant.** Genau hier steht
das $q(\T_{<s})$ des Suchbefunds von `sharp.py`.

**(C4) ist bei nichtnegativen Massen falsch, bei positiven richtig.** Der
Rangvergleich über alle Halbordnungen mit kleinstem Element auf fünf Punkten und
alle Massenvektoren aus $\{0,1,2\}$ findet $864$ Ausfälle von (C4) — bei
durchweg null Ausfällen der Dualität. Der kleinste Zeuge hat
$\T_{<1}=\{0,2,3,4\}$ mit $0<4<3<1$ und $0<2<1$ und $m=(0,0,1,0,1)$: dort bleibt
$\Psi(3,1)=m_4\kappa(4,1)$ frei, obwohl $3<1$. Alle Ausfälle haben
verschwindende Massen **oberhalb** von $0$ — und die sind nach dem Absatz oben
wegzustreichen. Mit strikt positiven Massen sind es $0$ Ausfälle unter
$1539+7008$ Fällen, und ebenso $0$ unter denselben Fällen mit $m_0=0$ und sonst
positiven Massen. Damit:

> **(C4$^+$)** Sind alle $m_a$ mit $a\neq0$ strikt positiv und ist $m_0\ge0$, so
> ist $\Psi(a,x)=0$ für alle $a<x$.

Da ist der Ansatzpunkt des nächsten Laufs: (C4$^+$) ist genau so stark, wie es
sein muss, in genau dem Massenbereich, den die Streichung der Nullmassen
übriglässt, und es ist eine Aussage über **ein Paar** statt über einen ganzen
Lösungsraum.

## Sackgassen, dritter Nachtrag

* **$\Psi\equiv0$ zu vermuten** ist falsch, und zwar schon bei strikt positiven
  Massen. Gegenbeispiel von Hand, fünf Punkte: $0<p<s$, $0<q<x$, sonst alles
  unvergleichbar; mit $m_0>0$ erzwingen die Relationen $\kappa(0,\cdot)=0$ auf
  $p,q,s,x$ und $m_p\kappa(p,x)+m_q\kappa(q,s)=0$, mehr nicht, und
  $\Psi(s,x)=m_p\kappa(p,x)$ bleibt frei. $\delta$ verschwindet dort trotzdem.
  $\Psi$ lebt also auf den unvergleichbaren Paaren, und nur dort — das ist
  gerade die Aussage (C4), und sie ist die richtige Abschwächung.
* **Gewichtete Summen über $a<t$ ein zweites Mal ansetzen** bringt nichts Neues:
  die Gewichtung mit $m_a$ gibt $q(\T_{<t})\delta(t)=\sum_a m_a\Psi(a,t)$, jede
  andere Gewichtung $w$ gibt dieselbe Identität mit $\sum_a w_a$ und
  $\sum_{a>c}w_a$ an den Stellen von $q(\T_{<t})$ und $\nu_c$. Ohne (C4)
  schließt keine davon, mit (C4) schließt schon die einfachste.

## Der Halbordnungsfall, 2026-08-31 (fünfter Lauf): die flache Spitze ist bewiesen, (C5) ist falsch

Der vierte Lauf hatte den Fall auf **(R)** eingeschränkt — auf einer
Halbordnung mit kleinstem Element $0$ und größtem Element $z$ ist
$\Psi(z,z)=0$ — und als Hebel die Vermutung (C4$^+$) benannt. Dieser Lauf hat
den Hebel zerbrochen und stattdessen ein Stück des Falles **bewiesen**.

**(C5) ist falsch, und damit jede termweise Fassung.** Die naheliegende
Verschärfung von (C4), aus der (C4) in einer Zeile folgte — in
$\Psi(a,x)=\sum_{c<a}m_c\kappa(c,x)$ hat jeder Summand ein $c$ mit $c<a<x$, also
genügte

> **(C5)** $m_c\,\kappa(c,x)=0$, sobald es ein $b$ mit $c<b<x$ gibt —

ist bei strikt positiven Massen **falsch**. Zeuge, exakt nachgerechnet
(`c5.py`): $\T=\{0,3,4,2,1\}$ mit $0<3$, $0<4$, $3<2$, $4<2$, $2<1$, alle Massen
$1$ (und ebenso für $m_0=0$ und $m_0=2$). Dort ist $3<2<1$, aber
$\kappa(3,1)$ bleibt auf dem Lösungsraum **frei**; erzwungen ist allein die
Kombination $m_3\kappa(3,1)+m_4\kappa(4,1)$, die in $\Psi(2,1)$ auftritt. Die
Aussage (C4$^+$) selbst hält an derselben Stelle: $0$ Ausfälle unter $2052$
Konfigurationen auf vier und $10512$ auf fünf Punkten, Massen aus $\{1,2,3\}$
bzw. $\{1,2\}$ und $m_0$ auch $0$. **Folgerung für jeden späteren Lauf:** der
Beweis muss über $\Psi$ geführt werden, nicht über die einzelnen $\kappa(c,x)$;
$\Psi$ ist auf vergleichbaren Paaren null, seine Summanden sind es nicht.

**Bewiesen: die flache Spitze.** Vollständig, ohne Vermutung, und mit einer
Hypothese, die schwächer ist als Positivität.

> **Satz.** $\T$ endliche Halbordnung mit kleinstem Element $0$, Massen
> $m_a\in\R$ beliebig, $\kappa$ antisymmetrisch mit $(\diamondsuit)$. Sei
> $t\in\T$ derart, dass jedes $c$ mit $0<c<t$ ein Atom ist
> ($\T_{<c}=\{0\}$) — die Elemente unter $t$ bilden also eine Antikette
> $M:=\T_{<t}\setminus\{0\}$ —, und sei $q(M)=\sum_{c\in M}m_c\neq0$. Dann ist
> $\delta(t)=0$ und $\Psi(a,t)=0$ für jedes $a<t$.

*Beweis.* Nach der Idealreduktion des vierten Laufs darf $\T=\T_{\le t}$
angenommen werden, $t$ also größtes Element. Ist $M=\emptyset$, so ist $t=0$
(nichts zu zeigen) oder $t$ ein Atom, und $(\diamondsuit)$ an $(0,t)$ lautet
$0+m_0\kappa(0,0)=0+m_0\kappa(0,t)$, gibt also $\delta(t)=m_0\kappa(0,t)=0$.
Sei $M\neq\emptyset$. Für $c\in M$ ist $\Psi(c,s)=m_0\kappa(0,s)$ und
$\delta(c)=m_0\kappa(0,c)$.

1. $(\diamondsuit)$ an $(0,c)$, $c\in M$, gibt $\Psi(c,0)=\delta(c)$, also
   $m_0\kappa(0,c)=0$.
2. $(\diamondsuit)$ an $(c,t)$, $c\in M$: mit
   $\Psi(c,t)=m_0\kappa(0,t)$,
   $\Psi(t,c)=m_0\kappa(0,c)+\sum_{c'\in M}m_{c'}\kappa(c',c)$,
   $\delta(c)=m_0\kappa(0,c)$ und $\delta(t)=m_0\kappa(0,t)+R$ mit
   $R:=\sum_{c'\in M}m_{c'}\kappa(c',t)$ heben sich beide $m_0$-Terme heraus und
   es bleibt
   $$\sum_{c'\in M}m_{c'}\kappa(c',c) = R \qquad\text{für jedes } c\in M .$$
3. Multiplikation mit $m_c$ und Summation über $c\in M$ lässt die linke Seite
   $\sum_{c,c'\in M}m_cm_{c'}\kappa(c',c)$ durch Antisymmetrie verschwinden und
   gibt $q(M) R=0$, also $R=0$.
4. Ist $m_0=0$, so ist $\delta(t)=m_0\kappa(0,t)+R=0$ und
   $\Psi(a,t)=m_0\kappa(0,t)=0$ für $a\in M$, $\Psi(0,t)=0$ ohnehin. Ist
   $m_0\neq0$, so gibt Schritt 1 $\kappa(0,c)=0$ für alle $c\in M$, also
   $\Psi(t,0)=\sum_{c\in M}m_c\kappa(c,0)=-\sum_{c\in M}m_c\kappa(0,c)=0$, und
   $(\diamondsuit)$ an $(0,t)$ — $\Psi(t,0)=\delta(t)$ — gibt $\delta(t)=0$;
   mit Schritt 3 folgt $m_0\kappa(0,t)=\delta(t)-R=0$, also $\kappa(0,t)=0$ und
   $\Psi(c,t)=m_0\kappa(0,t)=0$ für jedes $c\in M$. $\square$

Der Satz enthält den Diamanten als den Fall $|M|=2$ — den kleinsten offenen
Fall, dessen Begründung im Manuskript der dritte Lauf des 2026-08-30 als falsch
nachgewiesen hatte und der seither ohne Beweis war. Er enthält ihn mit
beliebig vielen unvergleichbaren Atomen und, was mehr ist, mit der **scharfen**
Hypothese: gebraucht wird nicht $m_c>0$, sondern allein $q(M)\neq0$. Das ist
genau die Bedingung, die `sharp.py` am 2026-08-30 aus der Suche abgelesen hatte,
und sie erklärt das Gegenbeispiel des dritten Laufs: der Diamant mit
$m_a=1$, $m_b=-1$ hat $q(M)=0$. Fallen kann die Dualität dort tatsächlich —
unter allen Halbordnungen mit kleinstem Element auf vier Punkten und Massen aus
$\{-2,\dots,2\}$ fällt sie an $60$ der $2625$ Stellen mit $q(M)=0$ —, die
Hypothese ist also nicht wegzulassen. Für eine echte Uhr ist sie automatisch:
$q$ ist ein Maß, und $q(M)=0$ hieße, kein Element von $M$ ist ein Atom.

**Nachgerechnet.** `flat.py` (neu) zählt alle Halbordnungen der Höhe $\le2$ mit
kleinstem Element auf bis zu **sechs** Punkten auf, wo die vollständige
Aufzählung von `posetsearch.py` nicht mehr hinreicht, und prüft Dualität und
(C4$^+$) durch Rangvergleich: $1053+21141+80736$ Konfigurationen, kein Ausfall.
Die scharfe Fassung — Massen beider Vorzeichen, geprüft nur an den Stellen $t$,
an denen die Hypothese des Satzes gilt — ergibt $10500$ Stellen auf vier Punkten
(alle Massenvektoren aus $\{-2,\dots,2\}$) und $5071$ auf fünf Punkten
(Stichproben), ebenfalls ohne Ausfall.

**Was damit vom Halbordnungsfall bleibt.** Die Idealreduktion und dieser Satz
erledigen jedes $t$, unter dem nur Atome liegen. Offen ist (R) für ein $t$, in
dessen Ideal eine Kette $0<a<b<t$ vorkommt — der Zeuge gegen (C5) oben ist der
kleinste solche Fall, und er zeigt zugleich, woran der Beweis dort anders
aussehen muss: Schritt 2 des obigen Beweises benutzt, dass $\Psi(c,t)$ für
alle $c\in M$ **dieselbe** Größe $m_0\kappa(0,t)$ ist. Sobald $\T_{<t}$ zwei
Stockwerke hat, ist das nicht mehr so, und die gewichtete Summe aus Schritt 3
schließt nicht mehr.

**Ein neues Werkzeug: der Zeuge statt der Antwort** (`certificate.py`). Der
Rangvergleich sagt, *dass* ein Funktional auf dem Lösungsraum verschwindet;
`certificate.py` rechnet mit sympy und symbolischen Massen die
Linearkombination der Relationen aus, die es *ist*. Am Diamanten kommt für
$\kappa(1,2)$ der Faktor $1/(m_1+m_2)$ heraus — dort sitzt die Positivität,
sichtbar statt vermutet —, für „drei Atome unter der Spitze" die Kombination
$\frac1{q(M)}\sum_{c\in M}m_c R_{(c,z)} + \frac1{m_0}\sum_{c}m_cR_{(0,c)} -
R_{(0,z)}$, also genau die vier Schritte des obigen Beweises. Für die
Fortsetzung ist das der schnellste Weg, aus einem gerechneten Fall ein Argument
abzulesen.

**Eine Umformung, die das Rechnen kürzt.** Mit
$\mu_s:=\sum_{a<s}m_a\varepsilon_a$ ist $(\diamondsuit)$ gleichwertig zu
$$\langle \mu_s-\mu_t, \kappa(\cdot,s)-\kappa(\cdot,t)\rangle = 0
  \qquad\text{für alle } s,t,$$
denn beide Seiten sind $\Psi(s,s)-\Psi(s,t)-\Psi(t,s)+\Psi(t,t)$. Gleichwertig:
die Bilinearform $(x,y)\mapsto \sum_s (\sum_{a<s}x_a) m_s\sum_t\kappa(s,t)y_t$
ist auf dem Hyperraum $\{\sum_i x_i=0\}$ antisymmetrisch. In dieser Gestalt ist
sofort zu sehen, dass nur Differenzen $\mu_s-\mu_t$ eingehen — der Grund, aus
dem alle Beweise hier mit dem kleinsten Element als Bezugspunkt arbeiten.

## Sackgassen, vierter Nachtrag

* **(C5)**, also jede termweise Fassung von (C4): widerlegt, siehe oben. Wer
  $\kappa(c,x)=0$ für $c<b<x$ zeigen will, sucht etwas Falsches.
* **Die Reduktion „ein maximales Element von $\T_{<z}$ streichen"** ist keine.
  Das Streichen eines Elements $w$, das nicht das größte ist, ändert
  $\Psi(z,t)$ um $m_w\kappa(w,t)$; eine Lösung auf $\T$ schränkt sich also
  nicht ein. Nur **abwärtsabgeschlossene** Teilmengen erben $(\diamondsuit)$,
  und das ist die Idealreduktion des vierten Laufs.
* **„Auf $\kappa(w,\cdot)$ wirken keine Relationen aus $\T_{<z}$"** ist falsch,
  auch wenn $w$ das größte Element von $\T_{<z}$ ist: als *zweites* Argument
  kommt $w$ in jedem $\Psi(s,w)$ vor. Wer das übersieht, hält den Fall
  „$\T_{<z}$ hat ein größtes Element" für offen, obwohl ihn die Kettenrechnung
  erledigt.

## Der Halbordnungsfall, 2026-08-31 (sechster Lauf): der Fall ist geschlossen

Der offene Punkt aus fünf Läufen — die Dualität für eine rein atomare Uhr mit
**unvergleichbaren** Atomen — ist bewiesen, und zwar in einer Allgemeinheit, die
die bisherigen Teilergebnisse enthält: beliebige endliche Halbordnung, kein
kleinstes Element nötig, kein größtes, keine Antikettenbedingung, keine
Idealreduktion. Gebraucht wird allein, dass die Massen **nichtnegativ** sind —
und das sind sie, weil $q$ ein Maß ist.

> **Satz.** Sei $\T$ eine endliche Halbordnung, $m:\T\to[0,\infty)$, und sei
> $\kappa:\T\times\T\to\R$ antisymmetrisch mit $(\diamondsuit)$, also
> $\Psi(s,t)+\Psi(t,s)=\Psi(s,s)+\Psi(t,t)$ für alle $s,t$, wobei
> $\Psi(s,t)=\sum_{a<s}m_a\kappa(a,t)$. Dann ist $\delta:=\operatorname{diag}\Psi
> \equiv 0$.

Der Beweis wechselt die Sprache: statt einzelner Relationen an einzelnen Paaren
eine Matrizenidentität, statt einer Induktion über die Halbordnung ein
Abzählargument über den Nilpotenzindex.

### Die Matrixgestalt

Setze, mit $\T$ als Indexmenge, $V_{s,a}:=[a<s]\,m_a$ und $K_{a,b}:=\kappa(a,b)$,
also $K^{\mathsf T}=-K$. Dann ist $\Psi=VK$ als Matrix und $\delta$ ihre
Diagonale, und $(\diamondsuit)$ lautet Eintrag für Eintrag

$$VK+(VK)^{\mathsf T}=\delta\mathbb 1^{\mathsf T}+\mathbb 1\delta^{\mathsf T}.
  \tag{S}$$

### Die Paarungsidentität, zwei Zeilen

Für **jede** symmetrische Matrix $T$ ist $\operatorname{tr}(TVK)
=\operatorname{tr}\bigl(T(VK)^{\mathsf T}\bigr)$ — man transponiert unter der
Spur und schiebt zyklisch —, also nach (S)

$$2\operatorname{tr}(TVK)
 =\operatorname{tr}\bigl(T[VK+(VK)^{\mathsf T}]\bigr)
 =\mathbb 1^{\mathsf T}T\delta+\delta^{\mathsf T}T\mathbb 1
 =2\,\langle\delta,\;T\mathbb 1\rangle .$$

Ist überdies $TV$ **symmetrisch**, so ist $\operatorname{tr}(TVK)=0$: die Spur
eines Produkts aus einer symmetrischen und einer antisymmetrischen Matrix
verschwindet. Zusammen:

> **(C)** Ist $T$ symmetrisch und $TV$ symmetrisch, so ist
> $\langle\delta,T\mathbb 1\rangle=0$.

Damit hängt alles an der Frage, welche Vektoren als $T\mathbb 1$ vorkommen. Setze

$$\mathcal L:=\{\,T\mathbb 1\;:\;T=T^{\mathsf T},\ TV=V^{\mathsf T}T\,\}.$$

Ist $e_t\in\mathcal L$, so ist $\delta(t)=0$. Die Umkehrung gilt ebenfalls und
ist am Rechner bestätigt (siehe unten): $\mathcal L$ ist **genau** der Raum der
erzwungenen Stellen. Der Grund ist, dass die $\binom n2$ Relationsmatrizen
$X_{st}=(e_s-e_t)(e_s-e_t)^{\mathsf T}$ eine Basis von
$\{S=S^{\mathsf T}: S\mathbb 1=0\}$ bilden und $\delta(t)$ genau dann im Spann
der Relationen liegt, wenn $E_{tt}-S$ für ein solches $S$ die Bedingung
„$(E_{tt}-S)V$ symmetrisch" erfüllt.

### Wo die Nichtnegativität eingeht, und nur dort

$V$ ist nilpotent: $V_{s,a}\neq0$ verlangt $a<s$, also ist $V$ in jeder linearen
Erweiterung strikt dreieckig. Sei $r$ der Nilpotenzindex, $V^r=0\neq V^{r-1}$.

> **Lemma.** Ist $m\ge0$, so ist $V^k\mathbb 1=0$ genau dann, wenn $V^k=0$.

*Beweis.* $V$ hat nichtnegative Einträge, also auch $V^k$, und $V^k\mathbb 1$ ist
der Vektor der Zeilensummen von $V^k$. Eine nichtnegative Matrix mit lauter
Zeilensummen $0$ ist die Nullmatrix. $\square$

Das ist die ganze Rolle der Positivität — eine Zeile. Insbesondere ist
$V^{r-1}\mathbb 1\neq0$: der Vektor $\mathbb 1$ hat im $\R[x]$-Modul
$(\R^\T,\,x\cdot{}=V)$ **maximale Ordnung**.

### Die Konstruktion von $T$, explizit

> **Satz.** Ist $V$ nilpotent vom Index $r$ und $V^{r-1}\mathbb 1\neq0$, so ist
> $\mathcal L=\R^\T$.

Begrifflich: ein Element maximaler Ordnung erzeugt einen direkten Summanden, und
auf $\R[x]/(x^{n_1})\oplus\dots$ ist eine invariante symmetrische Form durch
Funktionale $\ell_{ij}$ auf $\R[x]/(x^{\min(n_i,n_j)})$ gegeben; steht
$\mathbb 1$ im größten Summanden, so ist $\min(n_1,n_j)=n_j$, und
$B(\mathbb 1,\cdot)$ ist auf jedem Summanden frei. Für die Formalisierung ist die
Modulzerlegung aber unnötig, denn die Konstruktion lässt sich hinschreiben.

Wähle $i^*$ mit $(V^{r-1}\mathbb 1)_{i^*}\neq0$ und setze
$\lambda:=(V^{r-1}\mathbb 1)_{i^*}^{-1}e_{i^*}$ sowie
$p_k:=(V^{r-1-k})^{\mathsf T}\lambda$ für $0\le k\le r-1$. Dann ist

$$V^{\mathsf T}p_k=p_{k-1}\ (k\ge1),\qquad V^{\mathsf T}p_0=0,\qquad
  p_0^{\mathsf T}\mathbb 1=1 .$$

Sei $(w_k)_{k<r}$ das Inverse von $\sum_k(p_k^{\mathsf T}\mathbb 1)x^k$ in
$\R[x]/(x^r)$ — es existiert, weil der konstante Term $1$ ist — und
$\hat p_k:=\sum_{j\le k}w_{k-j}p_j$. Diese erfüllen dieselbe Shiftrelation und
zusätzlich $\hat p_k^{\mathsf T}\mathbb 1=[k=0]$. Setze schließlich
$\psi_k:=(V^{\mathsf T})^k e_t$ und $c_j:=(V^j\mathbb 1)_t$ (mit $c_j=0$ für
$j\ge r$) und

$$T:=\sum_{k=0}^{r-1}\bigl(\hat p_k\psi_k^{\mathsf T}
   +\psi_k\hat p_k^{\mathsf T}\bigr)
   -\sum_{k,l=0}^{r-1}c_{k+l}\,\hat p_k\hat p_l^{\mathsf T}.$$

Dann ist $T$ symmetrisch nach Bauart; $T\mathbb 1=\sum_k c_k\hat p_k+\psi_0
-\sum_k c_k\hat p_k=e_t$; und $TV=V^{\mathsf T}T$, weil in beiden Produkten
dieselben drei Summen stehen — die Shifts
$\psi_k^{\mathsf T}V=\psi_{k+1}^{\mathsf T}$ und
$\hat p_l^{\mathsf T}V=\hat p_{l-1}^{\mathsf T}$ führen den ersten und den
zweiten Term ineinander über, und der dritte ist invariant, weil $c_{k+l}$ nur
von $k+l$ abhängt. **An dieser Stelle irrt man sich leicht:** im dritten Term von
$TV$ trifft das $V$ den *zweiten* Faktor $\hat p_l$, in $V^{\mathsf T}T$ den
*ersten*, und beide Male läuft der andere Index über den vollen Bereich; die
Randterme fallen weg, weil $c_j=0$ für $j\ge r$ ist. Wer nur einen der beiden
Indizes einschränkt, findet einen Defekt, den es nicht gibt.

### Was der Satz mit den früheren Ergebnissen macht

* **Die flache Spitze** (fünfter Lauf) ist der Spezialfall „$\T_{<t}$ ist
  $\{0\}$ plus eine Antikette". Ihre Hypothese $q(M)\neq0$ ist eine *andere*
  Abschwächung als $m\ge0$ und bleibt eigenständig richtig: sie erlaubt
  gemischte Vorzeichen. Für eine Uhr ist $m\ge0$ die einschlägige.
* **Die Idealreduktion** (vierter Lauf) wird nicht mehr gebraucht. Sie bleibt
  richtig und ist die Aussage, mit der man den Satz auf $\T_{\le t}$
  einschränkt, wenn man will; der Beweis oben braucht sie nicht.
* **Der Kettenfall** (`lem:atomgrid`, 2026-08-30) ist nicht subsumiert: er gilt
  für beliebige Massen $m_i\neq0$, also auch mit Vorzeichenwechsel, wo der
  heutige Satz nichts sagt. Für Uhren subsumiert der heutige Satz ihn.
* **(C4$^+$)** ist als Hebel gegenstandslos. Bewiesen ist sie nicht; gebraucht
  wird sie nicht mehr.
* **Der Diamant** mit $m_a=1$, $m_b=-1$, $m_0=0$ bleibt der Zeuge dafür, dass
  $m\ge0$ nicht wegzulassen ist, und das Kriterium erklärt ihn jetzt: dort ist
  $r=2$ und $V^{r-1}\mathbb 1=V\mathbb 1=0$, $\mathbb 1$ hat also **nicht**
  maximale Ordnung, und $\mathcal L$ ist echt kleiner als $\R^\T$.

### Nachgerechnet

`selfadjoint.py` (neu) prüft in exakter Bruchrechnung vier Dinge, jeweils über
**alle** Halbordnungen — auch ohne kleinstes Element — auf bis zu fünf Punkten:

1. **Das Kriterium als Äquivalenz.** „$\delta(t)$ ist erzwungen" (Rangvergleich
   wie in `antisym.py`) gegen „$e_t\in\mathcal L$", auch bei gemischten
   Vorzeichen, wo beide Seiten fallen dürfen: alle Halbordnungen auf bis zu vier
   Punkten, alle Massenvektoren aus $\{-1,0,1,2\}$, $228\,000$ Stellen,
   **null Abweichungen**. Das ist der schärfste der vier Punkte, denn er prüft
   nicht die Hinrichtung des Beweises, sondern die Behauptung, dass
   $\mathcal L$ die Lage vollständig beschreibt.
2. **Das Lemma** $V^k\mathbb 1=0\Leftrightarrow V^k=0$ für $m\ge0$:
   $6\,259\,626$ Potenzen, kein Ausfall.
3. **Die explizite Formel**: $T$ symmetrisch, $T\mathbb 1=e_t$,
   $TV=V^{\mathsf T}T$ — $265\,128$ Konstruktionen, kein Ausfall.
4. **Der Satz** über `antisym.duality_fails_at`: $89\,440$ Fälle, kein Ausfall.

Ende zu Ende, also im vollen System in $(\Phi,\gamma)$ statt in der
$\kappa$-Gestalt, mit `posetsearch.clock_sweep` gegengeprüft: $1539$ Fälle auf
vier Punkten (Massen aus $\{0,1,2\}$) und $7008$ auf fünf (Massen aus
$\{0,1\}$), kein Ausfall.

Jenseits der vollständigen Aufzählung — sie reicht nur bis fünf Punkte, und ein
Fehler in der Konstruktion von $T$ könnte an der Länge $r$ der Potenzkette
hängen — prüft `stress.py` (neu) $120$ zufällige Halbordnungen auf sechs, sieben
und acht Punkten mit Massen aus $\{0,1,2,5,7\}$: kein Dualitätsausfall und kein
Formelausfall.

### Was zu formalisieren ist

Der Beweis zerfällt in vier Aussagen, von denen drei reine Matrizenalgebra sind
und weder Uhr noch Maß noch Halbordnung kennen:

* `Matrix.trace_mul_eq_zero_of_isSymm_of_transpose_eq_neg`: für `A.IsSymm` und
  `Bᵀ = -B` ist `(A * B).trace = 0`. Mathlib hat `Matrix.IsSymm`
  (`LinearAlgebra/Matrix/Symmetric.lean:35`) und `Matrix.trace_mul_comm`
  (`LinearAlgebra/Matrix/Trace.lean:158`); ein Prädikat für
  „schiefsymmetrisch" im schlichten Sinn `Bᵀ = -B` gibt es **nicht** —
  `Matrix.IsSkewAdjoint` (`LinearAlgebra/Matrix/SesquilinearForm.lean:562`) ist
  relativ zu einer Form `J`. Die Bedingung wird also ausgeschrieben.
* `trace_mul_eq_dotProduct_diag_of_isSymm`: die Paarungsidentität
  `(T * V * K).trace = δ ⬝ᵥ (T *ᵥ 1)` unter (S), für `T.IsSymm`.
* `exists_isSymm_mulVec_one_eq_single`: die Konstruktion oben, aus `V ^ r = 0`
  und `V ^ (r-1) *ᵥ 1 ≠ 0`.
* `mulVec_one_eq_zero_iff_of_nonneg`: das Lemma, und der einzige Punkt, an dem
  `0 ≤ m` vorkommt.

Erst danach kommt die Uhr. `atomGrid_symm` bleibt der kleinste Einstieg, aber
der Zielsatz `duality_of_atomic` verliert seine Vergleichbarkeitshypothese.

## Sackgassen, fünfter Nachtrag

* **Nach einer Induktion über die Halbordnung suchen.** Fünf Läufe haben es
  versucht — von unten, von oben, über Ideale, über die Antikette der maximalen
  Elemente. Der Beweis, der trägt, induziert über gar nichts: er ersetzt die
  Relationen durch eine Spur und die Halbordnung durch den Nilpotenzindex von
  $V$. Wer den Fall weiter aufteilt, arbeitet gegen die Struktur.
* **Die Positivität dort suchen, wo sie sichtbar ist.** `certificate.py` zeigt
  am Diamanten den Faktor $1/(m_1+m_2)$, und der fünfte Lauf hat daraus die
  scharfe Hypothese $q(M)\neq0$ abgelesen. Für den allgemeinen Fall führt das in
  die Irre: dort sitzt die Positivität nicht in einem Nenner, sondern in der
  Aussage „eine nichtnegative Matrix mit lauter Zeilensummen null ist null".

## Der Halbordnungsfall im Manuskript, 2026-08-31 (siebter Lauf)

Der Satz des sechsten Laufs steht jetzt im Manuskript, und beim Aufschreiben ist
eine Lücke sichtbar geworden, die keiner der sechs Läufe notiert hatte: **die
zweite Konvention.**

### Was eingetragen ist

Vier Stücke, hinter `rem:atomicdual` und vor `rem:dualscope`:

* `lem:selfadjoint` — die reine Matrizenaussage. Ist $V$ nichtnegativ und
  nilpotent, so gibt es zu jedem $t$ ein symmetrisches $T$ mit
  $TV=V^{\mathsf T}T$ und $T\mathbb 1=e_t$. Der Beweis ist der des PROTOKOLLs in
  drei Schritten: Zeilensummen (dort geht $m\ge0$ ein, und nur dort), die duale
  Kette $\hat p_k$, die explizite Formel für $T$.
* `prop:atomicposet` — die Uhr. Rein atomare Uhr, endlich viele Atome unter
  $t^*$, **keine** Bedingung an ihre gegenseitige Lage, $\Phi(t^*,0)=\Phi(0,t^*)$.
  Der Beweis führt die Reduktion aus, die im PROTOKOLL nur behauptet war: aus
  \eqref{eq:incrementrep} folgt $A(s,t)-B(s,t)=A(s,0)-B(0,t)$, daraus
  $(\diamondsuit)$ für $\Psi(s,t)=\sum_{a\prec s}m_a\kappa(a,t)$ und
  $\Psi(t,t)=\Phi(t,0)-\Phi(0,t)$; der Rest ist die Spuridentität. Dass $\prec$
  auf einer Präordnung transitiv und irreflexiv ist, ist eigens nachgerechnet —
  darauf ruht die Nilpotenz.
* `rem:atomicposet` — was die beiden atomaren Sätze je geben. Sie sind nicht
  geschachtelt: die Kette erlaubt Massen beider Vorzeichen und liefert die
  stärkere Symmetrie, die Halbordnung verlangt $m\ge0$ und liefert nur den
  Defekt. Für eine Uhr enthält der zweite den ersten. Das Kriterium
  $e_{t^*}\in\mathcal L$ erklärt dort den Diamanten.
* Statustabelle, Bündeltabelle und die fünf Stellen, die die Kettenhypothese
  zitierten (§1, `rem:dualscope`, §9 und zwei in §5.x).

Danach meldet `python3 check.py` `clean` (126 Seiten, keine undefinierten
Referenzen, größte Überlänge 7.7pt wie zuvor). `selfadjoint.py` ist vor dem
Eintrag noch einmal gelaufen: alle vier Punkte, kein Ausfall.

### Die Lücke, die dabei sichtbar wurde: $\iota=\mathrm o$

Der Satz ist für $\iota=\mathrm p$ bewiesen und **nur** dafür. Die Konvention
geht an genau einer Stelle ein, aber an einer tragenden: unter $\iota=\mathrm p$
ist $[0,s)=\T_{<s}$ und $V_{s,a}=[a\prec s]m_a$ strikt dreieckig, also
nilpotent. Unter $\iota=\mathrm o$ ist $(0,s]=\T_{\le s}\setminus\T_{\le 0}$,
also $V_{s,a}=[a\le s,\,a\ne0]m_a$ mit $V_{s,s}=m_s$ auf der Diagonale —
**nicht nilpotent**, und `lem:selfadjoint` greift nicht.

Auf einer Kette ist das kein Problem: `prop:atomicdual` erledigt
$\iota=\mathrm o$ durch die Spiegelung $(i,j)\mapsto(M-i,M-j)$ des Gitters. Eine
Halbordnung bietet keine Spiegelung — es gibt kein größtes Element, an dem man
aufhängen könnte, und die Aussage ist an $0$ verankert. Der Satz „die
o-Konvention ist die p-Konvention für die umgekehrte Ordnung", der so in
`TauCeti/MartingaleProblems` bei `duality_of_atomic` stand, ist damit für eine
Halbordnung **falsch**; die Roadmapzeile ist korrigiert.

**Evidenz statt Beweis.** `oconvention.py` (neu) baut dasselbe volle System in
$(\Phi,\gamma)$ wie `posetsearch`, nur mit $(0,s]$ statt $[0,s)$, und läuft über
alle Halbordnungen mit kleinstem Element auf bis zu fünf Punkten mit
nichtnegativen Massen: $81+1539+7008$ Fälle, **kein Ausfall**. Die Aussage ist
also vermutlich richtig; was fehlt, ist der Beweis. Sie steht deshalb als
einzige Zeile „verified, not proved" in der Statustabelle von
`rem:atomsnotchange` und als Punkt 1 des Rückstaus.

**Und der Ansatz ist schon eingegrenzt.** Der Spurteil des Beweises — (C) und
die Paarungsidentität — benutzt die Nilpotenz **nirgends**; er braucht nur $T$
symmetrisch, $TV$ symmetrisch und $K$ antisymmetrisch, und all das ist
konventionsfrei. Die ganze Last liegt auf der Frage, ob
$\mathcal L=\{T\mathbb 1: T=T^{\mathsf T},\,TV=V^{\mathsf T}T\}$ auch für das
reflexive $V$ ganz $\R^\T$ ist. `oconvention.criterion_o` prüft genau das und
vergleicht $\mathcal L$ Stelle für Stelle mit den tatsächlich erzwungenen: über
alle Halbordnungen auf drei und vier Punkten mit Massen aus $\{0,1,2\}$,
$243+6156$ Stellen, sind **beide** Abweichungsrichtungen null — $\mathcal L$
beschreibt die Lage auch unter $\iota=\mathrm o$ vollständig, und in jedem
geprüften Fall ist $\mathcal L=\R^\T$.

Damit ist die offene Frage keine Frage über Uhren mehr, sondern eine über
Matrizen, und sie lautet: *Sei $\prec$ eine strikte Halbordnung auf endlichem
$F$, sei $m:F\to[0,\infty)$ mit $m_0=0$, und sei
$V_{s,a}=[a\prec s\ \text{oder}\ a=s\ne 0]\,m_a$. Ist dann
$\mathcal L=\R^F$?* Für nilpotentes $V$ ist die Antwort der Satz des sechsten
Laufs; hier ist $V=N+D$ mit $N$ nilpotent und $D=\operatorname{diag}(m)$, und
zu klären ist, was an die Stelle der maximalen Ordnung von $\mathbb 1$ tritt.
Zwei Beobachtungen, die dabei zu benutzen sind: Zeile und Spalte $0$ von $V$
verschwinden, und $D$ und $N$ kommutieren im Allgemeinen nicht.

### Sackgassen, sechster Nachtrag

* **Annehmen, die Konvention sei eine Formsache.** Fünf Läufe lang war
  „$\iota=\mathrm o$ ist $\iota=\mathrm p$ nach Spiegelung" ein Satz, den
  niemand nachgerechnet hat, weil er auf der Kette stimmt. Er stimmt dort, weil
  eine endliche Kette ein größtes Element hat. Was allgemein bleibt, ist nicht
  die Spiegelung, sondern die Beobachtung, dass $\iota$ nur das Intervall
  ändert — und damit die Diagonale von $V$.

## Die o-Konvention, 2026-08-31 (achter Lauf): die Aussage ist falsch

Der siebte Lauf ließ die o-Fassung des Halbordnungssatzes als „verified, not
proved" stehen und nannte als Ansatz die Frage, ob $\mathcal L=\R^F$ auch für
das reflexive $V$ gilt. Die Antwort ist **nein**, und mit ihr fällt die Aussage
selbst: unter $\iota=\mathrm o$ ist der Satz auf einer Halbordnung **falsch**.
Der kleinste Zeuge steht auf vier Punkten, hat nichtnegative Massen und ist von
Hand nachzurechnen.

### Der Zeuge

$\T=\{0,a,b,c\}$ mit $0\prec a\prec c$, $0\prec b\prec c$ und $a,b$
unvergleichbar — der Diamant. Massen $m_a=1$, $m_b=4$, $m_c=2$, also
$(0,a]=\{a\}$, $(0,b]=\{b\}$, $(0,c]=\{a,b,c\}$. Setze

$$\gamma(0,c)=-1,\quad \gamma(a,c)=-2,\quad \gamma(b,c)=1,$$

$$\Phi(0,c)=-2,\quad \Phi(a,c)=-4,\quad \Phi(b,c)=2,$$

und $\gamma=\Phi=0$ an jedem anderen Paar. Beide Zuwachsdarstellungen von
`eq:incrementrep` gelten an jedem vergleichbaren Paar: in der ersten ist allein
die Spalte $t=c$ nicht $0=0$, in der zweiten allein der Summand $u=c$, und die
fünf Intervalle geben dann je eine Identität zwischen zwei ganzen Zahlen. Aber

$$\Phi(c,0)-\Phi(0,c) = 0-(-2) = 2 \ne 0.$$

Dieselbe Uhr trägt unter $\iota=\mathrm p$; die Konventionen unterscheiden sich
also nicht in der Beweisbarkeit, sondern in der Wahrheit.

### Warum, und wie dünn

Der Spurteil bleibt, wie der siebte Lauf schon belegt hatte, konventionsfrei;
was Schritt 3 braucht, ist unverändert $e_{t^*}\in\mathcal L$. Neu ist die
richtige Fassung des Kriteriums: **$\mathcal L=\R^F$ genau dann, wenn
$\mathbb 1$ maximale Ordnung hat**, und maximale Ordnung heißt allgemein
$\mu_{\mathbb 1}=\mu_V$ — das Minimalpolynom des Vektors ist das der Matrix. Für
nilpotentes $V$ ist $\mu_V=x^r$ und die Bedingung ist $V^{r-1}\mathbb 1\ne0$;
das ist genau `lem:selfadjoint`. Für reflexives $V$ ist sie nicht mehr
automatisch.

Am Diamanten steht sie explizit da. Auf den drei Atomen $a,b,c$ ist

$$V=\begin{pmatrix} m_a&0&0\\ 0&m_b&0\\ m_a&m_b&m_c\end{pmatrix},$$

die Eigenwerte sind $m_a,m_b,m_c$, der Linkseigenvektor zu $m_c$ ist
$w=(m_a/(m_c-m_a),\ m_b/(m_c-m_b),\ 1)$, und

$$\langle w,\mathbb 1\rangle=0
  \iff
  \frac{m_a}{m_c-m_a}+\frac{m_b}{m_c-m_b}+1=0
  \iff
  m_c^2=m_am_b .$$

Die Masse der Spitze ist das **geometrische Mittel** der beiden unvergleichbaren
Massen. Das ist eine abgeschlossene algebraische Bedingung, und sie ist echt:
auf jeder geprüften Halbordnung fallen zufällig gezogene Massen nicht. Der Satz
ist unter $\iota=\mathrm o$ also außerhalb einer Nullmenge richtig und auf ihr
falsch — nicht „fast bewiesen", sondern falsch.

Der kleinste ganzzahlige Fall ist $(1,4,2)$; $(1,9,3)$, $(4,9,6)$, $(2,8,4)$,
$(1,16,4)$ und $(1,1/4,1/2)$ tun es ebenso, und $m_a=m_b$ scheidet aus, weil
dann $m_c=m_a$ ist und die Eigenwerte zusammenfallen.

### Warum sieben Läufe es nicht gesehen haben

`oconvention.sweep_o` lief erschöpfend, aber auf fünf Punkten nur über Massen
aus $\{0,1\}$, und auf vier Punkten über $\{0,1,2\}$, wo $m_c^2=m_am_b$ mit
$m_a\ne m_b$ nicht vorkommt — der kleinste Fall braucht die 4. `criterion_o`
prüfte das Kriterium auf drei und vier Punkten, wo $\mathbb 1$ stets maximale
Ordnung hat; der Satz „in jedem geprüften Fall ist $\mathcal L=\R^\T$" war
richtig und trug nichts. Die Lehre ist nicht, dass zu wenig gerechnet wurde,
sondern dass ein Gitter, das eine algebraische Bedingung gar nicht treffen kann,
keine Evidenz gegen sie ist.

### Nachgerechnet

* `omaxorder.py` (neu) fragt nach der maximalen Ordnung von $\mathbb 1$ unter
  $\iota=\mathrm o$: auf drei (81 Fälle) und vier Punkten (1539) hat jeder sie,
  auf fünf (53217) haben 144 sie nicht. Es prüft zwei Dinge, die überall tragen:
  **das Kriterium** („maximale Ordnung" gegen „$\mathcal L=\R^F$",
  81+1539+53217 Fälle, keine Abweichung in beiden Richtungen) und **die
  Reduktion** auf $F'=\{m>0\}$ — mit $Z=\{m=0\}\ni 0$ zerfällt $V$ in die Blöcke
  $0,A,0,B$ mit $B=P'D'$ invertierbar, und $\mathbb 1$ hat maximale Ordnung für
  $V$ genau dann, wenn $\mathbb 1_{F'}$ sie für $B$ hat (1539+53217 Fälle, keine
  Abweichung). Diese Reduktion ist überdies bewiesen: aus $p(B)\mathbb 1_{F'}=0$
  und $g \mid p$ folgt $q(B)=-p(0)B^{-1}$, und die $Z$-Komponente von
  $p(V)\mathbb 1$ ist $p(0)$ mal
  $\mathbb 1_Z-P_{ZF'}(P')^{-1}\mathbb 1_{F'}$, deren Eintrag bei $0$ den Wert
  $1$ hat, weil kein Punkt von $F'$ unter $0$ liegt; also $p(0)=0$.
* `oconvention.criterion_o` ist zum ersten Mal auf **fünf** Punkten gelaufen
  (Massen aus $\{0,1,2\}$, 266085 Stellen): „in $\mathcal L$, aber nicht
  erzwungen" und „erzwungen, aber nicht in $\mathcal L$" sind beide null. Der
  siebte Lauf hatte das nur auf drei und vier Punkten, wo $\mathcal L$ ohnehin
  alles ist; jetzt ist es dort geprüft, wo $\mathcal L$ echt kleiner wird. Damit
  ist der Ausfall der o-Aussage nicht nur belegt, sondern **erklärt**:
  $\mathcal L$ beschreibt die erzwungenen Stellen genau, und wo $\mathbb 1$ die
  maximale Ordnung verliert, bleibt der Defekt frei.
* `ocounter.py` (neu) stellt den Ausfall im **vollen** homogenen System in
  $(\Phi,\gamma)$ fest, nicht nur im auf $\gamma$ reduzierten, und beide Wege
  sind einig. Erschöpfend: drei Punkte, Massen aus $\{0,1,2\}$ — kein Ausfall;
  vier Punkte, Massen aus $\{0,1,2,3\}$ (4864 Fälle) — kein Ausfall; fünf
  Punkte, Massen aus $\{0,1,2\}$ (53217 Fälle) — 144 Ausfälle.
* `odiamond.py` (neu) prüft die Vorhersage $m_c^2=m_am_b$ am Diamanten gegen
  zwölf Massenvektoren, beide Systeme und beide Konventionen: sie trifft genau.
* `certificate_o.py` (neu) schreibt $\Phi$ und $\gamma$ aus und rechnet beide
  Zuwachsdarstellungen an jedem vergleichbaren Paar nach, für den Diamanten und
  für den Zeugen auf fünf Punkten.
* `oshape.py` (neu) misst, wie dünn der Ausfall ist: auf der Halbordnung des
  Fünf-Punkte-Zeugen fällt kein einziger von 40 zufälligen Massenvektoren aus
  $\{1,\dots,97\}$, aus $\{1,2,3,4\}^4$ genau sechs; über alle Halbordnungen mit
  kleinstem Element auf vier und fünf Punkten mit zufälligen paarweise
  verschiedenen Massen aus $\{1,\dots,200\}$ (114+657 Fälle) fällt keiner.

### Was das für die Aufgabe heißt

Rückstaupunkt 1 ist erledigt, aber nicht durch einen Beweis: die Zeile
„verified, not proved" der Statustabelle wird zu **„falsch"**, und das
Manuskript sagt das jetzt (`rem:atomicposet`, letzter Absatz, mit dem Zeugen und
der Bedingung $m_c^2=m_am_b$). Die Hypothese $\iota=\mathrm p$ von
`prop:atomicposet` ist damit keine Beweisbequemlichkeit mehr, sondern eine
Eigenschaft der Aussage. `check.py` meldet `clean`, 126 Seiten, größte
Überlänge 7.7pt wie im Ausgangszustand.

Was als **richtige** Aussage übrig bleibt und formulierbar wäre: unter
$\iota=\mathrm o$ verschwindet der Defekt, sobald $\mathbb 1$ maximale Ordnung
für $V$ hat. Das ist keine Uhrenhypothese, sondern eine Bedingung an die Massen,
und der Preis für die Allgemeinheit ist, dass man ihr nicht ansieht, welche
Uhren sie trifft.

### Sackgassen, siebter Nachtrag

* **Ein Gitter für Evidenz halten.** $\{0,1\}$ auf fünf Punkten und $\{0,1,2\}$
  auf vier können $m_c^2=m_am_b$ mit $m_a\ne m_b$ nicht treffen. Wer eine
  Vermutung an einem Gitter prüft, prüfe zuerst, ob das Gitter die
  Ausnahmebedingung überhaupt enthalten kann. Umgekehrt hätte ein Zufallsvektor
  hier nichts gefunden — die Ausnahme ist eine Nullmenge. Gebraucht wurde beides:
  ein Gitter, das sie enthält, und die Frage, wonach man sucht.
* **Nach einem Ersatz für die Nilpotenz suchen.** Der siebte Lauf fragte, „was
  an die Stelle der maximalen Ordnung tritt". Nichts tritt an ihre Stelle: die
  maximale Ordnung ist die richtige Bedingung, in beiden Konventionen, und die
  Nilpotenz war nur der Grund, aus dem sie unter $\iota=\mathrm p$ geschenkt
  ist.

## Die gemischte Uhr, 2026-09-01 (neunter Lauf): bewiesen, sobald die Atome durch stetige Masse getrennt sind

Angegangen wurde Rückstaupunkt 1, zweite Hälfte: **Stufe 3, die gemischte Uhr**,
seit dem 2026-08-29 unberührt. Sie ist erledigt, unter einer Hypothese, die
genannt und nicht versteckt wird. Neu ist `Task23/mixed.py`.

### Die Aussage

> **Satz (gemischte Uhr).** Es gelte \eqref{T3}. Sei
> $q=\mu+\sum_{i=1}^N m_i\delta_{a_i}$ auf $\T_{\le t^*}$ mit $\mu$ atomlos,
> $0\le a_1<\dots<a_N\le t^*$ und $m_i>0$, und sei
> $$c_0=\mu(\T_{<a_1}),\quad c_j=\mu([a_j,a_{j+1}))\ (1\le j\le N-1),\quad
>   c_N=\mu([a_N,t^*))$$
> die stetige Masse zwischen den Atomen. Ist $c_j>0$ für $j=0,\dots,N-1$ — $c_N$
> darf verschwinden —, und erfüllen $\Phi,\gamma$ die Darstellung
> \eqref{eq:incrementrep} mit $\gamma_1=\gamma_2=\gamma$ nebst der
> Integrabilität \eqref{eq:calcint} in Uhrzeit, so gilt
> $$\Phi(t,0)=\Phi(0,t)\qquad\text{für \emph{jedes} } t\le t^*,$$
> und mehr: $\Phi(s,t)=\Phi(t,s)$ auf dem ganzen Quadrat.

Also: **stetige Masse zwischen je zwei Atomen genügt.** Nicht gebraucht werden
Translationsinvarianz, Regularität von $\gamma$, eine Bedingung an die Größe der
Massen und die Eckrelationen an zwei Atomen (dazu unten). Gebraucht wird
$m_i>0$, was für eine Uhr automatisch ist — anders als im Halbordnungsfall, wo
die Nichtnegativität eine echte Hypothese war.

### Schritt 0: der atomlose Fall, schärfer als `lem:calculus`

Auf einem Rechteck, auf dem die Uhr in beiden Koordinaten Lebesgue ist, sagt
\eqref{eq:incrementrep} mit $\gamma_1=\gamma_2$ nicht nur die Aussage von
`lem:calculus`, sondern

$$(\partial_x-\partial_y)\Psi=\gamma_1-\gamma_2=0 \quad\text{im Distributionssinn},
\qquad\text{also}\qquad \Psi(x,y)=f(x+y).$$

Die Kette dazu: $\Psi$ ist in jeder Variablen absolut stetig, also getrennt
stetig, also gemeinsam messbar und nach \eqref{eq:calcint} lokal integrierbar;
die schwachen Ableitungen sind $\gamma_1,\gamma_2$; eine Distribution, die von
einer konstanten Richtungsableitung annulliert wird, ist eine Funktion der
Querkoordinate; und aus „$\Psi(x,y)=f(x+y)$ fast überall" mit $f$ stetig und
$\Psi$ getrennt stetig folgt Gleichheit **überall**. Das ist der Grund, warum
der Satz oben „jedes $t$" sagt und nicht „fast jedes": das fast-überall in
`cor:atomless` ist ein Artefakt des Umwegs über `lem:calculus` (\EK{} 4.4.10),
nicht der Sache. Vermerkt als Auffälligkeit im Inventar.

### Schritt 1: Uhrzeit, Strecken und Lücken

$Q(s)=q(\T_{<s})$ bildet $\T_{\le t^*}$ auf $[0,L]$ ab bis auf die offenen
Lücken $G_i=(Q(a_i),Q(a_i)+m_i)$, eine je Atom. Wie in `cor:atomless` ist
$\Phi$ eine Funktion der $Q$-Werte, denn $q([s,s'))=0$ erzwingt
$\Phi(s,\cdot)=\Phi(s',\cdot)$. Was bleibt, ist eine Kette von Strecken

$$S_0=[\alpha_0,\beta_0],\ \dots,\ S_N=[\alpha_N,\beta_N],\qquad
\alpha_0=0,\quad \beta_i=\alpha_i+c_i,\quad \alpha_i=\beta_{i-1}+m_i,$$

und $\Psi$ lebt auf $\bigcup_i S_i$ zum Quadrat. Auf $S_i\times S_j$ ist die Uhr
in beiden Koordinaten Lebesgue, Schritt 0 gibt also

$$\Psi(x,y)=f_{ij}(x+y)\quad\text{auf } S_i\times S_j,\qquad
f_{ij}\in W^{1,1}(D_{ij}),\quad D_{ij}=[\alpha_i+\alpha_j,\ \beta_i+\beta_j].$$

Bemerkenswert: $D_{ij}=D_{ji}$, die beiden Funktionen leben auf **demselben**
Intervall. Der Defekt ist $\Psi(L,0)-\Psi(0,L)=f_{N0}(\beta_N)-f_{0N}(\beta_N)$.

### Schritt 2: die Kreuzungsrelation, und warum sie mehr sagt als ein Sprung

Sei $x$ über die Lücke $G_i$ geführt, $y\in S_j$ fest. Wegen
$[a_i,s')=\{a_i\}\cup(a_i,s')$ und dominierter Konvergenz für $s'\downarrow a_i$:

$$\Psi(\alpha_i,y)-\Psi(\beta_{i-1},y)=m_i\,\gamma(a_i,Q^{\leftarrow}(y)).$$

Der Sprung ist $m_i$ mal die **Zeile** $\gamma(a_i,\cdot)$. Und dieselbe Zeile
ist, nach der zweiten Darstellung in \eqref{eq:incrementrep} bei festem
$s=a_i$, die Dichte von $y\mapsto\Psi(\beta_{i-1},y)$, also
$\gamma(a_i,Q^{\leftarrow}(y))=f_{i-1,j}'(\beta_{i-1}+y)$ für fast alle
$y\in S_j$ — hier, und nur hier, geht $c_j>0$ ein. Mit $u=\beta_{i-1}+y$:

$$f_{ij}(u+m_i)=f_{i-1,j}(u)+m_i f_{i-1,j}'(u),\qquad u\in\beta_{i-1}+S_j,
\tag{B}$$

und symmetrisch, mit $x\in S_i$ fest und $y$ über $G_j$:

$$f_{ij}(u+m_j)=f_{i,j-1}(u)+m_j f_{i,j-1}'(u),\qquad u\in S_i+\beta_{j-1}.
\tag{C}$$

Das ist der ganze Gehalt der Atome. Der Kreuzungsoperator
$T_m=e^{-mD}(1+mD)$ hängt **nur an der Masse**, nicht daran, ob gerade $x$ oder
$y$ die Lücke überquert — genau das ist die Balance $\gamma_1=\gamma_2$ in
Operatorform, und genau daraus kommt die Symmetrie. Auf ganzen
Definitionsbereichen gelesen wäre der Satz die Trivialität, dass $T_{m_i}$ und
$T_{m_j}$ kommutieren (beide sind Funktionen von $D$); die Arbeit steckt darin,
dass (B) und (C) nur auf **Teilintervallen** gelten.

### Schritt 3: die Induktion über $d=i-j$

Sei $w_{ij}=f_{ij}-f_{ji}$ auf $D_{ij}$; zu zeigen ist $w_{ij}\equiv0$, denn
$w_{N0}(\beta_N)$ ist der Defekt. Abziehen der transponierten Relation von (B)
bzw. (C) gibt

$$w_{ij}=T_{m_i}w_{i-1,j}\ \text{auf }[\alpha_i+\alpha_j,\ \alpha_i+\beta_j],
\qquad
w_{i,j+1}(u+m_{j+1})=w_{ij}(u)+m_{j+1}w_{ij}'(u)\ \text{auf }
[\alpha_i+\beta_j,\ \beta_i+\beta_j].$$

Die beiden Intervalle sind das **untere** und das **obere** Stück von $D_{ij}$,
und sie stoßen im Punkt $\alpha_i+\beta_j$ aneinander. Induktion über
$d=i-j\ge0$ (der Fall $i<j$ folgt aus $w_{ij}=-w_{ji}$):

* $d=0$: $w_{ii}=0$, aus der Definition.
* $d-1\to d$: sei $i>j$, $i-j=d\ge1$. Auf dem unteren Stück ist
  $w_{ij}=T_{m_i}w_{i-1,j}=0$ nach Induktion ($i-1-j=d-1$; benutzt $c_j>0$,
  $j\le N-1$). Auf dem oberen Stück ist $w_{i,j+1}=0$ nach Induktion
  ($i-j-1=d-1$; benutzt $c_i>0$, was genau dann nötig ist, wenn das obere Stück
  nicht leer ist), also
  $$w_{ij}(u)+m_{j+1}w_{ij}'(u)=0,\qquad w_{ij}(\alpha_i+\beta_j)=0,$$
  und da $w_{ij}$ absolut stetig ist, gibt der integrierende Faktor
  $w_{ij}(u)=w_{ij}(\alpha_i+\beta_j)\,e^{-(u-\alpha_i-\beta_j)/m_{j+1}}=0$.

Fertig. Der Kern von $1+m\frac{\dif}{\dif u}$ ist $e^{-u/m}$, eindimensional,
und die Anfangsbedingung aus dem unteren Stück schneidet ihn weg: **das ist die
ganze Rolle der stetigen Masse.** Sie liefert die Stelle, an der die
Exponentialrichtung festgenagelt wird.

### Was der Beweis nicht braucht

Die **Eckrelationen**, an denen beide Koordinaten auf einem Atom stehen und
$\gamma(a_i,a_j)$ keine Dichte, sondern ein freier Wert ist:

$$\frac{f_{i-1,j}(\beta_{i-1}+\alpha_j)-f_{i-1,j-1}(\beta_{i-1}+\beta_{j-1})}{m_j}
=\frac{f_{i,j-1}(\alpha_i+\beta_{j-1})-f_{i-1,j-1}(\beta_{i-1}+\beta_{j-1})}{m_i}.
\tag{D}$$

Das ist wörtlich die Kreuzmultiplikation $(\ast)$ des rein atomaren Falls. Sie
gilt, sie steht im Modell, und der Beweis kommt ohne sie aus — `mixed.py` prüft
beides getrennt. Im rein atomaren Fall ist (D) alles, was übrig bleibt, und
`lem:atomgrid` ist der Satz darüber; in der gemischten Uhr mit getrennten Atomen
trägt allein (B)/(C). Die beiden Fälle sind also nicht Spezialfälle
voneinander, sondern zwei Enden.

### Abzählbar viele Atome

Häufen sich die Atome nur bei $t^*$ (Ordnungstyp $\omega$), so gilt der Satz
weiter: die Induktion läuft über endliche $d$ und braucht kein letztes Gebiet,
gibt also $\Phi(t,0)=\Phi(0,t)$ für jedes $t<t^*$; und
$\Phi(t^*,0)-\Phi(t,0)=\int_{[t,t^*)}\gamma(r,0)\,q(\dif r)\to0$ für
$t\uparrow t^*$ nach dominierter Konvergenz, ebenso in der zweiten Koordinate.
**Ordnungsdichte Atommengen bleiben offen** und sind davon unberührt: dort ist
nicht $c_j>0$ verletzt, sondern die Aufzählung der Atome als Kette
$a_1<a_2<\dots$ existiert nicht, und mit ihr fällt die Induktion über $d$.

### Nachgerechnet: `mixed.py`

Das Skript setzt Schritt 0 als Modellannahme voraus — $\Psi=f_{ij}(x+y)$ auf
$S_i\times S_j$ — und prüft alles Weitere exakt am vollen Lösungsraum. Die
$f_{ij}$ werden stückweise auf den Einheitsintervallen ihres
Definitionsbereichs angesetzt, jedes Stück in lokaler Koordinate mit der Basis
$1,\tau,\tau^2,\tau^3,e^{-\tau/m}$. Zwei Entscheidungen tragen das:

* **Lokale Koordinaten.** Alle $c_i,m_i$ sind ganzzahlig, alle Verschiebungen
  also auch; (B)/(C) ist damit ein koeffizientenweiser Vergleich zweier Stücke
  bei gleichem $\tau$, ohne Verschiebungskonstanten. Das hält die Matrix bei
  Größen der Ordnung $1$ — die Kernbestimmung per SVD ist gut konditioniert.
* **Die Exponentialfunktionen.** Sie sind mit Absicht in der Basis: der Kern von
  $1+mD$ ist die einzige Richtung, in der ein Gegenbeispiel Platz hätte. Über
  die Stücke hinweg wird nur Stetigkeit verlangt, denn mehr als absolute
  Stetigkeit ist von $f_{ij}$ nicht bekannt.

Befund, neun Konfigurationen mit $N=1,2,3$ Atomen und ungleichen Strecken und
Massen: der Defekt verschwindet auf einer Kernbasis, $\max<10^{-13}$, und die
volle Symmetrie $f_{ij}=f_{ji}$ ebenso. Dasselbe **ohne** die Eckrelationen (D),
sechs Konfigurationen — das ist die Probe auf den Beweis. Zwei Kontrollen:

* **Kanarienvogel.** Ohne die $y$-Kreuzungen (C) bleibt der Defekt stehen
  ($0.65$ bzw. $0.55$ bei $c=[1,3],m=[2]$ und $c=[2,1],m=[3]$), die Symmetrie
  fällt in allen vier Fällen. Der Test ist also nicht leer. Bei gleichen
  Strecken ($c=[1,1]$, $c=[1,1,1]$) verschwindet der Defekt auch ohne (C) — die
  symmetrische Konfiguration sieht zu wenig, und wer nur sie prüft, prüft
  nichts.
* **Probe aufs Modell.** Alle Strecken entartet ($c\equiv0$) ist die rein
  atomare Kette; das Modell reproduziert `prop:atomicdual`, Defekt und
  Antisymmetriedefekt null für $N=1,\dots,4$.

**Entartete Strecken, ein Befund über die Hypothese.** Läßt man einzelne $c_j$
verschwinden — zwei benachbarte Atome ohne stetige Masse dazwischen, oder ein
Atom ganz am Anfang —, so verschwindet der Defekt im Modell weiterhin (sechs
Konfigurationen, $\max<10^{-14}$). Die Hypothese $c_j>0$ ist also, soweit
geprüft, eine Hypothese des **Beweises** und nicht der Aussage. Das ist keine
Überraschung: fällt $c_j$ weg, so übernimmt an dieser Stelle (D), also der rein
atomare Mechanismus. Ein Beweis, der beide Mechanismen verschränkt, ist die
natürliche Fortsetzung und steht als Vorschlag im Inventar.

### Sackgassen, achter Nachtrag

* **Die gemischte Uhr numerisch prüfen wollen.** Eine Diskretisierung des
  stetigen Anteils ist eine rein atomare Uhr auf einer Kette, und für die ist
  die Dualität seit dem 2026-08-30 bewiesen. Jeder Test, der die stetige Masse
  durch viele kleine Atome ersetzt, bestätigt also `prop:atomicdual` und sagt
  über die gemischte Uhr nichts. Was trägt, ist der umgekehrte Weg: die stetige
  Richtung exakt behandeln (Schritt 0) und nur die Kreuzungen als lineare
  Relationen aufstellen.
* **Über die Lücke interpolieren, zweiter Anlauf.** Der Sprung
  $m_i\gamma(a_i,\cdot)$ ist genau der, den eine affine Fortsetzung mit der
  Steigung $\gamma(a_i,\cdot)$ über die Lücke erzeugen würde — es liegt nahe,
  $\Psi$ so auf $[0,L]^2$ fortzusetzen und `lem:calculus` anzuwenden. Das
  scheitert an den Quadraten Lücke $\times$ Lücke, in denen die Fortsetzung
  beide Steigungen zugleich erfüllen müßte; das ist dieselbe Sperre wie in
  `rem:atomsnotchange`, nur an der kleinstmöglichen Stelle. Der Beweis oben
  vermeidet sie, indem er die Lücken gar nicht betritt.

### Nachtrag am selben Tag: Schritt 0 braucht keine Distributionen

Der Beweis von Schritt 0 oben ist distributionell. Im Manuskript steht ein
kürzerer, und er ist der bessere. Seien $(x,y)$ und $(x',y')$ im Rechteck mit
$x+y=x'+y'$ und $x<x'$, und $t=x'-x=y-y'$. Auf dem Quadrat der Seitenlänge $t$
mit der linken unteren Ecke $(x,y')$ ist `lem:calculus` anwendbar — sein Beweis
liest sein Argument nur auf $[0,T]^2$ —, und seine rechte Seite ist null wegen
$\gamma_1=\gamma_2$. Das gibt $\Psi(x+r,y')=\Psi(x,y'+r)$ für fast alle
$r\le t$; beide Seiten sind in $r$ stetig, also gilt es für **alle** $r$, bei
$r=t$ insbesondere, und das ist $\Psi(x',y')=\Psi(x,y)$.

Kein Distributionsbegriff, keine schwache Ableitung, nur das Lemma, das das
Manuskript ohnehin führt, und ein Stetigkeitsargument. Für die Formalisierung
ist das der Unterschied zwischen „Mathlib braucht Distributionen auf $\R^2$" und
„eine Zeile Stetigkeit"; die Roadmap führt es deshalb als
`eq_comp_add_of_chain_identity` auf
`chain_identity_of_absolutelyContinuous` zurück und nicht auf etwas Neues.

Nebenher fällt damit auch die Einschränkung in `cor:atomless`: auf einer
atomlosen Uhr gilt $\Phi(t,0)=\Phi(0,t)$ für **jedes** $t$, nicht nur für
$Q$-fast jedes. Das Manuskript sagt weiterhin „fast jedes"; die Beobachtung
steht als Auffälligkeit im Inventar, weil sie eine Aussage des Manuskripts
ändert, die dieser Lauf nicht selbst gebraucht hat.

### Nachtrag: ein Atom bei $t^*$

Die Satzfassung oben schrieb $0\le a_1<\dots<a_N\le t^*$. Das ist um einen
Grenzfall zu weit: liegt ein Atom auf $t^*$, so springt $Q$ dort nicht mehr
unterhalb von $t^*$, und $Q(t^*)=\beta_{N-1}$ statt $\beta_N$. Unter
$\iota=\mathrm p$ liegt ein solches Atom in keiner Menge
$[s,s')\subseteq\T_{<t^*}$ und ist ohne Wirkung; das Manuskript verlangt
deshalb $a_N<t^*$ und sagt in einem Halbsatz, warum das keine Einschränkung ist.
Ein Atom bei $0$ ist durch $c_0>0$ ohnehin ausgeschlossen. *(Der zehnte Lauf hat
$c_0>0$ gestrichen; ein Atom bei $0$ ist seitdem gedeckt. Die Bedingung
$a_N<t^*$ bleibt.)*

## Die gemischte Uhr ohne Hypothese, 2026-09-01 (zehnter Lauf): $c_j>0$ faellt

Angegangen wurde der Rest, den der neunte Lauf ausdruecklich stehen liess: **zwei
benachbarte Atome ohne stetige Masse dazwischen**, also der Zusammenbruch von
$c_j>0$. Er ist erledigt, und zwar nicht durch eine Zusatzbedingung, sondern
durch Streichen der Hypothese: `prop:mixeddual` gilt fuer **jede** Uhr mit
endlich vielen Atomen, ohne jede Bedingung an die stetige Masse zwischen ihnen.
Damit deckt der Satz zugleich ein Atom bei $0$ ab, das $c_0>0$ vorher ausschloss.

### Der Angelpunkt: eine entartete Spalte traegt einen Eckwert

Der neunte Lauf las $c_j>0$ als die Bedingung, unter der die Zeile
$\gamma(a_i,\cdot)$ auf $S_j$ eine **Dichte** ist. Das ist richtig, aber es
uebersieht, was an ihre Stelle tritt. Ist $c_j=0$, so ist $S_j=\{\alpha_j\}$ ein
Punkt, und alle Zeiten $s$ mit $Q(s)=\alpha_j$ — das sind $(a_j,a_{j+1}]$, fuer
$j=0$ die Menge $[0,a_1]$ — liefern dasselbe $\Phi(\cdot,s)$. Die linke Seite von
$\Psi(\alpha_i,\alpha_j)-\Psi(\beta_{i-1},\alpha_j)=m_i\gamma(a_i,s)$ haengt also
nicht davon ab, welches $s$ genommen wird, und wegen $m_i>0$ ist
$\gamma(a_i,\cdot)$ auf dieser Menge **konstant**. Sie enthaelt $a_{j+1}$, denn
$Q(a_{j+1})=\beta_j=\alpha_j$. Der Sprung ueber eine entartete Spalte ist damit
$m_i\gamma(a_i,a_{j+1})$ — ein **Eckwert**, kein freier Wert:

$$f_{ij}(\alpha_i+\alpha_j)-f_{i-1,j}(\beta_{i-1}+\alpha_j)=m_i\gamma(a_i,a_{j+1}),
\tag{E}$$

und derselbe Eckwert wird laengs der anderen Koordinate erreicht, ohne jede
Bedingung an $c_j$:

$$f_{i-1,j+1}(\beta_{i-1}+\alpha_{j+1})-f_{i-1,j}(\beta_{i-1}+\beta_j)
=m_{j+1}\gamma(a_i,a_{j+1}).
\tag{F}$$

Die Elimination von $\gamma(a_i,a_{j+1})$ zwischen (E) und (F) ist woertlich die
Kreuzmultiplikation $(\ast)$ des rein atomaren Falls.

### Die Induktion, jetzt mit zwei Faellen

Mit $w_{ij}=f_{ij}-f_{ji}$ und dem antisymmetrischen Eckdefekt
$\delta_{kl}=\gamma(a_k,a_l)-\gamma(a_l,a_k)$ geben (E) und (F) minus ihre
Transponierten

$$w_{ij}(\alpha_i+\alpha_j)=w_{i-1,j}(\beta_{i-1}+\alpha_j)+m_i\delta_{i,j+1}
\quad (c_j=0),$$
$$m_{j+1}\delta_{i,j+1}=w_{i-1,j+1}(\beta_{i-1}+\alpha_{j+1})-w_{i-1,j}(\beta_{i-1}+\beta_j).$$

Die Induktion ueber $d=i-j$ laeuft dann wie im neunten Lauf, mit einer
Fallunterscheidung auf dem **unteren** Stueck:

* $c_j>0$: das Stueck ist ein Intervall, $w_{ij}=T_{m_i}w_{i-1,j}=0$ nach
  Induktion ($d-1$).
* $c_j=0$: das Stueck ist der Punkt $\alpha_i+\alpha_j$, und die erste Relation
  gibt $w_{ij}$ dort aus $w_{i-1,j}$ ($d-1$) und $\delta_{i,j+1}$. Letzteres ist
  null: fuer $d=1$ ist $i=j+1$ und $\delta_{kk}=0$; fuer $d\ge2$ nach der zweiten
  Relation, deren beide Glieder auf den Stufen $d-2$ und $d-1$ verschwinden.

Das obere Stueck ist unveraendert (nichtleer nur bei $c_i>0$, Gronwall mit dem
Anfangswert vom unteren). Fertig. Was die Induktion sich dabei leistet, ist genau
das, was `lem:atomgrid` sich leistet: sie benutzt ihre Hypothese auf **zwei**
Stufen zugleich, $d-1$ und $d-2$, und der Eckdefekt sitzt auf $d-2$.

### Was das ueber die Struktur sagt

Der neunte Lauf schrieb, der rein atomare und der gemischte Fall seien „nicht
Spezialfaelle voneinander, sondern zwei Enden". Das ist zurueckzunehmen. Sie sind
die **zwei Faelle einer Induktion**: auf einer Strecke traegt die
Kreuzungsrelation, an einer Nachbarschaft die Eckrelation, und beide liefern
demselben Gronwall-Schritt dasselbe Objekt, naemlich einen Anfangswert. Die
Probe: setzt man alle $c_i$ auf null, so ist nur noch der zweite Fall im Spiel,
und die Induktion oben ist Zeile fuer Zeile der Beweis von `lem:atomgrid`. Der
Halbordnungssatz `prop:atomicposet` ist davon unberuehrt — er sagt mehr, naemlich
etwas ueber Halbordnungen, wo es keine Aufzaehlung gibt.

Die Rolle der stetigen Masse ist damit genauer benannt als bisher: sie ist nicht
noetig, sie ist nur **bequem**. Was noetig ist, ist ein Punkt, an dem der Kern
$e^{-u/m}$ von $1+mD$ festgenagelt wird; eine Strecke liefert ihn, eine
Nachbarschaft zweier Atome liefert ihn auch, und die Uhr hat immer eines von
beidem.

### Nachgerechnet: `mixed.py`, um (E) erweitert

Dem Modell des neunten Laufs fehlte (E). Das war kein Fehler in seinen Befunden —
eine fehlende wahre Relation **vergroessert** den Loesungsraum, ein
verschwindender Defekt darauf ist die staerkere Aussage —, aber es machte den
Beweis nicht nachpruefbar. (E) und die transponierte Fassung stehen jetzt als
eigene Relationenfamilie im Skript, mit Schalter `degjump`.

Befund, **zehn** entartete Konfigurationen (neu darunter: ein Atom bei $0$ mit
mehreren Atomen, abwechselnd entartete Spalten, eine entartete Spalte am Ende,
und ein Fall mit $N=4$): Defekt und volle Symmetrie null, $\max<10^{-13}$. Die
drei Kontrollen sind der eigentliche Gehalt des Laufs:

* **ohne (D)**, also ohne die Eckrelationen an zwei Atomen, aber mit (E): null.
* **ohne (E)**, aber mit (D): null.
* **ohne beide**: der Symmetriedefekt bleibt in allen sechs geprueften
  Konfigurationen stehen (bis $1.0$), der Endpunktdefekt in den beiden mit
  entarteter erster Strecke ($0.37$).

Das ist die scharfe Aussage: (D) und (E) sind **zwei Wege ueber dieselbe
entartete Spalte**, jeder fuer sich genuegt, und ohne beide faellt die Symmetrie.
Der Beweis oben nimmt (E) und bindet den darin auftretenden Eckwert mit (F);
zusammen ist das (D). Vor der Erweiterung war das Skript auf (D) allein
angewiesen, und der Kanarienvogel „ohne die Ecken" schlug deshalb an — genau
dieser Befund des neunten Laufs ist mit (E) im Modell hinfaellig geworden, und
das ist der Grund, ihn nicht als Beleg fuer die Notwendigkeit von (D) zu lesen.

### Sackgassen, neunter Nachtrag

* **Eine entartete Spalte durch Einfuegen stetiger Masse aufblasen.** Naheliegend
  ist, in $\T$ zwischen $a_j$ und $a_{j+1}$ ein Intervall $I$ einzuschieben, $q$
  dort Lebesgue zu setzen und $\Phi$ konstant fortzusetzen, um den Satz mit
  $c_j>0$ anzuwenden. Das ist unmoeglich, und der Grund ist die Balance selbst:
  aus der ersten Darstellung folgt $\tilde\gamma(r,t)=0$ fuer $r\in I$, aus der
  zweiten $\tilde\gamma(s,r)=\gamma(s_0,r)$ fuer $s\in I$, und beide reden ueber
  $\tilde\gamma$ mit erstem Argument in $I$. Das erzwingt $\gamma(s_0,\cdot)=0$.
  Eine eingefuegte Strecke ist eben nicht dasselbe wie ein Punkt: sie zwingt
  $f_{ij}$ auf $D_{ij}$ konstant zu sein. Die Erweiterung ist keine treue
  Einbettung, und der direkte Weg ueber (E) ist kuerzer als jede Reparatur.
* **Den entarteten Fall als Grenzwert von $c_j$ gegen null nehmen.** Der
  Definitionsbereich von $\Phi$ ist die Zeitmenge, nicht die Uhrzeit; die Uhr
  laesst sich nicht stoeren, ohne das gegebene $\Phi$ mitzustoeren. Ein
  Kompaktheitsargument muesste ueber Paare $(\Phi,\gamma)$ laufen und braeuchte
  eine Schranke, die niemand hat. Der Fall ist algebraisch, nicht analytisch.

## Die ordnungsdichte Atommenge, 2026-09-01 (elfter Lauf): die Ausschöpfung ist quantifiziert, und sie scheitert an der Richtung des Massenprofils

Der Rückstau nannte für diesen Punkt einen Anfang: „ob eine ordnungsdichte
Atommenge mit lokal endlicher Gesamtmasse eine Ausschöpfung durch endliche
Teilmengen zulässt, längs deren der Defekt stetig ist". Der Lauf hat diese Frage
nicht mit ja oder nein beantwortet, sondern sie **rechenbar gemacht** und die
Rechnung ausgeführt. Das Ergebnis ist eine scharfe Bedingung, unter der die
Ausschöpfung trägt, und ein exakter Grund, warum sie im allgemeinen nicht trägt.
Neu ist `dense.py`; bewiesen ist nichts, und der Punkt bleibt offen.

### Der Beweis des sechsten Laufs, störungsweise gelesen

Es braucht keine neue Idee, nur eine Buchführung über den Fehler. Die
Paarungsidentität lautete: für $T$ symmetrisch mit $TV$ symmetrisch ist
$\langle\delta,T\mathbb 1\rangle=0$, weil $\operatorname{tr}(TVK)$ einerseits
gegen den symmetrischen Anteil von $VK$ paart, andererseits als Spur eines
Produkts aus Symmetrischem und Antisymmetrischem verschwindet. Hält (S) nur bis
auf einen symmetrischen Rest $E$, also

$$\operatorname{sym}(VK)=\tfrac12(\delta\mathbb 1^{\mathsf T}
  +\mathbb 1\delta^{\mathsf T})+\tfrac12E,$$

so bleibt die zweite Hälfte unberührt und die erste bekommt einen Zusatzterm:

$$\langle\delta,T\mathbb 1\rangle=-\tfrac12\operatorname{tr}(TE),
  \qquad\text{also}\qquad
  |\delta(t)|\le\tfrac12\|T\|_F\|E\|_F \tag{P}$$

für $T\mathbb 1=e_t$. Das ist eine **Identität**, keine Abschätzung; `dense.py
check` prüft sie an zufälligen $K$ und gestörtem (S) und findet sie in allen
Fällen exakt erfüllt.

### Was (P) für eine Ausschöpfung leistet

Sei $A$ die Atommenge, $q(A)=M<\infty$, $F\subseteq A$ endlich,
$\varepsilon_F:=q(A\setminus F)$. Schneidet man das volle System auf $F$ zurück,
so ist der Fehler in (S) genau der Beitrag der weggelassenen Atome, eintragsweise
höchstens $4\|\kappa\|_\infty\varepsilon_F$, und ebenso
$|\delta(t)-\delta_F(t)|\le\|\kappa\|_\infty\varepsilon_F$. Mit (P):

$$|\delta(t)|\le\|\kappa\|_\infty\varepsilon_F
  \bigl(1+2|F|\|T_F\|_F\bigr).$$

Der Defekt des vollen Systems verschwindet also, sobald **irgendeine** Folge
endlicher $F$ mit $|F|\|T_F\|_F\varepsilon_F\to0$ existiert. Damit hängt
alles an einer einzigen Zahl,

$$C(V,t):=\|T\|_F,\qquad T=T^{\mathsf T},\ TV=V^{\mathsf T}T,\ T\mathbb 1=e_t,$$

und die ist berechenbar: das System ist quadratisch — $N(N{+}1)/2$ Unbekannte
gegen $N(N{-}1)/2+N$ Gleichungen —, sein Kern ist durchweg eindimensional, und
die Minimalnorm-Lösung ist die richtige Messgröße, weil jede Lösung eine
Schranke liefert und die kleinste die beste.

Zwei Voraussetzungen sind dabei offen angemeldet und nicht unter den Tisch
gefallen: $\kappa$ muss **beschränkt** sein, was das Manuskript nirgends
hergibt, und $\varepsilon_F$ fällt nur so schnell, wie die Massen von $A$
summierbar sind. Beides ist beim Zurückschneiden zu bezahlen.

### $C$ ist skaleninvariant, hängt also nur an der Gestalt des Massenprofils

Mit $V$ löst auch $cV$ die Bedingung $TV=V^{\mathsf T}T$, und $T\mathbb 1=e_t$
kennt $V$ nicht. $C$ hängt deshalb **nicht** von der Gesamtmasse ab, sondern nur
von den Verhältnissen der Massen zueinander. Das ist der Grund, warum die
Messung überhaupt etwas über eine unendliche Atommenge sagen kann.

### Gemessen, exakt in Brüchen

Die Gleitkommarechnung bricht zusammen, sobald $C$ groß wird — für $n=8$,
$\rho=4$ meldet `lstsq` Kerndimension 2 und ein *kleineres* $C$ als für
$\rho=3$, was die `rcond`-Abschneidung ist und kein Messwert. Alles Folgende ist
deshalb in exakter Bruchrechnung gerechnet (`defect_bound_exact`), mit
Minimierung der Frobeniusnorm über den Kern in der richtigen, außerdiagonal
doppelt zählenden Form.

* **Gleiche Massen.** $C=\sqrt{2n-1}$ für eine Kette aus $n$ Atomen, auf allen
  geprüften Längen bis $n=40$. Wurzelwachstum, also für jede Ausschöpfung
  bezahlbar.
* **Geometrisch steigende Massen $m_k=\rho^k$.** $C$ wächst **überexponentiell**:
  für $\rho=2$ ist $C\approx 15.6;\ 126;\ 2028;\ 6.5\cdot10^4$ bei
  $n=4,5,6,7$, die Quotienten also $8,16,32$ — das heißt $C\sim\rho^{n^2/2}$.
  Zum Vergleich beträgt das bloße Massenverhältnis nur $\rho^{n-1}$; $C$ ist
  also weit mehr als die Kondition des Massenvektors.
* **Geometrisch fallende Massen $m_k=\rho^{-k}$.** $C\approx 1.55$ bis $1.63$,
  **gleichmäßig beschränkt** in $n$ und in $\rho$ (geprüft $n=4,6,8$,
  $\rho=2,3$). Dasselbe Massenverhältnis, dieselbe Länge — und der Unterschied
  zum steigenden Fall beträgt zehn Größenordnungen.
* **Die dyadische ordnungsdichte Menge.** Atome $k/2^j$ mit Masse $4^{-j}$,
  ausgeschöpft nach Level: $C$ vervierfacht sich je Level, also $C\sim|F|^2$,
  während $\varepsilon_n=2^{-n-1}$ nur halbiert. Das Produkt
  $|F|C\varepsilon$ divergiert wie $4^n$.

### Das Gesetz, das alles erklärt

Eine einzige kleine Masse $\varepsilon$ an der Stelle $k$ einer Kette aus $n$
Atomen (alle übrigen Massen $1$, $t$ die Spitze) kostet

$$C\sim\varepsilon^{-(n-2k)}\quad\text{für }2k<n,
  \qquad C=O(1)\quad\text{für }2k\ge n.$$

Der Exponent ist exakt $\max(n-2k,0)$, abgelesen über zwei Dekaden und bestätigt
für $n=4,6,8,10$ an **jeder** Stelle $k$ — vierzig Werte, keine Abweichung.

Das ist der schärfste Satz des Laufs, und er ist unerwartet: kleine Massen in der
**oberen Hälfte** der Kette sind gratis, kleine Massen in der unteren ruinieren
die Schranke, und zwar umso mehr, je weiter unten sie sitzen. Nicht die Größe
des Massenverhältnisses entscheidet, sondern seine **Richtung**. Damit erklären
sich beide geometrischen Fälle und der dyadische in einem: steigende Massen
heißen kleine Massen unten.

### Was das für den offenen Punkt heißt

Die Ausschöpfung ist damit kein blinder Weg mehr, sondern einer mit einer
benannten Bedingung. Sie trägt, sobald sich die Atome so ausschöpfen lassen, dass
in jedem $F$ die kleinen Massen oben liegen — dann ist $C$ beschränkt und
$|F|\varepsilon_F\to0$ genügt. Sie trägt **nicht** für eine beliebige
ordnungsdichte Menge, denn dort ist die Lage der Massen gegeben und nicht
wählbar: liegt ein großes Atom hoch und liegen beliebig kleine Atome darunter —
und das erzwingt die Ordnungsdichte, sobald unterhalb eines Punktes unendlich
viele Atome liegen —, so ist die teure Konfiguration unvermeidlich.

Damit ist der Grund, an dem die Ausschöpfung scheitert, ein **anderer** als der,
den der Rückstau vermutete. Er liegt nicht an der fehlenden Aufzählung
$a_1<a_2<\dots$ und nicht an der Endlichkeit einer Induktion, sondern an der
Richtung des Massenprofils, und er ist quantitativ: $\varepsilon^{-(n-2k)}$.

**Was der Befund nicht sagt, und das ist wichtig.** $C$ misst die beste Konstante
*dieser Beweisgestalt*, nicht die Wahrheit der Aussage. In
$|\operatorname{tr}(TE)|\le\|T\|_F\|E\|_F$ steckt eine Cauchy--Schwarz-Ungleichung,
die die Struktur von $E$ wegwirft: $E$ ist nicht beliebig, sondern der
Schwanzbeitrag der weggelassenen Atome. Eine feinere Paarung — $E$ gegen $T$ in
der richtigen Gewichtung statt in der Frobeniusnorm — ist durch nichts
ausgeschlossen. Widerlegt ist die **grobe** Ausschöpfung, nicht die Dualität für
ordnungsdichte Atommengen; ein Gegenbeispiel ist nicht gefunden und wurde nicht
gesucht.

### Sackgassen, zehnter Nachtrag

* **Das volle System auf eine endliche Teilmenge $F$ der Atome einschränken und
  den endlichen Satz anwenden.** Geht nicht exakt, und der Grund ist eine Zeile:
  die Relation $\Phi(s',t)-\Phi(s,t)=\sum_{a\in[s,s')}m_a\gamma(a,t)$ summiert
  über **alle** Atome der Lücke, nicht über die von $F$. Das eingeschränkte
  System erfüllt (S) also nur bis auf den Schwanz, und mehr als (P) ist daraus
  nicht zu holen.
* **Die Massen zu Blöcken zusammenfassen (Lumping).** Über eine Lücke ist der
  Zuwachs $M_j\bar\gamma_j(t)$ mit einem gewichteten Mittel $\bar\gamma_j$ —
  aber in der zweiten Koordinate steht $\gamma(s,r)$ mit demselben $\gamma$, und
  ein Mittel in der ersten Koordinate ist keines in der zweiten. Das gelumpte
  System schließt nicht; es ist kein System der gesuchten Gestalt.
* **Auf ein Wachstum von $C$ in $|F|$ allein hoffen.** $C$ ist keine Funktion der
  Länge. Bei gleichen Massen $\sqrt{2n-1}$, bei steigenden $\rho^{n^2/2}$, bei
  fallenden beschränkt — dieselbe Länge, drei Regime. Wer nur gleiche Massen
  prüft, sieht das gutartigste und schließt falsch; das ist derselbe Fehler wie
  der symmetrische Kanarienvogel des neunten Laufs ($c=[1,1]$ sieht zu wenig).
