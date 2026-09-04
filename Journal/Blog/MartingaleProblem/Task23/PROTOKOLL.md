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

## Die ordnungsdichte Atommenge, 2026-09-01 (zwölfter Lauf): das Problem ist ein lineares Programm, und die Messung sagt ein Energiegesetz

Der elfte Lauf endete mit einer Frage: kann die Cauchy--Schwarz-Ungleichung in
$|\operatorname{tr}(TE)|\le\|T\|_F\|E\|_F$ durch eine Paarung ersetzt werden,
die die Struktur von $E$ als Schwanzbeitrag benutzt? Dieser Lauf beantwortet
sie, und die Antwort ist zweigeteilt: als **lineare** Paarung nein — die beste
Konstante wächst linear in der Atomzahl —, aber die Messung zeigt ein
**quadratisches** Gesetz, das, wenn es sich beweisen lässt, den ordnungsdichten
Fall vollständig schließt. Neu ist `Task23/lp_dense.py`; bewiesen ist die
Reduktion dieses Abschnitts, gemessen das Gesetz, offen sein Beweis.

### Die Reduktion: drei Bedingungen, und die Diagonale ist das Ziel

Der dritte Lauf hatte $\Phi$ eliminiert und gezeigt, dass der Defekt nur am
antisymmetrischen Anteil $\kappa(x,y):=\gamma(x,y)-\gamma(y,x)$ hängt
(`duality_defect_eq_integral`). Das lässt sich zu Ende führen. Setze

$$h(a,t):=\kappa(a,t)-\kappa(a,0)\qquad(a\in A,\ t\in[0,t^*]),$$

und $w(s,t):=\Phi(s,t)-\Phi(t,s)$, $H(s,t):=\sum_{a<s}m_a\,h(a,t)$. Dann ist
das volle System aus \eqref{eq:incrementrep} für den Defekt **äquivalent** zu:

1. $h(a,0)=0$ (Definition; aus Bedingung 3 mit der vollen Schnittfamilie sogar
   herleitbar);
2. $h(a,b)+h(b,a)=h(a,a)+h(b,b)$ für alle Atompaare $a,b$ (das ist die
   Antisymmetrie von $\kappa$ auf $A\times A$);
3. $H(s,t)+H(t,s)=0$ für alle $s,t\in[0,t^*]$ (das ist die Antisymmetrie von
   $w$, und $w=H$ bis auf die Randspalte).

Der Dualitätsdefekt ist $\Phi(t,0)-\Phi(0,t)=-\Delta(t)$ mit
$\Delta(t):=\sum_{a<t}m_a\,h(a,a)$ — **die Behauptung des Manuskripts ist
äquivalent zu $h(a,a)=0$ für jedes Atom.** Und die Äquivalenz trägt in beide
Richtungen: aus jeder Lösung $h$ von 1--3 mit $h(a,a)\neq0$ für ein $a$ wird
mit $\gamma:=\kappa/2$, $\Phi:=w/2$ ein echtes Gegenbeispiel, beide
Darstellungen aus \eqref{eq:incrementrep} eingeschlossen. Wer sucht, sucht also
genau: $h$ mit 1--3 und nichtverschwindender Diagonale.

Die Probe an $N=2$ (Atome $1,2$): Bedingung 3 an $(s,t)=(2^+,1^+)$ isoliert
$m_1h(1,1)=0$ — der endliche Satz in einer Zeile. Der Mechanismus braucht ein
$t$ **echt zwischen** dem Atom und seinem Nachfolger; genau das nimmt die
Ordnungsdichte weg.

### Nebenbefund: Nachbaratome genügen, auch unendlich viele

Die Hypothese von `prop:atomicdual` — endlich viele Atome unter jedem Punkt —
ist stärker als nötig. Hat **jedes Atom auf beiden Seiten ein Nachbaratom**
(die Atommenge ist ordnungstheoretisch diskret, etwa $a_k\downarrow0$ vom Typ
$\omega^*$, oder eine $\mathbb Z$-Kette, die sich an einem inneren Punkt
häuft), so läuft die Zwei-Diagonalen-Induktion von `atomGrid_symm` unverändert:
sie induziert über den Abstand zur Diagonale und braucht **keinen Boden** —
jedes Indexpaar hat endlichen Abstand. Sie gibt $w=0$ auf allen
Atompaaren; daraus $\kappa=0$ auf Atompaaren (die Gitterlücke $[a_{k+1},a_k)$
trägt genau ein Atom, also $m_{k+1}\kappa(a_{k+1},a_j)=w(a_k,a_j)-w(a_{k+1},a_j)=0$);
daraus $w(t,y)=0$ für beliebiges $t$ und Gitter-$y$; und der Rand $y=0$ kommt
per dominierter Konvergenz, $|w(t,a_j)-w(t,0)|\le\|\kappa\|_\infty\,q([0,a_j))\to0$
— hier, und nur hier, geht die Beschränktheit von $\kappa$ ein. **Das ist eine
Skizze, kein geprüfter Beweis**; der nächste Lauf, der sie anfasst, rechne sie
nach, bevor sie in Roadmap oder Manuskript wandert. Hält sie, ist der wirklich
offene Kern exakt die **in sich dichte** Atommenge (und, per
Cantor--Bendixson, transfinite Mischfälle, die auf sie zurückführen dürften).

### Das LP-Experiment

Ein beschränktes Gegenbeispiel $|h|\le B$ auf der dyadischen Atommenge
(Level-$j$-Atome $k/2^j$, Masse $r^{-j}$, summierbar für $r>2$) erfüllt auf der
Trunkierung bis Level $J$ die Bedingungen 1 und 2 **exakt** und Bedingung 3 bis
auf $\eta=2B\varepsilon_J$, $\varepsilon_J$ die Schwanzmasse. Das LP maximiert
$\Delta_J(1)$ unter genau diesen Nebenbedingungen ($B=1$; Gitter für $s,t$:
Dyadische bis Level $J{+}1$, also alle Atome und alle Lückenmitten). Zwei
Eigenschaften machen es beweiskräftig:

* $v_J\to0$ **schließt jedes beschränkte Gegenbeispiel auf dieser Uhr aus**
  (ein solches erzwänge $v_J\ge|\Delta(1)|-\varepsilon_J$; die Skalierung
  $h\mapsto\lambda h$ erledigt beliebiges $B$).
* Die Kontrolle $\eta=0$ muss den endlichen Satz reproduzieren, $v_J=0$. Sie
  tut es, auf allen Leveln — die Kodierung erfasst die Starrheit vollständig.

### Die Messwerte

$v_J$ bei $\eta=2\varepsilon_J$, dyadische Uhr:

| $r$ | $J{=}2$ | $3$ | $4$ | $5$ | $6$ | $7$ |
|---|---|---|---|---|---|---|
| $2.5$ | $0.720^\dagger$ | $0.976^\dagger$ | $1.127$ | $1.112$ | $1.009$ | $0.913$ |
| $4$ | $0.278$ | $0.182$ | $0.136$ | $0.108$ | $0.078$ | — |
| $8$ | $0.034$ | $0.021$ | $0.0080$ | $0.0028$ | — | — |

($\dagger$: an der trivialen Schranke $M_J$ gesättigt, dort sagt der Wert
nichts.) Alle drei Profile fallen: $r=8$ schnell, $r=4$ etwa wie
$0.72^J$, $r=2.5$ geometrisch mit Faktor $\approx0.905<1$ je Level
(Quotienten $0.907$, $0.905$ bei $J=5\to6\to7$). **Auf keiner der drei Uhren
gibt es ein beschränktes Gegenbeispiel** — soweit $J\le7$ den Trend trägt.

Die intrinsische Verstärkung (kleines festes $\eta$, lineares Regime, ohne
aktive $h$-Schranke):

$$\kappa_J=2^J-\tfrac12=n_J+\tfrac12$$

exakt auf allen prüfbaren Leveln ($3.5,\,7.5,\,15.5$ für $J=2,3,4$, profilfrei).
**Die beste lineare Zertifikatskonstante wächst linear in der Atomzahl.** Für
$r<4$ divergiert $\kappa_J\varepsilon_J\sim(4/r)^J$ — die vom elften Lauf
gesuchte lineare Paarung mit beschränkter Norm existiert nicht, in keiner
Norm: $\kappa_J$ ist normfrei definiert.

### Das Zwei-Regime-Gesetz

Bei festem $J$ als Funktion von $\eta$ (gemessen $J=4$, $r=4$, $BM=0.5$):

$$v_J(\eta)\;\approx\;\min\bigl(\kappa_J\,\eta,\ c\,\sqrt{BM\eta}\bigr),
\qquad c\approx0.85,$$

mit Übergang exakt beim vorhergesagten $\eta^*=BM/\kappa_J^2\approx2\cdot10^{-3}$:
gemessen $v/\eta=15.500$ bei $\eta\le10^{-4}$ (linear, $=\kappa_4$), Plateau
$v/\sqrt{BM\eta}=0.84$--$0.85$ bei $\eta=10^{-2}$--$3\cdot10^{-2}$. Und die
$v_J$-Tabelle oben passt profilübergreifend auf dasselbe Gesetz:
$v_J/\sqrt{BM\cdot2\varepsilon_J}\in[0.69,0.88]$ für alle nicht gesättigten
Einträge mit $r\in\{2.5,4\}$ ($M=2$ bzw. $0.5$).

### Die Vermutung, und was sie schließen würde

**Energieschranke.** Für jedes endliche System mit Bedingungen 1, 2 exakt,
Bedingung 3 bis auf $\eta$, $|h|\le B$, Gesamtmasse $M$:

$$\Delta(t)^2\;\le\;C\cdot B\,M\,\eta,\qquad C\le1\ \text{(gemessen }c^2\approx0.72\text{)}.$$

Die Homogenität stimmt ($h\mapsto\lambda h$ skaliert beide Seiten mit
$\lambda^2$), die Kontrolle $\eta=0$ ist der endliche Satz, und die Numerik
sitzt profil- und levelübergreifend auf ihr. Bewiesen ist sie nicht.

**Konsequenz, wenn sie hält:** Ausschöpfung mit $\eta_F=2B\varepsilon_F$ gibt
$\Delta^2\le2CB^2M\varepsilon_F\to0$ längs **jeder** Ausschöpfung — die
Dualität gilt für jede rein atomare Uhr endlicher Masse mit beschränktem
$\kappa$, **ordnungsdichte Atommengen eingeschlossen**, und die Richtung des
Massenprofils, an der der elfte Lauf die grobe Ausschöpfung scheitern sah, ist
irrelevant geworden: die Beschränktheit von $h$ ersetzt, was der
Frobenius-Paarung fehlte. Der Grund, warum das lineare Regime nicht beißt: sein
Optimum sättigt $|h|=1$ auf den leichten Atomen (im Extremalpunkt sichtbar:
die leichten Atome liegen auf $\pm1$, das schwere Atom trägt kleines $h$, die
Diagonale wächst längs der Kette) — genau diese Sättigung deckelt den Gewinn
auf $\sqrt{BM\eta}$.

### Was offen bleibt

1. **Der Beweis der Energieschranke.** Sie ist eine endlich-dimensionale
   Aussage über Kettensysteme, quadratisch, mit vermuteter Konstante $\le1$.
   Der erste Paarungsschritt steht: $M\Delta=\sum_k m_kM_k\,h(a_k,s_n)+O(M\eta)$
   (Summation von Bedingung 2 gegen $m\otimes m$, Auflösung über Bedingung 3
   und die Diagonale $H(s_n,s_n)=O(\eta)$; $M_k$ die Masse bis einschließlich
   $a_k$, $s_n$ ein Schnitt über allen Atomen); trivial abgeschätzt gibt er nur
   $\Delta\le BM+O(\eta)$. Der quadratische Gewinn muss aus der Iteration über
   alle Schnittlevel kommen.
2. **Die $B$-Hypothese.** Das Manuskript gibt Beschränktheit von $\kappa$
   nirgends her; sie steht jetzt an zwei Stellen (Rand der Nachbaratom-Skizze,
   Energieschranke). Entweder sie wird Voraussetzung von `prop:atomicdual` in
   der dichten Fassung, oder ein Abschneideargument ersetzt sie.
3. **Geometrieabhängigkeit der Messung.** Gemessen ist dyadisch mit
   geometrischen Levelmassen, $J\le7$. Das Gesetz ist profilübergreifend, aber
   eine andere Uhrgeometrie (schiefe Teilungen, nicht selbstähnlich) ist
   ungemessen.

### Sackgassen, elfter Nachtrag

* **Eine lineare Paarung mit beschränkter Zertifikatsnorm suchen** (die Frage
  des elften Laufs). Gibt es nicht: $\kappa_J=n_J+\frac12$ ist die beste
  lineare Konstante überhaupt, normfrei, und wächst linear in der Atomzahl.
  Jede Fortsetzung muss die Beschränktheit von $h$ quadratisch benutzen.
* **$v_J$ bei großem $\eta$ als Evidenz lesen.** Für $\eta\gtrsim M_J$ klebt
  das LP an der trivialen Schranke $M_J$ (bei $r=2.5$ bis $J=3$ exakt
  $v=M_J$); solche Einträge messen nur die Schwanzmasse, nicht das System.
* **Aus $\kappa_J\varepsilon_J\to\infty$ auf ein Gegenbeispiel schließen.**
  Das lineare Regime gilt nur bis $\eta^*=BM/\kappa_J^2$; oberhalb übernimmt
  die Sättigung. Der elfte Lauf stand mit der Frobenius-Variante genau an
  dieser Klippe und konnte sie nicht sehen, weil (P) keine Schranke an $h$
  mitführte.

## Die Energieschranke, 2026-09-01 (dreizehnter Lauf): sie ist falsch, in jeder Konstante

Der zwölfte Lauf hinterließ als benanntes Ziel den Beweis der Energieschranke
$\Delta(t)^2\le C\,B\,M\,\eta$ ($C\le1$) für endliche Kettensysteme mit den
Bedingungen 1, 2 exakt, Bedingung 3 bis auf $\eta$ und $|h|\le B$ — und
vermerkte als offen, dass nur dyadisch mit geometrischen Levelmassen gemessen
war. Dieser Lauf hat zuerst gemessen, dann bewiesen: **die Schranke ist
falsch.** Nicht die Konstante ist zu klein — die Form ist es. Neu sind
`energy_lp.py` (das LP des zwölften Laufs mit freiem Massenvektor; auf den
dyadischen Instanzen bitgleich mit `lp_dense.py` gegengeprüft),
`energy_counterexample.py` (exakte Verifikation in Bruchrechnung) und
`dyadic_adversarial.py`.

Beide Skalierungen — $h\mapsto\lambda h$ mit $(\eta,B)\mapsto(\lambda\eta,
\lambda B)$ und $m\mapsto cm$ mit $\eta\mapsto c\eta$ — lassen
$\Delta^2/(BM\eta)$ fest; o.B.d.A. also $B=M=1$.

### Der Zwei-Atom-Zeuge, analytisch

Massen $(\mu,1)$, $\eta=2\mu^2/3$, $B=1$, und die Belegung

$$d_1=-\tfrac{2\mu}3,\quad x_{12}=\tfrac\mu3,\quad d_2=\mu+\tfrac{\mu^2}3,\quad
  x_{21}=\tfrac{\mu^2}3,\quad h(a_1,s_2)=-1,\quad
  h(a_2,s_1)=h(a_2,s_2)=\mu,$$

alle übrigen Werte $0$ ($x_{ij}=h(a_i,a_j)$, $s_p$ der Schnitt über Atom $p$).
Bedingungen 1 und 2 gelten exakt, jedes Residuum von Bedingung 3 ist
$\le2\mu^2/3$ (die Schnitte $(s_1,a_1)$, $(a_2,a_2)$ und $(s_2,a_2)$ sind
saturiert), und

$$\Delta=\mu-\tfrac{\mu^2}3,\qquad
  \frac{\Delta^2}{B\,M\,\eta}
  =\frac{(1-\mu/3)^2}{1+\mu}\cdot\frac32\;\xrightarrow{\mu\to0}\;\frac32.$$

In exakter Bruchrechnung nachgerechnet (`energy_counterexample.py`, Teil 1):
$\mu=1/10$ gibt exakt $841/660\approx1.274$, $\mu=1/1000$ gibt
$8994001/6006000\approx1.4975$. Schon $C\le1$ ist damit falsch, und zwar bei
$n=2$.

Der Mechanismus verkehrt die Deutung des zwölften Laufs ins Gegenteil: die
Bedingung $(s_2,a_2)$ lautet $m_2d_2=-\mu x_{12}-\mu\,h(a_1,s_2)+O(\eta)$, und
das leichte Atom saturiert $h(a_1,s_2)=-B$ und **trägt** damit die Diagonale
des schweren, $m_2d_2\approx\mu B$ — bei einem Residuenbedarf von nur
$\eta\sim\mu^2B$, denn die Bedingungen, die $d_1$ und $x_{12}$ klein zwingen,
tragen alle den Vorfaktor $\mu$. Die Sättigung, die nach der Lesart des
zwölften Laufs den Gewinn auf $\sqrt{BM\eta}$ deckeln sollte, ist der Motor,
der die Schranke schlägt.

### Keine Konstante rettet die Form

Zwei Familien, beide in exakter Bruchrechnung zertifiziert (LP-Lösung auf
rationale Zahlen gerundet, Bedingungen 1 und 2 per Konstruktion exakt erzwungen,
$\eta_{\text{used}}:=\max$ Residuum von Bedingung 3 und $B_{\text{used}}:=
\max|h|$ exakt bestimmt; jede Instanz ist ein echtes Gegenbeispiel gegen jede
Konstante, die sie schlägt):

* **Leichtes Präfix** $[\mu]^k+[1]$: das Verhältnis wächst etwa wie $1.85\,k$
  (zertifiziert $k=8$, $\mu=0.01$: Verhältnis $14.79$). Der Zwei-Atom-Motor
  läuft $k$-fach: $k$ leichte Atome saturieren, $d_{\text{schwer}}\approx
  k\mu B$, Residuenbedarf $\eta\sim k\mu^2B$.
* **Aufsteigend geometrisch** $m_k\propto\rho^k$: das Verhältnis explodiert.
  Zertifiziert für $\rho=2$: $1513.5$ ($n=6$), $4398.5$ ($n=8$), $5929.0$
  ($n=10$) und $27588.8$ ($n=8$ bei $\eta=10^{-9}$); das LP selbst erreicht
  dort $1.28\cdot10^5$, die Rundung kostet einen Faktor. Das optimale $\eta^*$
  kollabiert dabei ($10^{-7}$ und kleiner) — konsistent mit dem elften Lauf,
  dessen Frobenius-Konstante auf steigenden Profilen wie $\rho^{n^2/2}$ wuchs:
  das lineare Regime endet erst bei absurd kleinem $\eta$, und die
  Sättigungsschwelle liegt weit über $\sqrt{BM\eta}$.

Warum die Messung des zwölften Laufs das nicht sah: die dyadische Uhr mit
levelweise geometrisch **fallenden** Massen verschränkt leicht und schwer so,
dass unter keinem schweren Atom viel leichte Masse liegt. Das
Zwei-Regime-Gesetz $v\approx\min(\kappa\eta,\,0.85\sqrt{BM\eta})$ ist eine
Eigenschaft dieser Geometrie, kein Satz über Kettensysteme.

### Auch lokale Residuen retten sie nicht

In einer echten Trunkierung eines exakten Systems ist das Residuum an $(s,t)$
nicht uniform $\eta$, sondern $\le2B\cdot$(fehlende Masse unterhalb
$\max(s,t)$) — lokal. Die LP-Variante mit $\mathrm{rhs}(s,t)=\eta_0\cdot
M(\le\max(s,t))/M$ drückt den Zwei-Atom-Zeugen unter $1$ (gemessen $0.44$–$0.6$),
aber die aufsteigenden Ketten bleiben unbeschränkt: $14.5$, $131$, $8273$ für
$n=5,6,8$ bei $\rho=2$. Die Lokalität allein ist es also nicht.

### Was das bedeutet, genau

1. **Kein Gegenbeispiel zur Dualität.** Alle Instanzen haben $\eta>0$; die
   Rückrichtung der Reduktion (Lösung $\Rightarrow$ Gegenbeispiel) gilt nur
   für das exakte System. Widerlegt ist das Werkzeug, nicht die Aussage.
2. **Der Ausschöpfungsweg über eine profilfreie Schranke ist dreifach zu und
   damit ganz zu.** Frobenius (elfter Lauf: Konstante hängt am Profil),
   linear (zwölfter Lauf: beste Konstante $n+\frac12$), quadratisch (dieser
   Lauf: falsch). Der Grund ist jedes Mal derselbe, jetzt benannt: die
   Relaxation „endliches System plus Slack $\eta$" ist **echt schwächer** als
   „Trunkierung eines exakten Systems". Sie lässt Slack-Belegungen zu, die
   keine Trunkierung erzeugt, und auf diesen ist die Verstärkung unbeschränkt.
3. **Die schlimmsten Muster sind als Uhren nicht realisierbar.** Eine
   ordnungsdichte Uhr mit durchweg nach oben wachsenden Massen gibt es nicht:
   wächst $m$ mit der Position und liegen in $(x_0,1)$ unendlich viele Atome,
   so haben alle Masse $\ge m(x_0)>0$ — die Gesamtmasse wäre unendlich.
   Aufsteigende Teilstrukturen existieren, aber mit überwiegend präsenter
   Masse darunter. Das ist der Hebel, den eine Fortsetzung benutzen muss:
   nicht die Größe des Residuums, sondern seine **Gestalt** — es ist selbst
   von der Form $\sum_{\text{fehlend}}m_ah(a,\cdot)$ mit $h$, das die
   Bedingungen global erfüllt.

### Realisierbare steigende Profile: dort kollabiert $v_J$ weiterhin

Die Verstärkung braucht leichte Masse unter schwerer. Auf der dyadischen
Ordnung ist das realisierbar als $m(k/2^j)=(k/2^j)^p\,r^{-j}$ (nach rechts
wachsend, summierbar für $r>2$); `dyadic_adversarial.py` misst diese Profile
mit dem **echten** Trunkierungsresiduum $\eta_J=2B\varepsilon_J$:

| Profil | $J{=}2$ | $3$ | $4$ | $5$ | $6$ |
|---|---|---|---|---|---|
| $x^4\cdot4^{-j}$: $v_J/M_J$ | $1.00$ | $0.62$ | $0.40$ | $0.28$ | $0.16$ |
| $x^8\cdot3^{-j}$: $v_J/M_J$ | $1.00$ | $1.00$ | $0.95$ | $0.68$ | $0.51$ |
| Kontrolle $4^{-j}$: $v_J/M_J$ | $0.74$ | $0.42$ | $0.29$ | $0.22$ | $0.16$ |

Beide steigenden Profile fallen ($x^8\cdot3^{-j}$ nach einem Plateau bis
$J=4$), und bemerkenswert: $v_J^2/(M_J\eta_J)$ bleibt auf **allen** diesen
realisierbaren Instanzen unter $0.82$. Die Energieschranke ist also falsch als
Satz über $\eta$-relaxierte Systeme und sieht auf echten Trunkierungen der
getesteten Uhren dennoch erfüllt aus — das quantifiziert, wie viel die
Relaxation verschenkt, und stützt Punkt 3 unten.

### Nachgerechnet

`energy_lp.py` reproduziert `lp_dense.py` auf vier dyadischen Instanzen
bitgleich (Differenz $0$ bzw. $3\cdot10^{-18}$); die Kontrolle $\eta=0$ gibt
$v=0$ auf allen getesteten Massenvektoren. `energy_counterexample.py` prüft
den Zwei-Atom-Zeugen und die zertifizierten Instanzen vollständig in
`fractions.Fraction`: alle Gitterpaare von Bedingung 3, Bedingungen 1 und 2
per Konstruktion, $B_{\text{used}}$, $\Delta$ und das Verhältnis exakt.

### Sackgassen, zwölfter Nachtrag

* **Die Energieschranke $\Delta^2\le C\,B\,M\,\eta$ beweisen wollen.** Sie ist
  falsch; der kleinste Zeuge hat zwei Atome und schlägt $C=1$ um den Faktor
  $3/2-o(1)$, und entlang aufsteigend-geometrischer Ketten ist das Verhältnis
  unbeschränkt (zertifiziert bis $27588$). Jede Fortsetzung, die eine Schranke
  der Form $f(B,M,\eta)$ **gleichmäßig über die Massenprofile** sucht, geht
  dieselbe Sackgasse: schon die Zwei-Atom-Familie erzwingt
  $f(B,M,\eta)\gtrsim\sqrt{3BM\eta/2}$, und das leichte Präfix hebt mit
  wachsendem $k$ jede solche Kandidatin aus.
* **Lokale Residuenbudgets als Reparatur.** Masse-proportionale Budgets
  drücken den Zwei-Atom-Zeugen, lassen die aufsteigenden Ketten aber
  unbeschränkt. Wenn Lokalität hilft, dann nicht als Gewichtung der rhs allein,
  sondern zusammen mit der Realisierbarkeit des Slacks als Schwanz eines
  globalen $h$.

## Der intervallendliche Kettenfall, 2026-09-01 (vierzehnter Lauf): die Nachbaratom-Skizze ist nachgerechnet — bewiesen, mit korrigierter Hypothese und ohne die $B$-Hypothese

Der zwölfte Lauf hinterließ die Skizze „Nachbaratome genügen, auch unendlich
viele" mit dem Auftrag, sie nachzurechnen, bevor sie in Roadmap oder Manuskript
wandert. Dieser Lauf hat sie nachgerechnet. **Sie hält**, aber an zwei Stellen
anders, als sie dastand: die richtige Hypothese ist nicht „jedes Atom hat
beidseits ein Nachbaratom", sondern **Intervallendlichkeit** — zwischen je zwei
Atomen liegen nur endlich viele Atome —, und die Beschränktheit von $\kappa$,
die die Skizze am Rand brauchte, wird nirgends gebraucht. Die offene Frage 2
des zwölften Laufs (die $B$-Hypothese) fällt damit für den Kettenfall weg.
Neu ist `Task23/neighbor.py` (exakt rational, rc=0); die Roadmap
`MartingaleProblems` führt das Ergebnis in Meilenstein 8 als
`atomGrid_symm_int` und `duality_of_atomic_intervalFinite`.

### Der Satz

Sei $q$ rein atomar, $t^*\in\T$, die Atome von $q$ in $\T_{<t^*}$ paarweise
vergleichbar, und **je zwei von ihnen schließen nur endlich viele Atome ein**.
Dann gilt $\Phi(t^*,0)=\Phi(0,t^*)$, in beiden Konventionen, ohne Hypothese
über die Existenz der Integrale in \eqref{eq:incrementrep} hinaus — und wie im
endlichen Fall schärfer $\Phi(s,t)=\Phi(t,s)$ für alle $s,t\in\T_{\le t^*}$.

Das enthält `prop:atomicdual` (endlich viele Atome sind intervallendlich) und
erfasst neu: Atome, die sich bei $0$ häufen (Typ $\omega^*$), die sich von
unten an einem Punkt $\le t^*$ häufen (Typ $\omega$ — auch das war bisher
**nicht** abgedeckt, denn unter $t^*$ liegen dann unendlich viele Atome), und
$\mathbb Z$-Ketten mit beiden Enden (Typ $\zeta$).

### Der Beweis

**Aufstellung.** Intervallendlichkeit und Vergleichbarkeit machen die Atome in
$\T_{<t^*}$ ordnungsisomorph zu einem Intervall $I\subseteq\mathbb Z$: fixiere
ein Atom $u_0$ und indiziere jedes andere durch die (endliche!) gezählte Zahl
der Atome zwischen ihm und $u_0$, mit Vorzeichen. Hat $I$ ein Maximum $K$, so
ergänze $u_{K+1}:=t^*$; hat $I$ ein Minimum $k_0$, so ergänze
$u_{k_0-1}:=0$ mit $m_{k_0-1}:=0$. Für aufeinanderfolgende Gitterpunkte trägt
$[u_k,u_{k+1})=\T_{<u_{k+1}}\setminus\T_{<u_k}$ genau das Atom $u_k$ (ein
Atom dazwischen widerspräche der Nachbarschaft im Index; hier geht die
Vergleichbarkeit ein), bzw. kein Atom im ergänzten Bodenschritt. Also gelten
die Einschrittrelationen
$$\Phi(u_{k+1},y)-\Phi(u_k,y)=m_k\gamma(u_k,y),\qquad
  \Phi(y,u_{k+1})-\Phi(y,u_k)=m_k\gamma(y,u_k)$$
für **jedes** $y\in\T$, und Kreuzmultiplikation an $(u_i,u_j)$ eliminiert
$\gamma$ zu $(\ast)$, für alle $i,j$ im Gitter mit Nachfolger — beim
ergänzten Boden gilt $(\ast)$ mit $m_{k_0-1}=0$ von selbst, genau wie im
endlichen Beweis.

**Die Induktion braucht weder Boden noch Deckel.** Auf
$w(i,j)=\widehat\Phi(i,j)-\widehat\Phi(j,i)$ läuft die
Zwei-Diagonalen-Induktion von `lem:atomgrid` wörtlich: die Basis $d=1$ liest
$(\ast)$ auf der Diagonale $(j,j)$, der Schritt $d\to d+1$ an $(j+d,j)$, und
keine der beiden Stellen nennt ein kleinstes oder größtes Element — die
Schranken $1\le i,j\le M-1$ des endlichen Lemmas markieren, wo die Relationen
enden, nicht wo die Induktion beginnt. Wohlfundiert ist die Induktion über
$d$, weil **jedes Indexpaar endlichen Abstand hat** — das ist die
Intervallendlichkeit, und nur hier geht sie in die Algebra ein. Ergebnis:
$w\equiv0$ auf dem ganzen Gitter, ergänzte Punkte eingeschlossen.

**Die Ränder kommen per Schwanzsumme, ohne Schranke an $\kappa$.** Ist ein
Ende von $I$ unendlich, so liegt $t^*$ bzw. $0$ nicht im Gitter. Die Existenz
der Integrale in \eqref{eq:incrementrep} ist für das rein atomare $q$ die
**absolute** Konvergenz der Atomsummen, also
$\sum_{a}m_a|\gamma(a,y)|<\infty$ über die Atome unter $t^*$, für jedes
benutzte $y$. Für $k\to+\infty$ ist
$\Phi(t^*,y)-\Phi(u_k,y)=\sum_{j\ge k}m_j\gamma(u_j,y)$ ein Schwanz dieser
Summe und geht gegen $0$ (kein Atom liegt über allen $u_k$ — sonst hätte es
unendlichen Indexabstand zu $u_0$); für $k\to-\infty$ ebenso
$\Phi(u_k,y)-\Phi(0,y)=\sum_{j<k}m_j\gamma(u_j,y)\to0$. Beides gilt in beiden
Koordinaten. Damit:
$$w(t^*,0)\;=\;\lim_{l\to-\infty}\;\lim_{i\to+\infty}\;w(u_i,u_l)\;=\;0,$$
wobei je nach Endlage der Limes durch den Gitterwert ersetzt wird.
Die Schärfung auf beliebige Paare $(s,t)$: liegt unter $s$ ein größtes Atom
$u_k$, so ist $\Phi(s,\cdot)=\Phi(u_{k+1},\cdot)$ (das Intervall
$[u_k,s)$ trägt genau $u_k$); liegt keines, so ist $\Phi(s,\cdot)$ der
Schwanzlimes der $\Phi(u_k,\cdot)$ — in beiden Fällen erbt $(s,t)$ das
Verschwinden von $w$ vom Gitter.

**Die o-Konvention** ist dieselbe Rechnung nach der Spiegelung $i\mapsto-i$:
$(u_{k-1},u_k]$ trägt genau $u_k$, die Dichte sitzt am oberen Endpunkt, und
die Spiegelung von Punkten und Massenliste macht daraus wörtlich das p-System
der gespiegelten Kette; ein ergänzter Deckel $(u_K,t^*]$ trägt kein Atom und
wird zum masselosen Schritt. Induktion und Schwanzsummen laufen unverändert.

**Wo welche Hypothese eingeht.** $m_k\neq0$ ist die Definition eines Atoms;
die Vergleichbarkeit macht die Einschrittintervalle einelementig; die
Intervallendlichkeit macht die Induktion wohlfundiert und die Schwanzmengen
leer; die absolute Existenz der Integrale trägt genau die zwei Randlimiten.
Eine Schranke an $\gamma$ oder $\kappa$ kommt nicht vor.

### Was an der Skizze zu korrigieren war

1. **„Beidseits ein Nachbaratom" ist zu schwach formuliert.** Die Skizze
   begründete die Induktion mit „jedes Indexpaar hat endlichen Abstand" — das
   ist die Intervallendlichkeit, nicht die Nachbareigenschaft. Beide fallen
   auseinander: **zwei übereinandergestapelte $\zeta$-Ketten** (jede häuft
   sich an beiden eigenen Enden) haben an jedem Atom beidseits Nachbarn, aber
   Paare aus verschiedenen Ketten schließen unendlich viele Atome ein. Die
   Beispiele der Skizze ($\omega^*$, eine $\zeta$-Kette) sind
   intervallendlich; ihre wörtliche Hypothese ist es nicht.
2. **Die $B$-Hypothese war nie nötig.** Die Skizze schloss den Rand mit
   $|w(t,a_j)-w(t,0)|\le\|\kappa\|_\infty\,q([0,a_j))$; dominierte Konvergenz
   mit der ohnehin vorausgesetzten (absoluten) Existenz der Integrale liefert
   dasselbe ohne jede Schranke. Der offene Punkt 2 des zwölften Laufs ist
   damit für den Kettenfall erledigt; für die in sich dichte Atommenge bleibt
   die Frage stehen.
3. **Die Schritte 2 und 3 der Skizze ($\kappa=0$ auf Atompaaren, beliebiges
   $t$) sind nur für die volle Symmetrie nötig**, nicht für die Dualität an
   $(t^*,0)$: dort genügen Induktion und zwei Schwanzlimiten.

### Nachgerechnet, mechanisch

`Task23/neighbor.py`, exakt rational (rc=0). **(R) Randfreiheit:** eine
endliche Kette von Gitterpunkten nur mit ihren Einschrittrelationen — kein
Punkt $0$, kein $t^*$, keine Relation aus der Kette hinaus — erzwingt im Kern
die volle Symmetrie von $\Phi$; geprüft für $M=2..7$, drei Massenvektoren,
beide Konventionen, und symbolisch (p bis $M=4$, o bis $M=3$; das o-System
ist wortgleich das gespiegelte p-System, sympys symbolischer Nullraum braucht
in der o-Orientierung bei $M=4$ Stunden). Das ist die Gestalt, in der die
Induktion im unendlichen Fall läuft: jedes Fenster $[u_j,u_i]$ des Gitters
ist eine solche randlose Kette, und die Herleitung von $w(i,j)=0$ benutzt nur
Relationen im Fenster.
**(X) Kreuzblock:** zwei solche Ketten ohne verbindende Einschrittrelation —
das endliche Abbild zweier Blöcke mit Häufung dazwischen — erzwingen die
Symmetrie blockintern, auf den Kreuzpaaren **nicht** (Kerndimension 24 bzw.
28, alle Kreuzpaare frei). Die lokalen Relationen allein schließen den
diskret-in-sich-Fall also nicht; was ihn schlösse, müsste die
Schwanzrelationen über die Häufungspunkte hinweg benutzen. Das ist **kein**
Gegenbeispiel — das endliche Abbild lässt Relationen weg, die das unendliche
System hat; die Falle, eine Relaxation für das System zu halten, ist die des
dreizehnten Laufs.

Beim Schreiben des Skripts fand sich ein Bug (der Blockaufbau zählte Blöcke
statt Punkte, `start = len(pts)` statt `len(zug)`), der Block 2 mit Block 1
überlappen ließ und blockinterne Asymmetrie vortäuschte; nach dem Fix stimmen
Theorie und Kern überein. Wer das Skript erweitert, prüfe zuerst, dass die
Blocklisten disjunkt sind.

### Was jetzt offen ist, genau

* **Diskret in sich, aber nicht intervallendlich** (kleinste Instanz: zwei
  $\zeta$-Ketten). Die Induktion erreicht Kreuzpaare nicht, (X) zeigt, dass
  sie lokal auch nicht erzwungen sind; die Schwanzrelationen über den
  Häufungspunkt sind das einzige verbleibende Werkzeug.
* **Die in sich dichte Atommenge**, unverändert (elfter bis dreizehnter Lauf:
  profilfreie Schranken sind dreifach zu; die $\omega^*$-Skizze dieses Laufs
  war der andere benannte Weg und ist jetzt Satz, schließt die dichte Menge
  aber nicht).
* Per Cantor--Bendixson ist der intervallendliche Fall der Baustein; was
  fehlt, ist genau das Überqueren von Häufungspunkten.

### Sackgassen, dreizehnter Nachtrag

* **Die Nachbareigenschaft als Hypothese des Induktionswegs.** Sie gibt die
  Blöcke, aber nicht die endlichen Abstände; zwei $\zeta$-Ketten trennen sie
  von der Intervallendlichkeit, und (X) zeigt, dass die lokale Algebra dort
  endet. Wer den diskreten Fall fortsetzt, beginne bei den Schwanzrelationen
  über einem einzelnen Häufungspunkt zwischen zwei Blöcken, nicht bei einer
  feineren Induktion.

## Die Summierbarkeit als tragende Struktur, 2026-09-02 (fünfzehnter Lauf): auf echten Trunkierungen kehrt das Energiegesetz zurück

Teil (b) der Aufgabe vom 2026-09-01: die Frage der Läufe 11–13 neu stellen,
über der Klasse der **summierbaren** Massen statt über beliebigen endlichen
Massenvektoren mit freiem Slack. Neu ist `Task23/summable_lp.py`.

### Die Neuformulierung (S)

Eine Uhr hat $q(\T_{\le t})<\infty$; eine rein atomare Uhr auf einer Kette ist
ein **fest gewähltes summierbares Profil**, und eine Trunkierung ist
**geschachtelt** — Stufe $J{+}1$ fügt Atome hinzu, ändert keine Masse. Das
Residuum der Stufe $J$ am Paar $(s,t)$ ist dann nicht frei, sondern

$$R_J(s,t)=\sum_{a\text{ fehlt},\,a<s}m_a\,h(a,t)+\sum_{b\text{ fehlt},\,b<t}m_b\,h(b,s),
\qquad |R_J(s,t)|\le B\,(\varepsilon(s)+\varepsilon(t)),$$

mit $\varepsilon(g)$ = fehlende Masse unterhalb $g$ (monoton in $g$,
$\varepsilon(\text{top})=\varepsilon_J\to0$). **Frage (S):** gilt $v_J\to0$
für jede summierbare Uhr längs jeder Ausschöpfung? Das ist die
Finite-Variation-Analogie des Lévy-Bildes: $\sum_{a_k\le t}m_k<\infty$ ist
$\int(1\wedge|x|)\,\nu(\dif x)<\infty$, und Kompensation gibt es nicht.

Der Parameter, den die Summierbarkeit **nicht** kontrolliert, ist die
Schwanzgeschwindigkeit: $m_{(k)}\sim1/(k\log^2k)$ gibt
$\varepsilon_n\sim1/\log n$, und die profilfreie lineare Schranke
$v\le(n+\tfrac12)\eta$ des zwölften Laufs wird nutzlos. Getestet wurden
deshalb geschachtelte dyadische Uhren mit Levelgesamtmassen $c_j$ geometrisch
(Kontrolle), $1/j^2$ ($\varepsilon_J\sim1/J$) und $1/(j\log^2 j)$
($\varepsilon_J\sim1/\log J$), jeweils flach und mit Positionsfaktor $x^4$
(der realisierbare Rest des Verstärkungsmotors). Konservativ zugunsten des
Gegenspielers: $\varepsilon$ am Schnitt zählt die ganze Lücke, der
analytische Schwanz jenseits Level 20 wird jedem Gitterpunkt zugeschlagen.

### Die Messung: $v_J\approx c\cdot\sqrt{M\,\varepsilon_J}$, mit stabilem $c$

| Uhr | $v_6$ | $v_J/\sqrt{M\varepsilon_J}$ über $J=2..6$ |
|---|---|---|
| geometrisch flach | $0.106$ | $1.00,\,0.91,\,0.92,\,0.88,\,0.86$ |
| $1/j^2$ flach | $0.431$ | $0.98,\,0.91,\,0.89,\,0.89,\,0.90$ |
| $1/j^2\cdot x^4$ | $0.262$ | $0.61,\,0.54,\,0.54,\,0.55,\,0.55$ |
| $1/(j\log^2j)$ flach | $1.197$ | $1.08,\,1.02,\,1.00,\,0.99,\,0.98$ |
| $1/(j\log^2j)\cdot x^4$ | $0.859$ | $0.77,\,0.71,\,0.70,\,0.71,\,0.71$ |

$v_J$ fällt auf **allen** fünf Uhren monoton, auch auf den langsamen
Schwänzen — dort langsam, wie $\varepsilon_J$ selbst es diktiert —, und
$v_J/\sqrt{M\varepsilon_J}$ ist je Uhr über die Stufen hinweg nahezu
konstant. Die Energieform $v^2\lesssim BM\varepsilon$, die der dreizehnte
Lauf für frei-relaxierte Systeme in jeder Konstante widerlegt hat, kehrt auf
echten Trunkierungen als empirisches Gesetz zurück, mit $c^2\le1.17$ auf
allem Getesteten. Kontrolle: $\varepsilon\equiv0$ gibt $v=0$.

### Aber: keine uniforme Konstante über die Uhren

Die geformten Fassungen der Zeugen des dreizehnten Laufs bleiben Zeugen
gegen jede **uhrenfreie** Konstante. Wolke der Masse $\delta$ strikt unter
dem leichten Atom (also $\varepsilon(g)=\delta$ für alle $g$ über der
Wolke): der Zwei-Atom-Zeuge gibt $v^2/(M\varepsilon)\to3$
($\mu=10^{-3}$: $2.995$), das leichte Präfix $[\mu]^k+[1]$ gibt
$v\approx k\mu B$ und $v^2/(M\varepsilon)\approx0.77k$ (gemessen $1.98$,
$3.82$, $7.09$, $12.36$ für $k=2,4,8,16$; `summable_lp.py`-Nachlauf).
Jeder dieser Zeugen ist aber eine **einzelne Stufe**, keine Ausschöpfung:
sein Budget $\delta\approx k\mu^2$ ist an die festen Präfixmassen gebunden,
und sobald $\varepsilon_J<k\mu^2$, stirbt der Motor.

### Die Massenbilanz, heuristisch

Warum die Summierbarkeit anhaltenden Gewinn ausschließen sollte, in einer
Rechnung: der einzige gemessene Mechanismus trägt Gewinn
$v\approx\lambda B$ mit $\lambda$ = Masse eines leichten Präfixes unter
einem schweren Atom. Soll $\liminf_Jv_J\ge c>0$ längs einer Ausschöpfung
gelten, braucht es zu unendlich vielen Stufen frische Motoren auf feineren
Skalen, deren Präfixmassen $\lambda_i\ge c/B$ erfüllen — die Gesamtmasse
wäre unendlich. Das ist Punkt 3 des dreizehnten Laufs, jetzt quantitativ:
die Instanzen, auf denen die Relaxation unbeschränkt verstärkt, sind genau
die, die keine Uhr sind. **Lücke der Heuristik:** dass Motoren
verschiedener Skalen keine Präfixmasse teilen können (Interferenz), ist
unbewiesen; und ob es andere Mechanismen als den Präfixmotor gibt, weiß nur
das LP.

### Was (S) geben würde, und was nicht

Bewiesen würde: für jede rein atomare Uhr auf einer Kette — Summierbarkeit
ist bei einer Uhr keine Zusatzannahme — mit $|\kappa|\le B$ verschwindet der
Dualitätsdefekt, denn $|\Delta|\le v_J+\text{Schwanzsummen}\to0$ (die
Schwanzsummen wie im vierzehnten Lauf aus der absoluten Existenz der
Integrale). **Nicht** enthalten ist die $B$-Freiheit: die Reduktion braucht
$|h|\le B$ a priori, und die Frage des zwölften Laufs, ob die
$B$-Hypothese für die in sich dichte Atommenge fällt wie im
intervallendlichen Fall, bleibt offen und wird von (S) nicht berührt.

### Was als Nächstes zu rechnen bzw. zu beweisen ist

1. **Interferenztest:** eine Uhr mit hierarchisch geschachtelten Motoren
   ($\lambda_i$ summierbar, Wolke von Skala $i$ = Präfix von Skala $i{+}1$),
   gemessen längs der natürlichen Ausschöpfung — teilen sich Skalen die
   Masse, oder gilt $v_{J_i}\approx\lambda_iB$? Das ist der adversariale
   Rest der Massenbilanz-Heuristik.
2. **Beweisziel, benannt:** $v_J\le B\,\varepsilon_{J'}+\text{(Beitrag der
   zwischen $J'$ und $J$ eingetretenen Atome)}$ — eine Rekursion über
   Stufenpaare statt einer Schranke je Stufe; die Stabilität von $c$ über
   $J$ in allen fünf Messreihen sagt, dass die Stufen sich wie eine
   Kontraktion verhalten, nicht wie eine Kaskade.

### Teil (a) derselben Aufgabe

Die Einordnung der mengen-indizierten Lévy-Literatur steht in
`Facts/SETINDEXED.md` (Herbin–Merzbach am ar5iv-Text, Pedersen–Sato direkt
am PDF): Dualität, bivariate Zuwachsdarstellungen und Martingalprobleme
kommen dort **nicht** vor — Negativbefund —, die Flow-Projektion ist genau
der Zeitwechsel von `cor:atomless` und endet per Axiom (stochastische
Stetigkeit) vor den Atomen; für Task 23 gibt sie nichts her, was
`cor:atomless` nicht schon ist. Der Bedarf an *simple* statt *elementary*
flows ist wörtlich die Geometrie von `rem:fddnochain`, jetzt am Text belegt.

## Der Interferenztest, 2026-09-02 (sechzehnter Lauf): die Skalen teilen sich die Masse, (S) ist falsch, und die Relaxation kollidiert mit dem intervallendlichen Satz

Punkt 1 der Liste des fünfzehnten Laufs, ausgeführt; Punkt 2 (die
Stufenpaar-Rekursion) ist durch das Ergebnis erledigt, bevor er begonnen
wurde: die Stufen verhalten sich nicht wie eine Kontraktion — die Quotienten
$v_{i}/v_{i-1}$ steigen gegen $1$. Neu sind `Task23/interference.py`,
`interference_certificate.py` (exakte Bruchrechnung) und
`interference_separable.py`.

### Die hierarchische Motor-Uhr

Block $i$ = schweres Atom der Masse $M_i=\lambda_i$ über einem Präfix aus
$k=4$ leichten Atomen der Gesamtmasse $\lambda_i$, Blöcke absteigend
geschachtelt in $(2^{-i},2^{-i+1}]$, $\lambda_{i+1}=\lambda_i/k$,
$\lambda_1=2/5$. Gesamtmasse $16/15$, Atomtyp $\omega^*$ (Häufung bei $0$),
**intervallendlich** — eine echte summierbare Uhr, vom Satz des vierzehnten
Laufs abgedeckt. Die Wolke der Skala $i$ (Stufe $i$ der natürlichen
Ausschöpfung lässt die Blöcke $>i$ weg) ist genau der Präfix der Skala
$i{+}1$ samt allem Tieferen, $E_i=\tfrac{8}{3}\lambda_{i+1}=\tfrac{16}{15}4^{-i}$,
und deckt den Budgetbedarf des Motors $i$ ($\tfrac23\lambda_{i+1}$) vierfach.

### Messung 1: die Interferenz ist real, und sie ist mehr als additiv

LP des fünfzehnten Laufs (Residuum $\le B(\varepsilon(s)+\varepsilon(t))$;
hier ist $\varepsilon\equiv E_i$, weil alle fehlende Masse unter allen
präsenten Atomen liegt):

| Stufe | $2$ | $4$ | $6$ | $8$ | $10$ |
|---|---|---|---|---|---|
| $v_i$ | $0.414$ | $0.277$ | $0.176$ | $0.144$ | $0.109$ |
| $v_i/(\lambda_iB)$ | $4.1$ | $44$ | $452$ | $6.8\cdot10^3$ | $1.1\cdot10^5$ |
| $v_i/\text{additiv}$ | $0.83$ | $3.4$ | $22$ | — | — |
| $v_i/\sqrt{ME_i}$ | $1.6$ | $4.2$ | $10.6$ | — | — |

„additiv" ist die Einzelmotor-Buchhaltung
$\sum_j\min(1,E_i/\text{Budget}_j)\lambda_jB$ der Massenbilanz-Heuristik.
$\varepsilon$ fällt über fünf Größenordnungen, $v$ nur um Faktor sechs.
**Exakt zertifiziert** (`interference_certificate.py`, Rundung auf
Nenner $10^9$, Bedingungen 1 und 2 per Konstruktion, alle Gitterpaare von
Bedingung 3 in `Fraction`, dann Skalierung mit $\max(B_{\rm used},
\text{maxratio})$): $v_4\ge0.2767$, $v_6\ge0.1765$, $v_8\ge0.1440$.
Kontrolle $E=0$ gibt $v=0$.

**Damit ist die Frage (S) des fünfzehnten Laufs falsch**: es gibt eine
summierbare Uhr und eine Ausschöpfung, längs derer $v_J$ nicht gegen $0$
geht. Und die Lücke der Massenbilanz-Heuristik ist keine Lücke, sondern ihr
Fehler: die Relaxation verbraucht kein Budget — dieselbe fehlende Masse
steht allen Skalen zugleich zur Verfügung, die Konversionsrate
Budget$\to$Gewinn ist skalenfrei ($\approx\tfrac32kB$ je Motor), und die
gemessene Verstärkung liegt noch einmal um wachsende Faktoren über der
additiven Buchhaltung — die aufsteigende Kaskade des dreizehnten Laufs
(Blockmassen wachsen nach oben um Faktor $4$) läuft hier auf einer
realisierbaren Uhr.

### Messung 2: die Gestalt des Residuums, erstmals eingebaut — sie rettet den Kollaps nicht

Auf dieser Uhr ist jedes realisierbare Residuum separabel,
$R(s,t)=\varphi(s)+\varphi(t)$ mit $\varphi(g)=\sum_{\text{fehlend}}m_ah(a,g)$,
$|\varphi|\le BE$ — Punkt 3 des dreizehnten Laufs als LP: neue Variablen
$\varphi(g)$, Gleichheitszeilen, Schranke $BE$ (`interference_separable.py`).
Das ist echt enger als $|R|\le2BE$. Ergebnis, auf den Stufen $3$–$10$ **auf
alle gemessenen Stellen exakt**:

$$v_i^{\rm sep}\;=\;\tfrac1{24}+E_i\;\downarrow\;\tfrac1{24}\;>\;0,$$

(Stufe 10 verlangt die Reskalierung $\varphi=E\psi$, sonst bricht HiGHS ein;
reskaliert stimmt auch sie.) Der Gewinn sitzt stabil in **Block 1**: seine
Diagonalsumme ist auf jeder Stufe $\ge4$ exakt $1/24$, die Werte
konvergieren punktweise (schweres Atom: $h(a,a)\to\tfrac19$), nichts
wandert ins Feine — die tiefen Blöcke können die Diagonale auch nicht
tragen, ihre Gesamtmasse ist $E_J\ll\tfrac1{24}$.

### Die Kollision, präzise

Die Uhr ist intervallendlich; der Satz des vierzehnten Laufs gibt für sie
$\Phi(s,t)=\Phi(t,s)$, die Dualität **gilt**. Zugleich liefert das folgende
Kompaktheitsargument aus den Messwerten scheinbar ein exaktes Gegenobjekt:
optimale $h^{(i)}$ der separablen LPs sind gleichmäßig durch $B$ beschränkt;
eine Diagonalfolge gibt punktweise Konvergenz auf allen (Atom,
Gitterpunkt)-Paaren; für jedes feste Paar $(s,t)$ ist das Residuum
$\le2BE_i\to0$, die Schwänze der Summen sind durch $2BE_J$ gleichmäßig
kontrolliert, also erfüllt der Limes $h^*$ die Bedingungen 1–3 des
**unendlichen** Systems exakt, mit $|h^*|\le B$ und
$\Delta^*=\sum_am_ah^*(a,a)=\tfrac1{24}\neq0$. Nach der Äquivalenz des
zwölften Laufs („aus jeder Lösung von 1–3 mit $h(a,a)\neq0$ wird ein echtes
Gegenbeispiel") widerspräche das dem Satz. Einer von dreien hat eine Lücke:

1. **Die Äquivalenz des zwölften Laufs im Unendlichen** — der
   Hauptverdächtige. Die endliche Isolation der Diagonale ankert am
   **Bodenatom**: die Zeile an $(a_1,a_2)$ lautet $m_1h(1,1)=0$, weil unter
   dem untersten Atom nichts liegt. Auf $\omega^*$ gibt es kein unterstes
   Atom; jede Summe $\sum_{a<s}$ ist unendlich, und die Isolation
   teleskopiert ohne Anker nach unten. Es ist also offen — und jetzt die
   entscheidende Frage —, ob das unendliche $h$-System 1–3 auf $\omega^*$
   die Diagonale überhaupt erzwingt, oder ob es dort **echt schwächer** ist
   als das $\Phi/\gamma$-System des Manuskripts (dessen Starrheit der
   vierzehnte Lauf beweist). Gemessen passt dazu: am Stufe-8-Optimum ist
   $\max|H|$ auf Atompaaren $\approx372\,E_8$ — die Starrheitskonstante der
   endlichen Stufen explodiert wie $4^i$, das endliche System bleibt starr
   ($E=0$-Kontrolle), aber die Konstante ist im Limes wertlos.
2. **Das Kompaktheitsargument** — der Grenzübergang ist oben skizziert und
   sieht dicht aus, ist aber zwanzig Minuten alt und ungeprüft.
3. **Der Zusammenbau des vierzehnten Laufs** — mechanisch geprüft ist dort
   nur die Fensterstarrheit (R); die Schwanzlimiten sind Menschenarbeit.

Was daraus **unabhängig von der Auflösung** schon folgt: der LP-Weg — auch
mit separabler Residuengestalt — ist als Beweisvehikel für Uhren mit
hierarchisch aufsteigender Struktur zu schwach: auf einer Uhr, für die die
Dualität bewiesen ist, bleibt $v_J$ von $0$ weg. Für den ordnungsdichten
Fall heißt das: ein Kollaps-Argument à la (S) kann nicht der Weg sein; was
die Relaxation noch verschenkt, ist die **rekursive** Realisierbarkeit —
$\varphi$ muss selbst aus einem $h$ der fehlenden Atome kommen, das die
tiefen Bedingungen erfüllt, nicht nur $|\varphi|\le BE$.

### Was als Nächstes zu klären ist, in dieser Reihenfolge

1. **Die Adjudikation der Kollision**, am kleinen Modell: erzwingt das
   exakte $h$-System 1–3 auf der $\omega^*$-Kette $h(a,a)=0$? Entweder ein
   Beweis (dann liegt der Fehler im Kompaktheitsargument, und wo genau) oder
   eine explizite exakte Lösung mit $\Delta\neq0$ (dann ist die Äquivalenz
   des zwölften Laufs im Unendlichen falsch, die Reduktion auf $h$ ist für
   nicht bodenständige Atommengen nachzubessern, und alle
   $v_J$-Interpretationen der Läufe 12–16 sind entsprechend zu lesen). Die
   gemessene Blockstruktur (Block 1: $h(a,a)\approx[0,0,0.006,-0.03,\tfrac19]$,
   selbstähnliche Fortsetzung) ist der Kandidat für die Konstruktion.
2. Erst danach lohnt die rekursive Realisierbarkeit als LP.

### Sackgassen, vierzehnter Nachtrag

* **Die Stufenpaar-Rekursion / Kontraktions-Deutung des fünfzehnten
  Laufs.** Die Stabilität von $c$ in den fünf Messreihen war keine
  Kontraktion, sondern Artefakt der dort getesteten Uhren: auf der
  hierarchischen Motor-Uhr steigen die Quotienten $v_i/v_{i-1}$ gegen $1$.
  Wer $v_J\to0$ uhrenfrei beweisen will, beweist etwas Falsches — (S) hat
  ein zertifiziertes Gegenbeispiel.
* **Die Massenbilanz-Heuristik.** Ihr fehlendes Lemma (Motoren teilen keine
  Masse) ist falsch im einzig relevanten Sinn: die Relaxation kennt kein
  Budget, das verbraucht würde. Jede Fortsetzung, die Gewinn gegen
  verbrauchte Masse aufrechnet, braucht zuerst eine Bedingung, die das
  Teilen verbietet — die Separabilität allein tut es nicht.

## Die Adjudikation, 2026-09-02 (siebzehnter Lauf): das $h$-System ist auf $\omega^*$ starr, der Fehler lag im Kompaktheitsargument, und „(S) ist falsch" ist zurückgenommen

Punkt 1 der Liste des sechzehnten Laufs, entschieden — durch **Beweis**, nicht
durch eine Lösung: das exakte $h$-System 1–3 erzwingt auf jeder
intervallendlichen Kette $h(a,a)=0$. Der Bodenatom-Verdacht gegen die
Äquivalenz des zwölften Laufs war unbegründet; die Lücke lag im
Kompaktheitsargument, und zwar nicht in seiner Logik, sondern in seiner
gemessenen Prämisse. Neu ist `Task23/adjudicate.py`.

### Der Beweis, selbständig und kurz

Sei $q$ rein atomar, die Atome unter $t^*$ paarweise vergleichbar und
intervallendlich (Gitter $u_k$ wie im vierzehnten Lauf, ergänzter Deckel
$t^*$), $h$ eine Lösung von 1–3, alle Reihen $H(s,t)=\sum_{a<s}m_ah(a,t)$ und
$\Delta(t)=\sum_{a<t}m_ah(a,a)$ absolut konvergent (bei $|h|\le B$ und
summierbarer Masse automatisch). Setze
$$\kappa(a,t):=h(a,t)-h(a,a),\qquad
  \widehat w(s,t):=H(s,t)+\Delta(t)-\Delta(s).$$
Dann gilt, in drei Zeilen Algebra:

1. **Erstschritt** (definitorisch, die Schnittdifferenz ist $\{u_k\}$):
   $\widehat w(u_{k+1},t)-\widehat w(u_k,t)=m_k\kappa(u_k,t)$.
2. **Zweitschritt** (Bedingung 3 an $(s,u_{k+1})$ und $(s,u_k)$, dann 1.):
   $\widehat w(s,u_{k+1})-\widehat w(s,u_k)=-m_k\kappa(u_k,s)$.
3. **Antisymmetrie von $\kappa$ auf Atompaaren** ist wörtlich Bedingung 2;
   Antisymmetrie von $\widehat w$ ist wörtlich Bedingung 3.

Kreuzmultiplikation von 1. und 2. gibt für $\widehat w$ **exakt die Relation
$(\ast)$ des vierzehnten Laufs** — das $h$-System und das $\Phi$-System sind
im antisymmetrischen Sektor isomorph. Die Zwei-Diagonalen-Induktion läuft
also wörtlich (wohlfundiert durch die Intervallendlichkeit, ohne Boden und
Deckel) und gibt $\widehat w\equiv0$ auf dem ganzen Gitter. Die
Schwanzlimiten: für jedes Gitter-$t$ und $l\to-\infty$ ist
$0=\widehat w(t,u_l)=H(t,u_l)+\Delta(u_l)-\Delta(t)$, darin
$H(t,u_l)=-H(u_l,t)\to0$ — **Bedingung 3 verwandelt den
Zweitkoordinatenlimes in einen Schnittschwanz**, und genau hier, und nur
hier, geht die Summierbarkeit ein — und $\Delta(u_l)\to0$. Also
$\Delta(t)=0$ für jedes $t$, also $m_kh(u_k,u_k)=\Delta(u_{k+1})-\Delta(u_k)=0$. $\square$

Der Verdacht des sechzehnten Laufs — „die endliche Isolation der Diagonale
ankert am Bodenatom" — trifft die endliche Beweisführung, aber nicht das
System: den Anker ersetzt der Schwanzlimes.

### Die Äquivalenz des zwölften Laufs überträgt sich, mit korrigierter Konstante

Die Rückrichtung (aus $h$ mit 1–3 ein echtes Paar $(\Phi,\gamma)$) braucht
$\kappa(a,0):=-h(a,a)$, **nicht** $\kappa(a,0):=0$: nur damit ist
$\kappa(a,b)=h(a,b)-h(a,a)$ auf Atompaaren antisymmetrisch (Bedingung 2),
solange die Diagonale nicht schon verschwindet — im endlichen Fall ist der
Unterschied unsichtbar, weil sie dort verschwindet. Mit
$$\gamma:=\kappa/2,\qquad
  \Phi(s,t):=\tfrac12\textstyle\sum_{a<s}m_a\kappa(a,t)+\tfrac12\Delta(t)$$
gelten beide Einschrittrelationen aus \eqref{eq:incrementrep} für **jedes**
$y$, mit absolut konvergenten Summen, und der Dualitätsdefekt ist
$\Phi(t^*,0)-\Phi(0,t^*)=-\Delta(t^*)$. Der Satz des vierzehnten Laufs gibt
denselben Schluss also auch über diesen Umweg; beide Wege sind
gegeneinander konsistent.

### Wo das Kompaktheitsargument bricht

Nirgends in seiner Logik. Diagonalfolge, dominierte Konvergenz und der
Grenzübergang der Nebenbedingungen sind in Ordnung: ein Häufungswert der
$v_i$ **ist** die Diagonalsumme einer exakten beschränkten Lösung von 1–3.
Gebrochen ist die Prämisse $\lim v_i=\tfrac1{24}$ — sie war Extrapolation
aus den Stufen $\le10$. Mit dem Satz oben folgt zwingend $v_i\to0$;
quantitativ, mit Residuen $\varphi$ (die separable Gestalt):

* Der $(\ast)$-Defekt von $\widehat w$ ist **exakt**
  $-m_i\bigl(\varphi(u_{j+1})-\varphi(u_j)\bigr)$ — am LP-Optimum mechanisch
  bestätigt (`adjudicate.py`, Probe (d): $\le10^{-10}$ auf allen geprüften
  Paaren, Stufen 4–9); ebenso die exakt erzwungene Identität
  $h(u_j,u_{j+1})=h(u_j,u_j)$ (Probe (a), $\le10^{-8}$ — drei Zeilen von
  Bedingung 3, $\varphi$ kürzt sich).
* **Fensterschranke.** Läuft die Induktion nur im festen Fenster oberhalb
  eines Atoms $u_l$, so sind alle Koeffizienten Massenverhältnisse des
  Fensters — stufenunabhängig —, alle Fehlerterme $O(E_i)$, und die zwei
  Randterme kosten je $B\cdot M_{<u_l}$:
  $$v_i\;\le\;2B\,M_{<u_l}\;+\;(K_l+2B)\,E_i,\qquad
    K_l\ \text{stufenunabhängig}.$$
  Mit $M_{<u_l}\to0$ (Summierbarkeit) und $l=l(i)$ langsam wachsend folgt
  $v_i\to0$.

### Warum die Messung das nicht sieht

$K_l$ ist endlich, aber gewaltig: die Rekursionskoeffizienten sind
Massenverhältnisse bis $4^4$ je Blockübergang (rohe Schranke für die Blöcke
1–4: $\sim10^{48}$). Gemessen (`adjudicate.py`, Probe (b)) sättigt das
Optimum den Randterm exakt — $H(t^*,u_l)=B\,M_{<u_l}$ auf allen
Blockböden, $\Delta(u_l)\approx0$ — und $\widehat w(t^*,u_l)$ stagniert bei
$M_{<u_l}-\tfrac1{24}$; schon auf Stufe 9 heißt das $K_l\ge10^4$, und die
Stagnation kann das Plateau über Dutzende Stufen tragen. Die Stufen 10–14
(Reformulierung ohne $\varphi$-Variablen: Bedingung
$H(s,t)+H(t,s)=H(s,s)+H(t,t)$ exakt plus $|H(t,t)|\le BE$; HiGHS braucht
dafür `presolve=False`, sein Presolve meldet sonst fälschlich „Unknown";
die Ausreißer der Stufen 7 und 12 sind Solver-Unterschätzungen) bleiben bei
$\tfrac1{24}\pm2\cdot10^{-6}$. Das ist **kein** Gegenbefund: der Kollaps ist
bewiesen und liegt jenseits der numerisch erreichbaren Stufen.

### Was am sechzehnten Lauf zu korrigieren ist

* **„(S) ist falsch" ist zurückgenommen.** Die Motor-Uhr ist kein
  Gegenbeispiel: ihr $v_J$ geht gegen $0$, bewiesen. Die exakten Zertifikate
  ($v_8\ge0.144$ usw.) bleiben richtig als Aussagen über einzelne Stufen und
  sagen über den Limes nichts. Für intervallendliche Uhren, deren
  Ausschöpfung jedes Fenster irgendwann stabilisiert (alle bisher gebauten),
  ist (S) **wahr**. Für ordnungsdichte Atommengen bleibt (S) offen — dort
  stabilisiert kein Fenster, und das Argument dieses Laufs greift nicht.
* Richtig bleibt: die LP-Relaxation taugt nicht als Beweisvehikel — jetzt
  mit umgekehrtem Vorzeichen: nicht weil ihr Limes $\neq0$ wäre, sondern
  weil ihre endlichen Werte über den Limes nichts aussagen, sobald die
  Uhr aufsteigende Massenstruktur hat.

### Was der ordnungsdichte Kern davon hat

Der Isomorphismus $\widehat w\leftrightarrow\Phi$ ist das bleibende
Werkzeug: **jede** Aussage über das $\Phi$-System überträgt sich wörtlich in
das $h$-System und umgekehrt; wer den ordnungsdichten Fall angreift, kann
frei zwischen beiden wechseln und muss keine LP-Evidenz mehr konsultieren.
Der einzige offene Weg ist der schon im vierzehnten Lauf benannte: die
Schwanzrelationen über Häufungspunkte hinweg (kleinste Instanz: zwei
$\zeta$-Ketten), jetzt ohne die falsche Hoffnung, ein Kollapsargument über
LP-Werte könne ihn ersetzen.

### Die zwei $\zeta$-Ketten, reduziert: $(\ast)$ auf dem Viertelgitter mit Eckenabfall

Als Anzahlung auf diesen Weg ist die kleinste Instanz auf ihre algebraische
Normalform gebracht. Kette $A$ (Atome $a_j$, $j\in\mathbb Z$, aufsteigend,
Häufung von unten am Punkt $p$) unter Kette $B$ (Atome $b_i$, $i\in\mathbb Z$,
Häufung von oben an $p$), Massen $m^A_j,m^B_i>0$, summierbar. Dann:

1. **Blockintern** ist alles erledigt: innerhalb von $A$ und $B$ ist die
   Kette intervallendlich, der Satz des vierzehnten Laufs gibt $w\equiv0$ auf
   $A{\times}A$ und $B{\times}B$, und die Einschrittdifferenzen darin geben
   $\kappa\equiv0$ auf allen blockinternen Paaren. $\kappa$ lebt nur noch auf
   Kreuzpaaren, $x_{ij}:=\kappa(b_i,a_j)$.
2. **$\Phi$ ist an $p$ beidseitig stetig, in beiden Koordinaten**: die
   Differenz $\Phi(b_l,y)-\Phi(a_k,y)$ ist die Atomsumme über $[a_k,b_l)$,
   ein Schwanz der absolut konvergenten Reihe, und geht für $k,l\to\infty$
   gegen $0$; ebenso in der zweiten Koordinate. Daraus verschwinden die
   Kreuzwerte in Richtung $p$:
   $\lim_{i\to-\infty}w(b_i,a_j)=w(p,a_j)=\lim_k w(a_k,a_j)=0$ und
   $\lim_{j\to+\infty}w(b_i,a_j)=\lim_l w(b_i,b_l)=0$.
3. **Die Schwanzdarstellungen** (Einschritt plus 2.):
   $F(i,j):=w(b_i,a_j)=\sum_{i'<i}m^B_{i'}x_{i'j}=-\sum_{j'\ge j}m^A_{j'}\,
   \kappa(a_{j'},b_i)$, also
   $$F(i{+}1,j)-F(i,j)=m^B_i\,x_{ij},\qquad
     F(i,j{+}1)-F(i,j)=m^A_j\,x_{ij},$$
   und Kreuzelimination von $x$ gibt **wörtlich $(\ast)$** auf
   $\mathbb Z\times\mathbb Z$.

Die offene Frage ist damit exakt: *erzwingt $(\ast)$ auf dem vollen Gitter
zusammen mit dem Abfall $F(i,j)\to0$ für $i\to-\infty$ (jedes feste $j$) und
für $j\to+\infty$ (jedes feste $i$) — Abfall an den zwei an der Ecke
$(p,p)$ zusammenstoßenden Rändern, die anderen beiden Ränder sind frei —
schon $F\equiv0$?* Zwei Kandidatenfamilien sterben sofort: separables
$x_{ij}=\beta_i\lambda_j$ führt auf $\sum_{i'<i}m^B\beta_{i'}=c\,\beta_i$,
dessen Produktformel einen von $0$ weg konvergenten Limes $\beta_{-\infty}$
hat, während der leere Schwanz $\beta_{-\infty}=0$ verlangt; eine einzelne
besetzte Zeile $x_{i_0,\cdot}$ muss konstant sein und stirbt am
$j$-Abfall. Das ist kein Beweis, aber es zeigt: die Schwänze wirken genau
dort, wo Test X des vierzehnten Laufs die lokale Algebra enden sah. Wer den
Punkt aufnimmt, beginnt bei dieser Viertelgitterfrage — sie ist frei von
Uhren, Trunkierungen und LPs.

### Sackgassen, fünfzehnter Nachtrag

* **Limiten von LP-Werten messen und extrapolieren.** Das Plateau
  $\tfrac1{24}+E_i$ hielt exakt über sieben Stufen und ist trotzdem
  praeasymptotisch; die Konstanten, die es tragen, wachsen wie Produkte von
  Massenverhältnissen und sind jeder Messung voraus. Wer aus LP-Werten auf
  den Limes schließen will, braucht die Fensterschranke — und die beweist
  dann schon den Kollaps, ohne Messung.
* **Endliche Zertifikate als Aussagen über das unendliche System lesen.**
  Zum zweiten Mal dieselbe Falle wie im dreizehnten Lauf (Relaxation fürs
  System gehalten), diesmal in der Zeitrichtung: Stufenwerte fürs
  Limesverhalten gehalten.

## Die Viertelgitterfrage, 2026-09-02 (achtzehnter Lauf): Normalform als kommutierende Evolution, endliche Superpositionen und exponentiell abfallende Spektralmaße sterben, ohne Summierbarkeit ist die Aussage falsch

Vorab zur Laufgeschichte: die zwei Läufe zwischen dem siebzehnten und diesem
wurden von der Nutzungsgrenze abgeschnitten. Übrig blieb `Task23/zeta_cross.py`
mit Verweisen auf ein „Lemma 1", eine „Proposition 2", ein „Theorem 4" und
einen „Mechanismus (ii)", zu denen kein Protokolltext existierte. Dieser Lauf
hat die Aussagen aus dem Skript rekonstruiert, **selbst bewiesen** — nichts
davon ist aus dem Skript „übernommen" —, das Skript um die Probe (f) ergänzt
(rc=0) und schreibt hier den Text, der fehlte. Die Nummerierung folgt dem
Skript, damit die Verweise stimmen.

### Aufstellung: das System (Q)

Die Reduktion des siebzehnten Laufs, in einer Zeile. Massen
$\mu_i:=m^B_i>0$, $\nu_j:=m^A_j>0$ ($i,j\in\mathbb Z$), beide **summierbar**
($S:=\sum_i\mu_i<\infty$, $T:=\sum_j\nu_j<\infty$ — das ist `def:clock` für
die zwei $\zeta$-Ketten). Gesucht ist $x:\mathbb Z^2\to\mathbb R$ mit
zeilen- und spaltenweise absolut konvergenten Summen und

$$\sum_{i'<i}\mu_{i'}x_{i'j}\;=\;-\sum_{j'\ge j}\nu_{j'}x_{ij'}
\qquad\text{für alle }(i,j)\in\mathbb Z^2. \tag{Q}$$

Die gemeinsame Größe heißt $F(i,j)$; sie erfüllt dann automatisch beide
Einschrittrelationen $F(i{+}1,j)-F(i,j)=\mu_ix_{ij}$,
$F(i,j{+}1)-F(i,j)=\nu_jx_{ij}$, die Kreuzrelation $(\ast)$, den Westabfall
($F(i,j)\to0$ für $i\to-\infty$) und den Nordabfall ($F(i,j)\to0$ für
$j\to+\infty$), und auch $x_{ij}\to0$ in beiden Abfallrichtungen. **Die
Frage (V):** erzwingt (Q) schon $x\equiv0$? Ja ⟹ die Dualität gilt für die
zwei gestapelten $\zeta$-Ketten, und per Cantor–Bendixson öffnet sich der
diskrete, nicht intervallendliche Fall.

### Lemma 1 (der Haken): (Q) ist äquivalent zu $(\ast)$ plus Abfall

**(a) Flussebene.** Erfüllt $F$ beide Einschrittrelationen, so erfüllt $x$
selbst $(\ast)$ (Probe (a)). Erfüllt umgekehrt $x$ die Relation $(\ast)$ und
sind die Zeilensummen absolut konvergent, so erfüllt
$F^W(i,j):=\sum_{i'<i}\mu_{i'}x_{i'j}$ die $i$-Schritte immer und die
$j$-Schritte genau dann, wenn $\lim_{i\to-\infty}x_{ij}=0$ für jedes $j$:
Summation von $\mu_{i'}(x_{i',j+1}-x_{i'j})=\nu_j(x_{i'+1,j}-x_{i'j})$ über
$i'<i$ teleskopiert rechts zu $\nu_j(x_{ij}-x_{-\infty,j})$. **Der
Westlimes des Flusses ist die eigentliche Randbedingung**; genau an ihr
starb der separable Ansatz des siebzehnten Laufs.

**(b) Hakenkonstanz.** Gelten zusätzlich die spaltenweise absolute
Konvergenz und der Nordabfall von $F$, so ist der Haken
$D(i,j):=F(i,j)+\sum_{j'\ge j}\nu_{j'}x_{ij'}$ konstant: in $j$
definitorisch, in $i$ weil $(\ast)$ die Spaltensumme zu
$\mu_i(x_{i,\infty}-x_{ij})$ teleskopiert und $x_{i,\infty}=0$ aus dem
Nordabfall folgt (endlicher Kern: Probe (b),
$H(i{+}1,j)-H(i,j)=\mu_ix_{i,j_1+1}$). Entlang $j\to+\infty$ gehen beide
Summanden gegen $0$, also $D\equiv0$ — das **ist** (Q). Die Rückrichtung
(aus (Q) beide Schritte und beide Abfälle) ist die Dreieckszerlegung der
absolut konvergenten Schwänze.

### Die Normalform: eine kommutierende Evolution mit einem einzigen Operator

$(\ast)$ für $F$ ist äquivalent zu
$$F(\cdot,j{+}1)=(I+\nu_jL)\,F(\cdot,j),\qquad
(Lg)_i:=\frac{g_{i+1}-g_i}{\mu_i}.$$
**Alle Zeilenschritte sind $I+\nu_jL$ mit demselben $L$** — sie kommutieren,
die Evolution von Zeile $j$ nach Norden ist die Operatorfassung des
Produkts $\Pi_j(c)=\prod_{j'\ge j}(1+c\nu_{j'})$, einer ganzen Funktion vom
Geschlecht 0 mit Nullstellen genau bei $-1/\nu_{j'}$, und die
Summierbarkeit von $\nu$ ist die **endliche Horizontzeit** $T$. Die
Eigenvektoren von $L$ sind die separablen Moden
$\beta^c_i=\prod_{i'<i}(1+c\mu_{i'})$ (Eigenwert $c$, Probe (d)); ihre
$j$-Seite sind die Multiplikatoren $\lambda^c_j=\prod_{j'<j}(1+c\nu_{j'})$.
Wegen $\beta^c_{-\infty}=1\neq0$ hat $L$ auf dem Raum der westabfallenden
Zeilen **keine Eigenwerte**. Alle „$L$-Ableitungen" $L^kF$ sind ebenfalls
Lösungen und ebenfalls nordflach ($L^kF(i,j)\to0$ für $j\to\infty$, als
endliche Kombination) — die Frage (V) hat die Gestalt einer
**Quasianalytizitätsfrage**: ist die Evolutionsklasse starr gegen
Flachheit am Nordrand, d.h. ist $\Pi_j(L)$ auf dem Westraum injektiv?

Nebenbefund, der die Fensterschranke des siebzehnten Laufs einordnet:
$(I+\nu L)^{-1}$ existiert auf dem Westraum als Vorwärtsrekursion
$g_{i+1}=(1-\mu_i/\nu)g_i+(\mu_i/\nu)f_i$; sie ist Kontraktion, wo
$\mu_i\le\nu$, und bläht sonst mit Faktoren $\mu_i/\nu$ auf — die
$K_l$-Produkte von Massenverhältnissen sind genau die Norm dieser Inversen.

### Proposition 2: ohne Summierbarkeit ist (V) falsch

$\mu\equiv\nu\equiv1$, $g$ ein kompakter Buckel, $F(i,j):=g(i+j)$: erfüllt
$(\ast)$, beide Tail-Darstellungen, beide Abfälle, und ist nicht $0$
(Probe (c); die Darstellungen teleskopieren exakt, weil $g$ links wie
rechts schließlich $0$ ist). Die Summierbarkeit ist also keine
Bequemlichkeit, sondern die Aussage: sie macht die Massenkoordinaten
$B_i=\sum_{i'<i}\mu_{i'}\in(0,S)$, $A_j\in(0,T)$ endlich, und im
Kontinuumsbild $F=G(B+A)$ (Transportgleichung $\partial_BF=\partial_AF$)
decken die zwei abfallenden Ränder den **ganzen** Charakteristikenbereich:
der Westrand tötet $G$ auf $(0,T)$, der Nordrand auf $(T,T+S)$, und sie
stoßen an der Ecke $(p,p)$ zusammen. Das ist die geometrische Erklärung,
warum (V) plausibel ist und warum sie an der Ecke hängt.

### Proposition 3: jeder Einzelschritt ist injektiv

$\ker(I+\nu_jL)$ ist eindimensional, aufgespannt von $\beta^{-1/\nu_j}$
(bzw. dessen Abschneidung, wenn ein Faktor $1-\mu_{i_0}/\nu_j$
verschwindet: links davon $\beta$-förmig, rechts $0$). In jedem Fall ist
der Westlimes des Kernelements $\neq0$ — auf dem Westraum ist
$I+\nu_jL$ injektiv. Kein einzelner Schritt kann eine Lösung töten; wenn
(V) falsch ist, stirbt die Lösung erst **im Limes** der unendlich vielen
Schritte.

### Theorem 4: keine endliche Superposition separabler Moden löst (Q)

Sei $x=\sum_{r=1}^Rw_r\beta^{c_r}\lambda^{c_r}$ mit paarweise
verschiedenen $c_r\in\mathbb C$ (auch $c=0$, die konstante Mode, ist
zugelassen). Die Westbedingung aus Lemma 1(a) lautet
$\sum_rw_r\lambda^{c_r}_j=0$ für **alle** $j$. Der **Momentenschritt**
(Probe (d)): Anwenden von $(\Delta_jg)/\nu_j$ überführt sie wegen
$(\lambda^c_{j+1}-\lambda^c_j)/\nu_j=c\,\lambda^c_j$ in
$\sum_rw_rc_r^k\lambda^{c_r}_j=0$ für alle $j,k$. Jede Mode hat nur
endlich viele Nullstellenindizes ($1+c_r\nu_{j'}=0$ nur endlich oft, da
$\nu\to0$); wähle $j^*$ unterhalb aller, dann ist
$\lambda^{c_r}_{j^*}\neq0$ für alle $r$, und die Vandermonde-Matrix der
$c_r$ gibt $w=0$. (Ableitungsmoden $\partial_c^s[\beta^c\lambda^c]$
laufen wörtlich über die konfluente Vandermonde-Matrix.) Probe (d) zeigt
zugleich die **Schärfe**: auf einem $j$-Fenster der Länge $R-1$ gibt es
einen nichttrivialen Kern — erst das unendliche Fenster tötet. Der
Nordabfall wird nicht einmal gebraucht.

### Proposition 5: reelle Spektralmaße haben verschwindende Momente und sterben bei exponentiellem Abfall

Sei $x_{ij}=\int\beta^c_i\lambda^c_j\,d\sigma(c)$ mit einem signierten
Maß $\sigma$ auf $\mathbb R$, zulässig in dem Sinn, dass
$\int(1+|c|)^ke^{\Phi_\mu(|c|)+\Phi_\nu(|c|)}\,d|\sigma|<\infty$ für alle
$k$, wobei $\Phi_\mu(r):=\sum_i\log(1+r\mu_i)$ (und analog $\Phi_\nu$)
die **scharfe** gemeinsame Wachstumsschranke aller Moden ist:
$|\beta^c_i\lambda^c_j|\le e^{\Phi_\mu(|c|)+\Phi_\nu(|c|)}$ gleichmäßig
in $(i,j)$. Löst $x$ das System (Q), so gilt:

1. **Alle Polynommomente von $\sigma$ verschwinden.** Die Westbedingung
   gibt $\int\lambda^c_j\,d\sigma=0$ für alle $j$ (dominiert,
   $\beta^c_i\to1$); der Momentenschritt gibt
   $\int c^k\lambda^c_j\,d\sigma=0$ für alle $j,k$; und $j\to-\infty$
   mit der $j$-gleichmäßigen Dominante $|c|^ke^{\Phi_\nu(|c|)}$ liefert
   $\int c^k\,d\sigma=0$.
2. **Hat $\sigma$ exponentiellen Abfallspielraum**
   ($\int e^{\varepsilon|c|}\,d|\sigma|<\infty$ für ein
   $\varepsilon>0$), **so ist $\sigma=0$**: die Fourier–Laplace-
   Transformierte ist in einem Streifen analytisch, und alle
   Ableitungen in $0$ verschwinden.

Zwei Vorsichten, beide wesentlich. Erstens ist die Spektralgestalt eine
**Einschränkung**: dass jede westabfallende Lösung eine solche
Darstellung hat, ist nicht bewiesen; Proposition 5 begrenzt
Gegenbeispielkonstruktionen, sie beweist (V) nicht. Zweitens sind
komplexe Träger hier bewusst ausgeschlossen: über $\mathbb C$ ist die
Parametrisierung nur modulo der Annihilatoren ganzer Funktionen
definiert (ein Kreisintegral $\oint\beta^c\lambda^c\,dc$ ist $0$ nach
Cauchy und parametrisiert gar nichts).

### Die Mechanismen, warum es schwer ist

* **(i) Der Westlimes der Moden.** $\beta^c_{-\infty}=1$: jede einzelne
  Mode verletzt die Randbedingung; nur Auslöschung im Kontinuum von
  Moden könnte eine Lösung tragen. Endlich (Theorem 4) und exponentiell
  abfallend (Proposition 5) ist die Auslöschung unmöglich.
* **(ii) Die Dispersion.** Der charakteristische Ansatz $F=G(B_i+A_j)$
  hat für nichtaffines $G$ einen exakten $(\ast)$-Defekt mit dem Faktor
  $\mu_i\nu_j(\mu_i-\nu_j)$ (Probe (e): für $G(u)=u^2$ exakt dieser
  Faktor), und **derselbe antisymmetrische Faktor** sitzt in der exakten
  Energieidentität (Probe (f)): auf Lösungen von (Q) ist
  $$0=\tfrac12\sum_j\nu_jR_j^2+\tfrac12\sum_i\mu_iC_i^2
    +\tfrac12\sum_{ij}\mu_i\nu_j(\nu_j-\mu_i)\,x_{ij}^2,$$
  und der letzte Summand ist indefinit — die Paarung beweist nichts,
  solange kein Multiplikator das Vorzeichen repariert; separable
  Gewichte $\alpha_i\beta_j$ faktorisieren durch und ändern nichts
  (nachgerechnet, siehe Sackgassen). Das Kontinuum hat keinen solchen
  Term; die ganze Schwierigkeit von (V) ist diese Dispersion.

### Was jetzt offen ist, exakt

(V) selbst. Bewiesen ist: keine endliche Modensuperposition, kein
reelles Spektralmaß mit exponentiellem Abfall, kein endlich getragenes
$x$, kein Tod in endlich vielen Schritten — und ohne Summierbarkeit wäre
(V) falsch. Der verbleibende Raum ist scharf benannt: für **geometrisch
fallende Massen** ist $\Phi_\mu(r)+\Phi_\nu(r)=O((\log r)^2)$, die
Zulässigkeit verlangt von $\sigma$ also nur quasipolynomialen Abfall,
und Maße mit lauter verschwindenden Momenten und Abfall etwa
$e^{-\sqrt r}$ **existieren** (Stieltjes). Ob eines davon zusätzlich die
ganze Familie $\{\lambda_j\}_{j\in\mathbb Z}$ annihilieren kann — das
folgt aus den Momenten dann **nicht** mehr —, ist eine
Vollständigkeitsfrage für ein Geschlecht-0-Produktsystem in gewichtetem
$L^1(\mathbb R)$, in die die Massen über ihre Zählfunktion eingehen: die
erste Frage von Task 23, die echt an den **Asymptotiken** der Massen
hängen könnte (Denjoy–Carleman). Die zwei benannten Wege:

* **(α) Spektraldarstellung oder direkte Injektivität.** Zeige, dass
  $\Pi_j(L)$ auf dem Westraum injektiv ist — etwa indem man jeder
  westabfallenden Lösung eine Spektraldarstellung mit exponentiell
  abfallendem $\sigma$ verschafft (dann schließt Proposition 5), oder
  durch ein Carleman-Argument direkt an der Evolution.
* **(β) Das Gegenbeispiel.** Ein $\sigma$ mit quasipolynomialem
  Abfall, $\int\lambda^c_j\,d\sigma=0$ für alle $j$,
  $\int\beta^c_i\Lambda^c\,d\sigma=0$ für alle $i$
  ($\Lambda^c:=\lambda^c_{+\infty}$) und angepasster Konstante
  $\int(\lambda^c_j-\beta^c_i\Lambda^c)/c\,d\sigma=0$. Wer hier suchen
  will, suche zuerst bei stark lakunären Massen, wo die
  Produktsysteme am dünnsten sind.

### Sackgassen, sechzehnter Nachtrag

* **Die Energiepaarung mit separablen Gewichten.** In
  $\langle(P+N)x,\alpha_i\beta_jx\rangle$ faktorisieren die Gewichte aus
  dem indefiniten Diagonalterm heraus; die zusätzlichen positiven
  $F^2$-Terme (Abel) sind gegen ihn nicht abschätzbar, weil
  $\mu_i^2x_{ij}^2\le2F(i{+}1,j)^2+2F(i,j)^2$ einen Faktor $2$ kostet,
  den kein monotones Gewicht wieder hereinholt. Wer die Paarung
  fortsetzt, braucht einen **nichtdiagonalen** Multiplikator
  (Friedrichs), nicht bessere Gewichte.
* **Kompakt getragene Spektralmaße oder komplexe Konturen.** Kompakt
  reell: Momente töten sofort. Komplexe Konturen: parametrisieren
  modulo Cauchy nichts. Beides keine Quelle von Gegenbeispielen.
* **Aus dem Kontinuumsbild extrapolieren.** $F=G(B+A)$ ist im Diskreten
  um den Defekt aus Probe (e) falsch; die Starrheit des Kontinuums
  beweist nichts, sie erklärt nur, warum (V) plausibel ist. Die
  Dispersion ist der Gegenstand, nicht ein Störterm.

## Der Weg (β) ist zu, 2026-09-02 (neunzehnter Lauf): in der zulässigen Klasse entscheiden die Momente alles, die Vollständigkeitsfrage löst sich auf, und die Spektralschiene stellt nur die Null dar

Der Lauf gehört der Frage (V), an den zwei Wegen des achtzehnten Laufs.
Ergebnis in einer Zeile: **die „Vollständigkeitsfrage für ein
Geschlecht-0-Produktsystem", die der achtzehnte Lauf als offenen Kern von
Weg (β) benannt hat, ist keine Frage — in der zulässigen Klasse folgt die
Annihilation der ganzen Modenfamilie doch aus den Momenten**, und zwar aus
einem Ein-Zeilen-Mechanismus, den der achtzehnte Lauf übersehen hat: die
Geschlecht-0-Produkte haben **nichtnegative Taylorkoeffizienten**, und ihre
Koeffizienten-Majorante ist genau die Zulässigkeitsschranke. Damit ist
Weg (β) vollständig geschlossen: kein zulässiges reelles Spektralmaß kann
ein Gegenbeispiel zu (V) tragen, für keine summierbare Massenfolge,
lakunär oder nicht.

### Theorem 6: die Momente entscheiden die zulässige Paarung

Massen wie in (Q). **Zulässig** heiße ein reelles signiertes Borelmaß
$\sigma$ auf $\mathbb R$ mit
$\|\sigma\|_\Phi:=\int e^{\Phi_\mu(|c|)+\Phi_\nu(|c|)}\,d|\sigma|(c)<\infty$
— das ist *schwächer* als die Zulässigkeit von Proposition 5: die
Polynomgewichte $(1+|c|)^k$ sind entbehrlich, denn das Herausgreifen von
$k$ Faktoren $1+|c|\mu_{i_l}\ge|c|\mu_{i_l}$ gibt punktweise
$|c|^k\le C_k\,e^{\Phi_\mu(|c|)}$ mit $C_k=(\mu_{i_1}\cdots\mu_{i_k})^{-1}$.
Sei $\mathcal E$ die Klasse der ganzen Funktionen $E=\sum_kE_kc^k$ mit
$\sum_k|E_k|r^k\le C_E\,e^{\Phi_\mu(r)+\Phi_\nu(r)}$ für alle $r\ge0$.
Dann liegen $\beta_i$, $\lambda_j$, $\beta_i\lambda_j$, $\beta_i\Lambda$
und $(\lambda_j-\beta_i\Lambda)/c$ sämtlich in $\mathcal E$, und für
zulässiges $\sigma$ sind äquivalent:

1. $\int c^k\,d\sigma=0$ für alle $k\ge0$;
2. $\int E\,d\sigma=0$ für jedes $E\in\mathcal E$;
3. $\int\lambda^c_j\,d\sigma=0$ für alle $j\in\mathbb Z$;
4. $\int\beta^c_i\,d\sigma=0$ für alle $i\in\mathbb Z$.

*Beweis.* Mitgliedschaft: die Produkte haben nichtnegative Koeffizienten,
ihre Majorante ist der Wert auf der positiven Achse,
$\beta^r_i\lambda^r_j\le e^{\Phi_\mu(r)+\Phi_\nu(r)}$; für den Quotienten
$(\lambda_j-\beta_i\Lambda)/c$ (ganz, da der Zähler bei $0$ verschwindet)
schätze für $r\ge1$ mit $\sum_k|a_{k+1}-b_{k+1}|r^k\le
r^{-1}\sum(a_{k+1}+b_{k+1})r^{k+1}\le2e^{\Phi_\mu(r)+\Phi_\nu(r)}$ und für
$r\le1$ durch den Wert bei $1$. (1)⟹(2): wegen
$\int\sum_k|E_kc^k|\,d|\sigma|\le C_E\|\sigma\|_\Phi<\infty$ vertauscht
Fubini, $\int E\,d\sigma=\sum_kE_k\int c^k\,d\sigma=0$. (2)⟹(3),(4):
Mitgliedschaft. (3)⟹(1): $I_k(j):=\int c^k\lambda^c_j\,d\sigma$ ist
endlich ($|c|^k\lambda^{|c|}_j\le C_ke^{\Phi_\mu+\Phi_\nu}$), und die
punktweise Identität $\lambda^c_{j+1}=(1+c\nu_j)\lambda^c_j$ gibt
$I_k(j{+}1)=I_k(j)+\nu_jI_{k+1}(j)$; Induktion über $k$ (Basis (3), alle
$j$ zugleich) gibt $I_k\equiv0$ für alle $k$, und $j\to-\infty$ mit
$\lambda^c_j\to1$ punktweise und derselben Dominante gibt
$\int c^k\,d\sigma=\lim_jI_k(j)=0$. (4)⟹(1): wörtlich dasselbe auf der
$\beta$-Seite mit $i\to-\infty$. ∎

Das ist der Momentenschritt des achtzehnten Laufs, ergänzt um seine
Rückrichtung — und die Rückrichtung ist der ganze Punkt.

### Korollar 7: die Spektralschiene stellt nur die Null dar

**(a)** Ist $\sigma$ zulässig mit lauter Nullmomenten, so ist der
Spektralkandidat $x_{ij}:=\int\beta^c_i\lambda^c_j\,d\sigma$ **identisch
null** — Fall (2) mit $E=\beta_i\lambda_j$. **(b)** Löst ein
Spektralkandidat das System (Q), so gilt insbesondere der Westabfall
$x_{ij}\to0$ für $i\to-\infty$ (denn
$x_{ij}=(F(i,j{+}1)-F(i,j))/\nu_j$ und $F$ ist westabfallend), mit
dominierter Konvergenz ($\beta^c_i\to1$, Dominante
$e^{\Phi_\mu+\Phi_\nu}$) also $\int\lambda^c_j\,d\sigma=0$ für alle $j$ —
Bedingung (3) —, also $x\equiv0$. Der **Exponentialspielraum von
Proposition 5.2 ist für die Konklusion, auf die es ankommt, entbehrlich**:
$\sigma$ selbst muss nicht verschwinden — die Stieltjes-Maße überleben —,
aber alles, was ein zulässiges $\sigma$ darstellen kann, ist die Null.

### Korollar 8: Weg (β) ist leer, und die Denjoy–Carleman-Spekulation ist zurückgenommen

Die drei Bedingungen des Weges (β) — $\int\lambda^c_j\,d\sigma=0$,
$\int\beta^c_i\Lambda^c\,d\sigma=0$, $\int(\lambda^c_j-
\beta^c_i\Lambda^c)/c\,d\sigma=0$ — sind für zulässiges $\sigma$ nach
Theorem 6 sämtlich **äquivalent zu den Nullmomenten** (jede der
Funktionen liegt in $\mathcal E$; umgekehrt gibt (3) die Momente). Maße,
die sie erfüllen, existieren also in Hülle und Fülle — jedes
Stieltjes-Maß —, und jedes von ihnen stellt $x\equiv0$ dar. Zwei Sätze des
achtzehnten Laufs sind damit falsch bzw. gegenstandslos: *„ob eines die
ganze $\{\lambda_j\}$-Familie annihiliert — das folgt aus den Momenten
dann nicht mehr"* — es folgt doch, per Fubini über die nichtnegativen
Koeffizienten; und die Vermutung, hier liege „die erste echt
massenabhängige Stelle von Task 23 (Denjoy–Carleman)" — in der
Spektralklasse geht keinerlei Massenasymptotik ein, die Zählfunktion der
Massen tritt nie auf. Theorem 4 (endliche Superpositionen) ist als
Spezialfall enthalten: endlich getragenes $\sigma$ ist zulässig, seine
Nullmomente erzwingen per Vandermonde $\sigma=0$.

**Warum der achtzehnte Lauf das übersehen hat.** Er hat die Frage als
Vollständigkeitsfrage in einem gewichteten $L^1$ gelesen: dort sind
Polynome bei quasipolynomialem Gewicht nicht dicht (Stieltjes,
Momenten-Indeterminiertheit), also schien Momentenannihilation schwächer
als Familienannihilation. Aber die Moden sind keine beliebigen Elemente
des gewichteten Raums: sie sind ganze Funktionen, deren Taylorreihe gegen
jedes zulässige $\sigma$ **absolut paart**, weil die
Zulässigkeitsschranke als scharfe gemeinsame Majorante der Moden
*definiert* wurde. Was ein Stieltjes-Maß nicht annihiliert, liegt
außerhalb von $\mathcal E$ — etwa $e^{ac}$ mit Majorante $e^{ar}$, weit
über $e^{O((\log r)^2)}$ — und genau dort lebt die Indeterminiertheit.
Zwischen „$\sigma$ paart mit den Moden" und „die Paarung wird von den
Momenten berechnet" ist kein Platz.

### Mechanisch verifiziert

`Task23/spectral_closed.py` (mpmath, 50 Stellen; Gauß–Legendre 16 je
Halbperiode; rc=0): geometrische Massen $\mu_i=\tfrac12 8^{-|i|}$,
$\nu_j=\tfrac13 8^{-|j|}$, Stieltjes-Maß
$d\sigma=e^{-t^2/(2s^2)}\sin(2\pi t/s^2)\,dt$ unter $c=e^t$, $s^2=7/20$
(zulässig: $\Phi_\mu+\Phi_\nu\approx0.96(\log r)^2<\tfrac1{2s^2}(\log
r)^2\approx1.43(\log r)^2$; $\int e^{\Phi_\mu+\Phi_\nu}d|\sigma|=3.247$).
Alle Momente $k=0..10$, alle $\lambda_j$, alle $\beta_i$, das ganze
$13\times13$-Gitter $\int\beta_i\lambda_j\,d\sigma$ und die zwei übrigen
(β)-Bedingungen verschwinden relativ auf $<10^{-47}$ — bei
$\|\sigma\|_{TV}=0.943$. Die Trennschärfe der Klasse ist drastisch
sichtbar: die Kontrollfunktion $e^{-3c}$, außerhalb von $\mathcal E$,
paart auf $5.1\cdot10^{-13}$ — **37 Größenordnungen** über den
$\mathcal E$-Paarungen. Es ist die Koeffizienten-Majorante, die tötet,
nicht die Kleinheit von $\sigma$. Der Momentenschritt aus dem Beweis von
(3)⟹(1) ist auf den berechneten Integralen exakt (Probe (h)).

### Was das für (V) und Weg (α) heißt

* **Ein Gegenbeispiel zu (V), falls es existiert, ist nicht spektral**:
  es hat keine Darstellung $\int\beta^c_i\lambda^c_j\,d\sigma$ mit
  reellem $\sigma$, dessen Paarung absolut konvergiert — für keine
  Abfallrate. Mechanismus (i) des achtzehnten Laufs verschärft sich: auch
  die Auslöschung im **Kontinuum** von Moden ist unmöglich, nicht nur die
  endliche und die exponentiell abfallende.
* **Weg (α) wird leichter, nicht schwerer.** Sein Darstellungs-Unterweg
  verlangte „eine Spektraldarstellung mit exponentiell abfallendem
  $\sigma$ (dann schließt Proposition 5)". Nach Korollar 7 genügt
  **jedes zulässige** $\sigma$ — quasipolynomialer Abfall reicht. Wer
  jeder westabfallenden Lösung irgendeine zulässige reelle
  Spektraldarstellung verschafft, hat (V) bewiesen.
* **Ehrliche Grenze, unverändert die von Proposition 5:** Darstellungen,
  deren Integrale nur bedingt konvergieren, und komplexe Träger (modulo
  Cauchy-Annihilatoren) bleiben außerhalb des Satzes. Der Satz schließt
  die zulässige reelle Klasse, nicht jede denkbare Integraldarstellung.
* Offen ist damit **(V) selbst, jetzt ohne Gegenbeispielweg in der
  Spektralklasse**: was bleibt, ist Weg (α) — Carleman direkt an der
  Evolution, oder der Darstellungssatz für westabfallende Lösungen.

### Sackgassen, siebzehnter Nachtrag

* **Gegenbeispielsuche bei lakunären Massen über Spektralmaße.** Der
  Suchraum des achtzehnten Laufs („zuerst bei stark lakunären Massen, wo
  die Produktsysteme am dünnsten sind") ist leer: die Dünne der
  Produktsysteme ist irrelevant, weil die Paarung ohnehin von den
  Momenten berechnet wird. Wer nach Gegenbeispielen sucht, muss die
  Spektralgestalt ganz verlassen.
* **Den quasipolynomialen Abfallspielraum als Freiraum lesen.** Der
  Spielraum zwischen $e^{\varepsilon|c|}$ (Proposition 5.2) und
  $e^{\Phi_\mu+\Phi_\nu}$ (Zulässigkeit) sah aus wie Raum für
  Gegenbeispiele; tatsächlich ändert er nur, *welche* $\sigma\neq0$
  überleben, nicht, *was* sie darstellen (die Null). Die richtige
  Invariante war nie der Abfall von $\sigma$, sondern die Majorante der
  Gegenfunktionen.

## Weg (α), 2026-09-03 (zwanzigster Lauf): der Transformationsbeweis trägt — (V) ist bewiesen für quadrantensummierbare Lösungen, insbesondere für alle beschränkten, und die zwei $\zeta$-Ketten sind in der Klasse aller bisherigen Messläufe geschlossen

Vorab zur Laufgeschichte, zum dritten Mal dasselbe Muster: der Lauf 08:23 UTC
wurde von der Nutzungsgrenze abgeschnitten und hinterließ
`Task23/quarter_transform.py` — ein Prüfskript, das auf einen „Beweis des
zwanzigsten Laufs" verweist, den es nicht gab, und das nicht einmal lief
(Syntaxfehler in einer toten Platzhalterzeile; behoben). Dieser Lauf hat den
Beweis, auf den das Skript zeigt, **selbständig geführt** — nichts ist aus dem
Skript „übernommen" —, und dabei eine Hypothese gefunden, die das Skript
nirgends ausspricht und ohne die der Schluss nicht geht: die
Quadrantensummierbarkeit (H). Alle Proben des Skripts laufen exakt (rc=0);
sie verifizieren die endliche Beweisalgebra, wie der Docstring es ankündigt,
und der klassische Rest ist genau der dort benannte (Phragmén–Lindelöf für
Typ 0, Liouville).

### Die Hypothese (H), und wer sie erfüllt

System (Q) wie im achtzehnten Lauf; $\rho_j:=\sum_i\mu_i|x_{ij}|$ die
gewichtete Zeilennorm (nach Zeilenvoraussetzung endlich),
$R_j:=\sum_i\mu_ix_{ij}$ die volle Zeilensumme.

$$\textbf{(H)}\qquad \sum_{j\ge j_0}\nu_j\,\rho_j<\infty
\quad\text{für ein }j_0\in\mathbb Z.$$

„Für ein" ist „für jedes": beim Absenken von $j_0$ kommen endlich viele
endliche Terme hinzu. Nach Tonelli ist (H) dasselbe wie
$\sum_i\mu_i\kappa^{(j_0)}_i<\infty$ mit
$\kappa^{(j_0)}_i:=\sum_{j\ge j_0}\nu_j|x_{ij}|$ — die $\mu\nu$-gewichtete
Summierbarkeit von $|x|$ auf dem Nordquadranten; die gemeinsame Größe heiße
$\Sigma_{j_0}$. Hinreichend ist $\sup_{j\ge j_0}\rho_j<\infty$ (dann
$\Sigma_{j_0}\le T\sup\rho$), und dafür wiederum jedes **beschränkte** $x$
(dann $\rho_j\le BS$). Die Klasse (H) enthält also insbesondere die Klasse
$|h|\le B$, in der sämtliche LP- und Messläufe (zwölfter bis siebzehnter
Lauf) gearbeitet haben. Die nackte Voraussetzung von (Q) — nur zeilen- und
spaltenweise absolute Konvergenz — gibt (H) nicht her; genau dort bleibt (V)
offen, siehe unten.

### Theorem 9: die W-Transformation ist auf $\ell^1$ injektiv

Sei $\mu_i>0$ summierbar, $W^c_i:=\prod_{i'>i}(1+c\mu_{i'})$ (konvergent,
ganz in $c$, $|W^c_i|\le e^{\Phi_\mu(|c|)}$). Ist $a\in\ell^1(\mathbb Z)$ und
$\sum_ia_iW^c_i=0$ für alle $c$ mit $\Re c\ge0$, so ist $a=0$. **Keine
Hypothese (H); das ist ein unbedingter Satz über Geschlecht-0-Schwänze.**

*Beweis.* Fixiere $I_0$. Für $I\le I_0$ ist
$W^c_I=W^c_{I_0}\prod_{I<i'\le I_0}(1+c\mu_{i'})$, für $I>I_0$ ist
$W^c_I=W^c_{I_0}\big/\prod_{I_0<i'\le I}(1+c\mu_{i'})$ (Probe (D2), exakt).
Da $\sum_I|a_I||W^c_I|\le\|a\|_1e^{\Phi_\mu}$ absolut konvergiert, darf man
umgruppieren: auf $\Re c\ge0$, wo $W^c_{I_0}$ nullstellenfrei ist (alle
Nullstellen liegen bei $-1/\mu_{i'}<0$), gilt
$0=\sum_Ia_IW^c_I\big/W^c_{I_0}=P_{I_0}(c)+N_{I_0}(c)$ mit
$$P_{I_0}(c)=\sum_{I\le I_0}a_I\prod_{I<i'\le I_0}(1+c\mu_{i'}),\qquad
  N_{I_0}(c)=\sum_{I>I_0}\frac{a_I}{\prod_{I_0<i'\le I}(1+c\mu_{i'})}.$$
$P_{I_0}$ ist ganz mit $|P_{I_0}(c)|\le\|a\|_1e^{\Phi_\mu(|c|)}$, also vom
Exponentialtyp $0$, denn $\Phi_\mu(r)=o(r)$: jeder Summand
$\log(1+r\mu_i)/r$ ist durch $\mu_i$ dominiert und fällt gegen $0$
(dominierte Konvergenz — der im Skript angekündigte Typ-0-Nachweis).
$N_{I_0}$ ist auf $\Re c\ge0$ absolut und gleichmäßig konvergent (jeder
Nennerfaktor hat Betrag $\ge1$), dort also beschränkt durch $\|a\|_1$. Aus
$P_{I_0}=-N_{I_0}$ auf $\Re c\ge0$ folgt: $P_{I_0}$ ist auf der imaginären
Achse durch $\|a\|_1$ beschränkt, und eine ganze Funktion vom Typ $0$, die
auf einer Geraden beschränkt ist, ist überall beschränkt
(Phragmén–Lindelöf; Titchmarsh §5.62, Boas Kap. 6, Thm. 6.2.4 mit
$\tau=0$, gedreht), nach Liouville also konstant. Die Konstante ist $0$:
für reelles $c\to+\infty$ geht jeder Term von $N_{I_0}$ gegen $0$ (der
Faktor $1+c\mu_{I_0+1}$ divergiert), dominiert durch $|a_I|$, also
$P_{I_0}(c)=-N_{I_0}(c)\to0$. Damit ist $P_{I_0}\equiv0$, insbesondere
$P_{I_0}(0)=\sum_{I\le I_0}a_I=0$ — für **jedes** $I_0$, und Differenzen
benachbarter $I_0$ geben $a\equiv0$. $\square$

Die Probe (D1) (Dreiecksgestalt der Koeffizientenmatrix, Determinante
$\ne0$) ist das endliche Gegenstück; der unendliche Schluss läuft über die
Fußpunktzerlegung (D2), nicht über die Matrix.

### Theorem 10: (V) gilt unter (H)

Sei $x$ eine Lösung von (Q) (zeilen- und spaltenweise absolut konvergent)
mit (H). Dann ist $x\equiv0$.

*Beweis.* **1. Die Transformierte.** $G_j(c):=\sum_i\mu_iF(i,j)W^c_i$;
wegen $\sum_i\mu_i|F(i,j)|\le S\rho_j$ ist $G_j$ ganz mit
$|G_j(c)|\le S\rho_j\,e^{\Phi_\mu(|c|)}$ — Typ $0$, wie oben. **2. Abel
(Probe (A), Grenzfassung).** Für jedes $c\in\mathbb C$:
$$\sum_i\mu_ix_{ij}W^c_i \;=\; R_j+c\,G_j(c). \tag{A$\infty$}$$
Die endliche Identität ist exakte Algebra; im Limes $i_B\to+\infty$ geht
$F(i_B{+}1,j)\to R_j$ und $W_{i_B}\to1$, im Limes $i_A\to-\infty$ geht
$F(i_A,j)\to0$ (Westschwanz) gegen den beschränkten Faktor
$W_{i_A-1}\to\prod_{i'\in\mathbb Z}(1+c\mu_{i'})$. **3. Nordrekursion
(Probe (B), auf Lösungen $D\equiv0$).** Termweise Differenz und (A$\infty$):
$$G_{j+1}=(1+c\nu_j)\,G_j+\nu_jR_j \qquad\text{für alle }c. \tag{B$\infty$}$$
**4. Nordlimes — hier, und nur hier, steht (H).** Für festes $c$ und
$j\to+\infty$ ist $\mu_i|F(i,j)|\le\mu_i\kappa^{(j_0)}_i$ eine
$j$-gleichmäßige Dominante mit Summe $\Sigma_{j_0}$, und $F(i,j)\to0$
punktweise (Nordschwanz), also $G_j(c)\to0$. **5. Beschränktheit rechts.**
Für $\Re c\ge0$ ist $|1+c\nu_j|\ge1$, aus (B$\infty$) also
$|G_j|\le|G_{j+1}|+\nu_j|R_j|$, iteriert und mit Schritt 4:
$|G_{j_0}(c)|\le\sum_{J\ge j_0}\nu_J|R_J|\le\Sigma_{j_0}$ auf der ganzen
abgeschlossenen rechten Halbebene ($|R_J|\le\rho_J$, Reihe endlich nach
(H)). **6. Der reelle Limes.** Auflösen von (B$\infty$) nach unten (Probe
(C)) gibt auf $\Re c\ge0$ die Identität I
$$G_{j_0}(c)=-\sum_{J\ge j_0}\frac{\nu_JR_J}{\Pi_{j_0,J}(c)},\qquad
  \Pi_{j_0,J}(c)=\prod_{j'=j_0}^{J}(1+c\nu_{j'}),$$
(der Randterm $G_{j_B}/\Pi_{j_0,j_B-1}$ fällt nach Schritt 4 weg, die Reihe
ist durch $\Sigma_{j_0}$ dominiert), und für reelles $c\to+\infty$ geht
jeder Term gegen $0$ (der Faktor $1+c\nu_{j_0}$ divergiert), also
$G_{j_0}(c)\to0$. **7. Phragmén–Lindelöf und Liouville**, wörtlich wie in
Theorem 9: $G_{j_0}$ ist ganz vom Typ $0$ und auf der imaginären Achse durch
$\Sigma_{j_0}$ beschränkt, also überall beschränkt, also konstant, und die
Konstante ist der reelle Limes $0$. Damit $G_j\equiv0$ für jedes $j$.
**8. Rückweg.** (B$\infty$) mit $G\equiv0$ gibt $\nu_jR_j=0$, also
$R_j=0$; (A$\infty$) gibt $\sum_i(\mu_ix_{ij})W^c_i=0$ für alle $c$, und
die Zeilenfolge $a_i=\mu_ix_{ij}$ liegt in $\ell^1$ ($\|a\|_1=\rho_j$);
Theorem 9 gibt $a\equiv0$, und $\mu_i>0$ gibt $x_{ij}=0$ — für jede Zeile
$j$. $\square$

Konsistenzproben: ohne Summierbarkeit existiert schon $W^c_i$ nicht — der
Buckel von Proposition 2 wird nicht etwa übersehen, sondern die Transformation
verweigert sich ihm. Theorem 4 (endliche Superpositionen) und Korollar 7
(Spektralkandidaten) sind keine Spezialfälle — sie brauchen (H) nicht — und
bleiben als unbedingte Aussagen daneben stehen.

### Korollar 11: die zwei $\zeta$-Ketten in der beschränkten Klasse

**(a)** Jede beschränkte Lösung von (Q) verschwindet; allgemeiner jede mit
$\sup_{j\ge j_0}\rho_j<\infty$. **(b)** Über die Reduktion des siebzehnten
Laufs (blockintern erledigt der Satz des vierzehnten Laufs alles, $\kappa$
lebt nur noch auf Kreuzpaaren $x_{ij}=\kappa(b_i,a_j)$, und die
Schwanzdarstellungen sind wörtlich (Q)): für eine rein atomare Uhr, deren
Atome unter $t^*$ zwei übereinander gestapelte $\zeta$-Ketten bilden, gilt
die Dualität für jede Lösung des $h$-Systems, deren Kreuzwerte (H)
erfüllen — insbesondere für **beschränktes** $\kappa$, also in genau der
Klasse $|h|\le B$, in der alle bisherigen LPs, Zertifikate und Messungen
liefen. Die kleinste Instanz jenseits der Intervallendlichkeit ist damit in
dieser Klasse **geschlossen**; der Häufungspunkt zwischen den Ketten wird
von der Identität I überquert, nicht von einer Induktion.

### Was offen bleibt, exakt

* **(V) in der nackten Klasse.** Nur zeilen- und spaltenweise absolute
  Konvergenz, ohne (H). Beide Seiten der Methode brauchen dieselbe
  gemeinsame Größe: die $\mu$-seitige Transformation braucht
  $\Sigma_{j_0}$ für Nordlimes und Reihe I, und die gespiegelte
  $\nu$-seitige ($U_i(c)=\sum_j\nu_jF(i,j)\prod_{j'\ge j+1}(1+c\nu_{j'})$,
  Rekursion $U_{i+1}=(1+c\mu_i)U_i+\mu_iC_i\Pi_{-\infty}$ mit den vollen
  Spaltensummen $C_i$) braucht $\sum_i\mu_i|C_i|$ und für ihren Ostlimes
  $\sum_j\nu_j\rho_j$ — dieselbe Größe. (H) ist also keine Bequemlichkeit
  der Seitenwahl, sondern die Grenze der Transformationsmethode. Zwei
  benannte Angriffe: zeigen, dass Lösungen von (Q) (H) **automatisch**
  erfüllen (ein Bootstrap aus den Schwanzdarstellungen; offen), oder eine
  Paarung, die ohne die gemeinsame Summe auskommt.
* **Jenseits der zwei Ketten.** Der Cantor–Bendixson-Weg vom siebzehnten
  Lauf (diskrete, nicht intervallendliche Ketten mit mehr als einem
  Häufungspunkt; in sich dichte Atommengen) ist unberührt; die Werkzeuge —
  $\widehat w$-Isomorphismus, Theorem 9, die Identität I — stehen jetzt
  bereit, und die Identität I ist das erste Argument von Task 23, das
  einen Häufungspunkt überquert.
* **Die Roadmap.** `duality_of_atomic_intervalFinite` in
  `MartingaleProblems` Meilenstein 8 endet mit den gestapelten
  $\zeta$-Ketten als benannter Grenze. Ein Eintrag der (H)-Fassung wäre
  möglich, ist aber zurückgestellt, bis (V) in der nackten Klasse
  entschieden ist — die Manuskriptklasse verlangt nur absolute Konvergenz,
  und ein Roadmap-Punkt mit einer Hypothese, die das Manuskript nicht
  liefert, stünde schief. Das ist eine Entscheidung dieses Laufs und kann
  vom Nutzer umgestoßen werden.

### Sackgassen, achtzehnter Nachtrag

* **Die Spiegel-Transformation als Ausweg aus (H).** Nachgerechnet, siehe
  oben: sie tauscht nur, welche der beiden Tonelli-Lesarten von
  $\Sigma_{j_0}$ gebraucht wird. Wer (H) loswerden will, braucht eine neue
  Idee, keine neue Seite.
* **Die endliche Matrix (D1) statt der Fußpunktzerlegung (D2) im
  Unendlichen.** Die Dreiecksmatrix der elementarsymmetrischen Funktionen
  hat im Unendlichen keine Antidiagonale; die Zerlegung (D2) mit
  Phragmén–Lindelöf ersetzt sie vollständig. (D1) bleibt als endliche
  Konsistenzprobe wertvoll und als Beweisweg im Unendlichen unbrauchbar.

## Die nackte Klasse, 2026-09-03 (einundzwanzigster Lauf): (H) war nie die Grenze der Methode — (V) gilt, sobald der Fluss nach Norden beschränkt ist, und das ist die Hypothesengestalt, die das Manuskript an der einzigen Stelle, an der es $\Phi$ herstellt, ohnehin trägt

Der zwanzigste Lauf schloss mit „(H) ist keine Bequemlichkeit der Seitenwahl,
sondern die Grenze der Transformationsmethode" und nannte als Angriffe den
Bootstrap und „eine Paarung ohne die gemeinsame Summe". Beides ist zu kurz
gegriffen. Dieser Lauf hat den Beweis von Theorem 10 Schritt für Schritt
danach abgeklopft, **wofür** (H) dort steht, und findet: (H) trägt drei
Schritte, und zwar in einer Gestalt, die von der gemeinsamen Summe
$\Sigma_{j_0}$ gar nicht abhängt. Die abgezogene Bedingung — sie heiße (U) —
hat **zwei** unvergleichbare hinreichende Kriterien, (H) und die
Beschränktheit des Flusses; das zweite hat mit dem
$\mu\otimes\nu$-Integrierbarkeitsproblem nichts zu tun und ist in der
Manuskriptklasse erfüllt.

### Wofür (H) im Beweis von Theorem 10 steht

Aufstellung wie im achtzehnten Lauf: $\mu_i,\nu_j>0$ summierbar
($S=\sum_i\mu_i$, $T=\sum_j\nu_j$), $x:\mathbb Z^2\to\mathbb R$ mit
$\rho_j=\sum_i\mu_i|x_{ij}|<\infty$ (Zeilen), $\sigma_i=\sum_j\nu_j|x_{ij}|
<\infty$ (Spalten) und (Q); $F(i,j)$ der gemeinsame Wert,
$R_j=\sum_i\mu_ix_{ij}=\lim_{i\to+\infty}F(i,j)$,
$W^c_i=\prod_{i'>i}(1+c\mu_{i'})$, $G_j(c)=\sum_i\mu_iF(i,j)W^c_i$.

Die acht Schritte von Theorem 10 benutzen (H) an genau drei Stellen, und
jedesmal nur durch eine ihrer Folgerungen:

* **Schritt 4** (Nordlimes $G_j(c)\to0$) braucht eine in $j\ge j_0$
  gleichmäßige summierbare Majorante für $\mu_i|F(i,j)|$ — (H) liefert
  $\mu_i\kappa^{(j_0)}_i$. Gebraucht wird davon nur die **gleichmäßige
  Summierbarkeit** der Familie, nicht die Majorante.
* **Schritte 5 und 6** (Beschränktheit rechts, Reihe der Identität I)
  brauchen $\sum_{J\ge j_0}\nu_J|R_J|<\infty$ — (H) liefert es über
  $|R_J|\le\rho_J$. Gebraucht wird die Reihe, nicht $\rho$.

Damit ist die Bedingung abgezogen:

> **(U).** Für ein $j_0\in\mathbb Z$ gilt
> **(i)** *Straffheit nach Norden*:
> $\displaystyle\lim_{N\to\infty}\ \sup_{j\ge j_0}\ \sum_{|i|>N}\mu_i|F(i,j)|=0$,
> **(ii)** *Nordsummierbarkeit der Zeilensummen*:
> $\displaystyle\sum_{j\ge j_0}\nu_j|R_j|<\infty$.

(U)(i) ist wörtlich eine Straffheitsbedingung: die Flussmasse darf beim
Marsch nach Norden nicht nach Osten oder Westen entweichen. Die zwei freien
Ränder des Viertelgitters — Ost und Süd — sind genau die, an denen sie
entweichen könnte, und (U) verbietet das nur nach Osten und Westen, nicht
nach Süden.

### Theorem 12: (V) gilt unter (U)

*Sei $x$ eine Lösung von (Q) mit (U). Dann ist $x\equiv0$.*

*Beweis.* Alles für $j\ge j_0$; die Fortsetzung nach Süden ist Schritt 7.

**1. $G_j$ ist ganz vom Typ $0$.** Nach (U)(i) ist
$A:=\sup_{j\ge j_0}\sum_i\mu_i|F(i,j)|<\infty$ (endlich viele Terme plus ein
gleichmäßig kleiner Schwanz), und $|W^c_i|\le e^{\Phi_\mu(|c|)}$ mit
$\Phi_\mu(r)=\sum_i\log(1+r\mu_i)$. Also konvergiert $G_j$ auf Kompakta
gleichmäßig, ist ganz, und $|G_j(c)|\le A\,e^{\Phi_\mu(|c|)}$;
$\Phi_\mu(r)=o(r)$, weil $\log(1+r\mu_i)/r\le\mu_i$ punktweise gegen $0$
fällt (dominierte Konvergenz). Auf $\Re c\ge0$ ist überdies
$1\le|W^c_i|\le e^{\Phi_\mu(|c|)}$, jeder Faktor $|1+c\mu|\ge1$.

**2. Abel (A$\infty$).** $\sum_i\mu_ix_{ij}W^c_i=R_j+c\,G_j(c)$ für alle
$c\in\mathbb C$. Endlich ist das
$\sum_{i=i_A}^{i_B}(F(i{+}1,j)-F(i,j))W^c_i
 =F(i_B{+}1,j)W^c_{i_B}-F(i_A,j)W^c_{i_A}
  +c\sum_{i=i_A+1}^{i_B}\mu_iF(i,j)W^c_i$
(Probe (A), exakt), und im Limes geht $F(i_B{+}1,j)\to R_j$, $W^c_{i_B}\to1$,
$F(i_A,j)\to0$ (Westabfall) gegen den beschränkten Faktor $W^c_{i_A}$.

**3. Nordrekursion (B$\infty$).** Termweise Differenz und (A$\infty$):
$G_{j+1}=(1+c\nu_j)G_j+\nu_jR_j$ für alle $c$.

**4. Nordlimes.** Fixiere $c$ mit $\Re c\ge0$. $F(i,j)\to0$ punktweise für
$j\to+\infty$ (Nordschwanz), und die Familie $\mu_iF(i,j)W^c_i$ ist nach
(U)(i) und $|W^c_i|\le e^{\Phi_\mu}$ gleichmäßig summierbar; also
$G_j(c)\to0$. **Hier steht (U)(i), und nur hier.**

**5. Beschränktheit auf $\Re c\ge0$.** Aus (B$\infty$) und $|1+c\nu_j|\ge1$
folgt $|G_j|\le|G_{j+1}|+\nu_j|R_j|$; iteriert von $j_0$ bis $j_B$ und mit
Schritt 4 für $j_B\to\infty$:
$|G_{j_0}(c)|\le\sum_{J\ge j_0}\nu_J|R_J|<\infty$ nach (U)(ii), und dasselbe
mit jedem $j\ge j_0$ an der Stelle von $j_0$.

**6. Phragmén–Lindelöf, Liouville, und der Koeffizientenvergleich.** Jedes
$G_j$, $j\ge j_0$, ist ganz vom Typ $0$ und auf der imaginären Achse
beschränkt, also überall beschränkt (Titchmarsh §5.62; Boas Thm. 6.2.4 mit
$\tau=0$, gedreht) und nach Liouville konstant, $G_j\equiv K_j$. Setze das in
(B$\infty$) ein: $K_{j+1}=K_j+c\,\nu_jK_j+\nu_jR_j$ **für alle $c$**, also
$\nu_jK_j=0$, also $K_j=0$, und damit $K_{j+1}=\nu_jR_j=0$, also $R_j=0$ —
für jedes $j\ge j_0$. Nun gibt (A$\infty$) $\sum_i(\mu_ix_{ij})W^c_i=0$ für
alle $c$, die Folge $a_i=\mu_ix_{ij}$ liegt in $\ell^1$ ($\|a\|_1=\rho_j$),
und **Theorem 9** (unverändert, ohne jede Zusatzhypothese) gibt $a\equiv0$,
also $x_{ij}=0$ für alle $i$ und alle $j\ge j_0$.

**7. Fortsetzung nach Süden, hypothesenfrei.** Verschwinden alle Zeilen
$j'>j$, so ist $F(i,j)=-\sum_{j'\ge j}\nu_{j'}x_{ij'}=-\nu_jx_{ij}$, und mit
$P_i:=F(i,j)$ lautet die West-Darstellung $P_{i+1}-P_i=\mu_ix_{ij}
=-(\mu_i/\nu_j)P_i$, also $P_{i+1}=(1-\mu_i/\nu_j)P_i$ und
$P_i=P_{i_A}\prod_{i_A\le i'<i}(1-\mu_{i'}/\nu_j)$. Das Produkt konvergiert
für $i_A\to-\infty$ absolut (Summierbarkeit von $\mu$) gegen eine endliche
Zahl, und $P_{i_A}\to0$ (Westabfall); also $P\equiv0$ und $x_{\cdot j}=0$.
Induktion nach unten gibt $x\equiv0$ auf ganz $\mathbb Z^2$. $\square$

Zwei Nebenbefunde, die auch Theorem 10 betreffen. Erstens ist **die
Identität I entbehrlich**: Schritt 6 ersetzt den reellen Limes durch einen
Koeffizientenvergleich in (B$\infty$), der zugleich $K_j=0$ und $R_j=0$
liefert. Der zwanzigste Lauf hat sie als „das erste Argument von Task 23, das
einen Häufungspunkt überquert" gefeiert; das Überqueren steckt in Wahrheit im
**Nordlimes** von Schritt 4, und der ist in beiden Beweisen dieselbe Stelle.
Zweitens braucht Theorem 10 die Fortsetzung nach Süden (Schritt 7) genauso —
sie fehlte dort, weil (H) für ein beliebiges $j_0$ formuliert war und man
$j_0\to-\infty$ schicken konnte; unter (U) ist sie ein eigener Schritt, und
sie kostet nichts.

### Korollar 13: zwei unvergleichbare hinreichende Kriterien

**(a) (H) $\Rightarrow$ (U).** $|F(i,j)|\le\kappa^{(j_0)}_i$ für $j\ge j_0$
gibt die $j$-gleichmäßige Majorante $\mu_i\kappa^{(j_0)}_i$ mit endlicher
Summe $\Sigma_{j_0}$, also (U)(i); $|R_j|\le\rho_j$ gibt (U)(ii). Theorem 10
ist damit Korollar von Theorem 12.

**(b) Beschränkter Fluss $\Rightarrow$ (U).** Ist
$B_F:=\sup_{i\in\mathbb Z,\,j\ge j_0}|F(i,j)|<\infty$, so ist
$\sum_{|i|>N}\mu_i|F(i,j)|\le B_F\sum_{|i|>N}\mu_i\to0$ **gleichmäßig in
$j$** — hier, und nur hier, geht ein, dass die Uhr endliche Masse hat —,
also (U)(i); und $|R_j|\le B_F$ mit $\sum_{j\ge j_0}\nu_j\le T$ gibt (U)(ii).

**(c) Unvergleichbar, und wie diese Aussage zu lesen ist.** Weil jede der
beiden Bedingungen $x\equiv0$ erzwingt, kann es **keine** nichtverschwindende
Lösung geben, die die eine erfüllt und die andere nicht — die
Unvergleichbarkeit ist eine Aussage über die *Hypothesenklassen*, also
darüber, welche Paare $(\Phi,\gamma)$ man überhaupt einspeisen darf, nicht
über Zeugen. In dieser Lesart ist sie unmittelbar: (H) ist
$\sum_{j\ge j_0}\nu_j\rho_j<\infty$ und läßt $\rho_j\to\infty$ zu, sobald
$\nu_j$ schnell genug fällt; wegen $\sup_i|F(i,j)|\le\rho_j$ (Westabfall,
Probe (E)) ist das genau der Spielraum, in dem (b) fällt. Umgekehrt bindet
(b) nur den Wert und läßt die Zeilenvariationen $\rho_j$ frei, die (H)
gewichtet summierbar verlangt. Keine der beiden Bedingungen impliziert also
die andere; **(H) war nie die Grenze der Methode, sondern eines von zwei
Kriterien für dieselbe Bedingung (U).**

**(d) Beschränktes $x$ $\Rightarrow$ (b)**, denn $|F(i,j)|\le BS$. Korollar
11 des zwanzigsten Laufs ist damit doppelt abgedeckt.

### Korollar 14: die Manuskriptklasse liefert (b)

$F$ ist der **Dualitätsdefekt**: über die Reduktion des siebzehnten Laufs ist
$F(i,j)=\widehat w(b_i,a_j)$ und $\widehat w(s,t)=\Phi(s,t)-\Phi(t,s)$ — in
der Rückrichtung des zwölften Laufs ist $\Phi=\tfrac12\widehat w$, also
$\Phi(s,t)-\Phi(t,s)=\widehat w(s,t)$ nach dessen Antisymmetrie. Beschränktheit
des Flusses ist also die Beschränktheit des Defekts, und sie folgt aus der
Beschränktheit von $\Phi$ auf $\T_{\le t^*}\times\T_{\le t^*}$.

Genau das trägt das Manuskript an der einzigen Stelle, an der es ein solches
$\Phi$ probabilistisch **herstellt**: `thm:duality` (\EK{} 4.4.11) setzt in
\eqref{eq:dual1} eine integrierbare Dominante $\Gamma_T$ mit
$\sup_{r,s,t\le T}(|\alpha(X(r))|+1)|f(X(s),Y(t))|\le\Gamma_T$ und in
\eqref{eq:dual2} $\int_0^T|\alpha(X(u))|\dif u+\int_0^T|\beta(Y(u))|\dif u
\le C_T$ voraus; für
$\Phi(s,t)=E[f(X(s),Y(t))\exp\{\int_0^s\alpha(X(u))\dif u+\int_0^t\beta(Y(u))
\dif u\}]$ geben die beiden zusammen unmittelbar
$|\Phi(s,t)|\le e^{C_T}E[\Gamma_T]$ für alle $s,t\le T$. Die
Beschränktheit des Flusses ist also **keine Zusatzanalysis von der Art (H)**,
sondern die Hypothesengestalt, die dort ohnehin steht.

Ehrliche Einschränkung, und sie gehört dazu: `prop:atomicdual` und
`prop:mixeddual` sind abstrakt formuliert — $\Phi,\gamma:\T\times\T\to\R$ mit
\eqref{eq:incrementrep}, „no integrability hypothesis beyond the existence of
the integrals" —, und Theorem 12 ist unter dieser Formulierung **nicht**
hypothesenfrei. Der Satz für die zwei gestapelten $\zeta$-Ketten lautet
deshalb:

> **Korollar 14.** Ist $q$ rein atomar, bilden die Atome unter $t^*$ zwei
> übereinander gestapelte $\zeta$-Ketten, erfüllen $\Phi,\gamma$
> \eqref{eq:incrementrep} mit $\gamma_1=\gamma_2$, und ist $\Phi$ auf
> $\T_{\le t^*}\times\T_{\le t^*}$ beschränkt, so ist
> $\Phi(t^*,0)=\Phi(0,t^*)$.

Die Klasse $|h|\le B$, in der alle LPs, Zertifikate und Messungen des
zwölften bis siebzehnten Laufs liefen, ist echt kleiner: sie beschränkt die
**Dichte** $\gamma=\kappa/2$, Korollar 14 nur den **Wert** $\Phi$.

### Korollar 16: der Blockstapel — Theorem 12 iteriert über beliebig viele Häufungspunkte

Die zwei gestapelten $\zeta$-Ketten sind nicht die Reichweite von Theorem 12,
sondern nur seine kleinste Anwendung. Sei die Atommenge unter $t^*$ eine Kette,
und sei sie **diskret**: jedes Atom hat unter den Atomen einen unmittelbaren
Vorgänger und Nachfolger. Dann ist
$$a\sim b\ :\Longleftrightarrow\ \text{zwischen }a\text{ und }b\text{ liegen nur endlich viele Atome}$$
eine Äquivalenz, ihre Klassen — die **Blöcke** — sind konvex und
intervallendlich, also nach der Diskretheit vom Ordnungstyp $\zeta$, und die
Blöcke tragen die Quotientenordnung. Zusatzhypothese: **die Quotientenordnung
ist selbst intervallendlich**, je zwei Blöcke schließen also nur endlich viele
Blöcke ein; der *Blockabstand* $d(P,Q)$ ist dann endlich. Für zwei Blöcke ist
das der Fall des siebzehnten Laufs.

> **Korollar 16.** Ist $q$ rein atomar, ist die Atommenge unter $t^*$ eine
> diskrete Kette mit intervallendlicher Blockordnung, erfüllen $\Phi,\gamma$
> \eqref{eq:incrementrep} mit $\gamma_1=\gamma_2$, und ist $\Phi$ auf
> $\T_{\le t^*}\times\T_{\le t^*}$ beschränkt, so ist $\Phi(t^*,0)=\Phi(0,t^*)$.

*Beweis, Induktion über den Blockabstand.* Sei $w(s,t)=\Phi(s,t)-\Phi(t,s)$.

**$d=0$** (blockintern): der Satz des vierzehnten Laufs, jeder Block ist
intervallendlich; $w\equiv0$ auf $P\times P$ und $\kappa\equiv0$ auf den
blockinternen Atompaaren.

**Der Induktionsschritt.** Seien $P<Q$ Blöcke mit $d(P,Q)=d\ge1$, $P$ unten.
Numeriere $P=\{a_j\}_{j\in\mathbb Z}$ und $Q=\{b_i\}_{i\in\mathbb Z}$
aufsteigend und setze $F(i,j)=w(b_i,a_j)$, $x_{ij}=\kappa(b_i,a_j)$,
$\nu_j=m^P_j$, $\mu_i=m^Q_i$ — beide positiv und summierbar, weil sie
Teilsummen der Uhrenmasse sind. Weil die Atomkette diskret ist, trägt
$[b_i,b_{i+1})$ genau das eine Atom $b_i$ und $[a_j,a_{j+1})$ genau das eine
Atom $a_j$; \eqref{eq:incrementrep} gibt daher
$$F(i{+}1,j)-F(i,j)=\mu_i\,x_{ij},\qquad
  F(i,j{+}1)-F(i,j)=\nu_j\,x_{ij}$$
(die zweite mit der Antisymmetrie von $\kappa$), also die Flussgestalt von (Q).

Die **zwei Abfälle stehen an den einander zugewandten Rändern**. Nach unten
von $Q$: $\lim_{i\to-\infty}F(i,j)$. Sei $R$ der größte Block in $[P,Q)$ — er
existiert, weil diese Menge $P$ enthält und nach der Intervallendlichkeit der
Blockordnung endlich ist; für $d=1$ ist $R=P$, und dann ist der folgende Limes
ein blockinterner —, so
ist $w(b_i,a_j)-w(r_l,a_j)$ in beiden Koordinaten eine Atomsumme über
$[r_l,b_i)$, ein Schwanz der nach \eqref{eq:incrementrep} absolut
konvergenten Reihe, und geht für $i\to-\infty$, $l\to+\infty$ gegen $0$; also
$\lim_{i\to-\infty}F(i,j)=\lim_{l\to+\infty}w(r_l,a_j)$, und das ist $0$, weil
$d(R,P)=d-1<d$. Nach oben von $P$ ebenso mit dem kleinsten Block in $(P,Q]$,
der für $d=1$ gerade $Q$ ist: $\lim_{j\to+\infty}F(i,j)=0$. Damit ist (Q)
erfüllt.

$\Phi$ ist beschränkt, also ist $|F|\le2\sup|\Phi|$ beschränkt, also gilt
Korollar 13(b), also (U), also nach **Theorem 12** $x\equiv0$ und $F\equiv0$
auf $Q\times P$. Das schließt den Schritt.

**Der Abschluss.** $w$ verschwindet damit an jedem Paar von Atomen unter
$t^*$. Die Randwerte $w(t^*,0)$ und $w(t^*,a)$ kommen als Schwänze derselben
absolut konvergenten Atomsummen, wie im Beweis von
`duality_of_atomic_intervalFinite`, und geben $\Phi(t^*,0)=\Phi(0,t^*)$.
$\square$

Drei Bemerkungen dazu, und die dritte ist eine Grenze.

1. Die Beschränktheit von $\Phi$ geht **nur** über Korollar 13(b) ein, an
   jedem Induktionsschritt gleich; eine blockweise Schranke genügte.
2. Der Fall $d=1$ mit zwei Blöcken ist Korollar 14. Neu ist $d\ge2$, und
   neu ist, dass die Blockordnung unendlich sein darf: $\omega$, $\omega^*$
   und $\zeta$ von $\zeta$-Ketten sind erfaßt, also Atommengen mit abzählbar
   unendlich vielen Häufungspunkten.
3. **Was nicht erfaßt ist.** Erstens Blockordnungen, die nicht
   intervallendlich sind — dort ist der Blockabstand unendlich und die
   Induktion hat keinen Anfang; das ist der Cantor–Bendixson-Weg eine Stufe
   höher, und er wiederholt die Ausgangsfrage auf dem Quotienten. Zweitens
   nichtdiskrete Atomketten, insbesondere in sich dichte: dort gibt es keine
   Nachbaratome, die Einschrittrelationen existieren nicht, und Theorem 12
   ist nicht anwendbar. Der ordnungsdichte Kern bleibt also offen, und zwar
   an derselben Stelle wie seit dem elften Lauf — an der Einschrittrelation,
   nicht mehr an der Analysis.

### Proposition 15: die Gestalt jedes Gegenbeispiels

Zwei Umformulierungen, die der Buchhaltung guttun. Aus
$F(i{+}1,j)-F(i,j)=\mu_ix_{ij}$ und $F(i,j{+}1)-F(i,j)=\nu_jx_{ij}$ folgt
$$\rho_j=\operatorname{Var}_i F(\cdot,j),\qquad
  \sigma_i=\operatorname{Var}_j F(i,\cdot):$$
die nackte Voraussetzung von (Q) ist genau, dass **jede Zeile und jede Spalte
des Flusses von beschränkter Variation ist**, (H) ist die
$\nu$-gewichtete Summierbarkeit der Zeilenvariationen nach Norden, und (U)(i)
ist Straffheit statt Summierbarkeit. Damit hat jede nichtverschwindende
Lösung von (Q) zwingend, für **jedes** $j_0$:

1. $\sup_{i,\,j\ge j_0}|F(i,j)|=\infty$ (Korollar 13(b));
2. $\sum_{j\ge j_0}\nu_j\rho_j=\infty$ und $\sum_i\mu_i\sigma_i=\infty$
   (Korollar 13(a); die zweite Summe dominiert die erste nach Tonelli), also
   insbesondere $\sup_j\rho_j=\infty$, weil $\sum_j\nu_j<\infty$;
3. $\rho_j<\infty$ für jedes einzelne $j$ und $\sigma_i<\infty$ für jedes
   einzelne $i$ — ein Fubini-Hindernis: $|x|$ ist zeilen- und spaltenweise
   $\mu$- bzw. $\nu$-integrierbar und auf keinem Nordquadranten
   $\mu\otimes\nu$-integrierbar;
4. entweder entweicht die Flussmasse beim Marsch nach Norden nach Osten oder
   Westen — (U)(i) fällt —, oder $\sum_{j\ge j_0}\nu_j|R_j|=\infty$.

Punkt 1 ist der brauchbarste: ein Gegenbeispiel muss einen **unbeschränkten
Dualitätsdefekt** haben, und zwar auf jedem Nordquadranten. Wer nach einem
sucht, sucht nicht mehr eine Lösung mit unsummierbarer Doppelreihe, sondern
eine mit unbeschränktem $\Phi$.

### Was jetzt offen ist, exakt

* **(V) bei unbeschränktem Defekt.** Die Straffheit (U)(i) aus (Q) allein zu
  gewinnen, ist unverändert offen; der Bootstrap-Angriff des zwanzigsten
  Laufs richtet sich jetzt auf (U)(i) statt auf (H) und ist damit schwächer
  geworden — Straffheit ist weniger als Summierbarkeit. Der Ansatzpunkt ist
  die Evolutionsgestalt: $\rho_{j+1}\le\rho_j+2\sum_i(\nu_j-\mu_i)^+|x_{ij}|$
  (aus $\mu_ix_{i,j+1}=(\mu_i-\nu_j)x_{ij}+\nu_jx_{i+1,j}$, einer
  Konvexkombination genau dort, wo $\nu_j\le\mu_i$) — die Zeilenvariation
  kann nur dort wachsen, wo die $\nu$-Masse die $\mu$-Masse übersteigt, und
  das sind wegen der Summierbarkeit beider Seiten die Ränder
  $i\to\pm\infty$. Das ist dieselbe Stelle, an der (U)(i) entweichen ließe.
* **Jenseits der zwei Ketten** ist bei beschränktem $\Phi$ erledigt, soweit
  die Atomkette diskret ist und die Blockordnung intervallendlich
  (Korollar 16). Offen bleiben dort genau zwei Dinge, und beide sind
  benannt: eine Blockordnung, die nicht intervallendlich ist — die
  Ausgangsfrage eine Cantor–Bendixson-Stufe höher, auf dem Quotienten —, und
  die nichtdiskrete, insbesondere in sich dichte Atomkette, wo es keine
  Einschrittrelationen gibt und Theorem 12 nicht ansetzt. Der ordnungsdichte
  Kern hängt damit nicht mehr an der Analysis, sondern an der Algebra der
  Einschrittrelation.
* **Die Roadmap.** Der zwanzigste Lauf hat einen Eintrag der (H)-Fassung
  zurückgestellt, weil „die Manuskriptklasse nur absolute Konvergenz
  verlangt". Für Korollar 14 gilt der Einwand nicht mehr: seine Hypothese ist
  die Beschränktheit von $\Phi$, und die steht in `thm:duality` als
  \eqref{eq:dual1}+\eqref{eq:dual2} ohnehin da. Der Eintrag ist mit diesem
  Lauf gemacht (`MartingaleProblems` Meilenstein 8,
  `duality_of_atomic_twoChains_of_bounded`).

### Sackgassen, neunzehnter Nachtrag

* **Die Spiegel-Transformation, zum zweiten Mal.** Der achtzehnte Nachtrag
  hielt fest, dass sie nur die Tonelli-Lesart von $\Sigma_{j_0}$ tauscht. Das
  bleibt richtig und ist jetzt gegenstandslos: nicht die Seite war das
  Problem, sondern dass $\Sigma_{j_0}$ überhaupt für einen **Limes** benutzt
  wurde, wo Straffheit genügt.
* **„(H) ist die Grenze der Methode".** Der Schluss des zwanzigsten Laufs,
  und er war voreilig: er las aus „beide Seiten brauchen dieselbe Summe" ein
  Methodenhindernis, statt zu prüfen, wofür die Summe gebraucht wird. Die
  Lehre ist dieselbe wie im siebzehnten Lauf beim Kompaktheitsargument —
  eine Prämisse, die aus der Rechnung stammt statt aus dem Beweisbedarf.
* **Der reelle Limes als Weg zur Konstanten $0$.** Er funktioniert (Identität
  I), ist aber überflüssig: der Koeffizientenvergleich in (B$\infty$) gibt
  $K_j=0$ und $R_j=0$ in einer Zeile und braucht die Reihe nicht.

## Die Stieltjes-Transformation, 2026-09-04 (zweiundzwanzigster Lauf): die Einschrittrelation war nie nötig — der ordnungsdichte Kern fällt, für jede Atomkette, bei $m\otimes m$-integrierbarer Dichte

Der einundzwanzigste Lauf schloß mit „der ordnungsdichte Kern hängt damit
nicht mehr an der Analysis, sondern an der Algebra der Einschrittrelation":
Theorem 12 setzt an Nachbaratomen an, und eine in sich dichte Atommenge hat
keine. Dieser Lauf nimmt die Diagnose ernst und **entfernt die
Einschrittrelation aus der Methode**. Sie war eine Bequemlichkeit der
$\mathbb Z$-Indizierung, nicht ihr Träger: die Abelsche Summation, an der
alles hängt, ist in Wahrheit eine **Stieltjes-Produktregel**, und die gilt auf
jeder abzählbaren Kette. Damit ist der seit dem elften Lauf offene Kern
geschlossen — unter einer Integrierbarkeitshypothese an die Dichte, die
schwächer ist als die Klasse $|h|\le B$, in der alle LPs und Messungen des
zwölften bis siebzehnten Laufs gearbeitet haben.

Neu ist `Task23/dense_chain.py` (Proben (A)–(G), exakt in `Fraction`, rc=0).

### Die Aufstellung, und wie wenig sie verlangt

Das System ist wörtlich das des zwölften Laufs. $A\subset[0,t^*)$ sei die
Atommenge, eine **beliebige abzählbare Kette** — keine Diskretheit, keine
Intervallendlichkeit, in sich dicht erlaubt —, $m_a>0$ mit
$M=\sum_am_a<\infty$, und $h:A\times T\to\R$ mit

* **(C1)** $h(a,0)=0$;
* **(C2)** $h(a,b)+h(b,a)=h(a,a)+h(b,b)$ für alle $a,b\in A$;
* **(C3)** $H(s,t)+H(t,s)=0$, wobei $H(s,t):=\sum_{a<s}m_ah(a,t)$.

Behauptung: $h(a,a)=0$ für jedes Atom. Dazu die abgeleiteten Größen
$$\Delta(t):=\sum_{a<t}m_ah(a,a),\quad
  \kappa(a,t):=h(a,t)-h(a,a),\quad
  \widehat w(s,t):=H(s,t)+\Delta(t)-\Delta(s),$$
mit den drei Eigenschaften des siebzehnten Laufs: $\widehat w$ hat in der
ersten Koordinate die Zuwachsdarstellung
$\widehat w(s',t)-\widehat w(s,t)=\sum_{a\in[s,s')}m_a\kappa(a,t)$
(definitorisch), $\kappa$ ist auf $A\times A$ antisymmetrisch (das ist (C2)),
$\widehat w$ ist antisymmetrisch (das ist (C3)). Die Randfunktionen sind
$$\widehat w(0,t)=\Delta(t),\qquad
  \widehat w(s,0)=-\Delta(s),\qquad
  \psi(t):=\widehat w(t^*,t).$$

**Der Beweis benutzt (C3) nur an Punktepaaren aus $A\cup\{0,t^*\}$.** Das ist
die eigentliche Neuigkeit gegenüber allen bisherigen Anläufen: der endliche
Satz und die Zwei-Diagonalen-Induktion brauchen einen Punkt **echt zwischen**
einem Atom und seinem Nachfolger (zwölfter Lauf, Probe an $N=2$), und genau
den nimmt die Ordnungsdichte weg. Hier wird kein Lückenpunkt angefaßt. Probe
(E) prüft das an der Wurzel: auf endlichen Ketten $n=1,\dots,7$ erzwingt
schon die lückenfreie Teilmenge — (C1), (C2), (C3) nur auf
$(A\cup\{t^*\})^2$ — die Diagonale $h(a,a)=0$; Kontrolle (E'): läßt man (C2)
weg, ist sie frei.

### Lemma 17.1 (Stieltjes-Produktregel auf einer beliebigen Kette)

*Seien $f,V:T\to\C$ beschränkt mit Zuwachsdarstellungen
$f(s')-f(s)=\sum_{a\in[s,s')}j^f_a$ und $V(s')-V(s)=\sum_{a\in[s,s')}j^V_a$
für alle $s\le s'$, mit $\sum_a|j^f_a|<\infty$ und $\sum_a|j^V_a|<\infty$.
Dann hat $fV$ die Zuwachsdarstellung mit den Sprüngen
$f(a{+})V(a{+})-f(a)V(a)$, wobei $f(a{+}):=f(a)+j^f_a$.*

*Beweis.* Mit $J_f=\sum_{a\in S}j^f_a$, $S=[s,s')\cap A$, und
$f(a)=f(s)+\sum_{a'\in S,a'<a}j^f_{a'}$ ist die Summe der Sprünge gleich
$f(s)J_V+V(s)J_f+\big[\sum_{a'<a}+\sum_{a'>a}+\sum_{a'=a}\big]j^f_{a'}j^V_a
 =f(s)J_V+V(s)J_f+J_fJ_V=f(s')V(s')-f(s)V(s)$; alle Umordnungen sind absolut
konvergent. $\square$

Kein Wort über Nachbarn, kein Wort über den Ordnungstyp. **Hier stirbt die
Einschrittrelation.**

### Die Gewichte, und Lemma 17.2 (Abel–Stieltjes)

$$W^c(a):=\prod_{a'>a}(1+cm_{a'}),\qquad V(s):=\prod_{a\ge s}(1+cm_a),\qquad
  V_0(c):=V(0)=\prod_{a\in A}(1+cm_a).$$
Alle Produkte konvergieren absolut ($\sum m_a<\infty$), sind ganz in $c$ und
erfüllen $|W^c(a)|\le e^{\Phi(|c|)}$ mit $\Phi(r)=\sum_a\log(1+rm_a)=o(r)$.
Die Teleskopidentität $\prod_{a\in S}(1+z_a)-1=\sum_{a\in S}z_a
\prod_{a'\in S,a'>a}(1+z_{a'})$ gibt $V$ die Zuwachsdarstellung mit den
Sprüngen $j^V_a=-c\,m_aW^c(a)$ und $V(a{+})=W^c(a)$.

> **Lemma 17.2.** Für jedes $t\in T$ und jedes $c\in\C$ gilt
> $$K(t;c)-c\,G(t;c)\;=\;\psi(t)-\Delta(t)\,V_0(c),$$
> mit $K(t;c):=\sum_am_a\kappa(a,t)W^c(a)$ und
> $G(t;c):=\sum_am_a\widehat w(a,t)W^c(a)$.

*Beweis.* Lemma 17.1 auf $f=\widehat w(\cdot,t)$ und $V$; der Sprung von $fV$
bei $a$ ist $m_a\kappa(a,t)W^c(a)-c\,m_a\widehat w(a,t)W^c(a)$, und die
Zuwachsdarstellung über $[0,t^*]$ liest sich
$(fV)(t^*)-(fV)(0)=\psi(t)\cdot1-\Delta(t)\cdot V_0$. $\square$

Probe (A) prüft Lemma 17.2 **ohne jede Hypothese an $h$** auf zufälligen
Ketten und sieben Werten von $c$ — es ist eine Identität der Definitionen.

### Die drei Identitäten

Setze $P(c):=\sum_am_a\psi(a)W^c(a)$, $Q(c):=\sum_am_a\Delta(a)W^c(a)$,
$R(c):=\sum_am_ah(a,a)W^c(a)$ und $S(c):=\sum_am_ah(a,t^*)W^c(a)$.

**(2) $P=V_0Q$.** Summiere Lemma 17.2 bei $t=b\in A$ gegen $m_bW^c(b)$:
$$\sum_{a,b}m_am_b\kappa(a,b)W^c(a)W^c(b)
 -c\sum_{a,b}m_am_b\widehat w(a,b)W^c(a)W^c(b)=P(c)-V_0(c)Q(c).$$
Beide Doppelsummen verschwinden, weil $\kappa$ und $\widehat w$ auf $A\times A$
antisymmetrisch und die Gewichte symmetrisch sind. Also $P(c)=V_0(c)Q(c)$.
*Benutzt: (C2) und (C3) auf $A\times A$; Probe (B), nichttriviale Diagonale in
allen vier Fällen.*

**(4) $R(c)=\Delta(t^*)+c\,Q(c)$.** Lemma 17.2 bei $t=0$: dort ist
$\kappa(a,0)=-h(a,a)$, $\widehat w(a,0)=-\Delta(a)$, $\psi(0)=-\Delta(t^*)$
und $\Delta(0)=0$. *Benutzt: (C1); Probe (C).*

**(5) $S(c)-R(c)+c\,P(c)=-\Delta(t^*)V_0(c)$.** Lemma 17.2 bei $t=t^*$: dort
ist $\kappa(a,t^*)=h(a,t^*)-h(a,a)$, $G(t^*;c)=-P(c)$ und $\psi(t^*)=0$.
*Benutzt: (C1) und (C3) an $A\times\{t^*\}$ samt $(t^*,t^*)$; Probe (D),
nichttriviale Diagonale in allen vier Fällen.*

**(7)** Aus (5) mit $cP=cV_0Q=V_0(R-\Delta(t^*))$ folgt in einer Zeile
$$S(c)=R(c)\,\bigl(1-V_0(c)\bigr)$$
— Probe (D'). Bei $c=0$ ist das $H(t^*,t^*)=0$, also (C3) auf der Diagonale.

### Theorem 17: die Diagonale verschwindet, auf jeder Kette

> **Theorem 17.** $A$ sei eine abzählbare Kette in $[0,t^*)$ mit Massen
> $m_a>0$, $M=\sum m_a<\infty$; $h$ erfülle (C1), (C2) und (C3), alle Reihen
> $H(s,t)$ und $\Delta(t)$ seien absolut konvergent, und es gelte
> $$\textbf{(F)}\qquad \sum_{a,b\in A}m_am_b|h(a,b)|<\infty.$$
> Dann ist $h(a,a)=0$ für jedes $a\in A$.

*Beweis.* **1. $R$ ist auf der imaginären Achse beschränkt.** Auf
$\Re c\ge0$ ist $|1+cm|\ge1$ für jedes $m>0$, also
$|W^c(a)|\le\prod_{a'}|1+cm_{a'}|=|V_0(c)|$ und damit
$|S(c)|\le\rho^*|V_0(c)|$ mit $\rho^*:=\sum_am_a|h(a,t^*)|<\infty$. Ferner ist
$|1+cm|^2=1+2m\Re c+m^2|c|^2\ge1+m^2|c|^2$, also
$|V_0(c)|\ge\widetilde V(|c|):=\prod_a(1+m_a^2|c|^2)^{1/2}$, und
$\widetilde V(r)\to\infty$ (ein einziges Atom genügt). Wähle $r_0$ mit
$\widetilde V(r_0)\ge2$. Für $\Re c\ge0$, $|c|\ge r_0$ gibt (7)
$$|R(c)|=\frac{|S(c)|}{|1-V_0(c)|}\le\frac{\rho^*|V_0(c)|}{|V_0(c)|-1}\le2\rho^*,$$
und auf dem Kompaktum $\{\Re c\ge0,\ |c|\le r_0\}$ ist
$|R|\le D\,e^{\Phi(r_0)}$ mit $D:=\sum_am_a|h(a,a)|<\infty$. Probe (G) prüft
die beiden Ungleichungen numerisch.

**2. $R$ ist konstant.** $R$ ist ganz vom Exponentialtyp $0$
($|R(c)|\le D\,e^{\Phi(|c|)}$, $\Phi(r)=o(r)$) und nach 1. auf der imaginären
Achse beschränkt; eine ganze Funktion vom Typ $0$, die auf einer Geraden
beschränkt ist, ist überall beschränkt (Phragmén–Lindelöf, Titchmarsh §5.62 /
Boas Thm. 6.2.4 mit $\tau=0$ — dieselbe Schranke, auf der schon die
Theoreme 9, 10 und 12 ruhen), nach Liouville also konstant,
$R\equiv R(0)=\Delta(t^*)$.

**3. $Q\equiv0$.** (4) gibt $c\,Q(c)=R(c)-\Delta(t^*)=0$ für alle $c$.

**4. $\Delta$ verschwindet auf den Atomen.** Theorem 9 gilt wörtlich auf
jeder abzählbaren Kette: für einen Fußpunkt $s_0\in T$ ist
$W^c(a)=V(s_0)\prod_{a<a'<s_0}(1+cm_{a'})$ falls $a<s_0$ und
$W^c(a)=V(s_0)\big/\prod_{s_0\le a'\le a}(1+cm_{a'})$ sonst (Probe (F)); die
Zerlegung $0=\sum_a\alpha_aW^c(a)/V(s_0)=P_{s_0}(c)+N_{s_0}(c)$ liefert
$P_{s_0}$ ganz vom Typ $0$ und auf $\Re c\ge0$ durch $\|\alpha\|_1$
beschränkt, also konstant; für reelles $c\to+\infty$ geht jeder Term von
$N_{s_0}$ gegen $0$, also $P_{s_0}\equiv0$ und insbesondere
$P_{s_0}(0)=\sum_{a<s_0}\alpha_a=0$ **für jedes $s_0\in T$**. Angewandt auf
$\alpha_a=m_a\Delta(a)\in\ell^1$ (denn $|\Delta|\le D$): $\Delta(a)=0$ für
jedes $a\in A$.

**5. $h(a,a)=0$ für jedes nichtmaximale Atom.** Zu $a\in A$ mit Atomen
darüber wähle $t_n\in A$ fallend mit $\bigcap_n(a,t_n)\cap A=\emptyset$ — das
geht, weil $A$ abzählbar ist: zu einer Aufzählung $\{b_k\}$ von
$A\cap(a,t_1)$ setze $t_{k+1}:=\min(t_k,b_k)$. Dann ist
$0=\Delta(t_n)-\Delta(a)=m_ah(a,a)+\sum_{b\in(a,t_n)}m_bh(b,b)$, und der
zweite Term geht gegen $0$ (dominierte Konvergenz, $\sum_bm_b|h(b,b)|=D$).

**6. Das maximale Atom.** Hat $A$ kein Maximum, ist mit 5. alles gezeigt und
$\Delta\equiv0$. Andernfalls sei $a_{\max}$ das größte Atom und
$\lambda:=h(a_{\max},a_{\max})$; nach 5. ist $\Delta(t)=m_{a_{\max}}\lambda$
für $t>a_{\max}$, insbesondere $\Delta(t^*)=m_{a_{\max}}\lambda$. Aus (2) und
$Q\equiv0$ folgt $P\equiv0$, mit Schritt 4 also $\psi(a)=0$, mit
$\Delta(a)=0$ also $H(t^*,a)=\Delta(t^*)$ und mit (C3) an $(t^*,a)$
$$H(a,t^*)=-\Delta(t^*)\qquad\text{für jedes }a\in A.$$
Hat $A$ ein Minimum $a_0$, so ist $H(a_0,t^*)=0$ (leere Summe); hat es
keines, so wähle $a_n\in A$ streng fallend und kofinal nach unten, dann ist
$\bigcap_n[0,a_n)\cap A=\emptyset$ und $H(a_n,t^*)\to0$ (dominierte
Konvergenz, Majorante $\sum_am_a|h(a,t^*)|=\rho^*$). Beidemal
$\Delta(t^*)=0$, also $\lambda=0$. $\square$

### Was die Hypothese (F) ist, und was sie nicht ist

(F) ist die $m\otimes m$-Integrierbarkeit der Dichte **auf Atompaaren**, und
sie geht an genau zwei Stellen ein: die Doppelsumme in (2) muß nach Fubini
umgeordnet werden dürfen, und $P$ muß existieren
($\sum_am_a|\psi(a)|<\infty$). Alles Übrige — Lemma 17.2, (4), (5), (7) und
die Schritte 1 bis 6 — braucht nur die absolute Konvergenz, die das System
ohnehin voraussetzt.

* (F) folgt aus $|h|\le B$ **auf $A\times A$** (dann $\le2BM^2$). Das ist echt
  schwächer als die Klasse $|h|\le B$ auf $A\times T$, in der der zwölfte bis
  siebzehnte Lauf gemessen haben, und heißt über $\gamma=\kappa/2$ die
  Beschränktheit der **Dichte** auf Atompaaren.
* (F) ist **unvergleichbar** mit der Hypothese von Korollar 14 (Beschränktheit
  des **Wertes** $\Phi$). Korollar 14 deckt unbeschränkte Dichten auf zwei
  gestapelten $\zeta$-Ketten, Theorem 17 deckt beliebige Ketten bei
  integrierbarer Dichte. Keins subsumiert das andere; zusammen decken sie
  alles, was Task 23 bisher an Instanzen gesehen hat.
* Ehrlich dazu: `prop:atomicdual` und `prop:mixeddual` sind abstrakt
  formuliert („no integrability hypothesis beyond the existence of the
  integrals"), und (F) ist eine echte Zusatzhypothese. Der Satz fürs
  Manuskript lautet deshalb:

> **Korollar 18.** Ist $q$ rein atomar, bilden die Atome unter $t^*$ eine
> Kette, erfüllen $\Phi,\gamma$ \eqref{eq:incrementrep} mit
> $\gamma_1=\gamma_2$, und ist $\gamma$ auf $A\times A$
> $m\otimes m$-integrierbar, so ist $\Phi(t^*,0)=\Phi(0,t^*)$ — **ohne jede
> Voraussetzung an den Ordnungstyp der Atommenge.**

### Was das für den offenen Kern heißt

Der ordnungsdichte Fall, seit dem elften Lauf der benannte Rest von Task 23,
ist damit **in der Klasse (F) geschlossen**, und zwar zusammen mit allem, was
die Cantor–Bendixson-Leiter darüber noch hätte kosten können: Theorem 17
kennt keine Blöcke, keinen Blockabstand und keine Induktion. Die
Zusatzhypothese von Korollar 16 — intervallendliche Blockordnung — entfällt,
die Diskretheit entfällt, und die kleinste Instanz der zwei $\zeta$-Ketten
ist ein Sonderfall.

Offen bleibt danach genau zweierlei, und beides ist benannt:

* **Die nackte Klasse.** Weder (F) noch die Beschränktheit von $\Phi$, nur die
  absolute Konvergenz der Reihen von \eqref{eq:incrementrep}. Das ist
  dieselbe Lücke, die der einundzwanzigste Lauf als „(V) bei unbeschränktem
  Defekt" führt, jetzt für beliebige Ketten statt nur für zwei
  $\zeta$-Ketten. Proposition 15 gilt unverändert und sagt, wie ein
  Gegenbeispiel aussehen müßte; neu hinzu kommt aus Theorem 17, daß es
  $\sum_{a,b}m_am_b|\kappa(a,b)|=\infty$ haben muß.
* **Die Halbordnung.** Theorem 17 benutzt die lineare Ordnung an jeder
  Stelle — Intervalle $[s,s')$, Produkte über $a'>a$, die Teleskopidentität.
  Für unvergleichbare Atome ist `prop:atomicposet` (sechster Lauf) der Satz,
  und der ist endlich. Eine unendliche Halbordnung mit summierbaren Massen
  ist von keinem der beiden Sätze erfaßt.

### Sackgassen, zwanzigster Nachtrag

* **„Der ordnungsdichte Kern hängt an der Algebra der Einschrittrelation".**
  Der Schluß des einundzwanzigsten Laufs, und er war so voreilig wie „(H) ist
  die Grenze der Methode" im zwanzigsten. Er las aus „Theorem 12 setzt an
  Nachbaratomen an" ein Hindernis, statt zu prüfen, **wofür** die Nachbarn
  dort stehen: für die Abelsche Summation, und die ist eine
  Stieltjes-Produktregel, die keine Nachbarn kennt. Zum dritten Mal dieselbe
  Lehre — eine Prämisse, die aus der Rechnung stammt statt aus dem
  Beweisbedarf (siebzehnter Lauf: Kompaktheit; zwanzigster Lauf: (H)).
* **Die Suche nach einem Punkt zwischen Atom und Nachfolger.** Zehn Läufe
  lang galt die Bemerkung des zwölften Laufs, der Mechanismus brauche ein $t$
  echt zwischen dem Atom und seinem Nachfolger, als die Stelle, an der die
  Ordnungsdichte beißt. Sie beschreibt eine bestimmte einzeilige Herleitung,
  nicht das System: Probe (E) zeigt, daß schon die lückenfreie Teilmenge der
  Bedingungen die Diagonale erzwingt, auf jeder endlichen Kette bis $n=7$.
* **Der Zweikoordinaten-Transform als Quelle neuer Information.** Die
  Doppeltransformation $D(c,d)$, $E(c,d)$ des Antisymmetrieschritts sieht nach
  einem reichen System aus; ihr ganzer Ertrag steckt in der Diagonale $d=c$,
  wo beide Doppelsummen aus Antisymmetrie verschwinden. Die Nebendiagonale
  gibt nur die Teilerdifferenz
  $E(c,d)=-[V_0(c)-V_0(d)][Q(c)-Q(d)]/(c-d)$ zurück, also nichts über (2)
  hinaus.
