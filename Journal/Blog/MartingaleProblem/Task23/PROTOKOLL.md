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
