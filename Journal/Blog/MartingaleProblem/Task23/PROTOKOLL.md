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

* **Atome, die keine Kette bilden.** `prop:atomicdual` verlangt, dass die Atome
  unter $t^*$ paarweise vergleichbar sind; unter \eqref{T2a} ist das
  automatisch, unter \eqref{T0} nicht. Das Manuskript behauptete bisher mehr
  („uses no order structure beyond a preorder", gestützt auf die symbolische
  Prüfung von $\{0,1,2\}^2$); die Statustabelle trennt jetzt beide Zeilen. Der
  kleinste Fall geht von Hand: $\T=\{0,a,b,t^*\}$ mit $a,b$ unvergleichbar,
  Atome bei beiden. Die drei Relationen längs $[0,t^*)$, $[a,t^*)$ und $[b,t^*)$
  geben $\Phi(t^*,t)-\Phi(0,t)$ dreimal, einmal als $m_a\gamma(a,t)$, einmal als
  $m_b\gamma(b,t)$ und einmal als deren Summe; also sind beide Null und die
  Behauptung ist trivial. Ein allgemeines Argument fehlt.

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
