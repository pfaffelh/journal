# Die mengen-indizierte Lévy-Literatur, eingeordnet

*Lauf vom 2026-09-02. Teil (a) der Aufgabe vom 2026-09-01: die Theorie der
mengen-indizierten Lévy-Prozesse (Herbin–Merzbach) am Text lesen und gegen
\eqref{T0}–\eqref{T4} + Uhr stellen; die vier Fragen der Aufgabe beantworten.*

**Quellen dieses Berichts, und wie sie geprüft sind.** Der Haupttext ist
E. Herbin, E. Merzbach, *The set-indexed Lévy process: Stationarity, Markov and
sample paths properties*, Stochastic Process. Appl. **123** (2013), 1638–1670,
arXiv:1108.0873 — gelesen über die ar5iv-HTML-Fassung des arXiv-Texts, in fünf
gezielten Auszügen (Definition 2.1 vollständig, Definition 3.1 vollständig,
Satz 4.3, Definitionen 5.1/5.2 und Satz 5.3 samt umgebender Bemerkung,
Abschnitt 6). Pedersen–Sato (unten, Frage 4) ist als PDF geladen und die
ersten vier Seiten sind **direkt gelesen**, nicht über ein Zwischenmodell.
Bass–Pyke und Adler–Feigin sind nur bibliographisch verifiziert (Websuche);
ihre Inhalte werden hier nicht behauptet, nur ihre Rolle als Vorläufer für
$\R^N$-Rechtecke, die Herbin–Merzbach selbst nennen. Wo unten eine Folgerung
**unsere** Schlussfolgerung ist und nicht im Papier steht, ist das markiert.

## 0. Ihr Rahmen, am Text

**Die Indexklasse** (Definition 2.1). $\mathcal T$ ist ein lokal kompakter
vollständiger separabler metrischer Raum mit Radonmaß $m$; die *indexing
collection* $\mathcal A$ ist eine Klasse kompakter zusammenhängender Teilmengen
mit fünf Bedingungen:

1. $\emptyset\in\mathcal A$, $A^\circ\ne A$ für $A\notin\{\emptyset,\mathcal T\}$,
   und es gibt eine wachsende Folge $(B_n)$ in $\mathcal A(u)$ mit
   $\mathcal T=\bigcup_n B_n^\circ$ (σ-Ausschöpfung).
2. $\mathcal A$ ist unter **beliebigen Durchschnitten** abgeschlossen, und
   nichtleere $A,B\in\mathcal A$ haben nichtleeren Durchschnitt.
3. $\sigma(\mathcal A)=\mathcal B(\mathcal T)$, die Borelmengen.
4. *Separability from above*: es gibt wachsende **endliche** Teilklassen
   $\mathcal A_n$ (unter Durchschnitten abgeschlossen) und Abbildungen
   $g_n:\mathcal A\to\mathcal A_n(u)\cup\{\mathcal T\}$, die beliebige
   Durchschnitte und endliche Vereinigungen erhalten, mit
   $A\subseteq(g_n(A))^\circ$, $g_n(A)\subseteq g_m(A)$ für $n\ge m$,
   $A=\bigcap_n g_n(A)$, $g_n(A)\cap A'\in\mathcal A$, $g_n(\emptyset)=\emptyset$.
5. Jeder abzählbare Durchschnitt von Mengen aus $\mathcal A(u)$ ist Abschluss
   einer abzählbaren Vereinigung von Mengen aus $\mathcal A$.

Dazu $\mathcal A(u)$ = endliche Vereinigungen,
$\mathcal C=\{U_0\setminus\bigcup_{i=1}^nU_i:U_i\in\mathcal A\}$,
$\mathcal C_0=\{U\setminus V:U,V\in\mathcal A\}$, und
$\emptyset'=\bigcap_{U\in\mathcal A\setminus\{\emptyset\}}U$ mit $m(\emptyset')=0$.

**Der Prozess** (Definition 3.1). $X$ ist ein set-indexed Lévy process, wenn
(1) $X_{\emptyset'}=0$ f.s.; (2) für paarweise disjunkte
$C_1,\dots,C_n\in\mathcal C$ die Zuwächse $\Delta X_{C_1},\dots,\Delta X_{C_n}$
unabhängig sind; (3) $X$ *$m$-stationäre $\mathcal C_0$-Zuwächse* hat: für alle
$n$, alle $V\in\mathcal A$ und alle **wachsenden** Folgen $(U_i)$, $(A_i)$ in
$\mathcal A$ gilt
$$[\forall i:\ m(U_i\setminus V)=m(A_i)]\ \Longrightarrow\
(\Delta X_{U_1\setminus V},\dots,\Delta X_{U_n\setminus V})
\overset{d}{=}(\Delta X_{A_1},\dots,\Delta X_{A_n});$$
(4) $X$ stochastisch stetig ist längs monotoner Approximationen: aus
$\overline{\bigcup_n\bigcap_{k\ge n}U_k}=\overline{\bigcap_n\bigcup_{k\ge n}U_k}=A\in\mathcal A$
folgt $X_{U_n}\to X_A$ nach Wahrscheinlichkeit.

**Existenz** (Satz 4.3(iii)): zu jeder unendlich teilbaren
Wahrscheinlichkeitsverteilung $\mu$ auf $\R$ existiert ein set-indexed Lévy
process mit $P_{X_U}=\mu^{m(U)}$ für alle $U\in\mathcal A$ — die
Lévy-Chintschin-Schicht, mit $m(U)$ als Exponent.

**Flows** (Definitionen 5.1/5.2, Satz 5.3). Ein *elementary flow* ist eine
stetige wachsende Abbildung $f:[a,b]\to\mathcal A$; ein *simple flow* eine
stetige Abbildung $f:[a,b]\to\mathcal A(u)$, die stückweise aus elementaren
Flows $f_i$ durch $f(s)=f_i(s)\cup\bigcup_{j<i}f_j(t_j)$ zusammengesetzt ist.
Die *$m$-standard projection* ist $X^{f,m}_t=X_{f\circ\theta^{-1}(t)}$ mit
$\theta:t\mapsto m[f(t)]$. Satz 5.3: (i) die Projektion eines set-indexed Lévy
process längs eines elementaren Flows mit $f(0)=\emptyset'$ ist ein
gewöhnlicher Lévy-Prozess; (ii) für die **Umkehrung** (Charakterisierung)
braucht man die Unabhängigkeit der Zuwächse aller Projektionen längs
**simple** flows; Stationarität längs elementarer Flows genügt für die
Stationaritätshälfte. Das Papier sagt selbst: „At first glance, the notion of
simple flow may seem artificial and unnecessary but the embedding in
$\mathcal A(u)$ is the key point to get a characterization of distributions".

**Markov** (Abschnitt 6). Übergangssystem $\mathcal Q=\{Q_{U,V}\}$ indiziert
durch **Paare** $U\subseteq V$ in $\mathcal A(u)$; räumlich homogen heißt
$Q_{U,V}(x,B)=Q_{U,V}(0,B-x)$, *$m$-homogen* heißt: $Q_{U,V}$ hängt nur von
$m(V\setminus U)$ ab. Satz 6.6: ein set-indexed Lévy process ist
$\mathcal Q$-Markov mit räumlich homogenem, $m$-homogenem Übergangssystem.

## 1. Ihre Axiomatik gegen \eqref{T0}–\eqref{T4} + Uhr

Das Wörterbuch: ihr Grundraum $\mathcal T$ hat bei uns kein Gegenstück (wir
haben keinen Raum, nur den Index); ihre Klasse $\mathcal A$ entspricht unseren
Abwärtsmengen $\{\T_{\le t}\}$ bzw. $\{\T_{<t}\}$; ihr $U\setminus V$ ist
unser Intervall \eqref{eq:clockinterval}; ihr $m$ ist unsere Uhr $q$; ihre
$m$-Stationarität ist unsere Verschiebungsinvarianz.

| Ihr Axiom | Unser Gegenstück | Befund |
|---|---|---|
| (1) $\sigma$-Ausschöpfung, nichtleeres Inneres | keines | rein topologisch; wir brauchen es nicht, weil wir keine Pfadregularität aus der Indexklasse ziehen — die liegt bei uns in \eqref{T2b}/\eqref{T3} und §\ref{sec:cadlag} |
| (2) $\cap$-Abschluss (unterer Halbverband) | \eqref{T1} | $\T_{\le s}\cap\T_{\le t}=\T_{\le s\wedge t}$ **braucht Meets**. Unser Aufbau kommt ohne aus: der Kompensator läuft immer über die Intervalle *einer* Kette $s\le t$, nie über Durchschnitte. Wir sind hier echt schwächer (\eqref{T0} genügt), und `rem:fddnochain` zeigt den Preis auf der anderen Seite: die Hypothese von `prop:fddchar` muss über beliebige endliche Teilmengen quantifizieren |
| (3) $\sigma(\mathcal A)=\mathcal B$ | Definition~\ref{def:clock}: Abwärtsmengen messbar | wir verlangen nur Messbarkeit der Abwärtsmengen in einem frei wählbaren $\mathcal T$; keine Topologie. Echt schwächer |
| (4) separability from above | \eqref{T2b}, und \eqref{T1p} | die auffälligste Entsprechung: endliche, $\cap$-abgeschlossene Diskretisierungen, die von oben approximieren — das ist wörtlich die Rolle, die die abzählbar dichte Menge $D$ mit Rechtsapproximation in \eqref{T2b} spielt, und \EK{} §2.8 (\eqref{T1p}: „order intervals separable from above") ist der gemeinsame Vorfahr. `rem:ekindex` behandelt das schon; die mengen-indizierte Theorie ist der ausgebaute Zweig genau dieser Hypothese |
| (5) abzählbare Durchschnitte aus $\mathcal A(u)$ | keines | technisch-topologisch (für Pfadeigenschaften); kein Bedarf bei uns |
| Radonmaß $m$ | Uhr $q$, $q(\T_{\le t})<\infty$ | unsere Uhr ist schwächer: kein Radon, keine Topologie, nur Endlichkeit auf Abwärtsmengen. Und **allgemeiner**: $m$ tritt bei ihnen nur stationär auf ($P_{X_U}=\mu^{m(U)}$); unsere Uhr trägt auch nicht-stationäre Kompensatoren |
| $m$-Stationarität (Def. 3.1(3)) | Verschiebungsinvarianz in Definition~\ref{def:clock} | strukturell verschieden, und das ist der interessanteste Punkt: ihre Stationarität ist über **Gleichheit von $m$-Massen** definiert und braucht *keinerlei algebraische Struktur* auf dem Index — unsere braucht \eqref{T4}. Dafür ist ihre nur eine Verteilungsaussage über den Prozess, unsere eine Aussage über die Uhr allein |

**Was wir gewinnen.** Unsere Voraussetzungsfläche ist auf der Indexseite echt
kleiner: \eqref{T0} + Uhr gegen lokal kompakter polnischer Raum + fünf Axiome +
Radonmaß. Der Grund ist ehrlich benannt: wir beweisen keine
Existenz- und keine Pfadsätze aus der Indexstruktur — `prop:fddchar`,
Eindeutigkeit und Dualität sind Aussagen *über* gegebene Prozesse. Wo das
Manuskript Pfade baut (§\ref{sec:cadlag}), steht \eqref{T2b}, und das ist
genau die Achse ihres Axioms (4).

**Was wir verlieren.** Ihre Sätze 4.3 (Existenz zu jedem unendlich teilbaren
$\mu$, $P_{X_U}=\mu^{m(U)}$), die Markov-Theorie (Abschnitt 6) und die
Lévy–Itô-Zerlegung (Abschnitt 7) haben bei uns kein Gegenstück und sind mit
\eqref{T0}–\eqref{T4} allein auch nicht erreichbar — sie hängen an (1), (4),
(5). Das ist konsistent mit der Arbeitsteilung des Manuskripts: Existenz kommt
dort aus \EK{} auf \eqref{T3}.

## 2. Dualität und bivariate Zuwachsdarstellungen: Negativbefund

Die eigentliche Frage der Aufgabe, und die Antwort ist ein klares **Nein**.
Im ganzen Papier kommt weder „duality"/„dual" vor, noch eine bivariate
Funktion $\Phi(s,t)$ zweier Indexargumente, noch ein Vergleich
$\Phi(t,0)$ gegen $\Phi(0,t)$, noch eine Zuwachsdarstellung mit **gemeinsamer**
Dichte $\gamma$ in beiden Koordinaten, noch ein Martingalproblem oder ein
Generator (die ar5iv-Suche über den Volltext war ausdrücklich darauf
angesetzt; auch die Markov-Sektion formuliert nur Übergangssysteme). Das
nächstliegende Objekt ist das Übergangssystem $Q_{U,V}$ — bivariat im Index,
mit $m$-Homogenität über $m(V\setminus U)$ —, aber das ist ein
Übergangskern in der *Zeit*richtung, keine Darstellung
\eqref{eq:incrementrep} mit geteiltem $\gamma$, und es wird nirgends gegen
seine Spiegelung $Q_{V,U}$ gehalten. Auch Pedersen–Sato (unten) enthält
nichts dergleichen; „dual cone" dort ist konvexe Geometrie, nicht unsere
Dualität.

Für das Manuskript heißt das: die bivariate Zuwachsdarstellung
\eqref{eq:incrementrep} mit gemeinsamem $\gamma$ und die Frage, welche Uhren
Dualität tragen (§\ref{ssec:antidiag}), haben in der mengen-indizierten
Lévy-Literatur **kein Vorbild**. Der Negativbefund ist belastbar für
Herbin–Merzbach 2013 und Pedersen–Sato 2004; für die Bücher (Ivanoff–Merzbach
2000) ist er plausibel, aber nicht am Text geprüft.

## 3. Die Flow-Projektion und der ordnungsdichte Fall

Die $m$-standard projection $X^{f,m}_t=X_{f\circ\theta^{-1}(t)}$,
$\theta(t)=m[f(t)]$, ist strukturell **identisch** mit der Zeittransformation
von `cor:atomless`: $f$ ist bei uns $t\mapsto\T_{<t}$, $\theta$ ist
$Q(s)=q(\T_{<s})$, und $\theta^{-1}$ ist $Q^{\leftarrow}$. Drei Beobachtungen:

1. **Sie setzt Invertierbarkeit von $\theta$ voraus.** Definition 5.2 schreibt
   $\theta^{-1}$ hin; das Papier behandelt den Fall eines springenden $\theta$
   — ein Atom von $m$ längs des Flows — **nicht**. Mehr noch (das ist
   *unsere* Folgerung, nicht ihr Text): hätte $m$ ein Atom, das eine monotone
   Approximation $U_n\downarrow A$ mit $m(U_n\setminus A)\to m(\{x\})>0$
   sieht, so wäre $\Delta X$ über den Annuli nach Satz 4.3(iii) verteilt wie
   $\mu^{m(U_n\setminus A)}\to\mu^{m(\{x\})}\ne\delta_0$, im Widerspruch zur
   stochastischen Stetigkeit, Definition 3.1(4). Ihre Prozessklasse lebt also
   für nichtdegeneriertes $\mu$ ganz auf der **atomlosen** Seite; Atome —
   unsere festen Sprungzeiten, \CPS{} §5.3 — sind per Axiom ausgeschlossen,
   nicht behandelt.
2. **Elementare Flows genügen nicht, und das ist `rem:fddnochain`.** Ihr
   eigener Kommentar zu Satz 5.3 — „the embedding in $\mathcal A(u)$ is the
   key point" — sagt: Ketten in $\mathcal A$ (elementare Flows) erreichen die
   Unabhängigkeitsstruktur nicht, erst endliche *Vereinigungen* tun es. Das
   ist dieselbe Geometrie wie bei uns: Produkte über beliebige endliche
   Teilmengen von $\T_{\le s}$ statt Ketten. Die Aufgabenstellung hatte diese
   Entsprechung vermutet; sie stimmt, und sie ist jetzt am Text belegt.
3. **Für Task 23 gibt die Projektion nichts Neues her.** Sie *ist* der
   Zeitwechsel, den `cor:atomless` schon ausführt, und sie endet aus
   demselben strukturellen Grund an den Atomen, den `rem:atomsnotchange`
   benennt (eine Darstellung über die Lücke hinweg setzt die Konklusion
   voraus). Der ordnungsdichte rein atomare Fall hat in dieser Literatur kein
   Gegenstück — er ist dort durch Definition 3.1(4) wegdefiniert. Die Suche
   des elften bis vierzehnten Laufs nach einem Beweis muss also ohne Vorbild
   aus dieser Richtung auskommen; das ist ein Negativbefund, aber er schließt
   eine Tür, an der vier Läufe vorbeigelaufen sind, ohne zu wissen, ob
   dahinter etwas liegt.

## 4. Weitere Literatur über allgemeine Indexmengen

* **Pedersen–Sato, cone-parameter Lévy processes** — J. Pedersen, K. Sato,
  *Relations between cone-parameter Lévy processes and convolution
  semigroups*, J. Math. Soc. Japan **56** (2004), 541–559. **Direkt am PDF
  gelesen** (S. 541–544). Das ist die Arbeit, die einer Präordnung am
  nächsten liegt: Index ist ein Kegel $K\subset\R^M$ (abgeschlossen, konvex,
  keine Gerade durch 0), Ordnung $s\le_Kt:\iff t-s\in K$ — das ist wörtlich
  eine kanzellative geordnete kommutative Halbgruppe mit existierender
  Differenz, unser \eqref{T0}+\eqref{T4}. Stationär unabhängige Zuwächse sind
  längs $K$-wachsender **Folgen** definiert (nicht über eine Mengenklasse),
  und $K$-càdlàg wird über $K$-monotone Folgen erklärt (Definition 2.3) —
  auch das eine Präordnungs-, keine Mengenklassen-Formulierung. Die
  Hauptsätze sind **negativ** in der Richtung, die bei uns `rem:chainonly`
  entspricht: jeder $K$-Lévy-Prozess induziert eine
  $K$-Faltungshalbgruppe $\mu_{s+t}=\mu_s*\mu_t$, aber die Umkehrung gilt
  nicht — auf $K=S_d^+$ (nichtnegativ definite Matrizen, $d\ge2$) gibt es
  **keine** Brownsche Bewegung ($\mu_s=N_d(0,s)$ ist nicht generativ), und
  generativ ist eine Halbgruppe genau unter einer von drei Bedingungen:
  $d=1$, rein nicht-Gaußsch, oder $K\cong\R_+^N$; selbst dann ist das Gesetz
  des Prozesses i.A. nicht eindeutig. Moral für uns: schon auf dem
  ordnungstheoretisch gutartigsten nichtlinearen Index (\eqref{T4}, sogar
  Verband) bricht die Brücke Halbgruppe$\to$Prozess — dieselbe Sorte
  Hindernis, die `rem:chainonly` auf der Eindeutigkeitsseite markiert.
* **Rajput–Rosiński, unabhängig gestreute Zufallsmaße** — B. S. Rajput,
  J. Rosiński, *Spectral representations of infinitely divisible processes*,
  Probab. Theory Related Fields **82** (1989), 451–487 (bibliographisch
  verifiziert, Inhalt nicht am Text geprüft). Der maßtheoretische Zweig:
  Index ist ein δ-Ring, gar keine Ordnung; „Zuwächse" sind Werte auf
  disjunkten Mengen, Stationarität kommt nicht vor. Das ist die Uhr-zuerst-
  Sicht — am nächsten an unserer Uhr ohne Verschiebungsinvarianz — und der
  Rahmen, in dem „Lévy-Basen" (Barndorff-Nielsen) leben. Falls je eine
  Existenztheorie für unsere Kompensatoren auf \eqref{T0} gebaut werden soll,
  ist das der Anschlusspunkt, nicht Herbin–Merzbach.
* **Ivanoff–Merzbach, mengen-indizierte Martingale** — G. Ivanoff,
  E. Merzbach, *Set-Indexed Martingales*, Chapman & Hall/CRC, 2000
  (bibliographisch bekannt aus Herbin–Merzbach; nicht am Text geprüft). Die
  Martingalseite derselben Axiomatik; relevant, falls die Frage von
  `rem:ekindex` — starke Markoveigenschaft auf echt gerichtetem Index — je
  wieder aufgenommen wird.
* **Vorläufer für $\R^N$-Rechtecke:** R. F. Bass, R. Pyke, *The existence of
  set-indexed Lévy processes*, Z. Wahrsch. Verw. Gebiete **66** (1984),
  157–172; R. J. Adler, P. D. Feigin, *On the cadlaguity of random measures*,
  Ann. Probab. **12** (1984). Beide bibliographisch verifiziert; ihre Rolle
  (Definitionen auf Rechtecken, Pfadregularität) nach Herbin–Merzbachs
  eigener Einleitung.

## 5. Vorschlag für eine Manuskriptbemerkung *(Vorschlag, nicht eingetragen)*

Ort: hinter `rem:haarrole` oder als letzter Punkt von
Example~\ref{ex:clocks}' Umgebung in §2; sie gehört dorthin, wo Uhr und
Verschiebungsinvarianz diskutiert werden. Text (Manuskriptsprache Englisch):

> \begin{remark}[Set-indexed L\'evy processes]
>   \label{rem:setindexed}
>   The pair (index, clock) of Definition~\ref{def:clock} has a developed
>   relative in the theory of \emph{set-indexed L\'evy processes}
>   \cite{HM13}, with precursors on rectangles in $\R^N$ \cite{BP84, AF84}
>   and a martingale theory over the same index classes \cite{IM00}.  There,
>   the index is a class $\mathcal{A}$ of compact connected subsets of a
>   metric space, closed under intersections --- a lower semilattice, our
>   \eqref{T1} --- and increments run over the differences
>   $\mathcal{C}_0 = \{U \setminus V\}$; our predictable interval
>   $[s,t) = \T_{<t} \setminus \T_{<s}$ is such a difference, with
>   $\mathcal{A}$ the down-sets.  Their Radon measure $m$ plays the role of
>   the clock, with two instructive differences.  First, stationarity is
>   defined through equality of $m$-masses of increments and thus needs no
>   algebraic structure on the index at all, whereas our shift invariance
>   needs \eqref{T4}; in exchange, their $m$ only ever appears stationarily
>   ($X_U \sim \mu^{m(U)}$), whereas a clock also carries non-stationary
>   compensators.  Second, their processes are stochastically continuous by
>   definition, which for a nondegenerate law forces $m$ atomless: fixed
>   times of discontinuity --- our atoms, Example~\ref{ex:clocks}(iii) ---
>   are excluded by axiom, not treated.  Their reduction to one parameter,
>   the projection along a flow $f$ with the time change
>   $\theta(t) = m[f(t)]$, is the change of variables of
>   Corollary~\ref{cor:atomless}; and their characterization needs
>   \emph{simple} flows, with values among finite unions $\mathcal{A}(u)$,
>   rather than elementary ones with values in $\mathcal{A}$ --- the same
>   geometry as Remark~\ref{rem:fddnochain}, where chains do not reach the
>   generators either.  Neither there nor in the cone-parameter theory of
>   \cite{PS04} --- whose index, a cone $K$ with $s \leq t \iff t-s \in K$,
>   is exactly a \eqref{T0}+\eqref{T4} index --- does a bivariate increment
>   representation with a common density, or any duality in the sense of
>   Section~\ref{sec:duality}, appear.
> \end{remark}

Bibliographieeinträge im Stil der `thebibliography` des Manuskripts:

```latex
\bibitem{AF84}
R.~J.~Adler and P.~D.~Feigin.
\newblock On the cadlaguity of random measures.
\newblock \emph{Ann.\ Probab.} \textbf{12} (1984), 615--630.

\bibitem{BP84}
R.~F.~Bass and R.~Pyke.
\newblock The existence of set-indexed L\'evy processes.
\newblock \emph{Z.\ Wahrsch.\ Verw.\ Gebiete} \textbf{66} (1984), 157--172.

\bibitem{HM13}
E.~Herbin and E.~Merzbach.
\newblock The set-indexed L\'evy process: Stationarity, Markov and sample
  paths properties.
\newblock \emph{Stochastic Process.\ Appl.} \textbf{123} (2013), 1638--1670.

\bibitem{IM00}
G.~Ivanoff and E.~Merzbach.
\newblock \emph{Set-Indexed Martingales}.
\newblock Chapman \& Hall/CRC, Boca Raton, 2000.

\bibitem{PS04}
J.~Pedersen and K.~Sato.
\newblock Relations between cone-parameter L\'evy processes and convolution
  semigroups.
\newblock \emph{J.\ Math.\ Soc.\ Japan} \textbf{56} (2004), 541--559.
```

*Vor dem Eintragen zu prüfen (vom Nutzer oder einem Lauf mit Bibliothekszugang):
die Seitenzahlen von Adler–Feigin (615–630 stammen aus einer Websuche zweiter
Hand, nicht vom Verlag) und der Erscheinungsort des Ivanoff–Merzbach-Buchs.*
