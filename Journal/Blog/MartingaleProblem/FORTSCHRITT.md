# Fortschritt

Weg zum Manuskript `MartingaleProblem.tex`. Hier stehen die getroffenen
Entscheidungen mit Begründung, das Prüfprotokoll gegen die Quellen und der
chronologische Verlauf. Der Plan für das weitere Vorgehen steht in `PLAN.md`.

---

## Stand

**2026-08-25** — Manuskript v33, 98 Seiten, kompiliert ohne undefinierte oder
doppelte Referenzen, 8 Overfull-Boxen (max. 7,7 pt).

| § | Inhalt | Quelle |
|---|---|---|
| 1 | Wahl des Settings; Allgemeinheit (Index, Uhr, Zustandsraum, lokal); **1.4 was nicht verallgemeinert wurde** | — |
| 2 | Preliminaries; Zeitindex-Bündel (T0)–(T4), Uhr, Zustandsraum (E0)–(E3) + **fibriert**; drei Bündeltabellen | EK86 Kap. 1–3 |
| 3 | Abstrakter (lokaler) MP; Markovscher MP für $A$ | CPS23 §3.1, EK86 §4.3 |
| 4 | Càdlàg-Modifikation, abstrakt und Markovsch | EK86 Thm. 4.3.6 |
| 5 | Eindeutigkeit **ohne** Markov-Struktur; Markov-Schicht (Shift-Systeme, Pfad-Lift); lokale Theorie; lokale Eindeutigkeit | EK86 Thm. 4.4.2, KA21 §32, JS03 III.2 |
| 6 | Dualität: Kettenidentität, Rektifikation der Uhr, **jede Uhr lässt Dualität zu** | EK86 Lem. 4.4.10/Thm. 4.4.11 |
| 7 | Existenz, **fünf** Wege: Halbgruppe, **Dualer** (DGP24, mit Hawkes als Testobjekt), Sprungprozesse, SDEs, Konvergenz | EK86, CPS23, DGP24, JR16 |
| 8/9 | Formalisierungsnotizen, Mathlib-Bestandsaufnahme, Design-Entscheidungen | — |

**Erledigt:** Tasks 1, 2, 9–20 sowie Q1–Q3, Q5–Q8. Task 17 (Konsistenz-Durchgang
mit Prüfung jedes Arguments) ist abgeschlossen und hat acht mathematische Fehler
gefunden — siehe D39, D40, D43, D44, D48.

**Offen:** Tasks 3–8 (Lean-Formalisierung; auf Entscheidung des Nutzers pausiert,
„erst muss die Theorie stehen"), Task 19 (historischer Prozess allgemein — am
Hawkes-Beispiel durchgeführt, für Genealogien offen), Task 21 (pfadabhängige
Uhr), Task 22 (Submartingalprobleme), Q4 (Halbgruppen-/Feller-Weg, bewusst
ruhend).

---

## Entscheidungen

### D1 — Setting: Hybrid aus CPS23 und EK86  *(2026-08-24)*

**Entscheidung.** Definitionsschicht nach CPS23 Def. 3.2 (Familie $\mathbb{X}$ von
Testprozessen, (lokale) Martingale); Arbeitsschicht nach EK86 (Markovscher MP für
einen Operator $A$, als Spezialfall $\mathbb{X} = \mathbb{X}_A(X)$).

**Begründung.** Drei der vier Zielresultate — EK86 4.3.6, 4.4.2, 4.4.11 — haben in
CPS23 *kein* Gegenstück. CPS23 behandelt ausschließlich die Identifikation
schwacher Limiten und enthält keinen Eindeutigkeitssatz, keine
Markov-Eigenschaft und keine Aussage zur Pfadregularität; diese sind Aussagen
über einen Operator und seinen Definitionsbereich und im CPS-Rahmen nicht
formulierbar. Umgekehrt ist CPS23 beim vierten Resultat (Existenz via Konvergenz)
echt allgemeiner. Reines CPS deckt den Plan also nicht ab, reines EK verschenkt
Allgemeinheit an genau einer Stelle.

**Verworfene Alternativen.** Rein EK86 (weniger allgemein bei §7, lokale MPs nur
als Nachtrag über EK86 §4.6). Rein CPS23 (deckt drei von vier Punkten nicht ab).

**Bestätigt vom Nutzer** am 2026-08-24.

**Korrektur der Begründung (2026-08-24, nach D11–D13).** Der Satz oben, diese
Resultate seien „Aussagen über einen Operator und seinen Definitionsbereich und
im CPS-Rahmen nicht formulierbar", ist **falsch** und durch D11, D12 und D13
widerlegt: alle drei sind im CPS-Rahmen formulierbar, und zwar besser als im
EK-Rahmen. Was stimmt, ist nur die schwächere Aussage: **CPS23 enthält sie
nicht.** Für Thm. 4.1 ist die Auslassung strukturell (deren Setting 3.1 setzt den
Pfadraum voraus), für §5 und §6 ist sie es nicht — CPS23 wollte schlicht etwas
anderes.

Die **Entscheidung** D1 bleibt davon unberührt, ihre Architektur aber nicht: das
Manuskript hat jetzt *drei* Schichten statt zwei — Definitionsschicht (CPS),
abstrakte Arbeitsschicht (ebenfalls CPS, mit Thm. 4.3, Thm. 5.5/5.7,
Lem. 6.1/Prop. 6.2), und Markovsche Schicht (EK) als Korollare. §1.2 des
Manuskripts ist entsprechend neu geschrieben und benennt den Irrtum ausdrücklich.
Der Grund, die EK-Schicht zu behalten, ist nicht mehr „die Sätze brauchen einen
Operator", sondern: die abstrakten Hypothesen sind die, die ein *Beweis* braucht,
der Operator ist der, den ein *Anwender* hat.

### D2 — Zustandsraum polnisch, Kompaktheitsbedingung statt lokaler Kompaktheit  *(2026-08-24)*

$E$ ist durchweg polnisch. EK86 formuliert Thm. 4.3.6 für separables $E$ und
Lem. 4.5.1 für vollständig separables; polnisch ist die gemeinsame Allgemeinheit,
es geht nichts verloren. $E$ ist **nicht** lokalkompakt — deshalb gibt es kein
$C_c(E)$ und kein Einpunkt-Kompaktifizierungsargument, und die Rolle der lokalen
Kompaktheit übernimmt überall die *compact containment condition*
(Def. 3.12 im Manuskript). Diese ist als eigene Definition isoliert, weil sie an
vier Stellen wiederkehrt.

### D3 — Lokale Martingalprobleme: pro Satz ehrlich abgegrenzt  *(2026-08-24)*

Der lokale MP wird in Def. 3.2 von Anfang an mitdefiniert, aber es wird bei jedem
Satz explizit gesagt, ob er lokalisiert:

* **Thm. 4.1** (càdlàg): **nein**. Lokalisierung braucht Stoppzeiten, diese
  brauchen eine rechtsstetige Filtration und in der Praxis Pfadregularität —
  genau das, was bewiesen wird. Das Argument wäre zirkulär. Ehrliche lokale
  Fassung nur mit deterministischer Lokalisierung bzw. via
  $A^K = \{(f,g) \in A: f,g \text{ beschränkt auf } K\}$ (Rem. 4.3).
* **Thm. 5.1** (Eindeutigkeit): nur über gestoppte MPs (Rem. 5.3), entsprechend
  EK86 §4.6.
* **Thm. 6.2** (Dualität): bereits für unbeschränkte $f,g,h$ formuliert, nichts zu
  ändern.
* **Thm. 7.3** (Konvergenz): liefert im Limes stets *echte* Martingale; lokale MPs
  entstehen durch Anwendung auf lokalisierte Testprozess-Familien (Rem. 7.4), so
  wie CPS23 es in ihrem §4.3 tun.

**Bestätigt vom Nutzer** am 2026-08-24.

### D4 — Sprache: Englisch  *(2026-08-24)*

Passt zu `PLAN.md`, zu den Quellen und zum Lean-/Mathlib-Umfeld. Diese Datei ist
bewusst deutsch — sie ist internes Protokoll, nicht Teil des Manuskripts.

### D5 — Kein Halbgruppen-Weg  *(2026-08-24)*

In v2 waren EK86 Thm. 4.4.1 (Markovprozess ist eindeutige Lösung des MP für
seinen Erzeuger) und Cor. 4.4.4 / Rem. 4.4.5 (Range-Bedingung, ohne dass
$\mathcal{D}(A)$ trennend sein muss) als §5.1 enthalten. **Auf Wunsch des Nutzers
wieder entfernt.**

Folge: Aus EK86 Kapitel 1 wird nur noch übernommen, was in §3 tatsächlich
gebraucht wird — Halbgruppe/Erzeuger (Def. 2.1), *dissipativ* (Def. 2.2, für
Prop. 3.10 = EK86 4.3.5) und der *volle Erzeuger* messbarer
Kontraktionshalbgruppen (Def. 2.3, Fact 2.4 = EK86 Prop. 1.5.1, für Rem. 3.11).
Nicht übernommen: Hille–Yosida, Cores, mehrwertige dissipative Operatoren,
Exponentialformel. Rem. 2.5 im Manuskript grenzt das explizit ab und sagt, wo es
hingehörte, falls es später doch gewünscht wird. Damit ruht das Manuskript wieder
auf EK86 Kap. 2 und 3 allein, wie in `PLAN.md` ursprünglich vorgesehen.

### D6 — Nummerierung in `PLAN.md`  *(2026-08-24)*

"Lemma 5.5.1, Remark 5.5.2" in `PLAN.md` ist **EK86 Lemma 4.5.1 / Remark 4.5.2**
(Kapitel 4, Abschnitt 5, S. 196f., im Buch gedruckt als "5.1 Lemma" / "5.2
Remark"). Kapitel 5 von EK86 hat nur fünf Abschnitte (§5.5 = "Notes", S. 305) und
enthält kein solches Resultat. Inhaltlich passt nur 4.5.1: "One of the simplest
ways of obtaining solutions is as weak limits of solutions of approximating
martingale problems."

### D7 — Thm. 4.1 braucht **kein** atomloses $q$; Konvention $(0,t]$  *(2026-08-24)*

**Frage (Q2).** `PLAN.md` hatte vermutet, der Beweis von Thm. 4.1 (EK86 4.3.6)
brauche ein atomloses Uhr-Maß, weil er die *Stetigkeit* von
$t\mapsto\int_0^t g(X_s)\,q(\mathrm{d}s)$ benutzt, und mit Atomen sei die Aussage
falsch, „weil $f(X_t)$ dann an den Atomen springt".

**Befund.** Die Vermutung ist falsch, und die Begründung enthält den Fehler:
Springen ist mit *càdlàg* gerade verträglich. Setze
$C_t=\int_{(0,t]} g(X_s)\,q(\mathrm{d}s)$ für ein lokalendliches Borelmaß $q$ auf
$[0,\infty)$ und $Y_t=f(X_t)-C_t$. Der Beweis geht Schritt für Schritt durch:

* **Schritt 1.** $C$ ist càdlàg: rechtsstetig wegen $q((t,s])\downarrow q(\emptyset)=0$
  für $s\downarrow t$ (Stetigkeit von oben, $q$ lokalendlich), linke Limiten wegen
  endlicher Variation, $|\Delta C_t|\le\lVert g\rVert\,q(\{t\})$. Fact 2.10
  (EK86 Prop. 2.2.9) liefert einseitige Limiten von $Y$ längs $\mathbb{Q}$ — die
  Regularisierung stellt *keine* Stetigkeitsforderung. Also hat auch
  $f_i(X)=Y+C$ einseitige Limiten längs $\mathbb{Q}$. Was der Schritt braucht, ist nicht
  Stetigkeit von $C$, sondern nur die Existenz einseitiger Limiten, und die gilt
  für jedes lokalendliche $q$. Die „Lipschitz-Stetigkeit" im Manuskript ist der
  Spezialfall $q=\lambda$.
* **Schritte 2, 3.** Kommen ohne Kompensator aus, unverändert.
* **Schritt 4.** $\bigl|E[\int_{(t,s]}g\,\mathrm{d}q\mid{}^{*}\mathcal{F}^X_t]\bigr|
  \le\lVert g\rVert\,q((t,s])\to0$ für $s\downarrow t$. Ein Atom **in** $t$ liegt
  in $(0,t]$, nicht in $(t,s]$ — es stört also gerade nicht. (2.cadlag3)
  unverändert.

**Konsequenz für Task 1c.** §4 und §7 können *ein* Setting teilen, Atome
eingeschlossen. Das war laut `PLAN.md` „the first thing to settle"; es ist damit
erledigt, und zwar zugunsten der allgemeineren Variante.

**Neue Frage Q8.** Der Befund hängt an der Konvention. Mit
$C_t=\int_{[0,t)}g\,\mathrm{d}q$ (prädiktabel, linksstetig) gilt stattdessen
$\int_{[t,s)}g\,\mathrm{d}q\to g(X_t)q(\{t\})$, also
$E[f(Y_t)\mid{}^{*}\mathcal{F}^X_t]=f(X_t)+g(X_t)q(\{t\})$: $Y$ ist dann **keine
Modifikation** von $X$ an den Atomen, sondern $X$ ist die càglàd- und $Y$ die
càdlàg-Version. Umgekehrt ist $[0,t)$ genau die Konvention, unter der
$q=$ Zählmaß auf $\mathbb{N}_0$ die Doob-Zerlegung $Y_n=f(X_n)-\sum_{k<n}g(X_k)$ und
$A=P-I$ liefert; unter $(0,t]$ lautet die Bedingung im diskreten Fall
$Pf-f=Pg$. **Beides zugleich geht nicht.** Bei atomlosem $q$ stimmen die
Konventionen überein, deshalb sieht man die Frage weder in EK86 noch in CPS23 §4.

### D8 — §7.2 hängt nicht am Skorokhod-Raum  *(2026-08-24)*

**Frage (Q7).** Braucht Thm. 7.3 (CPS23 Thm. 4.1) wirklich $D_E$ mit der
$J_1$-Topologie?

**Befund.** Nein. Am Aufsatz geprüft (CPS23 S. 15f., Thm. 3.14 und Cor. 3.17):
der Pfadraum $F$ geht dort *ausschließlich* ein über

1. $F$ polnisch und $X^n\to X$ schwach auf $F$,
2. Existenz einer determinierenden Menge $\mathcal{Z}^\circ$,
3. $P$-Stetigkeit von $Y^\circ_t$ und $Y^\circ_t Z^\circ_s$ an $X$,
4. gleichgradige Integrierbarkeit von $\{Y^\circ_r(X^n)\}$,

plus die Approximation (3.2). Weder càdlàg-Pfade noch $J_1$ noch eine
Markovstruktur werden benutzt; CPS23 nennt selbst $F=L^p_{\mathrm{loc}}$ als
Beispiel. Der Skorokhod-Raum tritt erst bei der **Instanziierung** auf, an genau
zwei Stellen: $\mathcal{B}(D_E)=\sigma(\pi_t)$ (EK86 Prop. 3.7.1) für die
determinierende Menge aus Bsp. 3.6(i), und die Stetigkeit der Auswertung
$\omega\mapsto\omega(t)$ in Pfaden ohne Sprung in $t$ — daher die Hypothese
„$\Gamma$ mit abzählbarem Komplement" in Thm. 7.3.

**Zeitindex.** Im Beweis von Thm. 3.14 geht die Struktur von $\mathbb{T}$ nur in
den *letzten* Schritt ein, die Ausdehnung von $s,t\in D$ auf beliebige $s<t$ über
$t_n\downarrow t$, $s_n\downarrow s$ mit $s_n<t_n$, Rechtsstetigkeit von $Y$ und
Vitali. Mit $D=\mathbb{T}$ ist dieser Schritt leer. Also: Thm. 3.14 gilt unter
**(T0)** (bloße Präordnung), und unter **(T2)** mit abzählbar dichtem $D$.

**Konsequenz.** Task 8 zerfällt in 8a (abstrakter Konvergenzsatz, klein, direkt
nach Task 5 machbar) und 8b (Skorokhod-Raum, das größte Einzelstück des Plans).
Der abstrakte Konvergenzsatz ist damit der billigste echte Satz im ganzen Plan
und nicht mehr, wie bisher geplant, der teuerste.

### D9 — Q1/Q6: maximal allgemein — und zwar mit einem Mathlib-`Measure`  *(2026-08-24)*

**Entscheidung des Nutzers.** Der Mehrparameterfall wird mitgetragen: (T1') als
Basisbündel für die Stoppzeitenschicht, und das Uhr-Datum so allgemein wie
möglich.

**Verschärfung beim Ausformulieren.** Die in `PLAN.md` §1b vorgeschlagene
*abstrakte additive Intervallfunktion* $q_{s,u}=q_{s,t}+q_{t,u}$ ist der falsche
Begriff, und der in der Frage genannte Preis („kein Mathlib-`Measure`, Fubini von
Hand") ist vermeidbar. Zwei Beobachtungen:

1. **Additivität allein trägt Prop. 3.6 nicht.** Der Beweis braucht Fubini,
   $E[\int_{(s,t]} g(X_u)\,q(\mathrm{d}u)\,Z] = \int_{(s,t]} E[g(X_u)Z]\,q(\mathrm{d}u)$,
   und dafür muss $q$ ein Maß sein. Eine bloß längs Ketten additive
   Intervallfunktion liefert das nicht — auf $[0,\infty)^d$ ist Kettenadditivität
   echt schwächer als $d$-Monotonie, und nur letztere gibt ein Maß auf Quadern.
2. **Umgekehrt braucht man für den Halbordnungsfall gar keine Intervallfunktion.**
   Es genügt ein Maß auf $\mathbb{T}$ selbst; die Intervalle entstehen als
   Differenz von Unterhalbmengen.

**Das Datum.** Ein messbarer Raum $(\mathbb{T},\mathcal{T})$ mit Präordnung $\le$,
so dass jede Unterhalbmenge $\mathbb{T}_{\le t} = \{u : u \le t\}$ messbar ist, ein
Basispunkt $0$, und ein Maß $q$ auf $(\mathbb{T},\mathcal{T})$ mit
$q(\mathbb{T}_{\le t}) < \infty$ für alle $t$ („lokalendlich längs der Ordnung").
Setze für $s \le t$
$$(s,t] \;:=\; \mathbb{T}_{\le t} \setminus \mathbb{T}_{\le s},
  \qquad C_t \;:=\; \int_{(0,t]} g(X_u)\, q(\mathrm{d}u) .$$

Die Additivität $(s,u] = (s,t] \uplus (t,u]$ für $s \le t \le u$ ist damit
**geschenkt** — sie folgt aus der Transitivität, nicht aus einer Zusatzannahme.
Gebraucht wird nur noch die gemeinsame Messbarkeit von
$(u,\omega) \mapsto X_u(\omega)$.

**Was das abdeckt.**

| $\mathbb{T}$ | $q$ | $\mathbb{T}_{\le t}$ | $C_t$ |
|---|---|---|---|
| $[0,\infty)$ | Lebesgue | $[0,t]$ | $\int_0^t g(X_u)\,\mathrm{d}u$ — der klassische Fall |
| $\mathbb{N}_0$ | Zählmaß | $\{0,\dots,n\}$ | $\sum_{k \le n} g(X_k)$ — diskrete Zeit |
| $[0,\infty)$ | mit Atomen | $[0,t]$ | feste Unstetigkeitsstellen, CPS23 §5.3 |
| $[0,\infty)^d$ | Lebesgue | Quader $[0,t]$ | Mehrparameter, EK86 Kap. 6 |

**Folge.** Q6 ist damit zugunsten *„Maß"* entschieden, ohne dass der
Halbordnungsfall verloren geht — die vermeintliche Alternative „abstraktes $q$
oder Maß" war keine. In Lean ist $q$ ein `MeasureTheory.Measure T`, und die
Fubini-Schritte sind `MeasureTheory.integral_integral_swap` statt Eigenbau.
`PLAN.md` §1b ist entsprechend zu korrigieren (Task 1b).

### D10 — Q8: Kompensator über $(0,t]$  *(2026-08-24)*

**Entscheidung des Nutzers.** $C_t = \int_{(0,t]} g\,\mathrm{d}q$, also
rechtsstetig.

**Begründung.** Testprozesse sind in CPS23 Setting 3.1 als rechtsstetig
vorausgesetzt, und Thm. 4.1 liefert unter dieser Konvention eine echte
*Modifikation* (D7). Der Preis ist der diskrete Fall: unter $(0,t]$ lautet die
Martingalbedingung für $Y_n = f(X_n) - \sum_{k \le n} g(X_k)$ nicht
$g = (P-I)f$, sondern $Pf - f = Pg$. Die Doob-Zerlegung ist also **nicht** der
Spezialfall $q = $ Zählmaß dieses Rahmens; wer sie will, muss $[0,t)$ nehmen und
auf Thm. 4.1 verzichten. Das ist im Manuskript an der Stelle von Def. 3.5 zu
vermerken, damit die Lücke nicht später als Fehler gelesen wird.

Passt zur Notation $(s,t] = \mathbb{T}_{\le t} \setminus \mathbb{T}_{\le s}$ aus D9:
$(0,t]$ ist dort die Unterhalbmenge von $t$ ohne die von $0$.

### D11 — Abstrakte Fassung von Thm. 4.1 (neu, nicht in der Literatur)  *(2026-08-24)*

**Auftrag des Nutzers.** „Suche bitte nach einer CPS-Verallgemeinerung von
Thm. 4.1."

**Befund zur Literatur.** Es gibt keine. CPS23 enthält *keinen*
Pfadregularitätssatz, und zwar aus einem strukturellen Grund, nicht aus Versehen:
CPS23 Setting 3.1 **setzt** einen polnischen Pfadraum $F$ und rechtsstetige
Testprozesse **voraus** — genau das, was ein Regularisierungssatz erst herstellen
muss. Eine Websuche nach einer abstrakten Fassung (Stichworte: abstract
martingale problem, càdlàg modification, test processes; sowie
Bhatt–Karandikar, Kurtz) hat nichts geliefert, was über EK86 4.3.6 hinausgeht.

**Also selbst formuliert.** Der Beweis von EK86 4.3.6 benutzt vom Operator $A$
*nichts*. Was er benutzt, ist ausschließlich: $f(X)$ zerfällt für hinreichend
viele $f$ in ein Martingal plus einen zeitlich regulären Rest. Das ist als
Hypothese formulierbar. Neu im Manuskript (§4.1):

**Def. 4.1 (regularisierende Klasse).** $\Phi \subset C_b(E)$ heißt
regularisierend für $(X,\mathbb{X})$, wenn es zu jedem $f \in \Phi$ ein
$Y^f \in \mathbb{X}$ und einen adaptierten Prozess $C^f$ gibt mit

* **(R1)** $f(X_t) = Y^f_t + C^f_t$ f.s. für alle $t$;
* **(R2)** f.s. hat $t \mapsto C^f_t$ längs $\mathbb{Q}$ überall einseitige Limiten;
* **(R3)** $C^f$ ist rechtsstetig in $L^1$: $E|C^f_s - C^f_t| \to 0$ für $s \downarrow t$.

**Thm. 4.2.** Ist $\Phi$ regularisierend, enthält $\Phi$ eine abzählbare
punktetrennende Teilmenge, ist $\Phi$ trennend, und erfüllt $X$ die
compact containment condition, so hat $X$ eine Modifikation mit Pfaden in $D_E$.

EK86 4.3.6 ist der Spezialfall $\Phi = \mathcal{D}(A)$,
$C^f_t = \int_0^t g(X_s)\mathrm{d}s$ (dann sind (R2), (R3) trivial, weil $C^f$
Lipschitz ist) — im Manuskript jetzt ein einzeiliges Korollar.

**Was das bringt.** Drei Hypothesen fallen weg, und es sind genau die drei, die
CPS23 stören würden:

1. **Kein Operator.** $C^f$ darf *pfadabhängig* sein. Der CPS23-Prototyp
   $C^f_t=\int_{(0,t]} g(s,L,X)\,q(\mathrm{d}s)$ mit Kontrollvariable $L$ erfüllt
   (R2) (endliche Variation) und (R3)
   ($E|C^f_s-C^f_t| \le \int_{(t,s]}E|g(u,L,X)|q(\mathrm{d}u) \to 0$ unter der
   Integrierbarkeitsbedingung, die CPS23 ohnehin stellen — (5.6) dort). In der
   Sprache eines Operators $A \subset C_b(E)\times B(E)$ ist das nicht sagbar.
2. **Atome sind harmlos.** (R2) verlangt einseitige Limiten, nicht Stetigkeit.
   Das ist D7 in abstrakter Form, und es zeigt, dass D7 kein Kunstgriff für den
   Spezialfall war, sondern die richtige Hypothese.
3. **Keine spezielle Filtration.** ${}^{*}\mathcal{F}^X$ spielt keine Rolle;
   $\mathbb{F}$ ist irgendeine Filtration, die $X$ adaptiert und die $Y^f$ zu
   Martingalen macht. ${}^{*}\mathcal{F}^X$ wird nur für Prop. 3.6 gebraucht.

**Was es nicht bringt.** Keine lokale Fassung — das Argument aus D3 ist
unberührt.

**Einordnung.** Thm. 4.2 ist der Satz, der eine Lösung *in* das CPS23-Setting
hineinträgt ($F = D_E$). Er ist der fehlende erste Schritt von deren Programm,
nicht eine Folgerung daraus. Für die Formalisierung ist er außerdem der
billigere: (R1)–(R3) sind drei Hypothesen über ein Prozesspaar, $\mathcal{D}(A)$
zöge Operator, Definitionsbereich und ${}^{*}\mathcal{F}^X$ mit herein.

### D12 — Abstrakte Fassung von Thm. 5.1 (Eindeutigkeit/Markov)  *(2026-08-24)*

**Befund zur Literatur.** CPS23 beweist keinen Eindeutigkeitssatz. Anders als bei
Thm. 4.1 (D11) ist das aber **kein struktureller Ausschluss**: die Aussage passt
in ihr Setting, sobald man die eine Zutat ergänzt, die eine Eindeutigkeits- von
einer Konvergenztheorie unterscheidet — eine Möglichkeit, das Martingalproblem
**neu zu starten**.

**Kernbeobachtung.** Der Beweis von EK86 4.4.2 sieht aus wie vier verschiedene
Argumente (Maßwechsel für die Markoveigenschaft; Variante davon im
Induktionsschritt; Stoppzeitversion in (b); Konstruktion aus $P_{X(\tau)}$ in
(c)). Es ist **ein** Argument, viermal angewandt:

> **Restart-Lemma.** $P \in \mathcal{M}(\mathbb{X}^\circ)$, $r$ fest,
> $Z \ge 0$ **$\mathcal{F}^\circ_r$-messbar** mit $E^P Z = 1$. Ist
> $\mathbb{X}^\circ$ shift-stabil und hat eine determinierende Menge, so ist
> $(Z\cdot P)\circ\theta_r^{-1} \in \mathcal{M}(\mathbb{X}^\circ)$.

Die vier Fälle sind $Z=\mathbf{1}_{F_0}$, $Z=E[\mathbf{1}_{F_0}\mid X_r]$,
$Z=\prod_k f_k(\pi_{t_k})$ und $Z=\mathbf{1}_{F_0}$ an einer Stoppzeit. Die
einzige je benutzte Eigenschaft von $Z$ ist Nichtnegativität plus
$\mathcal{F}^\circ_r$-Messbarkeit. Dass $Z_2=E[\mathbf{1}_{F_0}\mid X_r]$ in
dieses Schema passt, ist die Rechnung
$E[\mathbf{1}_{F_0}E[\mathbf{1}_B\mid\sigma(X_r)]] = E[Z_2\mathbf{1}_B]$ —
EK86 schreibt $P_2$ als iterierte bedingte Erwartung und verdeckt damit, dass es
schlicht ein Dichtewechsel ist.

**Was der Beweis wirklich benutzt.** Nur zwei Dinge, beide als Hypothese
formulierbar:

* **Shift-Stabilität** (Def. 5.4 im Manuskript): zu $\hat Y^\circ$ und $r$ gibt
  es $Y^\circ \in \mathbb{X}^\circ$ und $\mathcal{F}^\circ_r$-messbares $\kappa$
  mit $\hat Y^\circ_t\circ\theta_r = Y^\circ_{r+t}-Y^\circ_r+\kappa$.
* **Determinierende Menge** (CPS23 Def. 3.5) — genau die Rolle, die bei EK86
  Prop. 3.6 spielt. Damit ist auch geklärt, wie sich EK86s
  fdd-Charakterisierung zur CPS-Sprache verhält: es ist dieselbe Bedingung.

Alles übrige ist Turmeigenschaft.

**Antwort auf Q3.** Für $\mathbb{X}_A$ mit allgemeiner Uhr $q$ gilt
Shift-Stabilität **genau dann**, wenn $q$ shift-invariant ist:
$\int_{(0,t]}g(\omega(r+u))q(du)=\int_{(r,r+t]}g(\omega(v))q(dv)$ ist die
Invarianz. Damit ist die in Q3 vermutete Bedingung nicht mehr eine Randnotiz,
sondern *die* Hypothese des Satzes. Ohne sie löst der geshiftete Prozess ein
anderes MP und man bekommt einen zeitinhomogenen Markovprozess.

**Zusätzlich, ohne EK86-Gegenstück:** $\mathcal{M}(\mathbb{X}^\circ)$ ist konvex
und stabil unter messbaren Mischungen (Lem. 5.3), weil die Martingaleigenschaft
in $P$ **linear** ist. Das ist es, was den Übergang von $\delta_x$ zu allgemeinem
$\mu$ trägt — EK86 benutzt es in 4.4.2(c) und in Cor. 6.7 stillschweigend, und
Cor. 6.7 war laut Task 2.6 „the weakest point in §6".

**Ferner:** Thm. 5.5(a),(b) brauchen weder $C_b(E)$ noch $D_E$ — $F$ darf jeder
polnische Pfadraum sein, etwa $L^p_{\mathrm{loc}}$. Pfadregularität kommt erst in
Thm. 5.6 (starke Markoveigenschaft) und dort nur über Optional Sampling.

### D13 — §6: die Uhr muss ein Haarmaß sein (Kettenidentität)  *(2026-08-24)*

**Befund.** Auf der *probabilistischen* Seite gibt es in §6 nichts abzustreifen:
Thm. 6.x setzt bereits nur messbare Prozesse voraus, keine Pfadregularität,
keine Topologie auf $E_1,E_2$, keine Beschränktheit — das ist schon
CPS-Allgemeinheit. Verallgemeinerbar ist die **Uhr**. Und dort ist die Antwort
scharf und *anders* als in §4/§5.

**Kettenidentität (Lem. 6.1 neu).** Ohne jede Hypothese außer den beiden
Inkrementdarstellungen
$\Phi(s',t)-\Phi(s,t)=\int_{[s,s')}\gamma_1(r,t)q(dr)$,
$\Phi(s,t')-\Phi(s,t)=\int_{[t,t')}\gamma_2(s,r)q(dr)$
gilt für **jede** Kette $0=s_0\le\dots\le s_m=t$
$$\Phi(t,0)-\Phi(0,t)=\sum_k\Bigl[\int_{[s_k,s_{k+1})}\gamma_1(r,t-s_{k+1})q(dr)-\int_{[t-s_{k+1},t-s_k)}\gamma_2(s_k,r)q(dr)\Bigr].$$
Beweis: Teleskopieren längs der Antidiagonalen über die Ecke
$(s_k, t-s_{k+1})$. Zwei Zeilen.

**Konsequenz (Prop. 6.2).** Unter der Balancebedingung $\gamma_1=\gamma_2$ laufen
die beiden Integrale über einen Block und seinen **gespiegelten** Block. Also:

* $\mathbb{T}=\mathbb{N}_0$, $q$ Zählmaß: jeder Summand ist *exakt* null
  ($\gamma(k,t-k-1)-\gamma(k,t-k-1)$), ohne jede Regularität von $\gamma$.
  Duality gilt für alle $t$.
* $\mathbb{T}=\mathbb{R}_+$, $q$ Lebesgue: EK86 Lem. 4.4.10, für f.a. $t$.
* **Allgemeines $q$: falsch.** Gegenbeispiel $q=\delta_a$: für $t>a$ ist
  $\Phi(t,0)-\Phi(0,t)=\gamma(a,0)-\gamma(0,a)\ne0$. Das erste Integral sitzt auf
  dem Block mit $a$ in der *ersten*, das zweite auf dem mit $a$ in der *zweiten*
  Koordinate — verschiedene Punkte der Antidiagonalen, durch keine Kette
  zusammenzubringen.

**Damit ist die Vermutung aus `PLAN.md` §1c bestätigt und geschärft:** §6 braucht
(T4) **plus ein Haarmaß**. §6 ist also echt enger als der Rest des Manuskripts,
und die Kettenidentität macht sichtbar, warum.

**Korrektur (2026-08-24, beim Übergang zu Task 1).** Die erste Fassung dieser
Entscheidung sagte „Haarmaß der von $\mathbb{T}$ erzeugten Gruppe" und schloss
daraus, Lebesgue auf $\mathbb{R}_+$ und Zählmaß auf $h\mathbb{N}_0$ seien bis auf
Normierung die einzigen. **Translationsinvarianz allein genügt nicht**, und die
Schlussfolgerung war deshalb nur zufällig richtig. Was \eqref{eq:cancel}
verlangt, ist, dass die Spiegelung $u\mapsto t-u$ den Block
$[s_k,s_{k+1})$ *massegleich* auf $[t-s_{k+1},t-s_k)$ wirft. Beide Blöcke sind
Differenzen von **Unterhalbmengen**; die Spiegelung einer Unterhalbmenge ist aber
eine **Oberhalbmenge**, und beide fallen nur bei **linearer** Ordnung zusammen.

Konkretes Gegenbeispiel: Lebesgue auf $\mathbb{T}=\mathbb{R}_+^2$ ist
translationsinvariant, lässt aber keine Dualität zu. Für $t=(1,1)$ und die Kette
$0\to(1,0)\to(1,1)$ ist der erste Block $[0,(1,0))$ Lebesgue-null, sein
Spiegelpartner $\mathbb{T}_{\le(1,1)}\setminus\mathbb{T}_{\le(0,1)}$ hat Masse 1.

**Also: §6 braucht lineare Ordnung + translationsinvariantes $q$**, und der
Mehrparameterfall ist in §6 ausgeschlossen — nicht wegen der Uhr, sondern wegen
der Ordnung. Im Manuskript als Rem. 6.4 richtiggestellt.

**Neu abgefallen:** Cor. 6.10, Dualität für Markovketten
($Pf(\cdot,y)=Qf(x,\cdot) \Rightarrow E_x[f(X_n,y)]=E_y[f(x,Y_n)]$), als
Ein-Zeilen-Korollar der Kettenidentität. `PLAN.md` §1c hatte das als „worth
writing out" markiert; es kostet jetzt nichts.

### D14 — Konventionskollision: §4 will $(0,t]$, §6 will $[0,t)$  *(2026-08-24)*

Beim Ausformulieren von D13 aufgefallen, und es korrigiert die Einschätzung in
D10, die Wahl sei nur ein Preis im diskreten Fall.

* **§4 (Thm. 4.2) verlangt $(0,t]$.** Ein Atom in $t$ muss *innerhalb* des
  Kompensators bis $t$ liegen, damit (R3),
  $E[|C_s-C_t|]\to0$ für $s\downarrow t$, gilt — und genau dieser Limes macht den
  càdlàg-Prozess zu einer **Modifikation** statt bloß zu einer Regularisierung.
* **§6 (Prop. 6.2) verlangt $[0,t)$.** Mit $(0,t]$ lautet der $k$-te Summand
  $\gamma(k+1,t-k-1)-\gamma(k,t-k)$, die Summe teleskopiert zu
  $\gamma(t,0)-\gamma(0,t)\ne0$: **diskrete Dualität fällt aus.**

Keine Konvention bedient beide. Bei atomlosem $q$ — insbesondere
$\mathbb{R}_+$/Lebesgue, dem einzigen in EK86 und CPS23 behandelten Fall — ist
der Konflikt unsichtbar, weshalb keine der Quellen sich entscheiden muss. Ein
Text, der Atome zulässt, muss es.

**Status.** Die Entscheidung D10 ($(0,t]$) bleibt, aber sie ist jetzt eine
Entscheidung *gegen* die diskrete Dualität, nicht bloß gegen die
Doob-Zerlegung. Im Manuskript als Rem. 6.3 dokumentiert. Falls der Nutzer §6 im
diskreten Fall haben will, ist die saubere Lösung, Def. 3.5 mit beiden
Konventionen zu führen (die dritte Option aus der Q8-Frage) — dann gilt §4 für
$(0,t]$ und §6 für $[0,t)$, und beide Aussagen sind ehrlich abgegrenzt. **Das
ist dem Nutzer vorzulegen.**

### D15 — Task 1: zwei Schichten, (T0) als Basis  *(2026-08-24)*

**Entscheidung des Nutzers.** Option 2 aus der Diskussion: §3, §5-Markov und §7
auf (T0), §4 / §5-Eindeutigkeit / §6 auf (T2b) bzw. (T2a); jeder Satz trägt sein
Bündel.

**Bündel (Def. 2.1 im Manuskript).** Gegenüber `PLAN.md` §1a in einem Punkt
geändert: **(T2) ist in (T2a) und (T2b) aufgespalten**. Grund: der
Eindeutigkeitsteil von Thm. 5.6 und ganz §6 brauchen die *lineare Ordnung*, aber
*keine Topologie*; nur §4 und die konkreten Konvergenzsätze brauchen die
Topologie. Das Bündeln der beiden verdeckte das.

| Bündel | Annahme | wo gebraucht |
|---|---|---|
| (T0) | Präordnung mit kleinstem Element | §3, §5-Markov, §7-abstrakt |
| (T1) | + gerichteter Verband | Stoppzeiten |
| (T1′) | EK86 §2.8, metrischer Verband | **gar nicht** — siehe D16 |
| (T2a) | + linear geordnet | §5-Eindeutigkeit, §6 |
| (T2b) | (T2a) + Ordnungstopologie, abz. dicht, rechts nicht isoliert | §4, §7-konkret |
| (T3) | $[0,\infty)$ oder $[0,T]$ | Skorokhod, §6-kontinuierlich |
| (T4) | kürzbares geordnetes kommutatives Monoid | §5, §6 |

**Zweite Korrektur an `PLAN.md`.** Der Plan behandelte (T1′) als
*Basisannahme* („Q1: (T1) oder (T1′)?"). Der Audit zeigt: die Basis ist (T0), und
(T1′) kommt praktisch nicht vor. Wie wenig, präzisiert D16 (nachträglich: **gar
nicht**). Q1 ist damit beantwortet, aber anders, als die Frage es zuließ.

**Ergebnis des Audits (§2.8 im Manuskript).** Der Halbordnungsfall — und damit
$\mathbb{T}=[0,\infty)^d$ — überlebt in §3, im Markov-Teil von §5 und im
abstrakten Konvergenzsatz. Er stirbt an genau zwei Stellen, und beide Male aus
einem *mathematischen* Grund:

* **Rem. 5.6.** Die Induktion im Eindeutigkeitsbeweis startet bei $t_n$ neu, wozu
  $\prod_{k\le n}f_k(\pi_{t_k})$ $\mathcal{F}^\circ_{t_n}$-messbar sein muss —
  die Zeiten müssen eine **Kette** bilden. Auf $[0,\infty)^2$ sind $(1,0)$ und
  $(0,1)$ unvergleichbar, und keine Kette sieht ihre gemeinsame Verteilung.
  „Eindimensionale Verteilungen genügen" ist im Mehrparameterfall also **falsch**.
  Der Ausweg über $t_1\vee\dots\vee t_n$ (den (T1) erlauben würde) hilft nicht,
  weil $t_{n+1}$ dieses Supremum nicht dominieren muss.
* **Rem. 6.4.** Siehe D13-Korrektur: Spiegelung wirft Unterhalbmengen auf
  Oberhalbmengen, beide fallen nur bei linearer Ordnung zusammen.

**Muster.** Die Markoveigenschaft ist *algebraisch* und überlebt auf der
Halbordnung; Eindeutigkeit und Dualität sind *ordnungstheoretisch* und nicht.
Das ist die schärfste Formulierung dessen, was Task 1 herausfinden sollte.

### D16 — Abgleich mit EK86 §2.8 (Martingale über gerichteten Indexmengen)  *(2026-08-24)*

Auf Nachfrage des Nutzers am Scan geprüft (EK86 S. 84–88 = PDF 94–98, sowie
Kap. 6 §6.1–6.3, S. 306–325). §2.8 ist die einzige Stelle, an der EK selbst mit
einer allgemeinen Indexmenge arbeiten. Drei Fehler bei mir, eine Bestätigung.

**Fehler 1 — der Verband wird für $\vee$ gebraucht, nicht für $\wedge$.**
`PLAN.md` §1a und §2.2 des Manuskripts sagten beide: „Stoppzeiten brauchen
$\tau_1\wedge\tau_2$, $\mathcal{F}_\tau$ braucht Infima." Beides falsch.

* EK86 **Prop. 2.8.1(a)**: $\max_{k\le n}\tau_k$ ist eine Stoppzeit, denn
  $\{\max_k\tau_k\le u\}=\bigcap_k\{\tau_k\le u\}$.
* EK86 **Rem. 2.8.3**: „Note that $\tau^a$ is not in general equal to
  $\tau\wedge a$, **which need not be a stopping time**."
* Der Grund, nachgerechnet: in einem Verband ist $x\wedge y\le u$ echt schwächer
  als „$x\le u$ oder $y\le u$" — in $\mathbb{R}_+^2$ ist
  $(1,0)\wedge(0,1)=(0,0)\le(0,0)$, ohne dass ein Faktor unter $(0,0)$ läge.
  Also ist $\{\tau\wedge a\le u\}$ echt größer als
  $\{\tau\le u\}\cup\{a\le u\}$ und liegt nicht in $\mathcal{F}_u$. EK ersetzen
  $\tau\wedge a$ deshalb durch die Trunkierung $\tau^a$ ihrer (8.10).
* EK86 **(8.6)**: $\mathcal{F}_\tau=\{A: A\cap\{\tau\le u\}\in\mathcal{F}_u\}$ —
  wörtlich das übliche, ohne Infima.

**Fehler 2 — (T1′) kommt im Manuskript gar nicht vor.** D15 sagte „genau einmal,
bei Thm. 5.7". Auch das ist zu großzügig: Thm. 5.7 setzt $F\subset D_E$, also
(T2b), also lineare Ordnung voraus — dort ist die Verbandsstruktur trivial. Die
lokalisierten Aussagen (Rem. 5.11, 4.7, 7.4) ebenso. (T1′) ist damit **nirgends**
im Einsatz; es bliebe nur für eine starke Markoveigenschaft auf einem echt
gerichteten Index relevant, und die ist nach Rem. 5.6 schon auf der
Eindeutigkeitsseite blockiert. Das Bündel bleibt in der Liste, aber als
Vergleichspunkt zu EK, nicht als Annahme. Tag von Thm. 5.7 und die Zeile in §2.8
entsprechend korrigiert.

**Fehler 3 — meine Beschreibung von (T1′) war unvollständig.** EK verlangen
zusätzlich, dass $(u,v)\mapsto u\wedge v$ und $(u,v)\mapsto u\vee v$ **stetig**
sind. „Separabel von oben" ist bei EK keine globale Annahme, sondern wird dort
gestellt, wo es gebraucht wird (Prop. 8.4, Prop. 8.5(c), Thm. 8.7). Ihr Optional
Sampling (Thm. 8.7) verlangt außerdem die Einschachtelung (8.16),
$\lim_n P\{u_n\le\tau_1\le\tau_2\le u_m\}=1$ — eine Bedingung, die es im
linear geordneten Fall nicht gibt.

**Bestätigung — und zwar für Rem. 5.6.** EK bauen §2.8 laut eigener Aussage für
Kapitel 6. Dort (Thm. 6.3.4) trägt der Mehrparameterindex aber die
**Filtration** $\{\mathcal{F}_u: u\in\mathbb{R}_+^k\}$ und eine
komponentenweise nichtfallende Familie $\mathbb{R}_+^k$-wertiger **Stoppzeiten**
$\tau(t)$ — die Prozesse selbst leben in $\prod_k D_{E_k}[0,\infty)$, und der
zeittransformierte Prozess $Z(t)=Y(\tau(t))$ ebenfalls. **EK indizieren nie einen
Prozess mit $\mathbb{R}_+^d$.** Der Mehrparameterindex ist ein Hilfsmittel
*innerhalb* einer Einparametertheorie, und was §2.8 dafür liefert, ist Optional
Sampling und sonst nichts.

Es gibt in EK also keinen Mehrparameter-Eindeutigkeits- oder Markovsatz, an dem
sich Rem. 5.6 messen ließe — was kein Zufall ist, sondern indirekte Evidenz für
Rem. 5.6.

**Ein Unterschied, der bleibt und harmlos ist.** EK86 (8.2) fordert
Antisymmetrie, ihr Index ist also eine Halbordnung, nicht bloß eine Präordnung.
(T0) ist an dieser Stelle schwächer. Nichts im Manuskript benutzt Antisymmetrie,
und Mathlibs `Preorder` hat sie nicht — der Unterschied ist bewusst und im
Manuskript (Rem. 2.5(i)) vermerkt.

**Eine Bestätigung der Methode.** EK schreiben „we assume throughout this section
that $\mathscr{I}$ is a metric lattice" und definieren *danach* Filtration,
Stoppzeit, $\mathcal{F}_\tau$, Adaptiertheit und in (8.15) die
Martingaleigenschaft — von denen keine den Verband benutzt und alle auf einer
bloßen Präordnung korrekt sind. Der Verband wird erst in Prop. 8.1 gebraucht.
Genau diese Vermengung soll Def. 2.1 auflösen. Die ganze Martingalschicht dieses
Manuskripts ruht auf EK86 (8.15) allein, und die ist für halbgeordnete Indizes
formuliert.

Im Manuskript als **Rem. 2.5** dokumentiert (vier Punkte).

### D17 — Nachaudit: §2 war noch nicht umgestellt  *(2026-08-24)*

Auf die Frage des Nutzers, ob der allgemeine Parameterraum nun wirklich
durchgängig drin ist, habe ich die tex-Datei systematisch nach `\Rp`,
`[0,\infty)`, `t \geq 0`, `\int_0^` und `\Q` durchsucht und jeden Treffer seiner
Sektion zugeordnet. Ergebnis: **nein, noch nicht** — und die Lücke saß an der
unangenehmsten Stelle.

**Die eigentliche Lücke.** §2.4 „From Chapter 2", also genau die Schicht, die
(T0) sein soll und für die Mathlib-Anbindung zählt, war noch komplett über
$[0,\infty)$ geschrieben:

* Def. 2.11: messbarer Prozess, Filtration, adaptiert, progressiv, Version,
  Modifikation, ununterscheidbar, Stoppzeit, $\mathcal{F}_\tau$;
* Def. 2.13: Martingal und Submartingal;
* Facts 2.14/2.15: Regularisierung längs einer dichten Menge $F\subset[0,\infty)$.

Das war nicht bloß kosmetisch: **Thm. 4.3 ist (T2b), zitierte aber Facts über
$[0,\infty)$.** Die Aussage war also strenggenommen nur für $\mathbb{T}=[0,\infty)$
belegt, obwohl sie für (T2b) formuliert war.

**Behoben.** Def. 2.11 und Def. 2.13 sind jetzt (T0) über $\mathbb{T}$ mit Uhr;
Rechtsstetigkeit von Filtration und Pfaden ist in einen eigenen Absatz unter
(T2b) ausgelagert. Def. 2.13 verweist jetzt ausdrücklich darauf, dass sie
EK86 (8.15) wörtlich ist und `MeasureTheory.Martingale` in Mathlib entspricht —
das schließt den Kreis zu D16. Facts 2.14/2.15 sind (T2b) über $F\subset\mathbb{T}$.
Fact 2.12 (Stoppzeiten) und Facts 2.16/2.17 (Optional Sampling, Doob) sind (T2b)
getaggt, mit dem Hinweis auf Rem. 2.5(ii), dass $\tau_1\wedge\tau_2$ auf einem
gerichteten Index keine Stoppzeit sein muss.

**§2.5 (Skorokhod) trägt jetzt eine Kopfzeile:** alles dort ist (T3), weil die
$J_1$-Topologie über Zeittransformationen $\lambda:[0,\infty)\to[0,\infty)$
definiert ist. Das ist der einzige Prerequisites-Block, der sich nicht
abstrahieren lässt, und das steht jetzt dort statt implizit zu bleiben.

**Kosmetische Reste**, alle behoben: „$t\ge0$" in Def. 4.2 (R1)/(R3), im Beweis
von Thm. 4.3, in Def. 5.3 (Shift), in Thm. 5.7 und in Thm. 5.9(b); „$\mathbb{Q}$"
in §8.

**Ergebnis des Nachaudits.** Alle verbleibenden Vorkommen von $[0,\infty)$ liegen
in Blöcken, die als (T3) ausgewiesen sind: §2.5, §3.2 (Lem. 3.9, Prop. 3.10),
§6.2, §7, sowie §1.1 und die Beispiele in §2.2, wo $[0,\infty)$ die Quelle bzw.
ein Spezialfall *ist*. Die Bündeltabelle §2.8 enthält jetzt auch die
§2-Prerequisites.

**Antwort auf die Frage des Nutzers:** ja, jetzt.

### D18 — Abgleich mit Kallenberg (3. Aufl., Kap. 32)  *(2026-08-24)*

Der Nutzer hat Kallenberg in `references/` gelegt mit der Vermutung, dort werde
viel mit dem lokalen MP gemacht. Zutreffend: Kap. 32 („Stochastic Equations and
Martingale Problems") führt den MP **von vornherein lokal**. Der Abgleich deckt
eine echte Lücke bei mir auf, bestätigt aber die Architektur.

**Kallenbergs Setting.** $M^f_t=f(X_t)-f(X_0)-\int_0^t A_sf(X)\,ds$ für
$f\in\hat C^\infty$, Pfadraum $C_{\mathbb{R}_+,\mathbb{R}^d}$ **postuliert**,
$P$ löst den lokalen MP für $(a,b)$, wenn $M^f$ lokales Martingal ist. Er
notiert ausdrücklich: „For bounded $a,b$ it is clearly equivalent that $M^f$ be a
true martingale" — der lokale MP entsteht also aus **unbeschränkten
Koeffizienten**, nicht aus unbeschränkten $f$.

**Die Lücke: Lokalität ist nicht linear in $P$.** Lem. 5.2
(Mischungsstabilität) und Lem. 5.6 (Restart) ruhen beide darauf, dass die
Martingaleigenschaft linear in $P$ ist. Für **lokale** Martingale gilt das nicht,
weil die lokalisierende Folge von $P$ abhängen darf. D3 sagte „lokale MPs pro
Satz ehrlich abgegrenzt", aber §5 sagte dazu nichts — die abstrakte Schicht hatte
schlicht keine lokale Fassung.

**Kallenbergs Lösung (Thm. 32.10, 32.11; er schreibt sie Stroock–Varadhan zu).**
Verlange eine lokalisierende Folge, die ein **Pfadfunktional** ist, also für alle
$P$ dieselbe: $\tau^f_n=\inf\{t:|M^f_t|\ge n\}$. Dann ist „$P$ löst den lokalen
MP" wieder abzählbar viele in $P$ **lineare** Bedingungen
$E[M^{f,n}_t-M^{f,n}_s; F]=0$. Für die starke Markoveigenschaft braucht er
zusätzlich **Shift-Kovarianz**: $\sigma_n=\tau+\tau_n\circ\theta_\tau$ ist wieder
Stoppzeit und
$(M^{f,n}_t-M^{f,n}_s)\circ\theta_\tau=M^f_{(\tau+t)\wedge\sigma_n}-M^f_{(\tau+s)\wedge\sigma_n}$
— das ist seine Formel (17), und es ist wörtlich die lokale Form meiner Def. 5.5
(Shift-Stabilität). Sein Beweis benutzt außerdem
$\theta_\tau^{-1}\mathcal{F}_s\subset\mathcal{F}_{\tau+s}$ — genau der Schritt in
meinem Lem. 5.6.

Als **Rem. 5.10** ins Manuskript aufgenommen, mit (L1) gemeinsames Pfadfunktional
und (L2) Shift-Kovarianz.

**Zweiter Fund: die Disintegration fehlte.** Kallenbergs Thm. 32.10(ii) enthält
neben der Mischung auch deren **Umkehrung**: aus
$E[M^{f,n}_t-M^{f,n}_s;F\mid X_0]=0$ folgt, dass $P(\cdot\mid X_0)$ f.s. den
lokalen MP mit Startverteilung $\delta_{X_0}$ löst, also $P=\int P_x\mu(dx)$.
Das hatte ich nicht. Neu als **Lem. 5.3 (Disintegration)** mit Beweis: für
beschränktes $h$ ist $Z^\circ_s h(\pi_0)$ beschränkt und
$\mathcal{F}^\circ_s$-messbar, also
$E^P[(Y_t-Y_s)Z^\circ_s h(\pi_0)]=0$, also
$E^P[(Y_t-Y_s)Z^\circ_s\mid\pi_0]=0$ f.s.; Abzählbarkeit liefert **eine**
Nullmenge für alle Daten.

Das ist auch eine Verbesserung von **Cor. 6.14**: dort begründe ich den Übergang
$\delta_x\to\mu$ über die Markoveigenschaft (Thm. 5.7(a)). Lem. 5.3 braucht sie
nicht. In Rem. 5.4 vermerkt.

**Ein Unterschied im Zugang zur Lokalisierung.** EK86 §4.6 — und damit meine
Rem. 5.14 — lokalisiert, indem der **Operator** verändert wird
($A^{(m)}=\{(f\mathbf{1}_{K_m},g\mathbf{1}_{K_m})\}$). Kallenberg lässt den
Operator in Ruhe und stoppt den **Testprozess**. Für den abstrakten Rahmen ist
Letzteres richtig, weil dort $\mathbb{X}^\circ$ primitiv ist und $A$ nicht.
Rem. 5.14 verweist jetzt darauf.

**Bestätigungen.**

* Kallenberg **postuliert** den Pfadraum $C_{\mathbb{R}_+,\mathbb{R}^d}$ und
  beweist **keinen** Pfadregularitätssatz. Das stützt D3 (Thm. 4.1 lokalisiert
  nicht) und D11 (CPS/Kallenberg setzen den Pfadraum voraus, statt ihn zu
  erzeugen). Seine Notes zu Kap. 32 verweisen für „more information on the
  martingale problem" auf Jacod (1979), Stroock–Varadhan (1979), EK (1986) —
  kein Regularitätsresultat.
* Seine Normierung $M^f_t=f(X_t)-f(X_0)-\dots$ macht das $\kappa$ in meiner
  \eqref{eq:shiftstable} zu Null. Das $\kappa$ ist also Buchhaltung, keine
  Hypothese — eine schöne Bestätigung, dass Def. 5.5 richtig geschnitten ist.
* Sein Beweis von Thm. 32.11(i) ist strukturell mein Lem. 5.6 plus Thm. 5.9,
  im lokalen Fall.

Kallenberg ist als `\KA` in die Bibliographie aufgenommen.

### D19 — Task 2.2b durchgeführt: die lokale Theorie  *(2026-08-24)*

Neu als **§5.2 „The local martingale problem"**, mit vollständigen Beweisen statt
der Behauptung aus D18, es gehe alles durch.

**Def. 5.11 (localizing system).** Eine Familie $\Sigma$ von Stoppzeiten auf $F$
— Pfadfunktionale, nicht maßabhängig — mit

* **(L1)** gleichmäßige Lokalisierung: $\tau_n\uparrow\infty$ in $\Sigma$ und
  $P\in\mathcal{M}_{\mathrm{loc}} \iff Y^{\circ,\tau_n}$ ist $P$-Martingal für
  alle $Y^\circ,n$;
* **(L2)** Shift-Kovarianz: $r+\sigma\circ\theta_r\in\Sigma$;
* **(L3)** integrierbare Zuwächse nach einem Neustart: für $\sigma\ge r$ ist
  $t\mapsto Y^\circ_{(r+t)\wedge\sigma}-Y^\circ_r$ ein
  $(\mathcal{F}^\circ_{r+t})$-Martingal.

**Der ganze lokale Apparat hängt an einer Identität.** In Lem. 5.17 (lokaler
Restart), Schritt 1:
$$\hat Y^{\circ,\tau_n}_t\circ\theta_r = Y^\circ_{(r+t)\wedge\sigma}-Y^\circ_r+\kappa,
\qquad \sigma=r+\tau_n\circ\theta_r,$$
Beweis: $u=t\wedge\tau_n(\theta_r\omega)$, dann
$r+u=(r+t)\wedge(r+\tau_n\circ\theta_r)$, weil $r+\cdot$ ordnungserhaltend und
kürzbar ist. Das ist Kallenbergs (17), und es ist die **einzige** Rechnung im
lokalen Teil, die nicht schon in §5.1 steht. Alles andere ist entweder das
globale Argument wörtlich oder die Linearität, die (L1) wiederherstellt.

Thm. 5.18 (lokale Eindeutigkeit/Markov/starke Markov) ist dann Buchhaltung: der
Beweis von Thm. 5.7 benutzt genau drei Dinge — Lem. 5.6, die
Eindimensionalitäts-Hypothese und Fact 2.14 —, und die ersten beiden werden
ersetzt.

**(L3) ist nicht aus (L1) folgerbar.** Stoppt man ein lokales Martingal bei
$\sigma\in\Sigma$, bleibt ein lokales Martingal: vor $r$ ist nichts gestoppt.
Verlangt wird nur die Integrierbarkeit der Zuwächse *nach* $r$ — im
Diffusionsfall ist das die Beschränktheit auf $\overline{B}_n$.

### D20 — Abgleich mit Jacod & Shiryaev (Kap. III)  *(2026-08-24)*

Auf Nachfrage geprüft. **J&S bringt viel Neues**, in fünf Punkten.

**1. Die abstrakte Formulierung ist von 1987, nicht von CPS23.** J&S Def. III.1.3
hängt ein Martingalproblem an eine Familie $\mathcal{X}$ optionaler Prozesse auf
einem filtrierten Raum *ohne Maß*, und zwar mit **lokalen** Martingalen als
Normalfall, nicht als Variante. Das ist CPS Def. 3.2, Jahrzehnte früher. Zwei
Details ihrer Fassung sind besser:

* Die Anfangsbedingung ist ein Maß $P_{\mathcal{H}}$ auf einer **Anfangs-σ-Algebra**
  $\mathcal{H}$, nicht bloß eine Startverteilung. Mein Lem. 5.3 (Disintegration)
  gilt wörtlich mit $\sigma(\pi_0)\to\mathcal{H}$.
* J&S Rem. III.1.6 sagt ausdrücklich, dass die Elemente von $\mathcal{X}$ weder
  càdlàg noch adaptiert sein müssen — genau die Beobachtung, die Setting 4.1
  braucht und die CPS' Standing Assumptions ausschließen.

Als **Rem. 3.6** ins Manuskript.

**2. Korrektur an mir: Konvexität ist gratis.** Ich hatte in D18 und in der
ersten Fassung von §5.2 behauptet, Mischungsstabilität brauche (L1). Für
**endliche** Konvexkombinationen stimmt das nicht: nimm $\tau_n\wedge\tau'_n$,
dann ist $Y^{\circ,\sigma_n}$ Martingal unter beiden Maßen und $\sigma_n\to\infty$
unter beiden. J&S III.1.13 und III.2.8 beweisen die Konvexität denn auch
unbedingt. Erst die Mischung über ein **Kontinuum** braucht (L1) — man bräuchte
$\inf_\vartheta\tau^\vartheta_n$, das weder gegen $\infty$ gehen noch messbar
sein muss. Genau deshalb formuliert Kallenberg Thm. 32.10 für einen **Kern**.
Lem. 5.13 ist entsprechend in (a) Konvexität (hypothesenfrei) und (b) Mischung
(unter (L1)) aufgeteilt, mit Rem. 5.14 zur Erläuterung.

**3. (L1) ist eine Konstruktion, keine Hypothese.** J&S III.2.8 benutzen
$T_n=\inf\{t:|Y_t|>n\}$ und die Beobachtung, dass $Y_0=0$ plus beschränkte
Sprünge $Y^{T_n}$ **beschränkt** machen — ein beschränktes lokales Martingal ist
ein gleichgradig integrierbares Martingal. Kallenberg macht dasselbe mit
$\tau^f_n=\inf\{t:|M^f_t|\ge n\}$. Neu als **Lem. 5.15** mit Beweis. Beide
lokalisieren längs des **Testprozesses**, nicht längs des Zustandsraums; die
Austrittszeiten aus Kugeln sind die unkanonischere Wahl, weil sie auf $E$
verweisen.

**4. J&S III.2.39: das geshiftete Problem — die richtige Verallgemeinerung.**
Meine Def. 5.5 verlangt, dass der geshiftete Testprozess in **derselben** Familie
liegt; genau das erzwingt die Shift-Invarianz der Uhr und die Homogenität des
Markovprozesses. J&S postulieren stattdessen eine ganze Familie geshifteter
Tripel $(\rho_tB,\rho_tC,\rho_t\nu)$ mit
$(\rho_tB)_s(\theta_t\omega)=B_{t+s}(\omega)-B_t(\omega)$. In meiner Notation:
\eqref{eq:shiftstable} mit $\kappa=0$, aber mit $Y^\circ$ aus einer
**geshifteten** Familie $\mathbb{X}^\circ_t$. Das ist billig zu haben — Lem. 5.6
und Lem. 5.17 benutzen nur, dass der geshiftete Prozess ein $P$-Martingal ist,
nicht dass er in der Ausgangsfamilie liegt — und es ersetzt
„zeithomogener Markovprozess" durch „Markovprozess" und streicht die
Shift-Invarianz der Uhr aus den Hypothesen. **Das ist die nächste Revision von
§5.1** (neu in `PLAN.md` als Task 2.2c).

**5. J&S III.2.37: lokale Eindeutigkeit.** Ein echt stärkerer Begriff als meine
\eqref{eq:localonedim}: für **jede** strikte Stoppzeit $T$ stimmen zwei Lösungen
des *gestoppten* Problems auf $\mathcal{F}_T$ überein. Impliziert Eindeutigkeit
($T\equiv\infty$) und ist das, was Absolutstetigkeits- und Grenzwertargumente
wirklich brauchen. J&S Thm. III.2.40: Eindeutigkeit *impliziert* lokale
Eindeutigkeit, sobald das Problem Markovschen Typs im Sinne von Punkt 4 ist.
Dazu habe ich nichts.

**Ferner: strikte Stoppzeiten** (J&S III.2.35). $\mathcal{F}^\circ_t$ ist nicht
rechtsstetig, deshalb unterscheiden J&S Stoppzeiten bzgl. der rohen Filtration.
Meine Stoppzeiten in Def. 5.11 sind strikt — sie müssen Pfadfunktionale sein, das
ist dieselbe Forderung von der anderen Seite. Für die Formalisierung relevant,
weil Mathlibs `IsStoppingTime` relativ zur übergebenen Filtration ist.

Punkte 4, 5 und die strikten Stoppzeiten als **Rem. 5.19** dokumentiert.

**Panne beim Einbau.** Beim Ersetzen der alten Rem. 5.10 hatte
`s.index("What the abstract form buys")` die gleichnamige Bemerkung in **§4**
getroffen statt die in §5, wodurch ein 411-Zeilen-Block dupliziert wurde (23
doppelte Labels). Gefunden über `grep -o '\\label{...}' | uniq -d`, Duplikat
gelöscht, Backup unter `scratchpad/MP_backup.tex`. Lehre: beim Suchen nach
Ankern immer `s.index(anker, ab_position)` verwenden, wenn der Anker mehrdeutig
sein kann.

### D21 — Task 2c: geshiftete Familien, Zeitinhomogenität  *(2026-08-24)*

Umsetzung von D20.4. **Def. 5.5 ist ersetzt**: statt „$\mathbb{X}^\circ$ ist
shift-stabil" jetzt „$(\mathbb{X}^\circ_r)_{r\in\mathbb{T}}$ ist ein
**Shift-System**":
$$\hat Y^\circ_t\circ\theta_r = Y^\circ_{r+t}-Y^\circ_r+\kappa,
\qquad \hat Y^\circ\in\mathbb{X}^\circ_r,\ Y^\circ\in\mathbb{X}^\circ .$$
Das ist J&S III.2.39 in meiner Notation; die Messbarkeitsklausel ist deren
III.2.39(i) und wird für die starke Markoveigenschaft an einer Stoppzeit
gebraucht ($\mathbb{X}^\circ_\tau$ durch Einsetzen).

**Was sich ändert.**

* **Lem. 5.8 (Restart)**: Konklusion jetzt $R\in\mathcal{M}(\mathbb{X}^\circ_r)$
  statt $\mathcal{M}(\mathbb{X}^\circ)$. Der Beweis ist wörtlich derselbe — er
  benutzt nur, dass der *geshiftete* Prozess ein $P$-Martingal ist.
* **Thm. 5.9**: Hypothese jetzt „für jedes $r$: Eindeutigkeit der
  eindimensionalen Verteilungen in $\mathcal{M}(\mathbb{X}^\circ_r)$". Beide
  Beweisteile gehen durch, weil in beiden Fällen $R$ und $R'$ im *selben*
  geshifteten Problem liegen ($\mathbb{X}^\circ_r$ bzw. $\mathbb{X}^\circ_{t_n}$).
  Konklusion ist die Markoveigenschaft, im Allgemeinen **zeitinhomogen**.
* **Thm. 5.11 (starke Markov)**: Zweiparameter-Kern $T_{r,s}$ mit
  Chapman–Kolmogorov $T_{r,s}T_{s,t}=T_{r,t}$, aus einer messbaren Familie
  $P_{x,r}\in\mathcal{M}(\mathbb{X}^\circ_r,\delta_x)$.
* **§5.2** (lokale Theorie) analog: Lem. 5.19 liefert
  $\mathcal{M}_{\mathrm{loc}}(\mathbb{X}^\circ_r)$.

**Neu: Ex. 5.7, das geshiftete Problem für $\mathbb{X}_A$.** Mit der
**zurückgezogenen Uhr** $q_r(A)=q(r+A)$ und zeitabhängigem $g$:
$$\mathbb{X}^\circ_r=\Bigl\{f(\pi_t)-\int_{(0,t]}g(r+u,\pi_u)\,q_r(du)\Bigr\},$$
und die Substitution $v=r+u$ gibt die Identität mit $\kappa=f(\pi_r)$.

**Das ist der eigentliche Gewinn, und er beantwortet Q3 endgültig.** Das
geshiftete Problem **existiert immer**. Was von $q$ und $g$ abhängt, ist nur, ob
es *dasselbe* Problem ist: $\mathbb{X}^\circ_r=\mathbb{X}^\circ$ genau dann, wenn
$q$ shift-invariant und $g$ zeitunabhängig ist — und nur dann ist der
Markovprozess homogen. Die Shift-Invarianz der Uhr ist damit **aus den
Hypothesen verschwunden**; sie ist jetzt das Kriterium für Homogenität, nicht
mehr die Voraussetzung für die Markoveigenschaft.

D12 („Shift-Stabilität gilt genau dann, wenn $q$ shift-invariant ist") bleibt
richtig, bezieht sich aber auf den *engen* Begriff. In der Bündeltabelle steht
in der Uhr-Spalte jetzt „clock" statt „shift inv."; nur EK86 Thm. 4.4.2 selbst
trägt die Shift-Invarianz noch, und zwar ausdrücklich „for homogeneity".

Rem. 5.21(i) („was J&S anders machen") ist von „wäre zu tun" auf „übernommen"
umgeschrieben.

### D22 — §1.1 nachgezogen  *(2026-08-24)*

Der Abschnitt hieß „(EK) vs. (CPS)" und schrieb die abstrakte Formulierung CPS23
zu. Nach D20.1 ist das falsch. Jetzt heißt die zweite Option **(A) The abstract
setting**, mit einem Absatz zur Herkunft: J&S Def. III.1.3 (1987) hat sie in
essentiell der hier benutzten Form, mit lokalen Martingalen als Normalfall und
Anfangs-σ-Algebra; CPS23 entdecken sie in der für schwache Konvergenz passenden
Gestalt wieder (kanonische Testprozesse, determinierende Mengen,
$P$-Stetigkeit), und dieser folgt §3; Kallenberg Kap. 32 arbeitet im selben
Geist für Diffusionen.

Neuer Absatz „What each setting is good for": (A) ist, wo **alle vier**
Zielresultate natürlich *bewiesen* werden, (EK) ist, wo sie *angewandt* werden.
Das ist dieselbe Korrektur wie in §1.2, jetzt auch dort, wo sie zuerst
aufgeschlagen hätte. Die Marken in §1.2 sind von „(CPS)" auf „(A)" umgestellt.

### D23 — Task 2.1: Prop. 3.7 ausgeschrieben — und die Aussage war falsch  *(2026-08-24)*

Auftrag: das Monotone-Klassen-Argument in Prop. 3.7 (EK86 (3.4)) vollständig
ausschreiben. Beim Ausschreiben stellte sich heraus, dass die **Aussage** nicht
trägt, wie sie dastand.

**Der Fehler.** Prop. 3.7 quantifizierte über **Ketten**
$t_1\le\dots\le t_{n+1}$, EK86 (3.4) folgend. Auf $\mathbb{T}=\mathbb{R}_+$ ist
das äquivalent zu „beliebige endliche Teilmenge von $\mathbb{T}_{\le s}$", auf
einer Präordnung nicht — und das Argument braucht die stärkere Fassung. Der
Beweis testet gegen die Erzeuger von
$\mathcal{F}^X_s=\sigma(X_u:u\in\mathbb{T}_{\le s})$, und das sind Produkte über
**beliebige** endliche Teilmengen. Auf $\mathbb{R}_+^2$ liegen $(1,0)$ und
$(0,1)$ beide unter $(1,1)$, ohne vergleichbar zu sein; keine Kette erreicht
$h_1(X_{(1,0)})h_2(X_{(0,1)})$.

Die Hypothese ist also zu **verstärken**, und dann geht alles durch. Das ist das
Spiegelbild von Rem. 5.10 (dort konnte die *Konklusion* nicht gerettet werden,
hier die *Hypothese* problemlos). Als Rem. 3.8 dokumentiert.

**Der Beweis, in vier Schritten.** Fixiere $s\le t$; schreibe
$I^h_u=\int_{(0,u]}h(X_v)q(dv)$, so dass
${}^{*}\mathcal{F}^X_s=\sigma(X_u, I^h_u: u\le s, h\in B(E))$.

1. $\mathcal{H}=\{W$ beschränkt, ${}^{*}\mathcal{F}^X_s$-messbar,
   $E[(Y_t-Y_s)W]=0\}$ ist ein Vektorraum, enthält die Konstanten (das ist
   \eqref{eq:fdd} mit $n=0$) und ist unter beschränkter monotoner Konvergenz
   abgeschlossen (majorisierte Konvergenz mit $|Y_t-Y_s|\in L^1$).
2. $\mathcal{K}$ = endliche Produkte
   $\prod_k h_k(X_{t_k})\cdot\prod_j I^{g_j}_{u_j}$ mit $t_k,u_j\le s$ ist
   multiplikativ und erzeugt ${}^{*}\mathcal{F}^X_s$. **Jedes $I^h_u$ ist
   beschränkt**, $|I^h_u|\le\|h\|q(\mathbb{T}_{\le u})<\infty$ — hier wird die
   Endlichkeit aus Def. 2.2 zum ersten Mal gebraucht.
3. $\mathcal{K}\subset\mathcal{H}$: das ist **Fubini, keine Approximation**.
   Schreibe $\prod_j I^{g_j}_{u_j}$ als *ein* Integral über
   $(0,u_1]\times\dots\times(0,u_m]$ bzgl. $q^{\otimes m}$; die Majorante ist
   $\|h\|\|g\|\,|Y_t-Y_s|$, integrierbar für $P\otimes q^{\otimes m}$, weil
   $q^{\otimes m}$ der Menge endliche Masse gibt. Der innere Erwartungswert
   verschwindet nach \eqref{eq:fdd} mit $n+m$ Zeiten. **Genau hier ist die
   Kettenfassung zu schwach:** die $v_j$ entstehen durch die Integration und
   lassen sich mit den $t_k$ nicht zu einer Kette ordnen.
4. Funktionaler Monotone-Klassen-Satz (Fact 2.39) $\Rightarrow$ $\mathcal{H}$
   enthält alle beschränkten ${}^{*}\mathcal{F}^X_s$-messbaren Funktionen.

Die frühere Beweisskizze sagte, die $I^h_u$ seien „Limiten $q$-einfacher
Approximationen von Produkten". Das ist unnötig und im atomaren Fall auch
unangenehm; Fubini erledigt es direkt.

**Ferner ausdrücklich gemacht:** die Integrierbarkeit von $Y^{f,g}_t$ ist eine
**Hypothese**, keine Folgerung — $A\subset M(E)\times M(E)$ ist nicht
beschränkt. Steht jetzt in der Aussage.

**Was benutzt wird** (jetzt im Beweis vermerkt): nur die Präordnung, über
$\mathbb{T}_{\le u}\subset\mathbb{T}_{\le s}$ und \eqref{eq:clockinterval}; die
Endlichkeit $q(\mathbb{T}_{\le u})<\infty$, zweimal; und die gemeinsame
Messbarkeit von $X$. Keine Topologie, keine lineare Ordnung, keine weitere
Eigenschaft von $q$. Das Bündel (T0)+Uhr bestätigt sich.

Nachgezogen: die Stelle in §5.3, wo Prop. 3.7 als determinierende Menge benutzt
wird (jetzt „über beliebige endliche Teilmengen", plus der Hinweis, dass sie
mehr liefert als Def. 3.4 verlangt, nämlich ${}^{*}\mathcal{F}^X$ statt der
kanonischen Filtration).

### D24 — Task 2.8: der abstrakte Konvergenzsatz, mit Beweis  *(2026-08-24)*

D8 hatte festgestellt, dass CPS Thm. 3.14/Cor. 3.17 ohne Skorokhod-Raum auskommt
und deshalb als (F5a) direkt nach (F2) machbar ist. Er stand aber nur als
**Bemerkung ohne Beweis** da (Rem. 7.5 alt); der einzige Beweis im Text war der
von Thm. 7.3, also der konkreten Instanz. Das war die Lücke.

§7 ist jetzt wie §4 und §5 gebaut: **§7.2 „The abstract convergence theorem"**
mit Def. 7.3 ($P$-Stetigkeit an $X$), Thm. 7.4 mit vollständigem Beweis,
Rem. 7.5/7.6; **§7.3** enthält Thm. 7.7 (CPS) als Instanz, dessen Beweis auf eine
Hypothesenprüfung geschrumpft ist.

**Der Beweis, vier Schritte.**

* **Schritt 0 (Integrierbarkeit).** $|Y^\circ_r|$ ist $P$-stetig an $X$, also
  $|Y^\circ_r(X^n)|\Rightarrow|Y^\circ_r(X)|$ (Fact 2.22), gleichgradig
  integrierbar nach (C3b), also $E^{P^n}|Y^\circ_r(X^n)|\to E^P|Y^\circ_r(X)|<\infty$
  (Fact 2.38). Erst damit ist $Y_r\in L^1(P)$, was Def. 3.4(ii) verlangt.
* **Schritt 1 (Martingalidentität auf $D$).** $\psi=(Y^\circ_t-Y^\circ_s)Z^\circ_s$
  ist $P$-stetig an $X$ — Def. 7.3 ist unter Differenzen und Produkten stabil,
  die Ausnahmemengen werden geschnitten. Also $\psi(X^n)\Rightarrow\psi(X)$;
  gleichgradig integrierbar, weil $Z^\circ_s$ nach Def. 3.4(i) beschränkt ist;
  Fact 2.38 plus (C3c) gibt $E^P[(Y_t-Y_s)Z^\circ_s(X)]=0$. Determinierende
  Menge $\Rightarrow$ Martingaleigenschaft für $s\le t$ in $D$.
* **Schritt 2 (g.g. Integrierbarkeit unter $P$).** Mit $\varphi_N(x)=|x|-|x|\wedge N$:
  $E^P[\varphi_N(Y_r)]=\lim_n E^{P^n}[\varphi_N(Y^\circ_r(X^n))]\le\sup_n(\dots)$,
  Supremum über $r\in D\cap\mathbb{T}_{\le t}$, dann $N\to\infty$ nach (C3b) und
  der zweiten Charakterisierung in Fact 2.38. Das ist CPS Lem. 3.15, das ich als
  Fact 2.38 ohnehin schon hatte.
* **Schritt 3 (von $D$ nach $\mathbb{T}$).** $s_m\downarrow s$, $t_m\downarrow t$
  in $D$ mit $s_m<t_m$; $G\in\mathcal{F}_s\subset\mathcal{F}_{s_m}$;
  Rechtsstetigkeit plus Schritt 2 plus Fact 2.38.

**Bestätigung von D8, jetzt am Beweis ablesbar.** Die Schritte 0–2 benutzen
**keinerlei** Struktur auf $\mathbb{T}$ außer der Präordnung — $D$ ist irgendeine
Teilmenge, $\mathbb{T}_{\le t}$ eine Unterhalbmenge. Nur Schritt 3 braucht (T2b),
und nur, um von $D$ auf das Komplement zu kommen. **Mit $D=\mathbb{T}$ ist
Schritt 3 leer und der Satz gilt unter (T0)** — insbesondere für
$\mathbb{T}=\mathbb{N}_0$, wo jeder Punkt rechts isoliert ist und eine
Approximation weder möglich noch nötig ist. Als Rem. 7.5 dokumentiert.

**Wo die Topologie des Pfadraums eingeht: an genau einer Stelle.** Rem. 7.6:
(C1) ist der Input, (C2) kommt von Ex. 3.4 bzw. Prop. 3.7, (C3c) ist die
Approximation durch Martingale, (C3b) macht die Limiten vertauschbar — und
(C3a) ist die *einzige* Stelle, an der die Topologie von $F$ auftritt. Für
$F=D_E$ ist sie der Grund für die Hypothese „$\Gamma$ mit abzählbarem
Komplement" in Thm. 7.7, weil $\alpha\mapsto\alpha(t)$ genau in den Pfaden ohne
Sprung in $t$ $J_1$-stetig ist. Der Beweis von Thm. 7.7 sagt das jetzt an der
Stelle, wo (C3a) geprüft wird.

**Rem. 7.9 umgewidmet.** Statt „abstract form" jetzt „Path spaces other than
$D_E$": $L^p_{\mathrm{loc}}$ für Volterra-Gleichungen (CPS Ex. 3.13), und der
Hinweis auf CPS Cor. 3.21 (ohne g.g. Integrierbarkeit) und Thm. 3.14 (mit
Kontrollvariablen und weak-strong convergence), das deren §5.3 braucht.

### D25 — Zustandsraum abgestuft: Bündel (E0)–(E3)  *(2026-08-24)*

Auf die Frage des Nutzers, ob der polnische Raum zu verallgemeinern sei,
nachgesehen, **wo** Polnischkeit tatsächlich eingeht. Ergebnis: an vier Stellen,
mit vier verschiedenen und jeweils schwächeren Bedürfnissen. Also dieselbe
Operation wie Task 1, nur für $E$ statt für $\mathbb{T}$.

**Def. 2.6 (neu, §2.3).**

| Bündel | Annahme | gebraucht für |
|---|---|---|
| (E0) | messbarer Raum $(E,\mathcal{E})$ | §3, §6, fast ganz §5 |
| (E1) | standard-borelsch | Lem. 5.3, Fact 2.43, $\mathcal{B}(F)=\sigma(\pi_t)$ |
| (E2) | (E1) + separabel metrisierbar, $\mathcal{E}=\mathcal{B}(E)$ | §4 |
| (E3) | polnisch | §7 |

Kette (E3) ⇒ (E2) ⇒ (E1) ⇒ (E0), und **beide Lücken sind bewohnt**: eine
borelsche, nicht-$G_\delta$ Teilmenge von $\mathbb{R}$ erfüllt (E2), nicht (E3);
$\mathcal{S}'(\mathbb{R}^d)$ erfüllt (E1), nicht (E2) — Lusin-Raum, also
standard-borelsch, aber nicht metrisierbar.

**Der Gewinn ist konkret, nicht kosmetisch.** Martingalprobleme für
distributionswertige Prozesse — die MP-Formulierung einer SPDE mit
$E=\mathcal{S}'$ oder $\mathcal{D}'$ — sind unter (E0)/(E1) von §3, §5 und §6
**ohne einen einzigen neuen Beweis** mit abgedeckt. §4 und §7 nicht, und dort ist
die Reparatur echte Arbeit (Ersatz für $D_E$ und Straffheit darin; für nukleare
Duale ist das Mitomas Satz). Das ist als Rem. 2.8 ausdrücklich abgegrenzt statt
angefangen.

**Ein Nebenbefund, der §5 vereinfacht.** Setting 3.1 verlangt jetzt
$\mathcal{S}=\sigma(\pi_t: t\in\mathbb{T})$ als **Teil der Definition** eines
Pfadraums. Damit wird Fact 2.33 ($\mathcal{B}(D_E)=\sigma(\pi_t)$) in §5 gar
nicht mehr gebraucht: Thm. 5.9(b) und Thm. 5.20 benutzen jetzt direkt
\eqref{eq:pathsigma}. Für $F=D_E$ ist das ein Satz (Fact 2.33, braucht $E$
separabel), im abstrakten Rahmen eine Annahme über den Pfadraum — und die
richtige, weil sie genau das ist, was „endlichdimensionale Verteilungen
bestimmen das Gesetz" bedeutet.

**Was ich nicht vorgeschlagen habe.** Souslin- oder Radon-Räume als durchgehende
Allgemeinheit: über standard-borelsch hinaus kauft man auf der messbaren Seite
nichts, und auf der topologischen verliert man die Werkzeuge, an denen §4 und §7
hängen.

**Umgesetzt:** §2.3 neu (Def. 2.6, Rem. 2.7, Rem. 2.8); §1.3 hat statt „Polish
state space" jetzt „State space: measurable, not Polish, where possible" (und
„vier" statt „drei" Verschärfungen); Setting 3.1 auf (E0) plus
\eqref{eq:pathsigma}; alle Satzköpfe von §3 bis §7 tragen ihr (E·); die
Bündeltabelle §2.9 hat eine dritte Spalte „State"; §8 nennt für (F1)–(F5b) das
Zielbündel und vermerkt, dass (E1) genau Mathlibs `StandardBorelSpace` ist —
dieselbe Annahme, die dort die Disintegration von Maßen verlangt. Abstract
nachgezogen.

### D26 — Task 2 komplett  *(2026-08-24)*

**2.2 — Lem. 3.11 (EK86 4.3.2), bewiesen.** Der Kern ist eine Identität, die
EK86 nicht hinschreibt:
$$Z_t = e^{-\lambda t}Y_t + \lambda\int_0^t e^{-\lambda u}Y_u\,du,
\qquad Y_t = e^{\lambda t}Z_t - \lambda\int_0^t e^{\lambda u}Z_u\,du,$$
wobei $Y_t=f(X_t)-\int_0^t g$ und $Z_t$ die Resolventenform ist. Beide Richtungen
sind **dieselbe Rechnung**, einmal mit $e^{-\lambda u}$, einmal mit
$e^{+\lambda u}$; die Äquivalenz ist damit nicht zwei Beweise, sondern einer.
Der Fubini-Schritt ist
$\lambda\int_0^t e^{-\lambda u}\int_0^u g\,dv\,du = \int_0^t g(e^{-\lambda v}-e^{-\lambda t})dv$.
Die Resolventendarstellung folgt aus $E[Z_{t+r}|\mathcal{G}_t]=Z_t$ mit
$r\to\infty$. Rem. 3.12 vermerkt, dass Lem. 3.11 aus einem Grund der *Analysis*
(T3) ist, nicht der Wahrscheinlichkeit.

**2.3 — Fact 2.43 (EK86 Kap. 3, Aufgabe 7), bewiesen.** Als Rem. 2.44. Der
interessante Punkt: **die Abzählbarkeit kommt vom Zustandsraum, nicht von $M$.**
Es wird *keine* abzählbare Teilfamilie von $M$ angenommen, und im Allgemeinen gibt
es auch keine.

* Schritt 1: für $G\in\mathcal{G}$ mit $P(G)>0$ stimmen die bedingten Gesetze von
  $U$ und $V$ gegeben $G$ gegen alle $f\in M$ überein, also — da $M$ trennend —
  überhaupt. Das gibt $P(U\in B|\mathcal{G})=\mathbf{1}_B(V)$ f.s. für **festes** $B$.
* Schritt 2: nach (E1) ist $\mathcal{E}$ abzählbar erzeugt; eine abzählbare
  erzeugende Algebra liefert **eine** Nullmenge, und zwei Maße, die auf einer
  erzeugenden Algebra übereinstimmen, sind gleich. Also
  $\mu(\omega,\cdot)=\delta_{V(\omega)}$ f.s.
* Schritt 3: $P\{U=V\}=E[\mu(\cdot,\{V\})]=1$.

(E2) wird nur in Schritt 1 gebraucht, damit „$M\subset C_b(E)$ trennend"
überhaupt Sinn ergibt; die Maßtheorie ist (E1).

**2.5 — Thm. 6.6, Zuwachsidentität und $O(h^2)$, bewiesen.** Vier Schritte.
Schritt 1 friert $Y$ ein (Unabhängigkeit; Bedingen auf $\sigma(Y)$ lässt Gesetz
und Filtration von $X$ unverändert). Schritt 2 zerlegt
$$f(X_{s+h},y)e_\alpha(s{+}h)-f(X_s,y)e_\alpha(s)
= [f(X_{s+h},y)-f(X_s,y)]e_\alpha(s) + f(X_{s+h},y)[e_\alpha(s{+}h)-e_\alpha(s)]$$
und benutzt in **beiden** Summanden die Martingaleigenschaft: im ersten mit
$e_\alpha(s)$ als ${}^{*}\mathcal{F}^X_s$-messbarem Testfaktor, im zweiten mit
$\alpha(X_r)e_\alpha(r)$ als ${}^{*}\mathcal{F}^X_r$-messbarem.

> **Abweichung von EK86.** Der zweite Term kommt bei mir als
> $\int_s^{s+h}\int_r^{s+h}\!E[g(X_v,\cdot)\alpha(X_r)\cdots]\,dv\,dr$ heraus,
> also mit $g$ zur **späteren** Zeit, während die frühere Fassung des Manuskripts
> (EK86 (44) folgend) $\int_s^r$ hatte. Beide sind $O(h^2)$ und für den Beweis
> gleichwertig; ich habe die Fassung hingeschrieben, die aus meiner Zerlegung
> folgt und die ich belegen kann.

Schritt 3: $|T_2|,|T_4|\le\frac12h^2e^{C_T}E[\Gamma_T]$, beide aus derselben
Schranke; für $T_4$ über $e_\alpha(s)-e_\alpha(r)=-\int_s^r\alpha e_\alpha$.
Schritt 4: die Hauptterme **teleskopieren exakt**, es wird gar kein Limes
gebraucht — nur die Fehlersumme
$\frac12 e^{C_T}E[\Gamma_T]\sum(s_i-s_{i-1})^2 \le \frac12 e^{C_T}E[\Gamma_T]\,s\max_i(s_i-s_{i-1})\to0$.

**2.2d — lokale Eindeutigkeit, neu als §5.3.** Nach J&S III.2.37/2.40, über das
**Zusammenkleben**. Def. 5.23 (lokale Eindeutigkeit), Def. 5.24 mit drei
Hypothesen an den Pfadraum, Lem. 5.25 (Pasting), Thm. 5.26.

* **(P1) strikte Stoppzeit**: $\mathcal{F}^\circ_T = a_T^{-1}(\mathcal{S})$ für den
  Stoppoperator $a_T$ — J&S Lem. III.2.43. Genau *einmal* gebraucht, dafür
  unentbehrlich.
* **(P2) Konkatenation** $\gamma(\alpha,\beta)$ mit $\theta_T\gamma=\beta$.
* **(P3) volles Shift-System**: Def. 5.5 gibt eine Inklusion, das Kleben braucht
  die andere.

**Beweisidee (Lem. 5.25).** Zerlege $Y^\circ_t-Y^\circ_s$ in den bei $T$
gestoppten Teil (I) und den Rest (II). (I) verschwindet auf $\{T\le s\}$, und auf
$\{T>s\}$ stimmt der geklebte Pfad bis $s$ mit $\alpha$ überein, also ist der
Erwartungswert der $P$-Erwartungswert und verschwindet. Für (II) liefert (P3)
$$(\mathrm{II}) = \bigl(\hat Y^\circ_{(t-T)^+}-\hat Y^\circ_{(s-T)^+}\bigr)\circ\theta_T,$$
wobei sich $\kappa$ auf $\{T\le s\}$ gegen sich selbst und auf $\{T>s\}$ gegen
$\hat Y^\circ_0$ weghebt. Dann bedingt auf $\mathcal{F}^\circ_T$: auf $\{T>s\}$
ist $W\mathbf{1}_{T>s}$ $\mathcal{F}^\circ_T$-messbar, auf $\{T\le s\}$ ist es
$\mathcal{F}^\circ_T\vee\theta_T^{-1}(\mathcal{F}^\circ_{s-T})$-messbar — in
beiden Fällen greift die Martingaleigenschaft unter $P_{x,T}$.

Thm. 5.26 ist dann drei Zeilen: Pasting gibt $Q\in\mathcal{M}(\mathbb{X}^\circ,\mu)$
mit $Q=P$ auf $\mathcal{F}^\circ_T$; Eindeutigkeit bestimmt $Q$ aus $\mu$; also
ist $P|_{\mathcal{F}^\circ_T}$ aus $\mu$ bestimmt.

**Rem. 5.27** hält fest, wo die neue Struktur sitzt: alles vor §5.3 braucht nur
den Shift $\theta_r$; lokale Eindeutigkeit braucht dessen **partielle Inverse**,
die Konkatenation. Das ist eine echte neue Annahme an $F$ und folgt aus nichts
Vorherigem — $\theta_r$ vergisst die Vergangenheit, und kein Vergessen
rekonstruiert ein Klebeverfahren.

### D27 — Der càdlàg-Raum ist schon formalisiert: `brownian-motion`  *(2026-08-24)*

Der Nutzer erinnerte sich, jemand habe den càdlàg-Raum bereits formalisiert, und
vermutete das Projekt **Tau Ceti**. Nachgesehen:

* **Mathlib v4.33.1**: nichts. Kein `cadlag`, kein `Skorokhod`; `docs/1000.yaml`
  führt „Skorokhod's representation theorem" **ohne** `decl:`-Feld, also als
  *unformalisiert*. Vorhanden ist nur `Topology/Order/LeftRightLim.lean`
  (`leftLim`, `rightLim`, Gouëzel).
* **TauCeti** (`TauCetiProject/TauCeti`, 4303 Dateien): **nichts**. Weder im
  Dateibaum noch in Code-Suche noch in Issues. Der dortige `Probability/…/PathSpace`
  ist $E^{\mathbb{N}}$ für Austauschbarkeit, nicht $D_E$.
* **Treffer: `RemyDegenne/brownian-motion`** — das Repo zu Degenne–Ledvinka–Marion–**Pfaffelhuber**,
  arXiv:2511.20118:
  - `StochasticIntegral/Cadlag.lean` (236 Z., **0 sorries**): `IsRightContinuous`
    über `[Preorder ι]`, `IsCadlag` als Structure, `leftJumpSet`,
    `largeLeftJumpSet`, keine Häufungspunkte großer Sprünge, endlich viele auf
    Kompakta, lokale Beschränktheit, Abschlusseigenschaften.
  - `Quasimartingale/CadlagModification.lean` (1162 Z., 4 sorries) mit
    `Submartingale.exists_cadlag_modification_iff_rightContinuous` und
    `Martingale.exists_cadlag_modification` — **das sind Fact 2.17 und Fact 2.18
    meines Manuskripts**, und zwar für *Quasimartingale*, also allgemeiner als
    hier gebraucht.

**Drei Konsequenzen**, als Rem. 8.1 ins Manuskript:

1. (F4) verliert seine teuerste Voraussetzung. Die §8-Liste „to be built" ist
   entsprechend korrigiert.
2. Der Index dort ist eine Präordnung mit Ordnungstopologie — das ist mein Bündel
   (T2b). Zwei unabhängige Entwicklungen treffen dieselbe Wahl.
3. **Der Skorokhod-Raum fehlt weiterhin**: kein $J_1$, kein
   $\mathcal{B}(D_E)=\sigma(\pi_t)$, kein Kompaktheitskriterium. (F5b) ist
   unberührt, Fact 2.35 und Fact 2.36 bleiben zu bauen.

`BM25` ist in die Bibliographie aufgenommen.

### D28 — Q5 und Q8 entschieden  *(2026-08-24)*

**Q5 — Ablage.** Manuskript, `PLAN.md` und `FORTSCHRITT.md` liegen jetzt in
`Journal/Blog/MartingaleProblem/`; `Journal/Notes/MartingaleProblem/` ist geleert
und den Lean-Dateien vorbehalten. Das passt zu `CLAUDE.md`, wo `Journal/Blog/`
als Ort für `.md`-Notizen außerhalb des Lean-Builds beschrieben ist. Die
Hilfsdateien (`.aux`, `.log`, `.out`, `.toc`) sind nicht mitgezogen, sondern
gelöscht — sie werden beim Übersetzen neu erzeugt. **Task 3 ist entblockt.**

**Q8 — beide Konventionen.** Statt zu wählen, werden beide geführt.

Def. 2.2 definiert jetzt **zwei** Unterhalbmengen,
$$\mathbb{T}_{\le t}=\{u: u\le t\},\qquad
\mathbb{T}_{<t}=\mathbb{T}_{\le t}\setminus\{u: t\le u\},$$
und daraus das **optionale** Intervall
$(s,t]=\mathbb{T}_{\le t}\setminus\mathbb{T}_{\le s}$ und das **prädiktable**
$[s,t)=\mathbb{T}_{<t}\setminus\mathbb{T}_{<s}$. Beide $t$-Familien sind monoton,
also sind **beide Intervalle additiv** — das ist die einzige Eigenschaft, die die
meisten Beweise benutzen. Notation $\langle s,t\rangle_\iota$ mit
$\iota\in\{\mathrm{o},\mathrm{p}\}$; Def. 3.5 trägt $\iota$ als Parameter,
$\mathbb{X}^\iota_A(X)$.

Die zweite Unterhalbmenge ist bewusst so definiert, dass sie auf einer
**Präordnung** funktioniert: $\mathbb{T}_{<t}$ entfernt die ganze
Äquivalenzklasse von $t$, nicht nur den Punkt. Auf $\mathbb{N}_0$ gibt das
$\{0,\dots,n-1\}$, auf $\mathbb{R}_+$ mit Atom in $a$ das $[0,t)$, auf
$\mathbb{R}_+^d$ mit Lebesgue keinen Unterschied.

**Der Preis ist überraschend klein, und das ist kein Zufall.** Die beiden
Konventionen trennen sich an **genau zwei** Sätzen des ganzen Manuskripts:

* **Thm. 4.3** braucht $\iota=\mathrm{o}$ — ein Atom in $t$ muss innerhalb des
  Kompensators bis $t$ liegen, sonst gilt (R3) nicht, und genau dieser Limes
  macht die càdlàg-Version zu einer *Modifikation*.
* **Prop. 6.2** braucht $\iota=\mathrm{p}$ — sonst teleskopiert die
  Kettenidentität zu $\gamma(t,0)-\gamma(0,t)\ne0$ und die diskrete Dualität
  fällt aus.

Alles andere ist konventionsagnostisch, weil es den Kompensator nur über die
Additivität benutzt: §3 (einschließlich Prop. 3.7, deren Beweis das jetzt
ausdrücklich vermerkt), ganz §5 — und, was ich vorher nicht gesehen hatte,
**auch Lem. 6.1**. Der analytische Kern von §6 ist konventionsfrei; nur seine
*Folgerung* Prop. 6.2 ist es nicht. Das war das Argument, das die Entscheidung
„beide" billig gemacht hat.

Nachgezogen: Rem. 2.4 („Optional or predictable: both"), Rem. 6.3
(Konventionskollision, jetzt mit der Auflösung), eq. (2)
(${}^{*}\mathcal{F}^X$), Ex. 5.7 (geshiftetes Problem), die Verifikationen in
§4.2 und §5.4, die Bündeltabelle §2.9 (die $\iota$-Spalte erscheint nur, wo sie
zählt) und §8 (F3)/(F4). D10 und D14 sind damit überholt: D10 hatte $(0,t]$
gewählt, D14 den Preis benannt — die Entscheidung ist jetzt, keinen zu zahlen.

### D29 — Existenztheorie: vier Routen, §7 umgebaut  *(2026-08-24)*

**Anlass.** Der Nutzer merkte an, die Existenztheorie sei dünn. Zutreffend, und
quantifizierbar: Eindeutigkeit hatte Thm. 5.9, 5.11, 5.20, 5.26 plus ganz §6,
Existenz hatte **eine** Route (§7), und die ist konditional. Prop. 3.11 geht
sogar in die falsche Richtung. Es gab im ganzen Manuskript **keine Stelle, an der
eine Lösung hingeschrieben wird.**

§7 heißt jetzt „Existence" und ordnet vier Routen: (a) aus einer
Übergangshalbgruppe, (b) explizite Konstruktion (Sprungprozesse), (c) aus SDEs,
(d) durch Konvergenz (das bisherige §7).

**Die Klammer.** (b) und (c) sind **dasselbe Argument auf zwei
Schwierigkeitsstufen: beide sind Picard–Lindelöf.** Bei (b) ist es eine
Gronwall-Abschätzung an der Erstsprunggleichung, bei (c) die Picard-Iteration für
eine Lipschitz-SDE; es unterscheidet sich nur der Raum, auf dem die Kontraktion
wirkt. Das steht in der Einleitung von §7 und ist der Grund, die beiden
nebeneinander zu stellen.

**(b) Sprungprozesse — der Kern, mit vollem Beweis.** Daten: Rate
$\lambda:E\to[0,\infty)$ messbar, Sprungkern $\mu$;
$Af(x)=\lambda(x)\int(f(y)-f(x))\mu(x,dy)$. Konstruktion: Sprungkette $(Y_n)$ mit
Kern $\mu$, unabhängige Exp(1)-Variablen, $\tau_{n+1}=\tau_n+\varepsilon_{n+1}/\lambda(Y_n)$.

Der Beweis von Thm. 7.5 ist drei Schritte, und **Schritt 2 ist der ganze Satz**:
zerlegt man
$$M_t=\sum_n\Bigl[(f(Y_{n+1})-f(Y_n))\mathbf{1}_{\tau_{n+1}\le t}
- Af(Y_n)\bigl((\tau_{n+1}\wedge t)-(\tau_n\wedge t)\bigr)\Bigr],$$
so ist mit $x=Y_n$, $a=t-\tau_n$:
$$E[(f(Y_{n+1})-f(Y_n))\mathbf{1}_{\tau_{n+1}\le t}\mid\mathcal{H}_n]
=(\mu f(x)-f(x))(1-e^{-\lambda a}),$$
$$Af(x)\cdot E[(\tau_{n+1}\wedge t)-\tau_n\mid\mathcal{H}_n]
=\lambda(\mu f(x)-f(x))\cdot\frac{1-e^{-\lambda a}}{\lambda},$$
und das ist **exakt dasselbe**. Der Faktor $\lambda$ im Generator hebt sich gegen
den Erwartungswert $1/\lambda$ der Haltezeit weg. Zwei Zeilen, keine
Halbgruppentheorie, kein Punktprozess-Kompensator.

**Eindeutigkeit (Prop. 7.6)** kommt aus §5, und der Input ist Gronwall an der
Erstsprunggleichung
$v(t,x)=e^{-\lambda t}f(x)+\int_0^t\lambda e^{-\lambda s}(\mu v(t-s))(x)ds$:
zwei beschränkte Lösungen haben Differenz $w$ mit
$\|w(t)\|\le\bar\lambda\int_0^t\|w(r)\|dr$. Damit sind die eindimensionalen
Verteilungen bestimmt, und Thm. 5.9 liefert den Rest. **Das ist der erste Ort im
Manuskript, an dem die Eindeutigkeitsmaschinerie tatsächlich benutzt wird.**

**Drei Abstraktionen werden dadurch validiert** (Rem. 7.9):

* **(E0) genügt.** $\lambda$ messbar, $\mu$ ein Kern — keine Topologie, keine
  Metrik. Sprungprozesse auf einem standard-borelschen $E$, etwa auf einem Raum
  von Maßen oder Distributionen, sind von Thm. 7.5 **wie es dasteht** abgedeckt.
  Diffusionen brauchen $E=\mathbb{R}^d$. Das ist der Beleg, dass Task 9 etwas
  trägt.
* **Explosion gibt Def. 5.13 endlich ein Beispiel** (Rem. 7.7). Bei unbeschränkten
  Raten ($E=\mathbb{N}$, $\lambda(n)=2^n$) ist $\zeta<\infty$; Schritt 2 ist eine
  *endliche* Rechnung und bleibt gültig, also ist $M^{\tau_n}$ Martingal, und
  $\tau_n$ ist ein **Pfadfunktional** — (L1) gilt *by construction*, genau wie
  Lem. 5.16 es vorhersagt. Bis hierhin war Def. 5.13 eine Hypothese ohne Beispiel.
* **Der diskrete Fall** (Rem. 7.8): ohne Haltezeiten bleibt die Kette, das ist
  $\mathbb{T}=\mathbb{N}_0$ mit Zählmaß, und $A=\mu-I$ gilt unter
  $\iota=\mathrm{p}$ — die konkrete Form von Rem. 2.4 und der Fall von Cor. 6.10.

**(c) SDEs — zitiert, wie vereinbart.** Fact 7.10 (Picard–Lindelöf), Fact 7.11
(Yamada–Watanabe), Fact 7.12 (Stroock–Varadhan = Kallenberg Thm. 32.7),
Cor. 7.13. Die Kette ist **dreigliedrig**, was oft verkürzt wird: Lipschitz gibt
*starke* Existenz und pfadweise Eindeutigkeit, Yamada–Watanabe macht daraus
schwache Existenz und Eindeutigkeit in Verteilung, erst Stroock–Varadhan
überträgt beides aufs MP.

Rem. 7.14 rechnet den Preis eines Beweises vor: Itô-Integral gegen ein stetiges
lokales Martingal, quadratische Variation, Kunita–Watanabe, Itô-Formel und
Lévy-Charakterisierung — Letztere ist das, was in Fact 7.12 aus einer MP-Lösung
zurück eine Gleichungslösung macht. Ein Kapitel, keine Sektion. Für die
Formalisierung ist die Lage besser als sie aussieht, weil `brownian-motion`
(D27) gerade stochastische Integration baut.

**§8 hat einen neuen Schritt (F0)** — bewusst außer der Reihe: die
Sprungprozesse sind das billigste Theorem mit echtem Inhalt im ganzen Manuskript
und könnten **vor** (F1) gemacht werden, um die Definitionen an etwas Konkretem
zu prüfen.

**Zum Umfang.** Das geht über die vier Zielresultate von `PLAN.md` hinaus: (b) ist
EK86 §4.2, (c) ist EK86 Kap. 5 bzw. SV79/Kallenberg 32. Vom Nutzer so gewollt,
und (c) ist deshalb bewusst nur zitiert.

### D30 — Feller-Prozesse: vorerst nicht  *(2026-08-24)*

**Frage des Nutzers.** Sollen Feller-Prozesse getrennt behandelt werden?
**Entscheidung: nein, vorerst nicht.** Manuskript unverändert.

**Begründung.** Die Frage ist Q4 in anderer Verkleidung, denn Feller-Theorie
*ist* Halbgruppentheorie: Definition über eine stark stetige positive
Kontraktionshalbgruppe auf $\hat C(E)$, Existenz über Hille–Yosida,
Pfadregularität über die Regularisierung von Resolventen-Supermartingalen. Genau
das hat D5 gestrichen, und Rem. 2.5 dokumentiert die Grenze.

Drei weitere Einwände:

* **Lokale Kompaktheit.** $\hat C(E)$ gibt es nur für lokalkompaktes $E$, und
  **D2 lehnt das ausdrücklich ab** — $E$ ist polnisch und nicht lokalkompakt,
  die compact containment condition übernimmt die Rolle. Feller wäre ein Schritt
  *zurück*. In der Abstufung (E0)–(E3) bräuchte es ein Bündel
  „(E2) + lokalkompakt", das sonst nirgends vorkäme.
* **Duplikat von §4**, in einem echt schwächeren Rahmen: Thm. 4.3 gilt für
  allgemeines polnisches $E$ unter compact containment.
* **Teilduplikat von §7.2**: Feller-Sprungprozesse sind ein Spezialfall von
  Thm. 7.5; die interessanten Feller-Beispiele gehören zu §7.3.

**Der eine echte Payoff ist ohnehin schon da.** Pfadregularität *ohne* compact
containment steht als **Rem. 4.8**: für lokalkompaktes separables $E$ mit
$\mathcal{D}(A)$ dicht in $\hat C(E)$ kann \eqref{eq:cc} entfallen, über die
Einpunktkompaktifizierung (EK86 Cor. 4.3.7). Fünf Zeilen, ohne eine Halbgruppe
zu definieren.

**Falls Q4 später doch aufgemacht wird**, dann nicht Feller allein, sondern als
**Paket mit EK86 Thm. 4.4.1 und Cor. 4.4.4** — dem Halbgruppen-Eindeutigkeits\-kriterium,
das D5 mit entfernt hat. Beide hängen an derselben Maschinerie; eines ohne das
andere zahlt den vollen Preis für die halbe Ausbeute. Umfang grob: ein neues
Kapitel-1-Material in §2.4, ein Abschnitt in §5, einer in §7 — sechs bis acht
Seiten und ein deutlich größeres Formalisierungsziel.

Eine Bemerkung, die diese Abwägung im Manuskript festhielte, war vorgeschlagen
und ist auf Wunsch des Nutzers **nicht** geschrieben worden; sie steht hier.

### D31 — Konvergenz von Prozessen auf verschiedenen Uhren  *(2026-08-24)*

**Frage des Nutzers.** Kann man Konvergenz von Prozessen haben, die auf
verschiedenen Uhren leben? **Ja**, und die Antwort zerfällt in drei Teile. Neu
als **§7.7 „Approximation on different clocks"**.

**1. Thm. 7.4 erlaubt es bereits — das hatte ich in D24 nicht ausgesprochen.**
Die Hypothesen (C1)–(C3) reden ausschließlich über die kanonische Version
$Y^\circ$ des **Limes**, ausgewertet entlang $X^n$. Die approximierenden
Martingalprobleme kommen im Satz überhaupt nicht vor — weder ihre Testprozesse
noch ihre Uhren. Verschiedene Uhren sind also kein Problem des Satzes, sondern
seiner *Verifikation*.

**2. Thm. 7.25 (Uhrenwechsel).** Approximanten mit eigener Uhr $q^n$ und eigener
Konvention $\iota_n$:
$Y^n_t=\xi^n_t-\int_{\langle 0,t\rangle_{\iota_n}}\psi^n_u\,q^n(du)$ Martingal.
Mit der **Uhrdiskrepanz**
$$\Delta^n_{s,t}=\int_{\langle s,t\rangle_{\iota_n}}\psi^n\,dq^n-\int_{\langle s,t\rangle_{\iota}}\psi^n\,dq$$
und (K1)–(K4) folgt (C3c). Der Beweis ist die Zerlegung
$R^n_r=Y^\circ_r(X^n)-Y^n_r$ in vier Terme, von denen jeder einzeln gegen null
geht; benutzt wird nur die Additivität \eqref{eq:clockadd} — die für **beide**
Konventionen gilt, weshalb $\iota_n\ne\iota$ nichts kostet.

Das ist CPS Thm. 5.4 ohne Kontrollvariablen; (K4) ist deren (5.10).

**(K4) ist nicht schwache Konvergenz $q^n\Rightarrow q$** (Rem. 7.26), sondern
Konvergenz **gepaart mit den Integranden**. Aus $q^n\Rightarrow q$ folgt sie
nicht, solange die $\psi^n$ nicht gleichgradig stetig sind — und im
Hauptbeispiel sind sie es gerade nicht (stückweise konstant). Deshalb steht sie
bei CPS als Hypothese.

**3. Ex. 7.27 — das Invarianzprinzip als Uhrenaussage.** Mit
$q^n=\frac1n\sum_k\delta_{k/n}$, $\iota_n=\mathrm{p}$, $q=\lambda$ und
$X^n_t=\Xi^n_{\lfloor nt\rfloor}$ für eine Markovkette mit Kern $P_n$: setzt man
$\xi^n=f(X^n)$ und $\psi^n_u=n(P_nf-f)(X^n_u)$, so ist \eqref{eq:approxclock}
**genau die Doob-Zerlegung**, weil $q^n(\{k/n\})=1/n$. Dann ist (K2) trivial,
(K3) die klassische Generatorkonvergenz $n(P_nf-f)\to Af$, und (K4) gilt, weil
$\psi^n$ auf jedem $[k/n,(k+1)/n)$ konstant ist: diskretes und
Lebesgue-Integral stimmen bis auf die zwei Randintervalle überein,
$|\Delta^n_{s,t}|\le\frac2n\sup|\psi^n|$.

> **„Reskalierte Markovkette konvergiert gegen Diffusion" ist in diesem
> Formalismus eine Aussage über Uhren.**

**Rem. 7.28 — was dafür bezahlt wurde.** Drei frühere Entscheidungen sind nötig,
um Ex. 7.27 überhaupt hinschreiben zu können, und keine wurde mit Blick darauf
getroffen:

* **Atome** (D7): ohne Uhr mit Atomen *ist* das MP der Kette kein
  Martingalproblem; man müsste die Kette in stetige Zeit interpolieren — genau
  das Manöver, das der Uhr-Begriff überflüssig macht.
* **Uhren als Maße auf $\mathbb{T}$** (D9): verschiedene Uhren auf *einem*
  $\mathbb{T}$ subsumieren verschiedene Zeitindexmengen, solange die sich
  einbetten — $\frac1n\mathbb{N}_0\subset\mathbb{R}_+$ trägt $q^n$, ein zweiter
  Indexraum wird nicht gebraucht.
* **Beide Konventionen** (D28): die Kette braucht $\iota=\mathrm{p}$, der Limes
  ist unter Lebesgue konventionsfrei. Hätte man eine fixiert, müsste man das
  halbe Beispiel umschreiben; so unterscheiden sich die beiden um
  $\psi^n_t q^n(\{t\})=(P_nf-f)(X^n_t)=O(1/n)$ und **waschen sich im Limes
  heraus**. Ein nachträgliches Argument für „beide führen".

**Nicht geliefert:** Straffheit. Thm. 7.25 setzt (C1) voraus; $X^n\Rightarrow X$
auf $D_E$ nachzuweisen ist die Skorokhod-Hälfte und bleibt zitiert.

### D32 — bp-Limes abgeschwächt: majorisierte Konvergenz genügt  *(2026-08-24)*

**Frage des Nutzers.** Wo wird der bp-Limes gebraucht, und kann man ihn nicht
durch geeignete Konvergenz unter dem Integral ersetzen? **Antwort: an genau einer
Stelle, und ja.**

**Der Befund.** bp taucht inhaltlich nur in Rem. 3.9(b),(c) auf (EK86
Prop. 4.3.1). Und **Fact 2.29 wurde in keinem einzigen Beweis zitiert** — die
beiden `\ref`s standen in der Verwendungstabelle und in der „to be built"-Liste;
selbst Rem. 3.9 verwies im Text nicht darauf. Von den vier Aussagen des Facts
wurde höchstens die erste gebraucht; bp-Dichtheit von $C_b$, der separable Fall
und die Identifikation mit der schwach-\*-Topologie waren **tote
Voraussetzungen**.

**Was das Argument wirklich braucht:** majorisierte Konvergenz in \eqref{eq:fdd},
sonst nichts. Der Testfaktor $\prod_k h_k(X(t_k))$ ist beschränkt.

**Umsetzung.**

* **Lem. 3.10 (Abschluss längs einer Lösung).** Konvergiert
  $f_n(X_t)\to f(X_t)$ in $L^1(P)$ und
  $\int_{\langle s,t\rangle_\iota}g_n(X_u)q(du)\to\int_{\langle s,t\rangle_\iota}g(X_u)q(du)$
  in $L^1(P)$, so löst $X$ auch das MP für $A\cup\{(f,g)\}$. Beweis: Grenzübergang
  in \eqref{eq:fdd}, zwei Zeilen.
* **Cor. 3.11.** bp-Konvergenz impliziert das — für **jede** Lösung, jedes $P$ und
  jede Uhr. Damit bleiben Rem. 3.9(b),(c) und EK86 Prop. 4.3.1 in voller Stärke
  erhalten.
* **Rem. 3.12** erklärt die Rolle des Begriffs, die im Text bisher fehlte:
  **bp ist die stärkste $X$-unabhängige Bedingung.** Die Majoranten hängen allein
  von der Folge ab, nicht vom Gesetz von $X$, nicht von der Uhr, nicht von der
  Konvention — und *genau das* macht Cor. 3.11 zu einer Aussage über **Operatoren**.
  Lem. 3.10 ist eine Aussage über eine **gegebene Lösung**: schwächer als
  Behauptung über $A$, stärker als Werkzeug.

**Eine Inkonsistenz, die dabei aufgefallen ist.** Def. 3.5 lässt
$A\subset M(E)\times M(E)$ zu und Prop. 3.7 setzt **Integrierbarkeit** von
$Y^{f,g}$ voraus, nicht Beschränktheit. Die bp-Abschließung lebt aber in
$B(E)\times B(E)$ und verengte das stillschweigend — mitten in §3. Lem. 3.10
repariert das.

**Aufgeräumt.** Fact 2.29 auf die eine gebrauchte Aussage zusammengestrichen, der
Rest als Rem. 2.30 mit der Notiz, dass er unbenutzt ist. Verwendungstabelle:
Fact 2.29 → „Cor. 3.11 only". §9-Liste: der bp-Punkt trägt jetzt den Zusatz, dass
er optional ist, weil die Arbeitsaussage Lem. 3.10 ist und das majorisierte
Konvergenz ist — in Mathlib vorhanden.

### D33 — Eindeutigkeit ist nicht Markovsch: §5 umsortiert  *(2026-08-25)*

**Frage des Nutzers.** Gibt es Eindeutigkeit nur im Markov-Fall? **Nein**, und
das Manuskript hat die Rollen vermengt: der Beweis von Thm. 5.9(b) lief über das
Restart-Lemma, also über das Shift-System — **musste es aber nicht**.

**Was die Induktion wirklich braucht.** Nur

> **(U)** $P=Q$ auf $\mathcal{F}^\circ_s$ $\Rightarrow$ $P=Q$ auf
> $\mathcal{F}^\circ_s\vee\sigma(\pi_t)$ für $s\le t$

— „Übereinstimmung pflanzt sich eine Koordinate weiter fort". Daraus folgt die
Eindeutigkeit direkt: aus der Induktionsvoraussetzung folgt via Dynkin
$P=Q$ auf $\mathcal{F}^\circ_{t_n}$ (die Produkte $\prod h_k(\pi_{t_k})$ sind
eine multiplikative Erzeugendenklasse), dann (U). **Kein $\theta_r$, kein
Restart, keine geshiftete Familie** — und die Positivitätsannahme $f_k>0$, die
nur zum Normieren der Dichte diente, fällt weg.

**Umsetzung.**

* **Def. 5.5** (propagation of agreement) und **Prop. 5.6** (Eindeutigkeit),
  bewusst für eine **beliebige Familie $\mathcal{N}\subset\mathcal{P}(F)$**
  formuliert, nicht für $\mathcal{M}(\mathbb{X}^\circ)$. Damit gilt sie ohne
  Zusatzarbeit auch für $\mathcal{M}_{\mathrm{loc}}$ — §5.3 muss nichts
  wiederholen.
* **Lem. 5.11**: Shift-System + eindimensionale Eindeutigkeit $\Rightarrow$ (U).
  Das ist der isolierte Restart-Schritt.
* **Thm. 5.12** bleibt, sein Teil (b) ist jetzt Lem. 5.11 + Prop. 5.6.
* **Rem. 5.13** mit der Tabelle: Eindeutigkeit braucht (U) — *nicht* Markovsch;
  (U) aus eindimensionalen Verteilungen und die Markoveigenschaft brauchen das
  Shift-System.

**Warum EK Markovsch aussieht.** Weil die Hypothese **unbedingt** formuliert ist,
über die eindimensionalen Verteilungen — und eine unbedingte Hypothese lässt sich
zu einem späteren Zeitpunkt nur durch Neustarten anwenden. Formuliert man sie
bedingt, wie (U), verschwindet die Markov-Struktur aus der Eindeutigkeitshälfte.

**Gewinn in der Bündeltabelle: (T4) fällt weg.** Prop. 5.6 braucht nur (T2a) —
die lineare Ordnung für die Ketten (Rem. 5.14) —, kein Monoid, keine Uhr.

**§5 neu sortiert**, damit der nicht-Markovsche Kern vorn steht:
§5.1 „Uniqueness without a Markov structure" (Mischung, Disintegration,
Propagation, Eindeutigkeit), §5.2 „The Markov layer: shift systems"
(Shift-System, Ex. 5.9, Restart, Lem. 5.11, Thm. 5.12, starke Markov),
§5.3 lokale Theorie, §5.4 lokale Eindeutigkeit, **§5.5 nicht-Markovsche
Testobjekte**, §5.6 der Markovsche Fall.

### D34 — Testobjekte aus CPS  *(2026-08-25)*

Auf Wunsch des Nutzers als **§5.5** eingebaut, um die Aufteilung zu prüfen statt
sie zu behaupten.

**Ex. 5.32 — Volterra-SDEs (CPS Ex. 3.13).** Pfadraum
$L^p_{\mathrm{loc}}(\mathbb{R}_+,\mathbb{R}^d)\times D(\mathbb{R}^k)$,
Testprozesse $f(\pi^Z_t)-\int_0^t Lf(\pi^X_s,\pi^Z_s)ds$ plus die
Volterra-Nebenbedingung. **Kein Shift-System**, und zwar aus einem Grund: der
Kern $K_{t-s}$ macht $\pi^X_t$ von der ganzen Vergangenheit von $\pi^Z$
abhängig; Shiften um $r$ erzeugt einen Kern, der auch $\pi^Z$ vor $r$ sieht, und
das kann kein $\mathbb{X}^\circ_r$ im Sinne von Def. 5.7 reproduzieren.

Was überlebt: Def. 3.2/3.3, Lem. 5.2, Lem. 5.3 (der Pfadraum ist polnisch, also
(E1)), **Prop. 5.6** — Eindeutigkeit in Verteilung *ist* (U), und Prop. 5.6 macht
daraus die Eindeutigkeit des ganzen Gesetzes —, und Thm. 7.4 (CPS §4.2 ist genau
ein Stabilitätssatz für VSDEs daraus). Was ausfällt: Thm. 5.12, Thm. 5.15,
§5.4 und ganz §6.

**Ex. 5.33 — Semimartingale mit pfadabhängigem Tripel (J&S Kap. III).** Hier ist
§5.3 **vollständig** verfügbar: das lokalisierende System aus Lem. 5.21 wird aus
den Testprozessen selbst gebaut und braucht keinen Shift — genau J&S III.2.8.
§5.4 dagegen nicht, weil das Zusammenkleben eine Shift-Operation ist. Das ist die
schärfste Illustration:

> **Lokalisierung ist nicht Markovsch, Neustarten schon.**

**Rem. 5.34** stellt die Zweiteilung des ganzen Manuskripts tabellarisch dar.
Links steht: ganz §3, ganz §4, ganz §7, die Eindeutigkeitshälfte von §5 und der
analytische Kern von §6. Rechts: das Shift-System und was darauf ruht — und
**jeder** Eintrag rechts hat eine Konklusion, die selbst Markovsch ist
(Markoveigenschaft, Reduktion auf eindimensionale Verteilungen, Pasting,
Dualität). Nichts davon wäre durch ein besseres Argument vermeidbar gewesen.

### D35 — Weak-strong convergence: warum sie bisher fehlte  *(2026-08-25)*

**Frage des Nutzers.** In CPS gibt es weak-strong convergence — wieso kommt sie
hier nicht vor?

**Antwort.** Weil Thm. 7.4 als CPS **Cor. 3.17** formuliert ist, dem Fall eines
**einpunktigen Kontrollraums**; nach CPS Rem. 2.2(i) ist weak-strong convergence
dort schlicht schwache Konvergenz. Das war eine bewusste Vereinfachung, stand
aber nur als Halbsatz in Rem. 7.23.

**Und es ist keine Randfrage, sondern hängt an den Atomen.** CPS §4.3 gibt das
Gegenbeispiel, und es ist genau unsere Situation: $q=\delta_1$,
$$F_t(\omega)=\int_{[0,t)}\omega(s)\,q(ds)=\begin{cases}0,&t<1\\ \omega(1-),&t\ge1\end{cases}$$
ist $J_1$-stetig für $t<1$ und **für jedes $t\ge1$ unstetig**
($\omega_n=\mathbf{1}_{[1-1/n,\infty)}\to\mathbf{1}_{[1,\infty)}$, aber
$F_t(\omega_n)=1\not\to0$). Es gibt also **keine dichte Menge $\Gamma$**, auf der
$F_t$ stetig wäre — (C3a) fällt nicht auf einer abzählbaren Ausnahmemenge aus,
sondern auf einer Menge vollen Maßes.

Damit ist das die **zweite** Stelle, an der Atome einen Preis fordern: bei der
Dualität war es die Wahl der Konvention (Rem. 6.3), hier ist es eine Verschärfung
des Konvergenzbegriffs.

**Eingebaut als §7.8.** Ex. 7.29 (das Gegenbeispiel), Def. 7.30 (weak-strong:
Stetigkeit nur in der zweiten Variablen, Messbarkeit in der ersten), Def. 7.31
($(P^n,P)$-Stetigkeit: Stetigkeit nur längs der Schnitte $A_\alpha$ und nur auf
einer Menge asymptotisch vollen Maßes), Fact 7.32 (Jacod–Mémin), Thm. 7.33,
Rem. 7.34 (was die Kontrollvariable tut: sie dominiert die Sprungzeiten, und auf
den Schnitten fallen $J_1$ und lokal gleichmäßige Topologie zusammen).

**Bemerkenswert am Beweis von Thm. 7.33:** es ist **nichts** zu ändern außer zwei
Zitaten. Schritte 0, 1, 2 von Thm. 7.4 bestehen jeweils daraus, den
Continuous-Mapping-Satz anzuwenden und dann mit gleichgradiger Integrierbarkeit
zur Konvergenz der Erwartungswerte aufzurüsten — und Fact 7.32 leistet beides in
einem, unter den schwächeren Hypothesen. Schritt 3 benutzt gar keine Stetigkeit.
Die ganze Arbeit steckt in Jacod–Mémin, das nicht bewiesen wird.

§7.7 und §7.8 sind damit ein Paar: die eine lockert (C3c), die andere (C3a) — die
beiden Hypothesen von Thm. 7.4, die in der Praxis ausfallen.

### D36 — Korrektur: der Neustart braucht den Shift nicht  *(2026-08-25)*

**Einwand des Nutzers.** „Ich verstehe nicht, wieso Neustart zur Markov-Annahme
führt. Wenn ich mir den ganzen Pfad merke, muss ich den Prozess doch ebenfalls
neu starten können." **Der Einwand trifft, und meine Erklärung in D33 war
falsch.**

Der Neustart ist voraussetzungsfrei. Neu als **Lem. 5.5**:

> $P\in\mathcal{M}(\mathbb{X}^\circ)$, $Z\ge0$ beschränkt und
> $\mathcal{F}^\circ_r$-messbar mit $E^PZ=1$. Dann ist $Z\cdot P$ **ab $r$**
> wieder eine Lösung: $E^{Z\cdot P}[Y^\circ_t\mid\mathcal{F}^\circ_s]=Y^\circ_s$
> für $r\le s\le t$.

Beweis: für $G\in\mathcal{F}^\circ_s$ ist $Z\mathbf{1}_G$ beschränkt und
$\mathcal{F}^\circ_s$-messbar, weil $r\le s$; also
$E^P[(Y_t-Y_s)Z\mathbf{1}_G]=0$. **Zwei Zeilen, kein Shift, keine
Markov-Struktur** — nur die Turmeigenschaft. Und wer die bedingten Gesetze selbst
will statt einer Umgewichtung, bekommt sie aus Lem. 5.3 (Disintegration):
$P(\cdot\mid\mathcal{F}^\circ_r)$ existiert für standard-borelsches $F$ und
besteht aus Lösungen ab $r$.

**Was der Shift wirklich leistet, ist eine *Umindizierung*.** Eine Hypothese über
**Anfangs**verteilungen — \eqref{eq:absonedim}, und ebenso EK86 Thm. 4.4.2 — lässt
sich auf das neu gestartete Objekt erst anwenden, nachdem dieses in einen bei $0$
beginnenden Prozess verwandelt wurde; und die Abbildung, die das tut, ist
$\theta_r$, die den Pfad vor $r$ **wegwirft**. Das ist die ganze Markov-Struktur
von §5.2:

> **nicht die Fähigkeit, neu zu beginnen, sondern die Forderung, dass Neubeginnen
> wie Beginnen aussieht.**

Def. 5.7 (Propagation) ist dieselbe Idee ohne Umindizierung: verglichen wird zur
Zeit $s$, wo die beiden Maße ohnehin übereinstimmen, also muss nichts nach $0$
transportiert werden. Deshalb ist Prop. 5.8 Markov-frei und Lem. 5.13 nicht.

Als **Rem. 5.6** dokumentiert; Rem. 5.15 und die Audit-Tabelle in Rem. 5.36
entsprechend korrigiert (Lem. 5.5 steht jetzt **links**, in der Markov-freien
Spalte).

### D37 — Hawkes-Prozesse und ihr Volterra-Limes (Task 15)  *(2026-08-25)*

Neu als **§7.9**. Zwei Teile, wie mit dem Nutzer vereinbart: Teil 1 bewiesen,
Teil 2 bedingt auf Straffheit und mit zitiertem Skalierungsresultat.

**Teil 1 — Sprungprozesse mit pfadabhängiger Rate (Setting 7.35, Thm. 7.37).**
Statt $\lambda(x)$, $\mu(x,\cdot)$ jetzt **prädiktable** Funktionale
$\Lambda(t,\omega)$, $\mu(t,\omega,\cdot)$, die nur von $\omega|_{[0,t)}$
abhängen. Die Haltezeit ist dann **nicht mehr exponentiell**; sie ist die erste
Punktzeit eines inhomogenen Poissonprozesses,
$$\tau_{n+1}=\inf\Bigl\{t>\tau_n:\int_{\tau_n}^t\Lambda(u,\omega^{(n)})du>\varepsilon_{n+1}\Bigr\}.$$

**Die Rechnung überlebt unverändert**, und das ist der Punkt. Mit
$A_n(u)=\int_{\tau_n}^u\Lambda(v,\omega^{(n)})dv$ ist die Sprungzeitdichte
$\Lambda_ue^{-A_n(u)}$ und die Überlebensfunktion $e^{-A_n(s)}$, also
$$E[(f(Y_{n+1})-f(Y_n))\mathbf{1}_{\tau_{n+1}\le t}\mid\mathcal{H}_n]
=\int_{\tau_n}^t\Lambda_ue^{-A_n(u)}(\mu_uf-f)\,du$$
$$E\Bigl[\int_{\tau_n}^{\tau_{n+1}\wedge t}\mathcal{A}_sf\,ds\Bigm|\mathcal{H}_n\Bigr]
=\int_{\tau_n}^t\Lambda_s(\mu_sf-f)\,e^{-A_n(s)}\,ds,$$
und das ist dasselbe. Es ist **dieselbe Aufhebung wie in Thm. 7.5** — Rate im
Generator gegen Überlebensfunktion der Haltezeit —, nur mit $\Lambda_ue^{-A(u)}$
statt $\lambda e^{-\lambda a}$. Thm. 7.5 ist der Fall konstanter Rate.

Verschwunden ist allein die Markov-Struktur, und mit ihr das Shift-System:
Thm. 7.37 liefert Lösungen, auf die **Prop. 5.8 anwendbar ist und Thm. 5.12
nicht** (Rem. 7.38). Damit hat die nicht-Markovsche Schicht endlich ein
konstruiertes Beispiel statt nur zitierter.

**Ex. 7.39 — Hawkes.** $\Lambda(t,\omega)=\mu_0+\int_{[0,t)}\phi(t-s)d\omega_s$.
Für $\|\phi\|_1<1$ keine Explosion; für $\|\phi\|_1\ge1$ das lokale Problem,
lokalisiert durch die Sprungzeiten. **Kein Defekt, sondern der Punkt:** der
interessante Skalierungslimes lebt bei $\|\phi\|_1\uparrow1$, also genau dort, wo
§5.3 gebraucht wird.

**Teil 2 — der Limes. Die Beobachtung, die alles trägt (Rem. 7.40):**

> **Ein Hawkes-Prozess *ist* eine Volterra-Gleichung.**

Mit $Z=N$, $X=\Lambda$ lautet \eqref{eq:hawkesrate} wörtlich
$X_t=g_0(t)+\int_{[0,t)}K_{t-s}dZ_s$ mit $g_0\equiv\mu_0$, $K=\phi$ — die
Nebenbedingung aus Ex. 5.34 —, und $Z$ ist ein Semimartingal mit von $X$
gesteuerten Charakteristiken, $a=0$, $\nu(x,dy)=x\delta_1(dy)$. Approximanten und
Limes sind also Elemente **einer** Lösungsmenge, für zwei Tripel derselben
Bauart: eines rein unstetig, eines stetig. Die Konvergenz ist damit keine
Analogie, sondern eine Anwendung.

**Thm. 7.41** formuliert sie als Anwendung von Thm. 7.4 (Identifikation) plus
**Prop. 5.8** (Eindeutigkeit des Limes — und die *muss* nicht-Markovsch sein,
weil ein Volterra-Prozess es nicht ist).

**Rem. 7.42, Abgrenzung.** Straffheit wird vorausgesetzt, hier wie überall in §7;
für Hawkes $\to$ rauhe Volterra ist sie die eigentliche Substanz
(Jaisson–Rosenbaum, `JR16`, jetzt in der Bibliographie), zitiert statt bewiesen.
Ferner: **weak-strong wird nicht gebraucht** (Sprunghöhe 1, stetiger Limes, also
keine festen Unstetigkeitsstellen), und **die Uhr wechselt nicht**, wenn man den
zeitstetigen Prozess reskaliert — §7.7 käme erst bei diskreten Approximanten ins
Spiel. Und der eigentliche Befund: **kein einziges Resultat aus §5.2 wird
benutzt.** Weder Approximanten noch Limes haben ein Shift-System, und keines wird
gebraucht.

**Nebenbei:** die Bündeltabelle in §2.9 war zu lang geworden und lief über den
Seitenrand; sie ist jetzt in drei Blöcke geteilt.

### D38 — Task 16: lokale Eindeutigkeit ohne Shift  *(2026-08-25)*

D36 hatte gezeigt, dass der Neustart keinen Shift braucht. §5.4 benutzte aber
weiter einen über den **Zustand** indizierten Kern $P_{x,r}$ plus Konkatenation
plus volles Shift-System. Das ist jetzt aufgelöst — und der Beweis wird dabei
**kürzer**, nicht länger.

**Die Änderung.** Statt (P1)/(P2)/(P3) nur noch zwei Dinge:

* **Def. 5.30** — strikte Stoppzeit, $\mathcal{F}^\circ_T=a_T^{-1}(\mathcal{S})$.
  Neu ausdrücklich vermerkt: daraus folgt $T\circ a_T=T$, die Stoppzeit ist durch
  den gestoppten Pfad bestimmt.
* **Def. 5.31 (Restart-Kern)** — ein Kern $\alpha\mapsto Q_\alpha$ von
  $(F,\mathcal{F}^\circ_T)$ nach $(F,\mathcal{S})$ mit (R1)
  $Q_\alpha\{a_T\beta=a_T\alpha\}=1$ (die Vergangenheit wird behalten) und (R2)
  $Y^\circ$ ist unter $Q_\alpha$ ab $T(\alpha)$ ein Martingal. **(R2) ist genau
  die Konklusion von Lem. 5.5.**

**Lem. 5.32 (Pasting mit Gedächtnis).** $Q=\int Q_\alpha P(d\alpha)$ löst das
volle Problem und stimmt auf $\mathcal{F}^\circ_T$ mit $P$ überein. Keine
Konkatenation — die $Q_\alpha$ leben schon auf $F$ und stimmen schon bis $T$ mit
$\alpha$ überein.

**Warum der Beweis kürzer wird.** Wegen $T\circ a_T=T$ ist $T$ unter $Q_\alpha$
**f.s. deterministisch**, gleich $T(\alpha)$. Damit entfallen Optional Sampling,
die Fallunterscheidung über $(t-T)^+$ und das Wegheben von $\kappa$ gegen
$\hat Y^\circ_0$; es bleiben zwei Fälle, $r\le s$ und $r>s$, beide direkt aus
(R2).

**Thm. 5.33** unverändert in der Aussage, **Cor. 5.34** ist der Markovsche Fall:
aus einem vollen, messbaren Shift-System, einem Kern $(P_{x,r})$ und einer
Konkatenation baut man einen Restart-Kern. Das bisherige Lemma ist damit das
Korollar geworden, das es sein sollte.

**Was ehrlich eine Annahme bleibt (Rem. 5.35).** Die *Existenz* eines
Restart-Kerns. Anders als der Neustart aus Lem. 5.5, der eine vorhandene Lösung
nur umgewichtet, muss das Kleben Lösungen nach $T$ für **jede mögliche
Vergangenheit** *liefern*; und die bedingten Verteilungen einer Lösung des vollen
Problems helfen nicht, weil deren Konstruktion gerade das Ziel ist. Das ist die
einzige Stelle in §5, an der etwas von außen gegeben werden muss.

**Folgen für die Audit-Tabelle.** §5.4 wandert von der Markov- in die
Markov-freie Spalte; nur Cor. 5.34 bleibt rechts. In Ex. 5.35 (pfadabhängige
Semimartingale) war die Aussage „§5.4 ist nicht verfügbar, weil Pasting eine
Shift-Operation ist" **falsch** und ist korrigiert: §5.4 ist verfügbar, sobald ein
Restart-Kern vorliegt, und das ist eine Anforderung an die *Daten*, keine
Markov-Hypothese — J&S weisen sie in ihrem Rahmen nach. Der Merksatz
„Lokalisierung ist nicht Markovsch, Neustarten schon" ist damit überholt und
gestrichen: **auch das Kleben ist es nicht.** Ebenso Rem. 5.23(ii) und die
Aufzählung in Ex. 5.34.

### D39 — Task 17: Konsistenz-Durchgang, gefundene Fehler  *(2026-08-25)*

Der Durchgang „jedes Argument prüfen" hat mehr gefunden als erwartet. Die
Befunde, nach Schwere geordnet.

**(1) §6 — die zentrale These war falsch.**
Bisher stand da: Dualität brauche eine *translationsinvariante* Uhr (Haar), und
das sei scharf; Prop. „haar"(c) führte $q=\delta_a$ als Gegenbeispiel an, und
Rem. „conventionclash" behauptete, in der Konvention $(0,t]$ scheitere die
diskrete Dualität.

**Beides ist falsch.** Der Fehlschluss: aus „die Blöcke in \eqref{eq:cancel}
heben sich auf der *arithmetischen* Antidiagonalen nicht auf" folgt nicht, dass
$\Phi(t,0)-\Phi(0,t)\ne 0$ ist. Ein einzelner Treppenzug, der nicht kollabiert,
ist kein Gegenbeispiel.

Nachgerechnet (symbolisch, sympy):
* $q$ rein atomar auf einem linear geordneten $\T$, beliebige Massen $m_k$,
  bis $n=5$ Atome: $\Phi(t,0)-\Phi(0,t)=0$, **exakt**, in *beiden* Konventionen.
* Ebenso auf dem *nicht* linear geordneten Index $\{0,1,2\}^2$.
* Grund: $\gamma$ ist **eine** Funktion zweier Variabler und wird an jedem
  Atompaar $(a_k,a_l)$ von *beiden* Darstellungen gleichzeitig festgelegt. Bei
  gleichen Massen sagen diese Relationen genau, dass $\Phi$ auf den
  Antidiagonalen des Atomgitters konstant ist.

**Die Korrektur.**
* Lem. „chain" verallgemeinert auf beliebige **Treppenzüge** $(s_k,t_k)$ statt
  Antidiagonalen. Damit fällt (T4) dort *ganz* weg — die Kettenidentität lebt auf
  (T0).
* Neu **Lem. „rectify"** (Rektifikation der Uhr): unter (T2b) ist jede Uhr durch
  die Zeittransformation $Q(s)=q(\T_{<s})$ plus affine Interpolation über die
  Atome auf das Lebesgue-Maß auf einem Intervall zurückzuführen.
* Neu **Thm. „anyclock"**: *jede* Uhr lässt Dualität zu, für $Q$-f.a. $t$, unter
  der Integrierbarkeit von Lem. „calculus".
* Prop. „haar" behält (a) und (b) — beide waren korrekt — und heißt jetzt
  ehrlich „Haar clocks": das sind die Fälle, in denen der *arithmetische*
  Treppenzug funktioniert.
* Rem. „haarrole", Rem. „atomicdual" und Rem. „dualscope" neu bzw. neu
  geschrieben. Rem. „conventionclash" ist ersatzlos gestrichen; §6 ist
  konventionsagnostisch.
* Offen bleibt: nicht-atomare Uhr auf nicht-linearem Index. Nichts im Manuskript
  hängt daran.

**Konsequenz für den Rest:** §1.2, §1.3, §2.9 (Bündeltabelle, drei neue Zeilen),
Rem. „dualischain" und §8 (F3) nachgezogen. Die Behauptung „Atome kosten an zwei
Stellen etwas" ist auf **eine** reduziert (§7.8, weak-strong convergence).

**(2) §5.3 — `lem:L1auto` benutzte keine Stoppzeiten.**
$\tau_n=\inf\{t:|Y_t|>n\}$ ist eine *offene* Debützeit und damit nur
$\mathcal{F}^\circ_{t+}$-Stoppzeit, **nicht** strikt: ein Pfad mit
$|Y_s|\le n$ auf $\T_{\le t}$ und $|Y_s|>n$ danach hat $\tau_n=t$, stimmt aber
auf $\T_{\le t}$ mit einem Pfad überein, der $n$ nie überschreitet. Def.
„localizing" verlangt aber strikte Stoppzeiten.

Ersetzt durch das **laufende Supremum**, $\tau_n=\inf\{t:S_t\ge n\}$ mit
$S_t=\sup_{s\le t}|Y_s|$; dann ist $\{\tau_n\le t\}=\{S_t\ge n\}$ und $S_t$ ist
über die abzählbar dichte Menge $D$ aus (T2b) $\mathcal{F}^\circ_t$-messbar. Der
Beweis hat jetzt vier Schritte; neu Rem. „strictdebut" zum Unterschied
strikt/rechtsstetig. Rem. „jsdiff"(iii) behauptete, die Zeiten seien „strikt by
construction, weil Pfadfunktionale" — das ist genau der Fehlschluss und ist
korrigiert.

**(3) `lem:localrestart` — $Z$ muss beschränkt sein.**
(L3) liefert eine Martingalidentität nur gegen *beschränkte* Testvariable, die
gestoppten Zuwächse liegen in keinem $L^p$, $p>1$. Außerdem ist das Lemma jetzt
— wie Lem. „restart" — zweistufig auf $(\Omega,\mathcal F,\mathbb G,P)$ formuliert,
weil Thm. „absuniq"(a) mit $Z=\mathbf 1_{F_0}$, $F_0\in\mathcal G_r$, arbeitet.
Def. „localizing" sagt jetzt, wie (L1)–(L3) auf einer Umgebungsfiltration zu
lesen sind, und wozu Striktheit dabei gebraucht wird.

**(4) `thm:absstrongmarkov` — die Mischung war nicht wohlgeformt.**
$R_2=\int P_{x,\tau}\,\mu_{F_0}(\dif x)$ mischt bei zufälligem $\tau$ über
*verschiedene* Probleme $\XX^\circ_r$ und löst dann keines. Die zweite Aussage
ist jetzt auf $\tau$ mit abzählbar vielen Werten eingeschränkt, der Beweis
partitioniert nach $\{\tau=r_j\}$. Im zeithomogenen Fall ist die Einschränkung
leer. Dazu Schritt 1 ausgeschrieben: $\tau+s$ ist Stoppzeit (via (T4)), und
optional sampling braucht gleichgradig integrierbare Zuwächse — neu Rem.
„strongmarkovscope".

**(5) Neu `lem:shiftembed`.** $r+\cdot$ ist unter (T4) eine Ordnungs*einbettung*
(nicht nur ordnungserhaltend), und unter (T2a) vertauscht sie mit $\wedge$. Das
wurde in `lem:localrestart` stillschweigend benutzt.

**(6) §5.4 präzisiert.** Messbarkeit des Ereignisses in (R1) braucht (E1);
Integrierbarkeitsvoraussetzung in Lem. „pasting" explizit; Term (I) sauber über
\eqref{eq:pastingI} statt „hängt nur über $a_T$ ab"; in Cor. „pastingmarkov" der
Filtrationstransport $\Filt^\circ_{r+u}=\theta_r^{-1}\Filt^\circ_u$ $Q_\alpha$-f.s.
ausgeschrieben.

### D40 — Task 17, §7: gefundene Fehler  *(2026-08-25)*

**(1) `ex:invariance` war falsch — und das ist der interessanteste Fund in §7.**
Behauptet war: die eingebettete Markovkette hat mit $\iota_n=\mathrm p$ und
$\psi^n_u=n(P_nf-f)(X^n_u)$ die Doob-Zerlegung als Martingal. In *stetiger* Zeit
ist das **kein Martingal**: der Kompensator $\int_{[0,t)}\psi^n\,q^n$ nimmt für
$t\in(m/n,(m+1)/n)$ schon den Summanden $k=m$ mit, während $f(X^n)$ noch bei
$\Xi_m$ steht — $Y^n$ fällt unmittelbar *nach* $m/n$ um $(P_nf-f)(\Xi_m)$, ohne
dass sich die Filtration ändert. Martingal ist es nur entlang des Gitters.

Reparatur: $\iota_n=\mathrm o$, Atome bei $k/n$, $k\ge1$, und **prädiktabler**
Integrand $\psi^n_u=n(P_nf-f)(X^n_{u-})$. Dann fallen Atom und Sprung zusammen.
Neu Rem. `embedflip`, das den Punkt isoliert. Das ist zugleich das **schärfste
Argument dafür, beide Konventionen zu führen**: dasselbe Objekt braucht
intrinsisch $\mathrm p$ (Rem. `jumpdiscrete`, $\T=\N_0$) und nach Einbettung in
$\Rp$ $\mathrm o$. Rem. `invariancepay`(iii) entsprechend umgeschrieben.

**(2) `prop:jumpwellposed` — Erstsprung-Gleichung nicht verfügbar.**
Der Beweis leitete \eqref{eq:firstjump} aus Prop. `fddchar` her. Das gibt sie
nicht her: `fddchar` charakterisiert endlichdimensionale Verteilungen, nicht
Sprungzeiten; \eqref{eq:firstjump} setzt voraus, dass die Lösung *ist*, was zu
zeigen wäre. Ersetzt durch die Picard-Iteration für den **beschränkten** Operator
$A$: $E[f(X_t)]=\int e^{tA}f\,\dif\nu$, mit $\lVert A^kf\rVert\le(2\bar\lambda)^k\lVert f\rVert$
und explizitem Restglied über dem Simplex. Neu Rem. `jumpgronwall`, die erklärt,
warum die Erstsprung-Route zirkulär wäre.

**(3) `thm:jumpMP` Step 3 war eine Skizze.** Jetzt fünf Schritte: $\lambda=0$
separat; Dominierung $\sum|D_n|\le2\lVert f\rVert N_t+\lVert Af\rVert t$ mit
$N_t$ stochastisch dominiert von Poisson($\bar\lambda t$); Markov-Eigenschaft der
Konstruktion explizit; dann $E[M_t-M_s\mid\Gilt_s]=0$.

**(4) `thm:pathjumpMP` brauchte $E[N_t]<\infty$.** Ohne das ist
$\int_0^t\mathcal A_sf\,\dif s$ nicht integrierbar und „ist ein Martingal" ist
inhaltsleer — und zwar auch dann, wenn $\zeta=\infty$ f.s. Jetzt zweiteilig: (a)
die **lokale** Aussage gilt unbedingt, weil
$\int_{\tau_k}^{\tau_{k+1}}\Lambda=\varepsilon_{k+1}$ (neu: \eqref{eq:compensatorexp});
(b) global unter $E[N_t]<\infty$, per Wald. Neu Rem. `pathjumpprimary`.

**(5) `ex:atomicdiscontinuity` rechnete falsch.** $\int_{[0,t)}\omega\,\dif\delta_1
=\omega(1)\one_{\{t>1\}}$, nicht $\omega(1-)$; und die Folge
$\one_{[1-1/n,\infty)}$ zeigt gar keine Unstetigkeit. Richtig ist
$\one_{[1+1/n,\infty)}\to\one_{[1,\infty)}$. Zusätzlich ergänzt: der Effekt tritt
nur ein, wenn $P\{X_1\ne X_{1-}\}>0$.

**(6) Kleinere Präzisierungen.** `lem:EKconv`: Stetigkeit des Integralterms und
die Rechtsapproximation ausgeschrieben. `thm:absconv`: $D$ muss das größte
Element von $\T$ enthalten (sonst scheitert Step 3 bei $\T=[0,T]$);
$(Y^\circ_sZ^\circ_s)$-Stetigkeit begründet; UI-Index in Step 3 fixiert.
`thm:CPSconv`: die Behauptung, Step 3 benutze \eqref{eq:cps1}, war falsch —
(C3b) kommt dort aus der Beschränktheit von $f,g$. `cor:sdewellposed`: das
lokalisierende System benannt.

### D41 — Task 18: Existenz aus einem Dualen, eingebaut  *(2026-08-25)*

\cite{DGP24} (Depperschmidt–Greven–Pfaffelhuber, TPB **159** (2024), 59–73) ist
jetzt §7.2 „From a dual process", mit Beweisen. Kopie in
`references/DepperschmidtGreven2019.pdf`.

**Aufbau.** Setting `dualdata` mit (D1) Balance in integrierter Form, (D2)
Separation, (D3) Kernel-Darstellbarkeit — Letztere für $H$ **und** $g$, weil
Schritt 2 des Beweises sie für beide braucht; das steht in DGP implizit über
$P_uG^X=G^XP_u$. Dann Lem. `dualsemigroup` (Halbgruppenidentität),
Prop. `dualCK` (Chapman–Kolmogorov), Thm. `exduality` (Existenz + Dualitäts-
relation), Cor. `exdualitywellposed` (Wohlgestelltheit), Prop. `rieszmarkov`
(Riesz–Markov als hinreichende Bedingung für (D3)). Neu Fact `kolmogorov`
(EK Thm. 4.1.1) in §2.6, da bisher nicht vorhanden.

**Drei Verallgemeinerungen gegenüber der Quelle**, jeweils belegt durch den
Beweis:
* **beliebige verschiebungsinvariante Uhr** — die Uhr geht nur über
  \eqref{eq:clockadd} und $q(\T_{\le t})<\infty$ ein (Letzteres macht den
  Feynman–Kac-Faktor beschränkt);
* **kein linear geordneter Index** — (T4) plus Kommutativität genügen; §7.2 ist
  damit das einzige Existenzresultat des Manuskripts, das $\T=\Rp^2$ überlebt;
* **(E1) statt kompakt** — Kompaktheit steckt allein in Prop. `rieszmarkov`,
  also im *Prüfen* von (D3), nicht im Satz.

**Der Kreis schließt sich:** dieselbe Dualitätsrelation wird zweimal benutzt —
vorwärts zur Konstruktion (Thm. `exduality`), rückwärts zur Eindeutigkeit
(Cor. `exdualitywellposed` über §6 und Thm. `absuniq`).

**Was nicht trägt:** \eqref{eq:dualityrel} ist eine Aussage über
eindimensionale Verteilungen aus einem festen Startpunkt, setzt also genau die
Markov-Struktur voraus, die §5.1/§5.4 vermeiden. Reparatur wäre DGP §5:
historischer Prozess, $E_1$ = Pfad- oder Genealogieraum. Als Task notiert, nicht
ausgeführt. Die zeitinhomogene Version (zwei-Parameter-$P_{r,t}$, Shift-System,
$q$-Reflexion statt $t-s$) ist in Rem. `exdualityscope` skizziert.

### D42 — weak-strong convergence weitgehend überflüssig  *(2026-08-25)*

Frage des Nutzers: ob die Argumente, die auf weak-strong convergence aufbauen,
mit einfacheren Mitteln gehen. **Ja, und zwar vollständig für alles, was im
Manuskript vorkommt.**

**Die Beobachtung.** Neu Lem. `contuse`: im Beweis von Thm. `absconv` werden
(C1) und (C3a) *ausschließlich* dazu benutzt, aus einem $P$-stetigen
$\psi:F\to\R$ die Konvergenz $\psi(X^n)\Rightarrow\psi(X)$ zu ziehen — für genau
drei Funktionale. Weder Filtration noch bestimmende Menge noch Konklusion hängen
davon ab. Also darf die Stetigkeit auf *irgendeinem* Raum verlangt werden, durch
den die Funktionale faktorisieren.

**Die Reparatur.** Neu Thm. `absconvaug`: mit $\hat F=F\times G$, $G$ polnisch,
$\gamma:F\to G$ borelsch und $\hat X=(X,\gamma(X))$ ersetzt man (C1) durch
$\hat X^n\Rightarrow\hat X$ und (C3a) durch $\hat P$-Stetigkeit auf $\hat F$.
Beweis: zwei Zeilen, alles andere unverändert.

**Der Fall der atomaren Uhr.** Neu Prop. `atomaug`: $G=E^A$ mit $A$ = Atome von
$q$, $\gamma(\omega)=(\omega(a))_{a\in A}$. Der atomare Summand von $Y^\circ$
wird dann **überall** stetig (gleichmäßig konvergente Reihe, da
$\sum_a m_a\le q(\T_{\le t})<\infty$), der diffuse Summand ist es ohnehin, und
übrig bleibt nur die klassische Ausnahmemenge der festen Unstetigkeitsstellen von
$X$ — dieselbe wie im atomlosen Fall, unabhängig von $A$.

**Warum das reicht.** Die Unstetigkeit sitzt an **deterministischen** Stellen.
CPS brauchen mehr, weil in ihrem §5.3 die kritischen Zeiten die *zufälligen*
Sprungzeiten der Approximanten sind; die fängt keine feste Koordinatenfamilie
ein. Rem. `augvsws` stellt beides in einer Tabelle gegenüber; die Trennlinie ist
deterministisch vs. zufällig.

**Bilanz.** Statt Def. `weakstrong`, Def. `PnPcont` und dem unbewiesen zitierten
Fact `jacodmemin` (Jacod–Mémin) nur noch Fact `cmt` und Fact `ui` — beide schon
da. Die weak-strong-Schicht bleibt stehen, aber als *Literaturbezug*, nicht als
Werkzeug. Damit ist auch die Behauptung aus D35 korrigiert, Atome erzwängen eine
Verschärfung des Konvergenzbegriffs: sie erzwingen eine gemeinsame
Konvergenzvoraussetzung (C1$'$), mehr nicht.

§7.8 heißt jetzt „Relaxing the continuity hypothesis"; Rem. `controlvars`,
Rem. `CPSabstract`, Rem. `hawkescaveat`, die Bündeltabelle und §8 (F5b)
nachgezogen.

### D43 — Task 17 abgeschlossen: §8, §9 und die Bündeltabellen  *(2026-08-25)*

**(1) Mathlib-Bestandsaufnahme war zu optimistisch — und das ist der wichtigste
Fund.** Fact `kolmogorov` behauptete, die Kolmogorov-Erweiterung liege in Mathlib
als `MeasureTheory.projectiveLimit` vor. Nachgeschaut in
`.lake/packages/mathlib` (v4.33.1): **falsch.** Vorhanden sind nur

* das Prädikat `IsProjectiveLimit` samt Eindeutigkeit
  (`MeasureTheory/Constructions/Projective.lean`),
* der Inhalt `projectiveFamilyContent` (`ProjectiveFamilyContent.lean`),
* `ClosedCompactCylinders.lean` (das Gerüst des klassischen Beweises),
* Ionescu–Tulcea `Kernel.traj` (`Probability/Kernel/IonescuTulcea/Traj.lean`) —
  ohne topologische Voraussetzung, aber nur für **sequentiellen** Index.

Der Kommentar in `ProjectiveFamilyContent.lean` sagt es ausdrücklich: „both
results are not yet in Mathlib". Damit ist Fact `kolmogorov` eine **echte
Vorleistung**, und (F6) zerfällt: für $\T=\N_0$ sofort machbar, für $\T=\Rp$
wartend. Nebenbei bestätigt: Riesz–Markov ist da
(`RieszMarkovKakutani/Real.lean`, `integral_rieszMeasure`), trägt also
Prop. `rieszmarkov`.

**(2) Die (F)-Liste war fehlnummeriert.** Die Labels hießen F1, F2, F3, F4, F5a,
F0, F3b, F5b, gedruckt wurde aber (F1)…(F8) in Reihenfolge — die Namen suggerierten
eine Ordnung, die der Druck nicht hatte. Jetzt in der empfohlenen
Arbeitsreihenfolge sortiert: F1 (Definitionen) → F0 (Sprungprozesse als
konkreter Test) → F2 (Eindeutigkeit) → F5a (abstrakte Konvergenz, mit
`contuse`/`absconvaug`) → F3 (Dualität) → F3b (Existenz aus dem Dualen) → F4
(càdlàg) → F5b (Skorokhod). Die drei Sätze, die auf die alte Reihenfolge
Bezug nahmen, umgeschrieben.

**(3) Design-Entscheidung (d) empfahl die verworfene Route.** Sie sagte, das
lokale MP solle über den gestoppten **Operator** $A^{(m)}$ abgeleitet werden.
Genau das hat §5.3 verworfen (Rem. `localsummary`: im abstrakten Setting ist
$\XX^\circ$ primitiv, $A$ nicht). Neu formuliert: Testprozesse lokalisieren,
(L1)–(L3) als wiederverwendbare Struktur, Lem. `L1auto` als das Lemma, das (L1)
*konstruiert*, plus Warnung vor nicht-strikten Stoppzeiten.

**(4) Design-Entscheidung (e) überzog.** „die einzige Stelle, wo Polnischkeit von
$E$ wirklich gebraucht wird" — stimmt nur für §4/§5; in §7 ist (E3) durchgehend
und unverzichtbar (Prohorov). Umformuliert. Neu (g) beide Konventionen und
(h) Augmentation vor weak-strong.

**(5) Bündeltabellen.** Stale Zeile `lem:chain` mit „(T0)+(T4), clock" in Tabelle 2
stand im **Widerspruch** zur Zeile derselben Lemma in Tabelle 3 („(T0), any") —
gelöscht. Präambel-Satz „die zwei $\iota$-Einträge sind die einzigen Stellen, wo
die Konventionen auseinandergehen" war nach D39/D40 falsch — neu gefasst
(nur §4 *braucht* seine Konvention). Neu: Zeilen für `lem:shiftembed`,
`contuse`/`absconvaug`, `atomaug`, und (E1)-Vermerk bei `localmix`(b).

**(6) Kleinere Nachzüge.** Abstract (iv): „the fourth" bei fünf Routen, und die
Dualitäts-Existenz fehlte. Rem. `Ebundleuse`(ii): (E1) wird an **fünf**, nicht
drei Stellen gebraucht (dazu `restartkernel` und `kolmogorov`). §1.3: das lokale
MP ist bei pfadabhängiger Rate *primär*, nicht nur allgemeiner; und §5.3 hat
drei Hypothesen, nicht zwei. Rem. `absconvcheck` auf `contuse` verwiesen.

**Task 17 ist damit vollständig.** Gesamtbilanz des Durchgangs: sechs echte
mathematische Fehler (D39: §6-These, `L1auto`, `localrestart`, `absstrongmarkov`;
D40: `ex:invariance`, `jumpwellposed`, `pathjumpMP`, `atomicdiscontinuity`), eine
falsche Bibliotheksbehauptung, eine fehlnummerierte Roadmap und eine
Design-Entscheidung, die der eigenen Theorie widersprach.

### D44 — Lem. `EKconv` hatte einen überflüssigen eigenen Beweis  *(2026-08-25)*

Frage des Nutzers: ob Lem. 7.23 (\EK{} 4.5.1) nicht eine Folgerung von Thm. 7.26
(`absconv`) sei. **Ja** — und das Manuskript behauptete es an drei Stellen (§1.2
Schicht 3, §7.5, §8 (F8)), gab dem Lemma aber trotzdem einen vollständigen
eigenständigen Beweis. Das widersprach der erklärten Architektur, nach der die
klassischen Resultate „Verifikationen von Hypothesen, keine Argumente" sein
sollen.

Nachgerechnet, dass die Herleitung wirklich durchgeht — je eine Hypothese pro
Bedingung, ohne Überlappung:

| Hypothese von Lem. `EKconv` | liefert |
|---|---|
| $X_n\Rightarrow X$ auf $\DE$ | (C1) |
| $A\subset\Cb\times\Cb$ | (C3a) |
| $f,g$ beschränkt | (C3b) |
| $\lVert f_n-f\rVert,\lVert g_n-g\rVert\to0$ | (C3c) |

Der Beweis ist jetzt diese Verifikation (Vorwärtsreferenz auf §7.6, bewusst).
Neu Rem. `EKconvcor`: EKs direktes Argument — „Stetigkeitszeiten $D(X)$, dort
Limes, per Rechtsstetigkeit fortsetzen" — ist wörtlich Step 1 und Step 3 von
Thm. `absconv`, ihr Konvergenzsatz-Aufruf ist dessen Steps 0 und 2 im Sonderfall
beschränkter $f,g$. Es geht nichts verloren, und gewonnen wird die
Arbeitsteilung: jede der vier Hypothesen kann jetzt einzeln abgeschwächt werden,
was Thm. `CPSconv` mit den letzten beiden und §7.8 mit (C3a) auch tut.

**Gegenprobe bei den anderen drei klassischen Resultaten.** Thm. `cadlag` (15
Zeilen) und Thm. `uniqueness` (45 Zeilen) sind reine Hypothesenverifikationen,
also in Ordnung. Thm. `duality` (110 Zeilen) ist keine Dopplung: die Rechnung
\eqref{eq:Fincrement}, die aus den Martingalvoraussetzungen die
Inkrementdarstellungen \eqref{eq:incrementrep} erzeugt, ist der einzige
probabilistische Teil von §6 und steht nirgends sonst.

Nebenbei: der Beweis von Thm. `uniqueness` beruft sich auf
Thm. `absstrongmarkov`, dessen zweite Aussage seit D39 auf abzählbarwertige
Stoppzeiten eingeschränkt ist. Hier ist die Einschränkung leer (konstantes
Shift-System), was jetzt dasteht.

### D45 — Fibrierter Zustandsraum: ja, von Anfang an  *(2026-08-25)*

Frage des Nutzers: bei der Formalisierung gibt es dependent types, der
Zustandsraum kann also mit $t$ variieren — soll das schon so angelegt werden?

**Antwort: ja.** Neu §2.3 Def. `Efibred`, Rem. `fibredaudit` (Audit),
Rem. `fibredrecommend` (Begründung), Design-Entscheidung (i) in §9.

**Der Audit ist das eigentliche Argument.** Die Trennlinie fällt *exakt* mit der
schon in Rem. `Ebundleuse` gezogenen zusammen — was $E$ nur über $\Bdd(E_t)$ und
$\mathcal E_t$ anfasst, ist gleichgültig; was eine Topologie auf $E$ braucht,
nicht:

* **frei:** §3.1 (abstraktes MP — erwähnt $E$ überhaupt nie), §3.2 mit $(f,g)$
  als Schnitten, §5.1, §5.2 (Shift-Systeme werden sogar *natürlicher*: $\theta_r$
  bildet $\prod_t E_t$ nach $\prod_t E_{r+t}$ ab, also ist $\XX^\circ_r\ne\XX^\circ$
  erzwungen), §5.3/§5.4, §6, §7.2;
* **braucht konstante Faser:** §4 (càdlàg vergleicht $\omega(s)$ mit $\omega(t)$)
  und §7.3–§7.9 ($\DE$, $J_1$, Straffheit);
* **braucht den Totalraum $\Sigma E=\coprod_t E_t$:** nur Thm. `absstrongmarkov`,
  weil $X(\tau)$ ein *abhängiger* Wert in $E_{\tau(\omega)}$ ist und
  $\mu_{F_0}=P\{X(\tau)\in\cdot\}$ daher auf dem Totalraum lebt.

**Drei Gründe, es jetzt zu tun.**
1. Es ist gratis, wo es zählt, und unerreichbar, wo nicht — die Entscheidung ist
   also nicht „wieviel Allgemeinheit", sondern „in welcher der beiden ohnehin
   getrennten Hälften", und die Antwort steht im Audit.
2. **Mathlib ist fibriert.** `IsProjectiveLimit`, `projectiveFamilyContent`,
   `Kernel.traj` sind alle für `α : ι → Type*` und `Measure (Π i, α i)`
   formuliert. Ein fixes `E` hieße überall `fun _ => E` schreiben und die
   abhängigen Aussagen von Hand nachbauen — dasselbe Argument wie bei
   `[Preorder ι]` in §1.3.
3. **Task 19 braucht es.** Der historische Prozess hat als Zustandsraum zur Zeit
   $t$ die Pfade auf $\T_{\le t}$ — ein fibrierter Zustandsraum, kein konstanter.
   Genealogiewertige Prozesse ebenso.

**Nebengewinn.** Wenn $f$ ein Schnitt sein darf, ist
$Y^{f,g}_t=f_t(\pi_t)-\int g_u(\pi_u)q(\dif u)$ automatisch das
**Raum-Zeit-Martingalproblem** ($g$ absorbiert $\partial_t f+Af$), das
Standardwerkzeug für zeitinhomogene Probleme. Das hätte sonst separat ergänzt
werden müssen. Zeitabhängiges $g$ war ohnehin schon da (Setting `diffclocks`).

**Was nicht getan wird:** §4 und §7.3–§7.9 in fibrierter Notation umschreiben.
Sie brauchen eine konstante Faser, sagen das, und die Bündeltabelle hält es fest;
einen Index mitzuschleppen, der sofort eingefroren wird, wäre Notation ohne
Inhalt.

### D46 — „Ist jeder Prozess Markov, wenn der Zustand der Pfad ist?"  *(2026-08-25)*

Frage des Nutzers. **Antwort: ja, trivial — und die Trivialität ist die Pointe.**
Neu §5.2: Def. `pathlift`, Lem. `liftmarkov`, Rem. `liftcollapse`.

**Die Rechnung.** Mit $\hat X_t=X|_{\T_{\le t}}$ gilt
$\sigma(\hat X_t)=\Filt^X_t$, also $\Filt^{\hat X}_t=\sigma(\hat X_t)$: die
beiden Bedingungs-$\sigma$-Algebren in der Markov-Eigenschaft sind **gleich**.
Es ist eine Identität von $\sigma$-Algebren, keine Eigenschaft von $X$. Für
strikte Stoppzeiten ebenso ($\Filt^\circ_T=a_T^{-1}(\mathcal S)$, Def. `pasting`)
— dabei braucht man den Totalraum $\Sigma\hat E$, weil der Faserindex den Wert
von $T$ trägt. Das ist genau der Punkt aus D45.

**Drei Kollapse.**
1. Thm. `absuniq`(a) behauptet vom Lift nur, was Lem. `liftmarkov` gratis gibt.
2. Die **eindimensionalen** Verteilungen von $\hat X$ sind die
   **endlichdimensionalen** von $X$. Also ist Hypothese \eqref{eq:absonedim} für
   den Lift die *Konklusion* von Thm. `absuniq`(b), und die Induktion über
   $t_1<\dots<t_n$ fällt auf ihre eigene Konklusion zusammen.
3. Auch §5.1 kollabiert: in Def. `propagation` durchläuft $h$ alle beschränkten
   messbaren Funktionen von $\hat\pi_s$, also alle beschränkten
   $\Filt^\circ_s$-messbaren Variablen — das absorbiert das Gewicht $Z$. Für den
   Lift heißt Propagation dann „$P=Q$ auf $\Filt^\circ_s$ $\Rightarrow$ $P=Q$ auf
   $\Filt^\circ_t$", bei $s=0$ also die Eindeutigkeit selbst.

**Das Prinzip.** Eine Markov-Struktur ist eine **Kompressionsaussage**: ihr Inhalt
ist die Lücke zwischen $\sigma(X_s)$ und $\Filt^X_s$, und die Sätze sind genau so
viel wert, wie diese Lücke breit ist. Der Lift erreicht die Markov-Eigenschaft,
indem er die Lücke schließt — und das ist dieselbe Operation wie das Löschen der
Sätze. Damit ist §5.1 nachträglich gerechtfertigt: es ist nicht eine schwächere
Theorie als „§5.2 auf den Lift angewandt", sondern dieselbe Theorie ohne die
Tautologie.

**Zwei Präzisierungen.**
* Die Trivialität ist **filtrationsrelativ**: Markov bzgl. der *eigenen*
  Filtration ist automatisch, Lösung bzgl. eines größeren $\mathbb G$ nicht —
  ein Grund mehr für die zweistufige Formulierung von Lem. `restart`.
* Der Lift ist nicht nutzlos, nur hier nutzlos. Wo der Inhalt woanders sitzt,
  ist er ein echtes Werkzeug: in §7.2 sitzt er in (D3), einer Aussage über den
  **Dualen** auf unverändertem, typisch kleinem Raum. Deshalb ist Task 19
  (historischer Prozess) sinnvoll und Task „Lift für Eindeutigkeit" nicht.
  Nebenbei: der Lift ist nie zeithomogen, lebt also zwingend im fibrierten
  Rahmen von D45.

### D47 — Task 19 durchdacht: Struktur, ein Lemma, ein Testobjekt  *(2026-08-25)*

Neu am Ende von §7.2: Setting `historical`, Lem. `histrestart`,
Rem. `histbuys`, Rem. `histobstruction`, Rem. `histhawkes`. Als **Programm**
gekennzeichnet, nicht als Satz.

**Was sich ändert** — und zwar in die Richtung, auf die das Manuskript schon
vorbereitet ist: $E_1$ wird fibriert ($\hat E_t$, das ist D45), das Problem ist
zwingend zeitinhomogen (die Fasern wachsen), also ist die Zwei-Parameter-Version
aus Rem. `exdualityscope` hier nicht optional; und der Duale läuft typischerweise
**rückwärts**, also erscheint die $q$-Reflexion aus Rem. `haarrole`.

**Das eine, was sich beweisen ließ.** Lem. `histrestart`: erfüllen die Kerne
$\mu_{r,t}$ die Zwei-Parameter-Form von (D3), und gibt es Dualitätsfunktionen,
die (i) nur die Vergangenheit bis $r$ lesen, (ii) unter der dualen Dynamik in
Ruhe sind und (iii) auf $\Prob(\hat E_r)$ separieren, dann gilt
$\mu_{r,t}(\hat x,\cdot)\circ\rho_{r,t}^{-1}=\delta_{\hat x}$ — **der Kern behält
die Vergangenheit**, ist also ein Restart-Kern im Sinne von Def. `restartkernel`.

Das ist mehr als eine technische Beobachtung. Rem. `pastingassumed` hält fest,
dass die Existenz eines Restart-Kerns „die eine Stelle in §5 ist, an der etwas
von außen gegeben werden muss", und §5.4 hat bisher **kein** nicht-Markovsches
Beispiel: Cor. `pastingmarkov` baut ihn aus einem Shift-System, das ein
pfadabhängiges Problem gerade nicht hat. Eine historische Dualität lieferte
einen — aus dem **Dualen**, ohne Shift. Damit wären Thm. `localuniqueness`
(lokale Eindeutigkeit im Sinne von J&S III.2.37) und Prop. `uniqfromprop`
(Eindeutigkeit in Verteilung) für ein pfadabhängiges, per Dualität konstruiertes
Problem verfügbar.

**Die Obstruktion, benannt.** Es ist (D3), genauer der *Weg* dorthin.
Prop. `rieszmarkov` braucht $E_1$ kompakt; ein Pfadraum ist polnisch, aber weder
kompakt noch — bei Genealogien — lokalkompakt. Ersatz ist eine
**Transformcharakterisierung** statt Riesz–Markov: DGP Prop. 2.8 abstrakt,
DGP Bsp. 6 konkret (negative Definitheit). Für Punktkonfigurationen ist das die
klassische Charakterisierung über das Laplace-Funktional und verfügbar; für
Genealogien nicht, und dort endet das Programm derzeit.

**Das Testobjekt.** Der Hawkes-Prozess aus Ex. `hawkes` hat einen klassischen,
**deterministischen** historischen Dualen: die Hawkes–Oakes-Clusterdarstellung
gibt mit $w_f(s)=1-E[e^{-\int f\dif C_s}]$
$$1-w_f(s)=e^{-f(s)}\exp\{-\int_s^\infty\phi(u-s)w_f(u)\dif u\},\quad
E[e^{-\int f\dif N}]=\exp\{-\mu_0\int_0^\infty w_f\}.$$
Also eine nichtlineare Volterra-Gleichung, **rückwärts** in der Zeit — das
gedächtnisbehaftete Analogon zu DGP Bsp. 6 ($\dot Y=-\Psi(Y)$).
Numerisch geprüft gegen eine Clustersimulation (200 000 Läufe, $T=3$,
$\phi=\alpha\beta e^{-\beta t}$ mit $\alpha=0{,}6$): Formel 0,23630,
Simulation 0,23635, relativer Fehler 0,024 % bei einem MC-Standardfehler von
0,22 %.

Gewonnen wäre: die Konstruktion einer Lösung eines **pfadabhängigen**
Martingalproblems aus einem deterministischen Dualen, ohne approximierende Folge
und ohne Shift-System — und eine Verbindung zwischen §7.2 und §7.9, die bisher
nur eine Querverweis-Beziehung ist.

**Nicht verifiziert:** dass Setting `historical` tatsächlich greift, insbesondere
(D1) und die Zwei-Parameter-Form von (D3). Das steht ausdrücklich als Status im
Manuskript.

### D48 — Task 19 durchgeführt am Hawkes-Prozess  *(2026-08-25)*

Der Schritt aus D47 versucht — **und er geht durch.** Neu in §7.2:
Setting `hawkesdual`, Lem. `hawkesflow`, Prop. `hawkesduality`,
Prop. `hawkesDcheck`, Cor. `hawkesrestart`, Rem. `hawkesscope`.

**Die bedingte Dualität.** Gegeben die Vergangenheit $\hat x$ auf $[0,r]$ ist die
Zukunft ein Poisson-Cluster-Prozess mit Immigrationsintensität
$\mu_0+\int_{[0,r]}\phi(u-v)\hat x(\dif v)$ — konstante Immigration plus
Nachkommen der Vergangenheit. Poisson-Superposition gibt
$$E[H_t(\hat N_t,f)\mid\hat N_r=\hat x]=H_r(\hat x,\Theta_{r,t}f)\,V_{r,t}(f)$$
mit $\Theta_{r,t}f(v)=f(v)+\int_r^t\phi(u-v)w^{(t)}_f(u)\dif u$ und
$V_{r,t}(f)=\exp\{-\mu_0\int_r^t w^{(t)}_f\}$. Das **ist**
\eqref{eq:dualityrel} in Zwei-Parameter-Form, mit deterministischem Dualem
(also $E^y[\cdot]$ = Auswertung), Flussdynamik $\Theta$ und
Feynman–Kac-Faktor $V$.

**Die Flusseigenschaft, bewiesen in zwei Zeilen.** Spaltet man in
\eqref{eq:hawkesdual} das Integral bei $s$, so erfüllt $w^{(t)}_f|_{[0,s]}$
dieselbe Gleichung mit Horizont $s$ und Datum $\Theta_{s,t}f$; Eindeutigkeit gibt
$w^{(t)}_f=w^{(s)}_{\Theta_{s,t}f}$ auf $[0,s]$ und daraus
$\Theta_{r,t}=\Theta_{r,s}\circ\Theta_{s,t}$ sowie den Kozykel für $V$.

**(D1).** $\frac{\dif}{\dif t}|_{t=r^+}$ der rechten Seite ist
$\Lambda_r(\hat x)(e^{-f(r)}-1)H_r(\hat x,f)$ — also genau
$\mathcal A_rH_r(\cdot,f)(\hat x)$ für den pfadabhängigen Generator
\eqref{eq:pathgen}. Das erzeugte Martingalproblem ist das Hawkes-Problem aus
Ex. `hawkes`.

**(D2).** Laplace-Funktionale bestimmen Punktprozessverteilungen.

**(D3), und zwar ohne Zirkel.** $1-w^{(t)}_f$ ist ein Laplace-Funktional: die
Generationen-Abschneidung $G_{n+1}(s)=e^{-f(s)}\exp\{-\int_s^t\phi(u-s)(1-G_n(u))\}$
ist per Induktion das Laplace-Funktional des nach $n$ Generationen
abgeschnittenen Clusters, $G_n\downarrow 1-w$, und der Grenzcluster hat f.s.
endlich viele Punkte, weil die Volterra-Resolvente lokal existiert. **Das
konstruiert den Cluster aus der Verzweigungsrekursion, setzt $N$ also nicht
voraus.**

**Der Gewinn ist Cor. `hawkesrestart`, nicht die Existenz.** Für $f$ mit Träger
in $[0,r]$ ist $w^{(t)}_f\equiv0$ auf $[r,t]$, also $\Theta_{r,t}f=f$ und
$V_{r,t}(f)=1$ — die Hypothesen von Lem. `histrestart` sind erfüllt und die Kerne
**behalten die Vergangenheit**. Damit ist ein **nicht-Markovscher Restart-Kern**
konstruiert, den §5.4 bisher nicht hatte (Rem. `pastingassumed`: „die eine
Stelle, an der etwas von außen gegeben werden muss"), und Thm. `localuniqueness`
liefert lokale Eindeutigkeit im Sinne von J&S III.2.37 für das Hawkes-Problem —
ohne Shift-System. Auf der Existenzseite reproduziert die Dualität dagegen die
Hawkes–Oakes-Konstruktion, spart also nichts.

**Numerik.** Bedingte Dualität gegen Clustersimulation: rel. Fehler 0,039 %
(MC-Fehler 0,22 %). Kozykel gegen Diskretisierung: $10^{-4}$.

**Nebenfund: Ex. `hawkes` war falsch.** „Für $\lVert\phi\rVert_1\ge1$ ist
Explosion möglich" — nein. Ein *linearer* Hawkes-Prozess explodiert nie: $m=\mu_0+\phi*m$
hat für jedes $\phi\in L^1_{loc}$ eine lokale Resolvente (auf $[0,\delta]$ mit
$\int_0^\delta\phi<1$ konvergiert die Neumann-Reihe, dann schrittweise weiter),
also $E[N_t]<\infty$ für alle $t$. Was $\lVert\phi\rVert_1=1$ trennt, ist nicht
Existenz sondern **Stabilität**: darunter ist die Schranke gleichmäßig in $t$,
darüber wächst $m$ exponentiell. Verwechslung von exponentiellem Wachstum mit
Explosion. Korrigiert.

### D49 — „Ist das allgemeine MP ein Spezialfall des Markovschen?"  *(2026-08-25)*

Frage des Nutzers während D48. Neu Rem. `liftform` in §5.2.

**Formal ja, und leer.** Jedes $Y^\circ$ ist $\Filt^\circ_t$-adaptiert, nach
Lem. `liftmarkov`(a) und Doob–Dynkin also $\varphi_t(\hat\pi_t)$. Auf dem Lift
hat es damit die Gestalt \eqref{eq:sectiontest} mit $g=0$. Das ist dieselbe
Leere, die §2.2 schon festhält: jeder Prozess löst das MP für *irgendeine*
Testfamilie, nämlich seine eigenen Martingale. **Die Markovsche Form ist keine
Einschränkung an den Prozess, sondern an die Präsentation** — ihr Inhalt ist,
dass $\XX_A$ eine kleine, durch $\dom(A)$ parametrisierte Familie mit punktweise
erzeugtem Kompensator ist, und $g=0$ wirft genau das weg.

**Informativ wird es mit $g\ne0$.** Der nützliche Lift hebt den Zustand und
**behält** den Generator, dessen Integrand dann ein Pfadfunktional ist. Das ist
auf dem Lift wieder wörtlich Def. `markovMP` — und steht schon im Manuskript:
**Setting `pathjump` (§7.9) ist das Markovsche Martingalproblem auf dem Lift**,
mit $\hat f_t(\hat x)=f(\hat x(t))$ an der Spitze und
$\hat g_u(\hat x)=\mathcal A_uf(\hat x)$ als pfadabhängiger Rate. Ex. `volterra`,
`pathdepsemi` und `hawkes` sind alle von dieser Art.

**Sätze folgen trotzdem keine** — D46 gilt für beide Versionen, und der
klassische Markov-Apparat (zeitunabhängiger Operator, Halbgruppe, Feller) fehlt
so oder so, weil die Fasern wachsen.

### D50 — Literaturcheck: die Hawkes-Dualität ist klassisch  *(2026-08-25)*

Frage des Nutzers, ob die Dualität aus D48 bekannt ist. **Ja, und unter drei
Namen.** Neu Rem. `hawkesknown` in §7.2; Novitätsanspruch in Rem. `hawkesscope`
zurückgenommen; fünf Referenzen ergänzt (via Crossref verifiziert).

**(1) Clusterdarstellung.** Hawkes & Oakes, *J. Appl. Probab.* **11** (1974),
493–503. Das Laplace-Funktional eines Poisson-Cluster-Prozesses ist
$\exp\{-\int\lambda(1-G_c)\}$, und $G_c$ erfüllt eine Fixpunktgleichung — das ist
genau \eqref{eq:hawkesdual}. Lehrbuchstoff, Daley–Vere-Jones Bd. I.

**(2) Exponentiell-affine Transformformel.** Mit
$\chi(s)=\int_s^t\phi(u-s)w^{(t)}_f(u)\dif u$, also $w=1-e^{-f-\chi}$, wird
\eqref{eq:hawkesdual} zur **Volterra–Riccati-Gleichung**
$$\chi(s)=\int_s^t\phi(u-s)\bigl(1-e^{-f(u)-\chi(u)}\bigr)\dif u,$$
Nichtlinearität $x\mapsto1-e^{-x}$ = Verzweigungsmechanismus für
Poisson-Nachkommen. (Symbolisch geprüft, Residuum $10^{-16}$.) Für
$\phi=\alpha\beta e^{-\beta\cdot}$ ist $(N,\Lambda)$ endlichdimensional affin und
das wird eine Riccati-ODE — Errais–Giesecke–Goldberg, *SIAM J. Financial Math.*
**1** (2010), 642–665. Für allgemeinen Kern: Abi Jaber–Larsson–Pulido,
*Ann. Appl. Probab.* **29** (2019), Nr. 5. Rough-Heston-Analogon:
El Euch–Rosenbaum, *Math. Finance* **29** (2019), 3–38.

**(3) Markovscher Lift.** Cuchiero–Teichmann, *J. Evol. Equ.* **20** (2020),
1301–1348, heben stochastische Volterra-Prozesse zu Markov-Prozessen auf einem
Raum von Forward-Kurven und charakterisieren sie über eine verallgemeinerte
Feller-Halbgruppe. **Das ist Def. `pathlift` richtig ausgeführt** — der Lift, der
den Generator *behält*, genau im Sinne von Rem. `liftform` (D49). Damit hat D45–D49
eine Literaturverankerung, die vorher fehlte; in Rem. `liftform` zitiert.

**Konsequenz fürs Manuskript.** Rem. `hawkesknown` sagt jetzt ausdrücklich, dass
auf der analytischen Seite nichts neu ist. Nicht klassisch ist allein die
*Verpackung*: die Transformformel als (D1)–(D3) von Setting `dualdata` zu lesen
und daraus Cor. `hawkesrestart` als Restart-Kern im Sinne von J&S III.2.37 zu
ziehen. Beides sind Umstellungen bekannter Tatsachen. Rem. `hawkesisvolterra`
zitiert jetzt ebenfalls ALP19.

### D51 — Audit der verbleibenden Verallgemeinerungen  *(2026-08-25)*

Frage des Nutzers, ob es weitere sinnvolle Verallgemeinerungen gibt — alle
Ansätze durchgehen. Neu §1.4 „Generalizations not made, and why" mit
Tabelle; dazu zwei Bemerkungen an Ort und Stelle.

**Zwei Kandidaten sind gratis und jetzt umgesetzt.**

* **Rem. `complexvalued`** — komplexwertige Testprozesse. Ein $\C$-wertiger
  Prozess ist Martingal gdw. Real- und Imaginärteil es sind, und §3, §5, §6 sind
  $\C$-linear im Testprozess; §4 und §7 spaltet man auf. Kostet nichts und ist
  die Form, die die Transform-Literatur benutzt ($e^{i\langle u,X_t\rangle}$ statt
  reeller Testfunktionen) — relevant nach D50.
* **Rem. `inequalitystable`** — Lem. `mixture`, `disint` und `restart` werden
  bewiesen, indem eine Identität gegen ein **nichtnegatives** Gewicht integriert
  wird, und keiner der drei Beweise benutzt, dass es eine Identität ist. Mit
  nichtnegativer bestimmender Menge gelten alle drei wörtlich für
  **Submartingalprobleme** — also für die Stroock–Varadhan-Formulierung
  reflektierter Diffusionen. Nicht übertragbar ist die Eindeutigkeitshälfte:
  Def. `propagation` vergleicht über Gleichheit von Erwartungswerten, und eine
  Ungleichung propagiert keine Übereinstimmung.

**Ein Kandidat entfällt, weil schon da.** Quasimartingale in §4:
Def. `regclass` verlangt von $C^f$ nur einseitige Limiten und
$L^1$-Rechtsstetigkeit, **nicht** endliche Variation — das Manuskript ist dort
bereits allgemeiner als die Quasimartingal-Aussage.

**Der eigentliche offene Kandidat: pfadabhängige (zufällige) Uhr.** Ersetzt man
$q$ durch einen prädiktablen wachsenden Prozess $A(\omega)$, ist das der Schritt
zu den Semimartingal-Charakteristiken aus J&S Kap. II. Zwei Beobachtungen:
(i) **die abstrakte Schicht enthält es bereits** — Def. `absMP` verlangt nur eine
Familie adaptierter Pfadfunktionale, und $f(\pi_t)-\int g(\pi_u)\dif A_u$ ist
eines; nur Def. `markovMP` fixiert ein deterministisches $q$. (ii) Eine
*absolutstetige* zufällige Uhr bringt nichts Neues — das ist der pfadabhängige
Integrand aus Setting `pathjump`. Neu ist allein ein **singuläres** $A$
(Lokalzeit, zufällige Sprünge).

**Und damit schließt sich ein Kreis aus D42:** eine deterministische Uhr hat ihre
Atome an *deterministischen* Zeiten, und Thm. `absconvaug` räumt die
Unstetigkeit durch Vergrößerung des Pfadraums weg. Eine zufällige Uhr hat sie an
*zufälligen* Zeiten — keine feste Koordinatenfamilie fängt die ein, und genau
dann werden Kontrollvariablen und weak-strong convergence nötig, wie
Rem. `augvsws` vorhersagt. Das Material aus §7.8, das dieses Manuskript nicht
braucht, ist präzise das, was die zufällige Uhr brauchen würde — ein guter Grund,
es stehen zu lassen.

**Zwei weitere Grenzen benannt.** *McKean–Vlasov*: hängt $A$ von
$\mathcal L(X_t)$ ab, so hängt $\XX$ von $P$ ab und Lem. `mixture`/`restart`
fallen sofort — dieselbe Nichtlinearität in $P$ wie beim lokalen MP, aber mit
anderer Reparatur: (L1) stellt dort Linearität wieder her, hier braucht es einen
Fixpunkt. *Kontrollvariablen*: in CPS durchgehend vorhanden, hier bewusst auf
$U$ = Punkt gesetzt, weil sonst ein Index durch fünf Abschnitte getragen und in
einem benutzt würde.

**Verworfen:** banachwertige Testprozesse (maß- und distributionswertige Prozesse
werden durch Paarung mit einer Testfunktion behandelt, also kein Gewinn, und §4
braucht eine Ordnung) und signierte Lösungsmaße (Disintegration fällt).

### D52 — Komplexwertige Testprozesse; und ein Fehler in der Prüfroutine  *(2026-08-25)*

**Umgesetzt** (Wunsch des Nutzers, aus D51): der Skalarkörper ist jetzt
durchgehend $\K\in\{\R,\C\}$. §2.1 führt ihn ein, Def. `martingale` und
Def. `canonical` sind $\K$-wertig, und Rem. `complexvalued` ist von „wäre
gratis" zu „ist durchgeführt" umgeschrieben.

**Designentscheidung:** die bestimmenden Mengen $\ZZ^\circ_s$ bleiben
**reellwertig**, welches $\K$ auch gewählt ist. Testet man
$E[(Y_t-Y_s)Z^\circ_s]=0$ gegen reelle $Z^\circ_s$, so trennt das Real- und
Imaginärteil des Zuwachses bereits; Komplexifizieren bringt nichts und kostet
Buchhaltung.

**Die vier Stellen, die $\K=\R$ brauchen** (vollständig aufgelistet):
(i) Ordnung — Submartingale gibt es nur über $\R$, betrifft Fact `cadlagext`
/`submgreg` in §4 (dort auf $\Re$ und $\Im$ anwenden) und Rem. `inequalitystable`;
(ii) Stone–Weierstrass braucht im Komplexen Abschluss unter Konjugation
(Rem. `EKrelcompact`, Prop. `rieszmarkov`); (iii) Positivität in
Prop. `rieszmarkov`, also (D3) — passt zu Rem. `histobstruction`;
(iv) §2.4 (dissipative Operatoren), reell belassen, ist ohnehin optionaler
Kontext.

**Gewinn:** Thm. `duality` braucht *keine* Änderung — seine Hypothesen
\eqref{eq:dual1}–\eqref{eq:dual2} sind schon über Beträge formuliert, also sind
komplexe $f,g,h,\alpha,\beta$ abgedeckt. Und das ist die Form, in der die
affine Literatur (ALP19) Dualität überhaupt anwendet: $e^{i\langle u,X_t\rangle}$
statt reeller Testfunktionen.

**Lean** (Frage des Nutzers): ja, `RCLike`. Zwei Dinge sind dabei zu trennen —
die **Martingaleigenschaft** braucht nichts, `MeasureTheory.Martingale` ist in
Mathlib schon für einen beliebigen reellen Banachraum formuliert (am Quelltext
geprüft: `[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]`), und die
bedingte Erwartung ist selbst `RCLike`-parametrisiert. Einen **Körper** braucht
erst, was Testprozesse *multipliziert*: Def. `canonical`, Prop. `fddchar`, §6.
Also `RCLike` für die Testfunktionen, Banachraum für die Martingale. In §9 als
Designentscheidung festgehalten.

---

**Und ein Fund in eigener Sache.** Beim Kompilieren fiel auf, dass meine
Prüfroutine nur auf `undefined`, `multiply defined` und `Overfull` gegrept hat —
**nie auf `! LaTeX Error`**. Dadurch sind zwei Defekte über die ganze Sitzung
unbemerkt geblieben:

* In `def:process` fehlte das `\end{definition}`. Vorhanden **seit dem
  allerersten Commit des Manuskripts** (`7cadc98`, vor dieser Sitzung) — geprüft
  durch Auszählen über die Commit-Historie. Alles ab §2.2 wurde also innerhalb
  einer `definition`-Umgebung gesetzt.
* Drei Unicode-Zeichen (α, ι, Π) in einem `\texttt` aus D45 fielen still aus dem
  PDF („Unicode character not set up for use with LaTeX").

Beides behoben. Neu `check.py` im Verzeichnis: prüft Umgebungsbalance,
doppelte Labels, Nicht-ASCII außerhalb von Kommentaren, **alle** `^!`-Fehler,
undefinierte Referenzen und Zitate sowie Overfull-Boxen, und läuft pdflatex
dreimal (zweimal genügt nach einem Fehlerlauf nicht, weil die `.aux` dann
unbrauchbar ist). Ab jetzt ist „kompiliert sauber" gleichbedeutend mit
`python3 check.py` ohne Befund.

### D53 — Ungleichungsstabilität: Einordnung und Begründung waren beide zu billig  *(2026-08-25)*

Einwand des Nutzers zu Rem. `inequalitystable`: um die Submartingaleigenschaft
überhaupt zu formulieren, braucht man eine Ordnung — dann ist es nicht mehr
allgemeiner. **Der Einwand trifft, und beim Nachrechnen trifft er schärfer als
gemeint.** Zwei getrennte Fehler.

**(1) Die Einordnung war falsch.** §1.4 führte „komplexwertige Testprozesse" und
„Submartingalprobleme" nebeneinander als zwei gratis verfügbare
Verallgemeinerungen auf. Das ist eine Kategorienverwechslung: die eine braucht
einen **Körper**, die andere eine **Ordnung**, und sie schließen einander aus.
Die Tabelle bietet eine *Wahl*, keine Summe. Zeile umformuliert („transverse,
not wider").

**Was aber stimmt, und jetzt präzise dasteht:** über $\R$ ist es sehr wohl eine
echte Verallgemeinerung, im genauen Sinn
$$\Msol(\XX^\circ)=\Msol^{\mathrm{sub}}\bigl(\XX^\circ\cup(-\XX^\circ)\bigr),$$
denn $Y^\circ$ und $-Y^\circ$ sind genau dann beide Submartingale, wenn
$Y^\circ$ ein Martingal ist. Das Martingalproblem ist also das
Submartingalproblem für eine **symmetrische** Testfamilie.

**(2) Die Begründung war zu billig.** Ich hatte geschrieben, die drei Lemmata
integrierten eine Identität gegen ein nichtnegatives Gewicht und benutzten
nirgends, dass es eine Identität ist — man müsse nur die bestimmende Menge
nichtnegativ wählen. Für Lem. `mixture` (das gar keine bestimmende Menge
benutzt) und Lem. `restart` stimmt das. **Für die bestimmende Menge selbst
stimmt es nicht:** ein endliches signiertes Maß, das auf einem erzeugenden
$\pi$-System nichtnegativ ist, muss es nicht sein. Def. `canonical`(ii) in der
einseitigen Form ist also eine *echt stärkere* Forderung.

Sie gilt trotzdem für Ex. `determining` — aber aus einem Grund, der geliefert
werden muss. Neu **Lem. `semiring`**: ist $\mathcal C$ ein **Semiring**, der
$\Gilt$ erzeugt, und $\mu\ge0$ auf $\mathcal C$, so ist $\mu\ge0$. Beweis über
endliche disjunkte Vereinigungen (Additivität) plus Hahn–Jordan: approximiert
man die Negativmenge $N$ durch $A$ aus der erzeugten Algebra mit
$|\mu|(A\triangle N)<\varepsilon$, so folgt $\mu^-(\Omega)<\varepsilon$.
Anwendung: nichtnegative $h_k\in\Cb$ fallen monoton auf Indikatoren
abgeschlossener Mengen, das gibt $\mu\ge0$ auf abgeschlossenen Rechtecken, per
Regularität auf allen Borel-Rechtecken — und die bilden einen Semiring. Braucht
**(E2)**.

**(3) Was wirklich verloren geht** (neu Rem. `submartlost`): Lem. `disint`
braucht den abzählbaren Test \eqref{eq:countabletest}, und eine abzählbare
Familie, die für Lem. `semiring` reicht, gibt es nur bei zweitabzählbarem $E$ —
(E2) liefert es, aber die Hypothese ist nicht mehr die harmlose von vorher. Und
die Eindeutigkeit fällt ohnehin: Def. `propagation` vergleicht über Gleichheit,
aus $E^P[Zf(\pi_s)]\ge E^Q[Zf(\pi_s)]$ folgt bei $t$ nichts.

**Nebenbei zwei Werkzeugfehler.** `sed 's/\eps/\varepsilon/g'` hätte auch
`\epsilon` zerschossen (Präfix); hier zufällig folgenlos, aber die Lehre steht.
Und `check.py` brauchte drei pdflatex-Läufe statt zwei, weil eine `.aux` aus
einem Fehlerlauf sonst hunderte Scheinbefunde erzeugt — bereits gefixt.

### D54 — Fehlerdurchgang durchs ganze Manuskript  *(2026-08-25)*

Auftrag: das Manuskript auf Fehler prüfen. Sieben Funde, der erste ist der
schwerste.

**(1) `lem:rectify` war falsch, und damit `thm:anyclock` unbewiesen.**
Die Konstruktion füllte die Lücke $[Q(a),Q(a)+q(\{a\})]$ eines Atoms durch
Interpolation. Das geht nicht. Gegenbeispiel, exakt nachgerechnet: $\T=[0,2]$,
$q=\delta_1$, $\Phi(s,t)=M(i(s),i(t))$ mit $i(s)=\one_{s>1}$,
$M(0,0)=0$, $M(1,0)=M(0,1)=c$, $M(1,1)=d$. Beide Inkrementdarstellungen gelten
mit **einem** $\gamma$ (am Punkt $(1,1)$ konsistent geprüft), und $d$ ist
**frei**. Die Konstruktion liefert dann
$\Psi(1,y)-\Psi(0,y)=d/2$ statt $\int_0^1\psi(z,y)\dif z=c$ — sie stimmt nur
für $d=2c$.

Und der Defekt ist nicht technisch: ein rektifiziertes $\Psi$ erfüllt
$\partial_x\Psi=\partial_y\Psi$, ist also Funktion von $x+y$, und enthält damit
$\Psi(L,0)=\Psi(0,L)$ bereits. Für eine Uhr mit Atomen **setzt die Konstruktion
die Konklusion voraus** — die Rektifikation ist nur dann eine Reduktion, wenn es
keine Lücken zu überbrücken gibt.

**Korrektur.** `lem:rectify` und `thm:anyclock` gelten jetzt für **atomlose**
Uhren unter (T3); dort ist $Q$ stetig und surjektiv, $\tau$ ein echtes
Rechtsinverses, und der Beweis wird kürzer statt länger (neu: die
Quantilidentität \eqref{eq:quantile}). Neu `rem:rectifyfails` mit dem
Gegenbeispiel und der Statusübersicht. **Stand von §6 jetzt:** Haar bewiesen
(`prop:haar`), atomlos bewiesen (`thm:anyclock`), rein atomar symbolisch
verifiziert aber nicht bewiesen (`rem:atomicdual`), **gemischt offen**. Die
negative Hälfte bleibt: Translationsinvarianz ist *nicht* nötig.

Nachgezogen: §1.2, §1.3, §1.4, `rem:haarrole`, `rem:atomicdual`,
`rem:dualscope`, `rem:dualischain`, `rem:controlvars`, `cor:exdualitywellposed`,
Bündeltabelle, §8 (F3).

**(2) `thm:absstrongmarkov` benutzte optional sampling unzulässig.**
Die Hypothese war „gleichgradig integrierbare Zuwächse auf beschränkten
Intervallen". Das ist eine Aussage über *deterministische* Fenster und sagt
nichts über das *zufällige* Fenster $[\tau+s,\tau+t]$, das bei unbeschränktem
$\tau$ unbeschränkt ist; Fact `optsampl` greift dort nicht. Neu
**`lem:optsamplafter`**: für rechtsstetiges Martingal, f.s. endliches $\tau$ und
$Y_{\tau+t}-Y_{\tau+s}\in L^1$ gilt die Identität — Beweis durch Abschneiden bei
einer abzählbaren kofinalen Folge, optional sampling bei *beschränkten*
Stoppzeiten, dominierte Konvergenz. Die Integrierbarkeit \eqref{eq:optafterint}
ist damit nicht nur nötig, sondern **hinreichend**; bei verschiebungsinvarianter
Uhr ist sie automatisch (Thm. `uniqueness`), sonst eine echte Einschränkung.

**(3) `thm:exduality` braucht (T2a).** Rem. `exdualityscope`(ii) behauptete, der
Satz überlebe einen partiell geordneten Index. Die Kern-Schicht
(`lem:dualsemigroup`, `prop:dualCK`) tut das, der **Satz nicht**: für Kolmogorov
braucht man endlichdimensionale Verteilungen über *alle* endlichen Teilmengen,
und an einer Antikette — $(1,0)$ und $(0,1)$ in $\Rp^2$ — ist die gemeinsame
Verteilung durch Ein-Parameter-Kerne nicht bestimmt. Setting, Satz, Tabelle,
Abstract und §1.3 nachgezogen; das ist das genaue Analogon zu Rem. `chainonly`,
mit der Kettenobstruktion jetzt in der Konstruktion statt in der Induktion.

**(4) `prop:hawkesDcheck`(a) bewies (D1) nur in Ableitungsform.**
$\Lambda_u(\hat x)$ ist für lokal integrables $\phi$ nicht stetig, also existiert
die Ableitung bei $t=r^+$ nicht für jedes $r$. (D1) ist jetzt in **integrierter**
Form \eqref{eq:hawkesD1} formuliert und über die pfadweise Sprungzerlegung von
$M_t=e^{-\int f\dif N}$ plus Kompensation bewiesen; die Ableitungsform folgt an
Lebesgue-Punkten von $\Lambda^{\hat x}$.

**(5) `lem:semiring` brauchte $\Omega\in\mathcal C$.** Ohne das ist die erzeugte
Familie keine Algebra und der Hahn–Jordan-Schritt bricht: auf $\{1,2\}$ ist
$\{\emptyset,\{1\}\}$ ein erzeugender Semiring und $\delta_1-5\delta_2$ darauf
nichtnegativ, aber nicht nichtnegativ. Hypothese ergänzt, Gegenbeispiel notiert,
und die Anwendung braucht jetzt zwei Semiring-Schritte (Rechtecke über *einer*
endlichen Zeitmenge, dann über allen).

**(6) `lem:rectify` (alt) benutzte Auswahl ohne es zu sagen** — $\psi_0$ war über
Urbilder von $Q$ definiert. Die neue Fassung benutzt die Quantilfunktion
$\tau(z)=\sup\{t:Q(t)\le z\}$, ist kanonisch und formalisierbar; dazu die
Hypothese, dass $\gamma$ ordnungsmessbar ist (automatisch, wenn $\mathcal T$ die
Ordnungs-$\sigma$-Algebra ist).

**(7) Struktur:** der Beweis von `lem:restart` stand hinter drei eingeschobenen
Blöcken (`rem:inequalitystable`, `lem:semiring`, `rem:submartlost`), die beim
Einfügen von D53 zwischen Lemma und Beweis geraten waren. Blöcke hinter den
Beweis verschoben.

### D55 — `thm:anyclock` war überverallgemeinert; zum Korollar zurückgestuft  *(2026-08-25)*

Einwand des Nutzers nach D54: eventuell sei zu stark verallgemeinert worden.
**Trifft zu.** Zwei Befunde beim Nachprüfen.

**(1) Kein Konsument.** Alle 15 Vorkommen von `thm:anyclock` waren Querverweise
in Prosa und Tabellen; **kein einziger Beweis** benutzte den Satz.
Thm. `duality` und Cor. `uniqviadual` laufen auf Lebesgue, Cor. `dualdiscrete`
auf dem Zählmaß, §7.2 nur auf \eqref{eq:clockadd}.

**(2) Der Satz ist ein Variablenwechsel.** Er stand unter (T3) — also auf
$\Rp$ —, und dort ist eine *atomlose* Uhr das Bild des Lebesgue-Maßes unter der
stetigen wachsenden Abbildung $\tau$. Ein Martingalproblem mit atomloser Uhr ist
also ein **deterministischer Zeitwechsel** eines Lebesgue-Problems, und der Satz
sagt nichts weiter, als dass Dualität unter diesem Zeitwechsel invariant ist.
Lem. `rectify` war die Substitutionsformel, aufgemacht als Lemma.

**Korrektur.** `lem:rectify` und `thm:anyclock` sind zu einem einzigen
**`cor:atomless`** („Atomless clocks, by time change") verschmolzen, Beweis eine
halbe Seite statt zwei; die Quantilidentität \eqref{eq:quantile} steht jetzt
dort, wo sie hingehört, nämlich als Substitution im Beweis.
`rem:rectifyfails` heißt jetzt `rem:atomsnotchange` und sagt ausdrücklich, dass
das Korollar *als* Variablenwechsel zu lesen ist und keinen Satznamen verdient —
mit dem Gegenbeispiel aus D54 und der Statustabelle. §6 ist dadurch rund zwei
Seiten kürzer.

**Was bleibt.** Die drei Dinge, die wirklich Inhalt haben: die
Treppenzug-Verallgemeinerung von `lem:chain` (die (T4) dort ganz beseitigt), die
Korrektur des ursprünglichen Fehlers (Translationsinvarianz ist *nicht* nötig),
und die Beobachtung, dass Atome eine strukturelle und keine technische Hürde
sind — ein rektifiziertes $\Psi$ ist Funktion von $x+y$ und enthält die
Konklusion bereits.

**Lehre fürs Protokoll.** Der Auslöser war ein *Fehler* (die falsche
Haar-Behauptung), und die Reparatur ist über das Ziel hinausgeschossen: aus
„Translationsinvarianz ist nicht nötig" wurde „jede Uhr geht", und aus einer
Substitution wurde ein Satz mit eigenem Lemma. Beim nächsten Mal: nach einer
Korrektur prüfen, wer das neue Resultat *benutzt*, bevor es einen Namen bekommt.

---

## Prüfprotokoll

Alle Aussagen sind am Scan `references/EthierKurtz1986.pdf` bzw. am PDF von
CPS23 verifiziert, nicht aus dem Gedächtnis rekonstruiert. Seitenangaben:
Buchseite (PDF-Seite = Buchseite + 10).

| Aussage | Buchseite | Status |
|---|---|---|
| Thm. 4.3.6 | 178f. | wörtlich geprüft |
| Thm. 4.4.2 (a)(b)(c) + Beweis | 184–186 | wörtlich geprüft |
| Cor. 4.4.3, Cor. 4.4.4, Rem. 4.4.5 | 187 | wörtlich geprüft |
| Lem. 4.4.10, Thm. 4.4.11, Rem. 4.4.12 | 192f. | wörtlich geprüft |
| Cor. 4.4.13, Cor. 4.4.14 | 195 | wörtlich geprüft |
| Lem. 4.5.1, Rem. 4.5.2 | 196f. | wörtlich geprüft |
| §4.3 Def. des MP, (3.2), (3.4), Lem. 4.3.2 | 173f. | wörtlich geprüft |
| Kap. 1: 1.1.5/1.1.6, 1.2.6, 1.2.12, 1.3.1/1.3.3, 1.4.2/1.4.3, 1.5.1, 1.6.8 | 7–33 | wörtlich geprüft |
| Kap. 2: 2.1.2/2.1.4, 2.2.8, 2.2.9, 2.2.13, 2.2.17, §2.3 | 51–87 | wörtlich geprüft |
| Kap. 2 §2.8: (8.1)–(8.6), (8.10), Prop. 8.1–8.6, Thm. 8.7 | 84–88 | wörtlich geprüft (D16) |
| Kap. 6: §6.1, Thm. 6.3.4 und Umfeld | 306–325 | wörtlich geprüft (D16) |
| Kap. 3: 3.1.7/3.1.9, 3.2.1/3.2.2, 3.3.1, 3.4.1–3.4.6, §3.5, 3.5.1/3.5.6, 3.6.2/3.6.3, 3.7.1, 3.7.7, 3.7.8, 3.9.1, 3.9.4 | 103–145 | wörtlich geprüft |
| Appendizes 2, 3, 4 | 493–496 | geprüft (OCR) |
| CPS23 §3.1, Def. 3.2/3.3/3.5, Bsp. 3.6, Thm. 3.14, Cor. 3.17, Thm. 3.20, Cor. 3.21, §4.1 Thm. 4.1 | S. 10–20 | wörtlich geprüft |

**Korrekturen während der Prüfung:**

* EK86 Lemma 1.4.2: $A_0 = \{(f,g) \in \bar{A} : g \in \overline{\mathcal{D}(A)}\}$
  — ich hatte zunächst $\overline{\mathcal{R}(A)}$ geschrieben. Am Scan (S. 21)
  korrigiert. *(Betrifft nur v2; der Fact ist in v3 nicht mehr enthalten, siehe D5.)*
* EK86: die Aussagen über $X(\tau)$-Messbarkeit stehen in **Proposition 2.1.4**,
  nicht 2.1.5. Zitat korrigiert.
* EK86 Thm. 4.4.1 und Cor. 4.4.4 tragen Abschlussstriche
  ($\overline{\mathcal{R}(\lambda-A')} = \overline{\mathcal{D}(A')}$), die das OCR
  verschluckt; am Scan (S. 182, 187) verifiziert. *(Nur v2, siehe D5.)*

| KA21 Kap. 32 (lokales MP, Thm. 32.7/32.10/32.11) | — | geprüft (D28, D31) |
| JS03 Kap. II–III (Charakteristiken, III.2.8/2.35/2.37/2.39/2.40/2.43) | — | geprüft (D29, D38) |
| DGP24 Thm. 2.1, Prop. 2.5/2.6/2.8, Bsp. 6, §5 | — | geprüft (D41, D47) |
| Mathlib v4.33.1: `IsProjectiveLimit`, `projectiveFamilyContent`, `Kernel.traj`, `integral_rieszMeasure` | — | am Quelltext geprüft (D43) |

**Numerisch geprüft** (nicht nur gelesen):

| Aussage | Verfahren | Ergebnis |
|---|---|---|
| Dualität für atomare Uhren, beide Konventionen, bis 5 Atome und auf $\{0,1,2\}^2$ | sympy, exakt | Differenz $\equiv 0$ (D39) |
| Hawkes-Dualität, unbedingt | Clustersimulation, 200 000 Läufe | rel. Fehler 0,024 % (MC-Fehler 0,22 %) |
| Hawkes-Dualität, bedingt auf die Vergangenheit | Clustersimulation | rel. Fehler 0,039 % (D48) |
| Kozykel $\Theta_{r,t}=\Theta_{r,s}\Theta_{s,t}$, $V$-Kozykel | Diskretisierung | $10^{-4}$ (Gitterfehler) |
| Volterra–Riccati-Umformung | symbolisch | Residuum $10^{-16}$ (D50) |

**Ehemals Black Box, inzwischen bewiesen:** EK86 Kapitel 3, Problem 7 (benutzt im
letzten Schritt von Thm. `absreg`). Das ist eine *Aufgabe* im Buch, kein Satz —
Rem. `sepcondproof` im Manuskript gibt jetzt einen Beweis.

---

## Verlauf

### 2026-08-24 — v1 (17 S.)

* Quellen gesichtet: `references/EthierKurtz1986.pdf` (551 S., Scan mit OCR),
  `references/CriensPfaffelhuberSchmidt2021.pdf` (EJP 28 (2023), Nr. 19).
* Die vier Zielresultate lokalisiert und wörtlich am Scan gelesen; Nummerierung
  in `PLAN.md` geklärt (→ D6).
* Setting-Frage aufgeworfen und mit dem Nutzer entschieden (→ D1, D3, D4).
* Manuskript geschrieben: §1 Scope, §2 Prerequisites (7 Facts), §3–§7 die vier
  Resultate mit Beweisen, §8 Formalisierungsnotizen.
* Mathlib-Bestandsaufnahme: Filtrationen, Martingale, Optional Stopping,
  Portmanteau, Lévy–Prokhorov, Prokhorov vorhanden; **kein** Skorokhod-Raum,
  keine Submartingal-Regularisierung, keine Kompaktheitskriterien in $D_E$, keine
  trennenden Klassen.

### 2026-08-24 — v2 (24 S.)

* §2 zu einer vollständigen Preliminaries-Sektion ausgebaut: §2.1 Notation,
  §2.2 Kapitel 1, §2.3 Kapitel 2, §2.4 Kapitel 3, §2.5 Appendizes,
  §2.6 Verwendungstabelle (jedes Fact → Stelle der Benutzung).
* §5.1 "The semigroup route" ergänzt (EK86 4.4.1, 4.4.4, Rem. 4.4.5), damit das
  Kapitel-1-Material nicht totes Gewicht ist.
* In §3 ergänzt: Def. Wohlgestelltheit, Lem. 4.3.2, Prop. 4.3.5 (Existenz von
  Lösungen ⇒ $A$ dissipativ), Rem. zum vollen Erzeuger.
* Zwei Zitatfehler gefunden und korrigiert (siehe Prüfprotokoll).

### 2026-08-24 — v3 (22 S.)

* §5.1 auf Wunsch entfernt, Kapitel-1-Material entsprechend zusammengestrichen
  (→ D5). §5 wieder flach.
* Rem. 2.5 ergänzt, die die Abgrenzung zu Kapitel 1 dokumentiert.
* Verwendungstabelle, §8 und die Design-Entscheidungen nachgezogen.
* Overfull-Boxen von 7 auf 3 (alle ≤ 5 pt) reduziert.

### 2026-08-24 — Korrektur an Task 1 der Roadmap

Der Nutzer hat eingewandt, dass man beim Zeitindex vermutlich mit allgemeinen
(halb-)geordneten Mengen auskommt. Berechtigt — die erste Fassung der
Roadmap-Tabelle hatte zwei verschiedene Dinge vermengt:

1. **Struktur auf $\mathbb{T}$** (Präordnung / Verband / lineare Ordnung /
   Monoid). Für die gesamte Martingal-Schicht — Filtration, adaptiert, Martingal,
   Def. 3.2, Def. 3.4 — reicht tatsächlich eine Präordnung, so wie Mathlib es
   macht. Für Stoppzeiten, $\mathcal{F}_\tau$ und Lokalisierung reicht eine bloße
   Halbordnung dagegen *nicht*: man braucht $\tau_1\wedge\tau_2$, Infima und
   $\tau_n\uparrow\infty$, also einen gerichteten Verband. Genau deshalb arbeitet
   EK86 §2.8 mit einem metrischen Verband; laut EK86 wird das dort für Kapitel 6
   (Mehrparameter-Zeittransformationen, $\mathbb{T}=[0,\infty)^d$) gebraucht.

2. **Datum des Martingalproblems**, nämlich der Kompensator. Das Uhr-Maß gehört
   *nicht* in die Annahmenliste über $\mathbb{T}$, sondern in Def. 3.5. Es ist
   auch nicht entbehrlich: die Additivität in der Zeit plus punktweise Erzeugung
   aus $g$ ist genau das, was Prop. 3.6 trägt (Lösung des MP = Eigenschaft der
   endlichdimensionalen Verteilungen), und ohne diese Charakterisierung ist „MP
   für den Operator $A$" leer, weil jeder Prozess den MP für die Familie seiner
   eigenen Martingale löst. Dieselbe Struktur braucht ${}^{*}\mathcal{F}^X_t$
   aus (2).

Minimal genügt aber keine Maß-, sondern nur eine **additive Intervallfunktion**
$q_{s,u}=q_{s,t}+q_{t,u}$ nebst messbarer Struktur auf $\mathbb{T}$ — und die ist
mit einer Halbordnung verträglich. Auf linear geordnetem $\mathbb{T}$ ist sie
genau ein lokalendliches Borelmaß, auf $[0,\infty)^d$ das Lebesguemaß auf
Rechtecken. Die Vermutung des Nutzers trägt also weiter als die erste Tabelle.

Task 1a/1b/1c in `PLAN.md` entsprechend neu geschrieben; Bündel jetzt (T0) Präordnung,
(T1)/(T1') Verband, (T2) lineare Ordnung + Topologie, (T3) $[0,\infty)$,
(T4) geordnetes Monoid — wobei (T4) bewusst *unabhängig* von (T2)/(T3) steht.
Neue offene Frage **Q6**: abstraktes additives $q$ oder Maß?

### 2026-08-24 — Abgleich Chat ↔ `PLAN.md`

Auf Nachfrage geprüft, ob alles aus der Diskussion im Plan steht. Drei Lücken
gefunden und geschlossen:

* **Q3** verwies noch auf das alte Bündel „(T5)"; korrekt ist (T4). Zudem fehlte
  dort die beim Umschreiben von 1c gefundene Bedingung, dass $q$ **shift-invariant**
  sein muss — sonst ist die Schlussfolgerung ein zeitinhomogener Markovprozess.
  Das stand nur in 1c, nicht in den offenen Fragen.
* **Q1 und Q6 sind eine Entscheidung**, nicht zwei: beide fragen, wie weit der
  Mehrparameterfall mitgetragen wird. Das war im Chat gesagt, aber nicht notiert.
* Die Beobachtung aus 1c, dass §7.2 sich womöglich vom Skorokhod-Raum ablösen
  lässt, hatte keine eigene offene Frage — obwohl sie die **Reihenfolge von Task 7
  und 8** ändern würde. Jetzt **Q7**.

Außerdem in Task 3 ergänzt: Mathlibs `IsStoppingTime` nimmt `τ : Ω → WithTop ι`,
also ist „$\tau_n\uparrow\infty$" eine Aussage in `WithTop ι`, nicht in `ι`. Das
greift in (T1) und in die lokale Variante von Def. 3.2 ein.

### 2026-08-24 — Q2 und Q7 geprüft und beantwortet

Beide waren in `PLAN.md` als „billig zu prüfen, große Wirkung" markiert, und
beide fallen anders aus als vermutet — in beiden Fällen zugunsten der
allgemeineren Variante:

* **Q2** (Atome im Uhr-Maß): Thm. 4.1 braucht *kein* atomloses $q$. Die
  Begründung in `PLAN.md` verwechselte „springt" mit „ist nicht càdlàg". → D7.
  Damit entfällt der Grund, §4 und §7 in verschiedenen Settings zu führen.
* **Q7** (Skorokhod in §7.2): der abstrakte Konvergenzsatz kommt ohne $D_E$ aus
  und sogar mit (T0). → D8. Task 8 in 8a/8b gesplittet, 8a nach vorn gezogen.

Neu aufgeworfen: **Q8**, die Konvention $(0,t]$ vs. $[0,t)$ für den Kompensator.
Sie wird erst durch Q2 sichtbar und ist nur dann eine echte Frage, wenn Q6 Atome
zulässt. Sie ist keine Geschmacksfrage: die eine Konvention macht Thm. 4.1 zu
einer Aussage über eine Modifikation, die andere macht den diskreten Fall zur
Doob-Zerlegung.

Nicht angefasst: Q1/Q6 (die eine Entscheidung über den Mehrparameterfall), Q3,
Q4, Q5. Q1/Q6 blockiert Task 1 und ist dem Nutzer vorgelegt.

### 2026-08-24 — Q1/Q6 und Q8 vom Nutzer entschieden

Q1/Q6: **maximal allgemein** (→ D9), Q8: **$(0,t]$** (→ D10). Beim Ausformulieren
von D9 stellte sich heraus, dass die in `PLAN.md` §1b angebotene Alternative
„abstrakte additive Intervallfunktion vs. Maß" gar keine ist: Additivität längs
Ketten trägt Prop. 3.6 nicht (Fubini), und ein Maß auf $\mathbb{T}$ selbst — statt
auf Intervallen — gibt den Halbordnungsfall geschenkt. Die Entscheidung ist damit
allgemeiner *und* billiger als in der Frage veranschlagt.

Task 1 ist entblockt.

### 2026-08-24 — v4 (24 S.): abstrakter Regularisierungssatz

Auf Nachfrage des Nutzers nach einer CPS-Verallgemeinerung von Thm. 4.1 (→ D11).
§4 ist jetzt zweigeteilt: §4.1 abstrakte Fassung (Setting 4.1, Def. 4.1
regularisierende Klasse, Thm. 4.2, Rem. 4.3 „What the abstract form buys"),
§4.2 der Markovsche Fall als Korollar. Der ausführliche Beweis ist von Thm. 4.3
nach Thm. 4.2 gewandert; Rem. 4.4 (Rollen der beiden Trennungsannahmen),
Rem. 4.5 (keine lokale Fassung) und Rem. 4.6 (compact containment) unverändert
angehängt.

Nachgezogen: Verwendungstabelle §2.6 (Facts 2.9, 2.10, 2.35 zeigen jetzt auf
Thm. 4.2), §8 (F4) und die Aufspaltung (F5) → (F5a)/(F5b) aus D8.
Kompiliert, 24 Seiten, keine undefinierten Referenzen, 2 Overfull-Boxen
(3,8 pt und 1,6 pt).

### 2026-08-24 — v5 (29 S.): §5 und §6 abstrahiert

Nachfrage des Nutzers: „Findest Du zu den beiden anderen nicht in CPS
vorkommenden Resultaten auch noch Versionen im CPS Setting?" — gemeint sind
EK86 4.4.2 (Manuskript §5) und EK86 4.4.11 (§6). Beides ja, mit sehr
verschiedenem Ergebnis.

* **§5** (→ D12): geht vollständig durch, und der ganze Satz reduziert sich auf
  *ein* Lemma (Restart), das viermal angewandt wird. §5 ist jetzt
  §5.1 (Setting, Lem. 5.3 Mischungsstabilität, Def. 5.4 Shift-Stabilität,
  Lem. 5.5 Restart, Thm. 5.6 abstrakte Eindeutigkeit/Markov, Thm. 5.7 starke
  Markoveigenschaft, Rem. 5.8) + §5.2 (EK86 4.4.2 als Korollar, Beweis auf eine
  Hypothesenprüfung geschrumpft). Nebenprodukt: **Q3 beantwortet** —
  Shift-Invarianz von $q$ ist genau die Shift-Stabilität.
* **§6** (→ D13, D14): auf der Prozessseite nichts zu holen, dafür auf der
  Uhrseite eine scharfe Antwort. Neu §6.1 mit der Kettenidentität (Lem. 6.1),
  Prop. 6.2 (welche Uhren Dualität zulassen), Rem. 6.3 (Konventionskollision),
  Rem. 6.4 (Reichweite von §6), und Cor. 6.10 Dualität für Markovketten.
  §6.2 ist die bisherige kontinuierliche Theorie.

Nachgezogen: Verwendungstabelle §2.6 (Facts 2.30, 2.13 zeigen jetzt auf die
abstrakten Sätze), §8 (F2) und (F3). Neues Makro `\T`.

Kompiliert, 29 Seiten, keine undefinierten Referenzen, 1 Overfull-Box (1,6 pt).

**Offen für den Nutzer:** D14 stellt Q8 neu — $(0,t]$ kostet die diskrete
Dualität, nicht nur die Doob-Zerlegung.

### 2026-08-24 — v6 (34 S.): Task 1 abgeschlossen

Der Nutzer hat Option 2 gewählt (→ D15). Umgesetzt:

* **§2.2 „The time index and the clock"** neu: Def. 2.1 (Bündel), Def. 2.2
  (Uhr, nach D9), Ex. 2.3 (die vier Uhren: $\mathbb{R}_+$/Lebesgue,
  $\mathbb{N}_0$/Zählmaß, $\mathbb{R}_+$ mit Atomen, $\mathbb{R}_+^d$/Lebesgue),
  Rem. 2.4 (Konvention $(0,t]$, mit Verweis auf die Kollision aus D14).
* **§1.3** um einen Absatz „Abstract time index" ergänzt; Abstract nachgezogen.
* **§3** vollständig auf $\mathbb{T}$ und $q$ umgeschrieben: eq. (2)
  ($^{*}\mathcal{F}^X$), Def. 3.x, Prop. 3.6 samt Beweis. Prop. 3.6 gilt unter
  (T0)+Uhr, und der Beweis sagt jetzt explizit, dass die Additivität
  $(t_n,t_{n+2}]=(t_n,t_{n+1}]\uplus(t_{n+1},t_{n+2}]$ aus der Transitivität
  kommt.
* **Bündel-Tags** in jedem Satzkopf von §3 bis §7.
* **§2.8 „Which result needs which bundle"** — die Ergebnistabelle aus
  `PLAN.md` §1d.
* **§8**: jeder Schritt (F1)–(F5b) nennt sein Zielbündel, mit der Notiz, dass
  (F1), (F5a) und die Hälfte von (F2) unter Mathlibs `[Preorder ι]` leben.
* **Rem. 5.6** und **Rem. 6.4** neu — die beiden Stellen, an denen der
  Halbordnungsfall stirbt.
* §4: Beweis der Markovschen Fassung auf die allgemeine Uhr umgestellt (die
  „Lipschitz"-Aussage ist jetzt der Spezialfall $q=\lambda$); $\mathbb{Q}$ durch
  das abzählbar dichte $D$ ersetzt.
* §5: Shift-Stabilität wird jetzt aus der Shift-Invarianz von $q$ hergeleitet,
  mit der ausdrücklichen Bemerkung, dass der Satz ohne sie falsch ist.

Kompiliert, 34 Seiten, keine undefinierten Referenzen, 1 Overfull-Box (1,6 pt).
`PLAN.md`: Task 1 und 1c/1d auf `done`, Q1 und Q6 beantwortet, (T2) in
(T2a)/(T2b) aufgespalten, 1b korrigiert.

### 2026-08-24 — EK86 §2.8 gegengelesen, drei Korrekturen

Der Nutzer bat um einen Abgleich mit dem, was EK selbst zu allgemeinen
Indexmengen sagen. Ergebnis in D16. Kurz:

* Der Verband wird für $\vee$ gebraucht, **nicht** für $\wedge$ — EK Rem. 2.8.3
  sagt ausdrücklich, dass $\tau\wedge a$ keine Stoppzeit sein muss. Meine
  Motivation für (T1) stand auf dem Kopf, in `PLAN.md` §1a wie in §2.2.
* (T1′) kommt im Manuskript **gar nicht** vor, nicht „einmal" (D15 war zu
  großzügig). Tag von Thm. 5.7 auf (T2b)+(T4) korrigiert.
* Meine (T1′)-Beschreibung fehlte die Stetigkeit der Verbandsoperationen.

Bestätigt wurde dagegen die Hauptsache: EK indizieren **nie einen Prozess** mit
$\mathbb{R}_+^d$ — in Kap. 6 trägt der Mehrparameterindex nur Filtration und
Stoppzeiten. Es gibt also keinen EK-Satz, der Rem. 5.6 widerspräche, und ihre
eigene Martingaldefinition (8.15) ist für halbgeordnete Indizes formuliert, also
genau die (T0)-Schicht.

Neu: **Rem. 2.5** im Manuskript, „Comparison with EK86, Section 2.8", vier
Punkte. Kompiliert, 34 Seiten, keine undefinierten Referenzen, 1 Overfull-Box.

### 2026-08-24 — Nachaudit, v8 (35 S.)

Nachfrage des Nutzers: „Ist das nun alles im Plan und im tex-File mit drin?"
Systematisch nachgezählt statt behauptet (→ D17). §3–§7 waren umgestellt und
getaggt, **§2.4 aber nicht** — und da §4 seine Regularisierungs-Facts von dort
bezieht, war das eine echte Inkonsistenz, keine Kosmetik. Behoben, plus sechs
kosmetische Reste, plus (T3)-Kopfzeile für §2.5, plus vier neue Zeilen in der
Bündeltabelle.

Kompiliert, 35 Seiten, keine undefinierten Referenzen, 1 Overfull-Box (1,6 pt).

### 2026-08-24 — §1.2 richtiggestellt

Der Nutzer hat gemeldet, dass in §1.2 inzwischen Falsches steht. Zutreffend: der
Abschnitt stammte aus v1 und behauptete, Eindeutigkeit, Markoveigenschaft und
Dualität seien „genuinely statements about an operator $A$ and its domain" und
im CPS-Rahmen nicht formulierbar — genau das Gegenteil dessen, was §4–§6 seit
v5 tun. Ferner stand dort „all characterization results are stated on this
[EK-] layer", was seit v5 ebenfalls nicht mehr stimmt.

§1.2 neu geschrieben: drei Schichten statt zwei, der Irrtum ausdrücklich
benannt, und die zwei Gründe, die trotzdem gegen „nur CPS" sprechen (CPS23
enthält die drei Sätze nicht; die EK-Schicht ist die anwendbare). Abstract
nachgezogen. §1.1: Pfadraum $E^{\mathbb{T}}$ statt $E^{\mathbb{R}_+}$.
Begründung von D1 entsprechend korrigiert.

Kompiliert, 35 Seiten, keine undefinierten Referenzen, 1 Overfull-Box.

### 2026-08-24 — Kallenberg gegengelesen, v9 (37 S.)

→ D18. Zwei echte Lücken geschlossen: **Lem. 5.3 (Disintegration)** neu, und
**Rem. 5.10** zum lokalen MP im abstrakten Rahmen mit (L1)/(L2). Beides nach
Kallenberg Thm. 32.10/32.11 (dort Stroock–Varadhan zugeschrieben). Ferner
Rem. 5.4 (Einordnung, und dass Cor. 6.14 dadurch besser wird), Rem. 5.14 um den
Hinweis auf den alternativen Lokalisierungsweg ergänzt, §1.3 um einen Absatz zur
lokalen Theorie, Bündeltabelle und Bibliographie nachgezogen.

Kompiliert, 37 Seiten, keine undefinierten Referenzen, 1 Overfull-Box (1,6 pt).

### 2026-08-24 — v10 (41 S.): lokale Theorie durchgeführt, J&S eingearbeitet

Task 2.2b erledigt (→ D19): §5.2 neu, mit Def. 5.11, Lem. 5.13, Lem. 5.15,
Lem. 5.17, Thm. 5.18 und Rem. 5.12/5.14/5.16/5.19/5.20 — alles bewiesen, nichts
durchgewunken.

Jacod & Shiryaev gegengelesen (→ D20): fünf Punkte, davon eine **Korrektur an
mir** (Konvexität ist hypothesenfrei), eine **Verstärkung** ((L1) als
Konstruktion, Lem. 5.15), eine **Prioritätsfrage** (die abstrakte Formulierung
ist J&S 1987, Rem. 3.6) und zwei **offene Punkte** (geshiftetes Problem →
Zeitinhomogenität; lokale Eindeutigkeit), beide in Rem. 5.19 benannt und in
`PLAN.md` als Task 2.2c/2.2d eingetragen.

Bibliographie um `JS03` und `Kal21` ergänzt. Kompiliert, 41 Seiten, keine
undefinierten oder doppelten Referenzen, 2 Overfull-Boxen (0,7 und 1,6 pt).

### 2026-08-24 — v11 (41 S.): Task 2c

Shift-Systeme statt Shift-Stabilität (→ D21), §1.1 nachgezogen (→ D22).
Kernpunkt: die Shift-Invarianz der Uhr ist keine Hypothese mehr, sondern das
Kriterium dafür, ob der resultierende Markovprozess homogen ist. Neu Ex. 5.7
(geshiftetes Problem für $\mathbb{X}_A$ mit zurückgezogener Uhr $q_r$) und
Rem. 5.6 (warum $\mathbb{X}^\circ_r=\mathbb{X}^\circ$ eine echte Einschränkung
ist).

Kompiliert, 41 Seiten, keine undefinierten oder doppelten Referenzen,
2 Overfull-Boxen (0,7 und 1,6 pt).

Offen bleibt aus D20: **Task 2d** (lokale Eindeutigkeit nach J&S III.2.37/2.40).
Sie wird durch 2c erst zugänglich, weil J&S Thm. III.2.40 genau die
Markov-Struktur im Sinne der Shift-Systeme voraussetzt.

### 2026-08-24 — v12 (43 S.): Task 2.1

Prop. 3.7 vollständig bewiesen (→ D23), mit Korrektur der Aussage: beliebige
endliche Zeitmengen statt Ketten. Neu Rem. 3.8. Damit ist die einzige Lücke auf
dem kritischen Pfad von (F1) geschlossen.

Kompiliert, 43 Seiten, keine undefinierten oder doppelten Referenzen,
3 Overfull-Boxen (≤ 1,9 pt).

### 2026-08-24 — v13 (44 S.): Task 2.8

Abstrakter Konvergenzsatz bewiesen (→ D24). §7 jetzt dreigeteilt wie §4 und §5:
§7.1 EK-Fassung, §7.2 abstrakter Satz mit Beweis, §7.3 CPS-Fassung als Instanz.
Damit ist auch (F5a) entblockt.

Kompiliert, 44 Seiten, keine undefinierten oder doppelten Referenzen,
3 Overfull-Boxen (≤ 1,9 pt).

Offene Task-2-Punkte: 2.2 (Lem. 3.10), 2.2d (lokale Eindeutigkeit), 2.3
(Fact 2.40), 2.5 (Thm. 6.6). Keiner davon blockiert (F1), (F2) oder (F5a).

### 2026-08-24 — v14 (46 S.): Zustandsraum abgestuft

→ D25. Bündel (E0)–(E3) analog zu (T0)–(T4), durchgetaggt, Tabelle um eine
Spalte erweitert. Kernaussage: §3, §5 und §6 brauchen von $E$ nur die
Messbarkeit (plus standard-borelsch an drei Stellen), und das macht sie ohne
neuen Beweis auf distributionswertige Prozesse anwendbar.

Kompiliert, 46 Seiten, keine undefinierten oder doppelten Referenzen,
4 Overfull-Boxen (≤ 1,9 pt).

### 2026-08-24 — v15 (51 S.): Task 2 abgeschlossen

2.2, 2.3, 2.5 und 2.2d erledigt (→ D26); dazu der Literaturfund zum càdlàg-Raum
(→ D27). Neu: Rem. 2.44 (Beweis von Fact 2.43), Beweis von Lem. 3.11 mit
Rem. 3.12, §5.3 „Local uniqueness" (Def. 5.23/5.24, Lem. 5.25, Thm. 5.26,
Rem. 5.27), vier Schritte in Thm. 6.6, Rem. 8.1 zum brownian-motion-Repo.

**Task 2 ist damit vollständig.** Kompiliert, 51 Seiten, keine undefinierten oder
doppelten Referenzen, 5 Overfull-Boxen (max 7,7 pt).

### 2026-08-24 — v16 (52 S.): Q5 und Q8, Umzug

→ D28. Dateien nach `Journal/Blog/MartingaleProblem/` verschoben,
`Journal/Notes/MartingaleProblem/` für Lean freigeräumt. Beide
Kompensator-Konventionen werden geführt, mit $\iota$ als Parameter in Def. 3.5.

Kompiliert, 52 Seiten, keine undefinierten oder doppelten Referenzen,
5 Overfull-Boxen (max 7,7 pt).

**Alle offenen Fragen außer Q4 sind beantwortet. Task 3 ist entblockt.**

### 2026-08-24 — v17 (56 S.): Existenztheorie

→ D29. §7 heißt jetzt „Existence" mit sechs Unterabschnitten und vier Routen.
Neu: §7.1 (aus einer Halbgruppe), §7.2 (Sprungprozesse, mit vollem Beweis),
§7.3 (SDEs, zitiert); §7.4–7.6 sind die bisherigen Konvergenzabschnitte.
Bündeltabelle, Abstract, §1.3 und §8 (neuer Schritt F0) nachgezogen.

Kompiliert, 56 Seiten, keine undefinierten oder doppelten Referenzen,
5 Overfull-Boxen (max 7,7 pt).

### 2026-08-24 — v18 (58 S.): verschiedene Uhren

→ D31. Neu §7.7 mit Setting 7.24, Thm. 7.25 (Uhrenwechsel), Rem. 7.26,
Ex. 7.27 (Invarianzprinzip) und Rem. 7.28. Bündeltabelle und Rem. 7.23
nachgezogen.

Kompiliert, 58 Seiten, keine undefinierten oder doppelten Referenzen,
5 Overfull-Boxen (max 7,7 pt).

### 2026-08-24 — v19 (59 S.): bp-Limes abgeschwächt

→ D32. Neu Lem. 3.10, Cor. 3.11, Rem. 3.12 und Rem. 2.30; Fact 2.29
zusammengestrichen; Tabelle und §9 nachgezogen.

Kompiliert, 59 Seiten, keine undefinierten oder doppelten Referenzen,
5 Overfull-Boxen (max 7,7 pt).

### 2026-08-25 — v20 (63 S.): nicht-Markovsche Schicht

→ D33, D34. §5 in sechs Unterabschnitte umsortiert; Def. 5.5/Prop. 5.6
(Eindeutigkeit ohne Markov, für beliebige Maßfamilien), Lem. 5.11 (Shift ⟹ (U)),
Rem. 5.13; neu §5.5 mit Ex. 5.32 (Volterra), Ex. 5.33 (pfadabhängige
Semimartingale) und Rem. 5.34 (Audit-Tabelle). Abstract, §1.2, Bündeltabelle und
§5.3 nachgezogen.

Kompiliert, 63 Seiten, keine undefinierten oder doppelten Referenzen,
5 Overfull-Boxen (max 7,7 pt).

### 2026-08-25 — v21 (65 S.): weak-strong convergence, Neustart korrigiert

→ D35, D36. Neu §7.8 (weak-strong convergence, mit dem Atom-Gegenbeispiel) und
Lem. 5.5 / Rem. 5.6 (Neustart mit Gedächtnis). Rem. 5.15, Rem. 5.36 und Rem. 7.23
nachgezogen.

Kompiliert, 65 Seiten, keine undefinierten oder doppelten Referenzen,
5 Overfull-Boxen (max 7,7 pt).

### 2026-08-25 — v22 (67 S.): Hawkes und Volterra

→ D37. Neu §7.9 mit Setting 7.35, Thm. 7.37 (pfadabhängige Rate, bewiesen),
Ex. 7.39 (Hawkes), Rem. 7.40 (Hawkes = Volterra), Thm. 7.41 (Konvergenz) und
Rem. 7.42. Bündeltabelle erweitert und dreigeteilt, §7-Einleitung nachgezogen,
`JR16` in der Bibliographie.

Kompiliert, 67 Seiten, keine undefinierten oder doppelten Referenzen,
7 Overfull-Boxen (max 7,7 pt), keine Seitenüberläufe mehr.

### 2026-08-25 — v23 (67 S.): Task 16

→ D38. §5.4 neu: Def. 5.30/5.31, Lem. 5.32, Thm. 5.33, Cor. 5.34 (Markovscher
Fall), Rem. 5.35. Audit-Tabelle, Ex. 5.34/5.35, Rem. 5.23 und die Bündeltabelle
nachgezogen.

Kompiliert, 67 Seiten, keine undefinierten oder doppelten Referenzen,
7 Overfull-Boxen (max 7,7 pt).

### 2026-08-25 — v24 (85 S.): Task 17 und Task 18

→ D39–D44. Konsistenz-Durchgang mit Prüfung jedes Arguments: §6-These korrigiert
(neu Lem. `rectify`, Thm. `anyclock`), `L1auto` auf strikte Stoppzeiten,
`localrestart` zweistufig, `absstrongmarkov` eingeschränkt, `ex:invariance`
Konvention, `jumpwellposed` neu bewiesen, `pathjumpMP` zweiteilig,
`atomicdiscontinuity` korrigiert. Neu §7.2 „From a dual process" (DGP24) mit
Fact `kolmogorov`. §8/§9 und die Bündeltabellen nachgezogen; Lem. `EKconv` ist
jetzt Korollar von Thm. `absconv`.

### 2026-08-25 — v25 (84 S.): weak-strong convergence entbehrlich

→ D42. Neu Lem. `contuse`, Thm. `absconvaug`, Prop. `atomaug`, Rem. `C1aug`,
Rem. `augvsws`. §7.8 heißt jetzt „Relaxing the continuity hypothesis"; die
weak-strong-Schicht bleibt als Literaturbezug stehen, wird aber für nichts im
Manuskript gebraucht.

### 2026-08-25 — v26 (90 S.): fibrierter Zustandsraum und Pfad-Lift

→ D45, D46, D49. Def. `Efibred` mit Audit und Begründung; Def. `pathlift`,
Lem. `liftmarkov`, Rem. `liftcollapse` („jeder Prozess ist Markov, und genau
deshalb ist es wertlos"); Rem. `liftform` zur Frage, ob das allgemeine MP ein
Spezialfall des Markovschen ist.

### 2026-08-25 — v27 (96 S.): Task 19 am Hawkes-Prozess

→ D47, D48, D50. Setting `historical`, Lem. `histrestart`; dann die vollständige
Verifikation am Hawkes-Prozess (Setting `hawkesdual`, Lem. `hawkesflow`,
Prop. `hawkesduality`, Prop. `hawkesDcheck`, Cor. `hawkesrestart`). Nach dem
Literaturcheck Rem. `hawkesknown` ergänzt: die Dualität ist klassisch (Cluster,
affine Transformformel, Markovscher Lift); fünf Referenzen aufgenommen.

### 2026-08-25 — v28 (98 S.): Audit der Verallgemeinerungen

→ D51. Neu §1.4 mit Tabelle; Rem. `complexvalued` und Rem. `inequalitystable`
(Submartingalprobleme) als die beiden gratis verfügbaren Verallgemeinerungen.
Tasks 21 und 22 notiert.

Kompiliert, 98 Seiten, keine undefinierten oder doppelten Referenzen,
8 Overfull-Boxen (max. 7,7 pt).
