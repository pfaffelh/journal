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

1. **`rem:skorokhodform` Stelle 2238 korrigieren.** Dort heißt
   `[Preorder ι] [TopologicalSpace ι]` „\eqref{T2b}"; das ist falsch, (T2b)
   verlangt mehr. Manuskriptänderung, also erst nach `check.py`. *Zwischenstand
   2026-08-31: dieser Punkt liegt außerhalb dessen, was ein Lauf tun darf. Die
   nicht verhandelbare Regel 2 des Auftrags — „Das Manuskript wird nicht
   verändert" — lässt nur Task 23 als Ausnahme zu, und diese Korrektur gehört
   nicht dazu. Der Befund steht seit dem 2026-08-30 unter den Auffälligkeiten
   des Inventars mit dem Beleg aus `PRAEORDNUNG.md` Teil 2; ausführen muss ihn
   der Nutzer.*

2. **Task 23, unvergleichbare Atome.** Der offene Punkt aus
   `Task23/PROTOKOLL.md`: die Vermutung ist durch $58081$ Konfigurationen
   belegt, der Beweis fehlt. Ansatzpunkt steht dort unter „Wo der Beweis hakt":
   die einzelnen Gleichungen über der Antikette der maximalen Elemente von
   $\T_{<t^*}$. *Zwischenstand 2026-08-31, vierter Lauf: der Fall ist auf eine
   einzige Aussage eingeschränkt. Die **Idealreduktion** — jede
   abwärtsabgeschlossene Teilmenge, die das kleinste Element enthält, erbt
   $(\diamondsuit)$ samt $\delta$ — gibt mit der Induktion über $|\T|$ sofort
   $\delta(s)=0$ für jedes $s$ außer einem größten Element. Zu zeigen bleibt (R):
   auf einer Halbordnung mit kleinstem Element $0$ und größtem Element $z$ ist
   $\Psi(z,z)=0$. Nullmassen oberhalb von $0$ darf man dabei streichen. Der
   Defekt hat dort die Gestalt $\delta(z)=\sum_{c<z}m_c\kappa(c,0)$, einer Summe,
   die über jedes echte Hauptideal verschwindet, und (R) folgt aus der
   nachgerechneten Vermutung (C4$^+$) „$\Psi(a,x)=0$ für $a<x$" in vier Zeilen.
   Alles am Quelltext von `antisym.py` und `reduction.py` geprüft; Einzelheiten
   im PROTOKOLL, Abschnitt „Der Halbordnungsfall, 2026-08-31 (vierter Lauf)".
   Der nächste Lauf beweist (C4$^+$) oder widerlegt sie.*
   *Zwischenstand 2026-08-31, fünfter Lauf: (C4$^+$) steht weiter (jetzt
   $12\,564$ Konfigurationen ohne Ausfall), aber der Hebel, mit dem sie bewiesen
   werden sollte, ist **widerlegt**: die termweise Fassung (C5)
   „$m_c\kappa(c,x)=0$, sobald $c<b<x$" ist schon bei lauter Massen $1$ falsch,
   Zeuge $0<\{3,4\}<2<1$ mit freiem $\kappa(3,1)$ (`c5.py`). Dafür ist ein Stück
   des Falles **bewiesen**: liegt unter $t$ nur eine Antikette von Atomen und ist
   deren Gesamtmasse $\neq0$, so gilt $\delta(t)=0$ und (C4$^+$) an $t$ — mit
   beliebigen Vorzeichen der Massen, also einschließlich des Diamanten, dessen
   Begründung im Manuskript seit dem 2026-08-30 fehlt. Beweis, scharfe
   Hypothese und die $102\,930+15\,571$ nachgerechneten Fälle stehen im
   PROTOKOLL, Abschnitt „Der Halbordnungsfall, 2026-08-31 (fünfter Lauf)"; neu
   sind `flat.py`, `c5.py` und `certificate.py`. Offen bleibt (R) für ein $t$,
   unter dem eine Kette $0<a<b<t$ liegt; der nächste Lauf setzt dort an, mit
   `certificate.py` am Zeugen $0<\{3,4\}<2<1$.*

3. **Prüfen, ob die Roadmaps noch zu Mathlib master passen.** Alle zitierten
   Deklarationen gegen master, auf Existenz und `deprecated`. Am 2026-08-29
   fanden sich so drei Fehler. Sinnvoll etwa alle zwei Wochen. *Am 2026-08-31,
   dritter Lauf, ist die Liste „What Mathlib already has" von `WeakConvergence`
   erledigt: elf Deklarationen, alle vorhanden, keine `deprecated`. Es fehlen
   also noch die drei übrigen Roadmaps und die Zitate in den Meilensteinen.*

4. **Die Grundtheorie von `ProbabilityMeasure E` als metrischem Raum
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
