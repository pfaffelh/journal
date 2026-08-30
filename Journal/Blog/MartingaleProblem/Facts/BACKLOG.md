# Rückstau

Damit nie ein Lauf ohne Arbeit dasteht. Der Prompt schickt einen Lauf hierher,
wenn die vorrangigen Aufgaben leer sind, das Inventar geschlossen ist und Task 23
gerade nicht weiterkommt. **Von oben nach unten**; wer einen Punkt erledigt,
streicht ihn hier und berichtet im Inventar unter „Läufe".

Wer einen Punkt für erledigt hält, ohne ihn erledigt zu haben, schadet mehr als
ein Lauf, der nichts tut. Im Zweifel: Punkt stehen lassen, Zwischenstand
anhängen.

## Offen

1. **EK Thm. 4.3.12 in die abstrakte Sprache heben.** Quasi-Linksstetigkeit:
   unter den Voraussetzungen von `thm:cadlag` gilt
   $P\{\lim_n X(\tau_n)=X(\tau),\ \tau<\infty\}=P\{\tau<\infty\}$ für
   aufsteigende Stoppzeiten. Der Beweis ist optional sampling plus Separiertheit
   von $\dom(A)$. Zu klären: geht es wie `thm:absreg` ohne Operator, allein über
   $\XX$ und eine regularisierende Klasse? Wenn ja, gehört es als Meilenstein zu
   `MartingaleProblems` M9 und als Satz ins Manuskript hinter `thm:cadlag`.

2. **EK §4.3 zu Ende auswerten.** Zitiert werden 4.3.1, 4.3.5, 4.3.6. Offen sind
   Thm. 4.3.8, Prop. 4.3.9/4.3.10 (die Anwendung steht seit dem 2026-08-30 in
   M9, der Satz selbst nicht im Manuskript) und Cor. 4.3.13. Für jede: trägt sie
   etwas, das das Manuskript braucht, und wenn ja, wo?

3. **`SkorokhodSpace` Meilenstein 2 zerlegen.** Nach `Facts/PRAEORDNUNG.md`
   Teil 2 setzt der Kopf `[Preorder ι] [TopologicalSpace ι]`, aber vier Punkte
   brauchen \eqref{T2b}. Vorschlag ausarbeiten: Prädikat und Sprungtheorie
   trennen, mit den Hypothesen je Punkt.

4. **`rem:skorokhodform` Stelle 2238 korrigieren.** Dort heißt
   `[Preorder ι] [TopologicalSpace ι]` „\eqref{T2b}"; das ist falsch, (T2b)
   verlangt mehr. Manuskriptänderung, also erst nach `check.py`.

5. **Die vier Facts ohne tragende Fundstelle abschließen.** `fact:fdd` und
   `fact:portmanteau` sind noch offen; für `fact:doob` und
   `fact:stoppedlocalmg` ist es geklärt. Implizit benutzt oder entbehrlich?

6. **Task 23, unvergleichbare Atome.** Der offene Punkt aus
   `Task23/PROTOKOLL.md`: die Vermutung ist durch $58081$ Konfigurationen
   belegt, der Beweis fehlt. Ansatzpunkt steht dort unter „Wo der Beweis hakt":
   die einzelnen Gleichungen über der Antikette der maximalen Elemente von
   $\T_{<t^*}$.

7. **Prüfen, ob die Roadmaps noch zu Mathlib master passen.** Alle zitierten
   Deklarationen gegen master, auf Existenz und `deprecated`. Am 2026-08-29
   fanden sich so drei Fehler. Sinnvoll etwa alle zwei Wochen.
