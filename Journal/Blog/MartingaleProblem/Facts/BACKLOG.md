# Rückstau

Damit nie ein Lauf ohne Arbeit dasteht. Der Prompt schickt einen Lauf hierher,
wenn die vorrangigen Aufgaben leer sind, das Inventar geschlossen ist und Task 23
gerade nicht weiterkommt. **Von oben nach unten**; wer einen Punkt erledigt,
streicht ihn hier und berichtet im Inventar unter „Läufe".

Wer einen Punkt für erledigt hält, ohne ihn erledigt zu haben, schadet mehr als
ein Lauf, der nichts tut. Im Zweifel: Punkt stehen lassen, Zwischenstand
anhängen.

## Offen

1. **`rem:skorokhodform` Stelle 2238 korrigieren.** Dort heißt
   `[Preorder ι] [TopologicalSpace ι]` „\eqref{T2b}"; das ist falsch, (T2b)
   verlangt mehr. Manuskriptänderung, also erst nach `check.py`.

2. **Die vier Facts ohne tragende Fundstelle abschließen.** `fact:fdd` und
   `fact:portmanteau` sind noch offen; für `fact:doob` und
   `fact:stoppedlocalmg` ist es geklärt. Implizit benutzt oder entbehrlich?

3. **Task 23, unvergleichbare Atome.** Der offene Punkt aus
   `Task23/PROTOKOLL.md`: die Vermutung ist durch $58081$ Konfigurationen
   belegt, der Beweis fehlt. Ansatzpunkt steht dort unter „Wo der Beweis hakt":
   die einzelnen Gleichungen über der Antikette der maximalen Elemente von
   $\T_{<t^*}$.

4. **Prüfen, ob die Roadmaps noch zu Mathlib master passen.** Alle zitierten
   Deklarationen gegen master, auf Existenz und `deprecated`. Am 2026-08-29
   fanden sich so drei Fehler. Sinnvoll etwa alle zwei Wochen.

5. **Die Uhr im Konvergenzteil auf Atome hin durchgehen.** Der Lauf vom
   2026-08-30 hat gezeigt, dass die c\`adl\`ag-Modifikation Atome der Uhr
   verträgt und die Quasi-Linksstetigkeit nicht. Zu prüfen ist, welche weiteren
   Aussagen des Manuskripts still auf Atomlosigkeit rechnen: Kandidaten sind
   `rem:EKrelcompact` und die Straffheitskriterien von §7, weil beide die
   Konvergenz der Pfade an festen Zeitpunkten benutzen. Je Aussage: die Stelle
   nennen, an der ein Atom stören würde, oder festhalten, dass keine da ist.
