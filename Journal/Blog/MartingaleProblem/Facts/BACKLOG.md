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
   $\T_{<t^*}$.

3. **Prüfen, ob die Roadmaps noch zu Mathlib master passen.** Alle zitierten
   Deklarationen gegen master, auf Existenz und `deprecated`. Am 2026-08-29
   fanden sich so drei Fehler. Sinnvoll etwa alle zwei Wochen.

4. **Den Abnehmer der konvergenzbestimmenden Produkthälfte finden oder
   ausschließen.** Der Lauf vom 2026-08-31 hat belegt, dass der Produktpunkt von
   `WeakConvergence` Meilenstein 1 heute von keinem Punkt der vier Roadmaps und
   von keinem Beweis des Manuskripts benutzt wird. Der eine Kandidat, der übrig
   bleibt, ist `SkorokhodSpace.tendsto_of_isTight_of_tendsto_finiteDimensional`
   (M8): dessen Vorlage ist \EK{} Thm. 3.7.8, und `fact:fdd` wird im Manuskript
   unter anderem \EK{} Prop. 3.7.1 zugeschrieben, also der
   konvergenzbestimmenden Produkthälfte. Ob 3.7.8 sie im Beweis wirklich
   benutzt, ist am Scan zu klären; findet sie sich dort, nennt M8 sie als
   Vorbedingung, sonst hält der Produktpunkt fest, dass sein einziger Grund §9
   des Manuskripts ist. Achtung: `references/EthierKurtz1986.pdf` ist aus dem
   Worktree `journal-facts` **nicht** erreichbar — frühere Läufe haben den Scan
   gelesen, dieser konnte es nicht.
