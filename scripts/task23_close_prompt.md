Du schließt **Task 23** ab. Du bist in einem git-Worktree auf dem Branch
`task23-atomic-duality`. Zeitbudget: 120 Minuten.

Dies ist **kein Forschungslauf.** Die Suche ist beendet; was fehlt, ist die
Verschriftlichung. Sechsunddreißig Läufe haben 54 numerierte Resultate ins
Protokoll geschrieben, im Manuskript stehen 15 Marken. Diese Lücke zu schließen
ist Deine ganze Aufgabe.

## Die eine Regel, die alles andere überwiegt

**Kein neues Theorem.** Findest Du beim Aufschreiben eines — und Du wirst
versucht sein, denn die letzten drei Läufe haben ihre eigene Vorgabe jeweils
überflüssig gemacht —, dann kommt es ins Protokoll und **nicht** ins Manuskript,
und Du arbeitest weiter am Abschluß. Ein Lauf, der §6 fertig macht, ist heute
mehr wert als ein weiterer Satz.

## Zuerst

Lies `Journal/Blog/MartingaleProblem/Task23/PROTOKOLL.md` **von Lauf 28 bis zum
Ende** (die früheren Läufe sind im Manuskript verarbeitet), dann §6 des
Manuskripts und die Statustabelle in `rem:atomsnotchange`.

## Die fünf Punkte, in dieser Reihenfolge

1. **Eintrag 34 zu Ende schreiben.** Der vierunddreißigste Lauf ist an der
   Sitzungsgrenze des Kontos abgebrochen, mitten im Eintrag: Lemma 40,
   Theorem 41, Theorem 42, Korollar 42.1, Lemma 40', Theorem 42' stehen da,
   aber es fehlen `### Ergebnis`, `### Sackgassen` und `### Vorschlag`. Schreibe
   sie, aus dem, was im Eintrag steht — nicht aus neuer Rechnung. Die Meßdateien
   `Task23/silent_chains.txt` und `Task23/disjoint_cores.txt` gehören dazu.

2. **Die Ernte einfahren.** Theoreme 38 bis 42' gehören ins Manuskript, §6,
   in der Ordnung, die dort schon angelegt ist (nach `rem:corereduction`, vor
   `rem:twomethods`). Theorem 38 und 39 stehen bereits; 40 bis 42' fehlen ganz.
   Kürze, wo das Protokoll ausführlicher ist als ein Manuskript sein darf: im
   Manuskript steht die Aussage mit Beweis, nicht der Weg dorthin.

3. **Die Statustabelle wird die maßgebliche Bilanz.** Heute nennt sie eine
   offene Zeile („countable with atoms lacking a minimum"), das Protokoll nennt
   drei lose Enden — die nackte Klasse auf Ketten, die gestapelten
   $\zeta$-Ketten ohne (F) und ohne beschränktes $\Phi$, und die Vermutung
   „endliche Ideale unter $t^*$, $W$ ohne maximale Elemente $\Rightarrow$
   Dualität". **Prüfe zuerst, welche davon die Theoreme 40 bis 42' inzwischen
   erledigt haben**, und trage dann jede verbliebene als eigene Zeile ein. Jede
   Zeile der Tabelle zitiert ein numeriertes Resultat oder ein Gegenbeispiel;
   eine Zeile ohne Beleg ist ein Fehler.

4. **Eine Schlußbemerkung „Stand und Grenze"** am Ende von §6. Sie sagt in
   Prosa: die drei Mechanismen (Idealausschöpfung, endliche Kernreduktion,
   Stapelausschöpfung), daß sie **weder (F) noch ein Vorzeichen an $m$**
   brauchen; daß die Zertifikatsmethode hinreichend und nicht notwendig ist
   (Theorem 37 des Protokolls, `prop:nocertificate`); die zwei Gegenbeispiele,
   die die Grenze scharf machen; und was offen bleibt, benannt statt umschrieben.

5. **`PLAN.md`, Task 23:** Status von `todo` auf `abgeschlossen mit benannter
   Grenze`. Die veraltete Vier-Zeilen-Tabelle dort ersetzt Du durch einen
   Verweis auf `rem:atomsnotchange` und die vier Lean-Ziele, die in
   `TauCeti/MartingaleProblems/README.md` schon eingetragen sind
   (`duality_of_atomic_idealExhaustion`, `duality_of_atomic_finiteCoreReduction`,
   `Matrix.krylovCertificate_unique`, `convex_recursion_bound`). Task 23 endet
   als Mathematik und geht als Formalisierung weiter; schreibe das hin.

## Regeln, die unverändert gelten

1. **Jede Zahl, die Du ins Manuskript schreibst, ist am Orakel oder an der
   Meßdatei belegt.** Du rechnest in diesem Lauf wenig; was Du zitierst, hat
   einen Beleg im Protokoll.
2. **`python3 Journal/Blog/MartingaleProblem/check.py` muß `clean` melden**,
   bevor Du fertig bist. Fällt er durch, reparierst Du, bis er clean ist.
3. **Nur dieser Branch.** Kein Wechsel auf `master`, kein Merge, kein Force-Push.
4. **Kein Vortäuschen.** Was Du nicht unterbringst, schreibst Du als
   unerledigt ins Protokoll.

## Am Ende, verpflichtend

Ein letzter Protokollabschnitt **„Abschluß von Task 23"** mit Datum: was ins
Manuskript gewandert ist (mit Marken), wie die Statustabelle jetzt lautet
(vollständig abgeschrieben), was offen bleibt und warum, und die Seitenzahl aus
`check.py`. Schreibe ihn **fortlaufend** mit, nicht erst am Schluß — die
Sitzungsgrenze des Kontos hat den letzten Lauf mitten im Satz beendet.
