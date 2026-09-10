#!/usr/bin/env bash
# Ein Lauf am Formalisierungs-Inventar (Fact-Aussagen des Manuskripts).
# aufgerufen.  Bauform uebernommen von scripts/run_iteration.sh des
# ratchet-Projekts; die dort teuer gelernten Punkte sind hier kommentiert.
#
# Jeder Lauf ist unabhaengig; das Gedaechtnis liegt in Facts/INVENTAR.md und
# in den Commits auf dem Branch.  Gearbeitet wird in einem git-Worktree, damit
# der Hauptcheckout des Nutzers nie angefasst wird.

set -uo pipefail

# Cron hat einen minimalen PATH -- claude liegt in ~/.local/bin, lake/lean/elan
# liegen in ~/.elan/bin.  Ohne den elan-Pfad ist "Bash(lake:*)" zwar erlaubt,
# aber `lake` nicht auffindbar: der Lauf vom 2026-09-05 (20260905T194326Z) sah
# genau das -- "lake: Befehl nicht gefunden" -- und konnte kein Lean uebersetzen.
# Der absolute Pfad hilft nicht, weil die Rechtefreigabe am Kommandonamen haengt.
export PATH="$HOME/.local/bin:$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"

REPO="${FACTS_REPO:-$HOME/Code/lean/journal-facts}"
BRANCH="${FACTS_BRANCH:-facts-inventory}"
TIMEOUT_MIN="${FACTS_TIMEOUT_MIN:-120}"
LOCK="$REPO/.facts.lock"
LOGDIR="$REPO/logs"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"

cd "$REPO" || { echo "Worktree $REPO fehlt"; exit 1; }
mkdir -p "$LOGDIR"
RUNLOG="$LOGDIR/run_$STAMP.log"

# --- Nicht ueberlappen ------------------------------------------------------
exec 9>"$LOCK"
if ! flock -n 9; then
  echo "$(date -u +%FT%TZ) vorheriger Lauf laeuft noch, uebersprungen" >> "$LOGDIR/skipped.log"
  exit 0
fi

# --- Sitzungsgrenze: nicht stuendlich gegen dieselbe Wand laufen ------------
# Die Grenze, die zaehlt, ist die des KONTOS, nicht die des Modells.  Am
# 2026-09-07 starben vier Laeufe hintereinander daran, und der Ausweich auf ein
# anderes Modell half nicht, weil er dieselbe Grenze trifft.  Steht der
# Ruecksetzzeitpunkt fest, wird bis dahin gar nicht erst gestartet: das spart
# den Aufruf, den Logeintrag und den leeren STATUS-Commit.
LIMITFILE="$LOGDIR/limit_until"      # liegt unter logs/, also von git ignoriert
if [ -f "$LIMITFILE" ]; then
  UNTIL="$(cat "$LIMITFILE" 2>/dev/null)"
  if [ -n "$UNTIL" ] && [ "$(date +%s)" -lt "$UNTIL" ] 2>/dev/null; then
    echo "$(date -u +%FT%TZ) Sitzungsgrenze bis $(date -d "@$UNTIL" '+%F %H:%M %Z'), uebersprungen" \
      >> "$LOGDIR/skipped.log"
    exit 0
  fi
  rm -f "$LIMITFILE"
fi

# Merkt sich den Ruecksetzzeitpunkt aus einer Meldung wie
# "You've hit your session limit - resets 8:20pm (Europe/Berlin)".
merke_sitzungsgrenze() {  # merke_sitzungsgrenze <logdatei>
  local t e
  t="$(grep -oiE 'resets [0-9]{1,2}:[0-9]{2} ?(am|pm)?' "$1" 2>/dev/null | tail -1 \
       | sed -E 's/^[Rr]esets //')"
  [ -z "$t" ] && return 1
  e="$(date -d "today $t" +%s 2>/dev/null)" || return 1
  [ -z "$e" ] && return 1
  if [ "$e" -le "$(date +%s)" ]; then
    e="$(date -d "tomorrow $t" +%s 2>/dev/null)" || return 1
  fi
  echo "$e" > "$LIMITFILE"
  return 0
}

status() {  # status <zustand> <notiz>
  {
    echo "# Formalisierungs-Inventar — Status"
    echo
    echo "- **Letzter Lauf (UTC):** $STAMP"
    echo "- **Zustand:** $1"
    echo "- **Notiz:** $2"
    echo "- **Host:** $(hostname)"
    echo "- **Laeufe bisher:** $(git log --oneline --grep='^Facts [0-9]\{8\}T' 2>/dev/null | wc -l | tr -d ' ')"
    echo
    echo "Logs unter \`logs/\`. Der inhaltliche Stand steht in"
    echo "\`Journal/Blog/MartingaleProblem/Facts/INVENTAR.md\`."
  } > "$REPO/Journal/Blog/MartingaleProblem/Facts/STATUS.md"
}

publish() {  # committen und pushen, auch im Fehlerfall
  git add -A >/dev/null 2>&1
  if ! git diff --cached --quiet 2>/dev/null; then
    git commit -q -m "$1" >/dev/null 2>&1
  fi
  git push -q origin "$BRANCH" >/dev/null 2>&1 || echo "PUSH FEHLGESCHLAGEN" >> "$RUNLOG"
}

git pull -q --rebase origin "$BRANCH" >/dev/null 2>&1

# master nachziehen.  Ohne das arbeitet der Lauf auf einem Stand, der beliebig
# alt werden kann, sobald der Nutzer auf master committet -- und schreibt dann
# Roadmap-Aenderungen gegen ein Manuskript, das es so nicht mehr gibt.
# Bei Konflikt wird NICHT gerechnet: lieber ein ausgelassener Slot als ein Lauf,
# der auf einem halb aufgeloesten Baum arbeitet und ihn dann pusht.
git fetch -q origin master >/dev/null 2>&1
if ! git merge -q --no-edit origin/master >/dev/null 2>&1; then
  # Das mitversionierte PDF ist ein Bauartefakt und kollidiert bei jedem
  # beidseitigen Uebersetzen.  Kollidieren NUR Artefakte, wird das aufgeloest
  # und weitergemacht; kollidiert irgendetwas anderes, bleibt es beim
  # Auslassen -- lieber ein verlorener Slot als ein halb aufgeloester Baum.
  CONFLICTS="$(git diff --name-only --diff-filter=U)"
  if [ -n "$CONFLICTS" ] && ! printf '%s\n' "$CONFLICTS" | grep -qv '\.pdf$'; then
    printf '%s\n' "$CONFLICTS" | while IFS= read -r f; do
      git checkout --theirs -- "$f" >/dev/null 2>&1 && git add -- "$f" >/dev/null 2>&1
    done
    if git commit -q --no-edit >/dev/null 2>&1; then
      echo "$(date -u +%FT%TZ) PDF-Konflikt automatisch aufgeloest" >> "$RUNLOG"
    else
      # Auch hier nicht aussteigen: ohne master weiterarbeiten ist besser als
      # ein Slot, der nie wiederkommt.
      git merge --abort >/dev/null 2>&1
      echo "$(date -u +%FT%TZ) ACHTUNG: PDF-Konflikt liess sich nicht aufloesen; Lauf arbeitet ohne master weiter" >> "$RUNLOG"
      MERGE_BLOCKED=1
    fi
  else
    # Echter Konflikt.  Frueher wurde hier ausgestiegen -- falsch, wenn tagelang
    # niemand hinsieht: master bewegt sich dann nicht, der Konflikt loest sich
    # nie von selbst, und JEDER Slot faellt aus.  Der Abbruch laesst einen
    # sauberen (nur veralteten) Baum zurueck, also wird ohne master
    # weitergearbeitet und der Konflikt laut vermerkt.
    git merge --abort >/dev/null 2>&1
    echo "$(date -u +%FT%TZ) ACHTUNG: Merge von origin/master konfliktiert; Lauf arbeitet ohne master weiter" >> "$RUNLOG"
    MERGE_BLOCKED=1
  fi
fi
status "laeuft" "Lauf gestartet"
publish "Facts STATUS: Lauf $STAMP gestartet"

MERGE_BLOCKED="${MERGE_BLOCKED:-0}"
PROMPT="$(cat "$REPO/scripts/facts_prompt.md")"
if [ "$MERGE_BLOCKED" = 1 ]; then
  PROMPT="$PROMPT

---

**ACHTUNG:** Der Merge von \`origin/master\` konfliktiert. Du arbeitest auf
einem veralteten Stand. Fasse in diesem Lauf **nur** Dateien an, die
unzweifelhaft zu Deiner Aufgabe gehoeren, und vermerke den Konflikt im Bericht."
fi

# Enge Werkzeug-Freigabe statt pauschalem Abschalten der Rechtepruefung.  Im
# -p-Modus wird ein nicht freigegebenes Werkzeug verweigert, nicht nachgefragt
# -- der Lauf bleibt also nicht haengen.
ALLOWED=(
  Read Write Edit Glob Grep
  "Bash(python3:*)"
  "Bash(git:*)"
  "Bash(ls:*)" "Bash(mkdir:*)" "Bash(head:*)" "Bash(tail:*)"
  "Bash(wc:*)" "Bash(grep:*)" "Bash(sed:*)" "Bash(sort:*)" "Bash(cut:*)"
  "Bash(find:*)" "Bash(cp:*)" "Bash(date:*)" "Bash(cat:*)"
  # Wer das Manuskript anfasst, muss es uebersetzen koennen.
  "Bash(pdflatex:*)" "Bash(latexmk:*)" "Bash(bibtex:*)" "Bash(pdftotext:*)"
  # Mathlib master gegenpruefen, wenn der lokale Checkout nicht ausreicht.
  WebSearch WebFetch "Bash(gh:*)"
  # Lean typpruefen.  Der Worktree hat kein .lake; der Hauptcheckout hat ein
  # fertig gebautes Mathlib, und `lake env lean <datei>` prueft dagegen, ohne
  # irgendwo zu schreiben.  Ohne diese drei Freigaben scheitert das an der
  # Rechtepruefung und nicht an Lean -- so geschehen am 2026-09-05.
  "Bash(lake:*)" "Bash(lean:*)" "Bash(elan:*)"
)

# Der Worktree hat kein .lake -- Mathlib liegt nur im Hauptcheckout.  Ohne
# diese Lesepfade kann der Lauf keinen einzigen Deklarationsnamen belegen.
# Ein nicht vorhandenes --add-dir laesst claude sofort abbrechen, daher geprueft.
ADDDIRS=()
# $HOME/Code/lean/journal ist noetig, weil dort die lakefile und das gebaute
# .lake liegen; der Auftrag verbietet ausdruecklich, dort zu schreiben.
for d in "${FACTS_JOURNAL:-$HOME/Code/lean/journal}" \
         "${FACTS_MATHLIB:-$HOME/Code/lean/journal/.lake/packages/mathlib}" \
         "${FACTS_MATHLIB_MASTER:-$HOME/Code/lean/mathlib4}"; do
  if [ -d "$d" ]; then
    ADDDIRS+=(--add-dir "$d")
  else
    echo "WARNUNG: $d fehlt -- Mathlib dort nicht lesbar" >> "$RUNLOG"
  fi
done

# Modell: Opus 5.  Fable stirbt nachweislich an der modellspezifischen
# Kontingentgrenze, ohne eine Sekunde zu rechnen (Erfahrung des
# ratchet-Projekts, dokumentiert in dessen run_iteration.sh).  Der Fallback
# muss ein ANDERES Modell sein als $MODEL, sonst ist er wirkungslos.
MODEL="${FACTS_MODEL:-claude-opus-5}"
FALLBACK="${FACTS_FALLBACK_MODEL:-sonnet}"

# Der Prompt geht ueber stdin, nicht als Argument: Linux begrenzt ein einzelnes
# Argument auf MAX_ARG_STRLEN = 128 KiB, und am 2026-09-10 ist der Prompt mit
# 131923 Bytes darueber gewachsen -- zwei Laeufe starben mit "Argumentliste zu
# lang" (Code 126), ohne dass claude auch nur aufgerufen wurde.
timeout "${TIMEOUT_MIN}m" claude -p \
    --model "$MODEL" \
    --fallback-model "$FALLBACK" \
    --allowedTools "${ALLOWED[@]}" \
    "${ADDDIRS[@]}" \
    >> "$RUNLOG" 2>&1 <<< "$PROMPT"
RC=$?

case "$RC" in
  0)   status "ok" "Lauf regulaer beendet" ;;
  124) status "timeout" "nach ${TIMEOUT_MIN} min abgebrochen -- Zwischenstand ist committet" ;;
  *)   # Nutzungsgrenze von einem echten Fehler unterscheiden, sonst sucht man
       # den Fehler im Repo, obwohl nur das Kontingent erschoepft war.
       if grep -qiE 'session limit' "$RUNLOG" 2>/dev/null; then
         # Die SITZUNGSgrenze gilt dem Konto, nicht dem Modell: ein zweiter
         # Versuch mit einem anderen Modell trifft dieselbe Wand und kostet nur
         # Zeit.  Also Ruecksetzzeit merken und bis dahin aussetzen.
         if merke_sitzungsgrenze "$RUNLOG"; then
           status "limit-sitzung" "Sitzungsgrenze des Kontos erreicht; kein Ausweichmodell, es traefe dieselbe Grenze. Naechster Versuch ab $(date -d "@$(cat "$LIMITFILE")" '+%F %H:%M %Z')"
         else
           status "limit-sitzung" "Sitzungsgrenze des Kontos erreicht; Ruecksetzzeit nicht erkennbar, naechster Slot versucht es erneut"
         fi
       elif grep -qiE 'rate limit|usage limit|limit reached|reached your .*limit|hit your .*limit|manage usage credits|quota|too many requests' "$RUNLOG" 2>/dev/null; then
         # Diese Grenzen sind modellspezifisch.  Statt den Slot zu verlieren,
         # sofort mit dem Ausweichmodell nachsetzen -- es hat ein eigenes Kontingent.
         echo "$(date -u +%FT%TZ) Kontingent fuer $MODEL erschoepft, zweiter Versuch mit $FALLBACK" >> "$RUNLOG"
         timeout "${TIMEOUT_MIN}m" claude -p \
             --model "$FALLBACK" \
             --allowedTools "${ALLOWED[@]}" \
             "${ADDDIRS[@]}" \
             >> "$RUNLOG" 2>&1 <<< "$PROMPT"
         RC2=$?
         if [ "$RC2" = 0 ]; then
           status "ok" "Kontingent fuer $MODEL erschoepft; mit $FALLBACK regulaer beendet"
         elif ! git diff --quiet HEAD 2>/dev/null || [ -n "$(git status --porcelain 2>/dev/null)" ]; then
           # Die Grenze kann MITTEN in einem Lauf zuschlagen.  Dann ist Arbeit da,
           # und "limit" allein liest sich, als sei nichts geschehen.
           status "limit-teilarbeit" "Nutzungsgrenze mitten im Lauf (Code $RC, Ausweich $RC2) -- die bis dahin geleistete Arbeit ist committet"
         else
           status "limit" "Nutzungsgrenze erreicht (Code $RC), zweiter Versuch mit $FALLBACK endete mit $RC2 -- nichts geleistet"
         fi
       else
         status "fehler" "claude endete mit Code $RC (siehe logs/run_$STAMP.log)"
       fi ;;
esac

# --- Aufraeumen: verirrte lake-Klone im Hauptcheckout -----------------------
# Ein `lake env lean` aus dem falschen Arbeitsverzeichnis laesst lake Mathlib als
# Wurzelpaket behandeln und seine Abhaengigkeiten neu klonen -- 57 MB, zweimal am
# 2026-09-08 vorgekommen.  Der Lauf selbst darf dort nicht loeschen; hier, ausser-
# halb der Sandbox, wird es nachgeholt.  `build` und `config` bleiben unberuehrt,
# nur das faelschlich angelegte `packages` unter mathlib faellt weg.
STRAY="$HOME/Code/lean/journal/.lake/packages/mathlib/.lake/packages"
if [ -d "$STRAY" ]; then
  echo "$(date -u +%FT%TZ) verirrte lake-Klone entfernt: $(du -sh "$STRAY" | cut -f1)" >> "$RUNLOG"
  rm -rf "$STRAY"
fi

# --- Schutznetz: das Manuskript muss uebersetzen ----------------------------
# Unbeaufsichtigt darf kein Lauf ein kaputtes Manuskript hinterlassen.  Faellt
# check.py durch, werden die .tex- und .pdf-Aenderungen dieses Laufs verworfen;
# alles andere (Inventar, Roadmaps, Protokolle) bleibt erhalten, denn dort kann
# check.py nichts kaputtmachen.
MS="Journal/Blog/MartingaleProblem"
if ! git diff --quiet -- "$MS/MartingaleProblem.tex" 2>/dev/null; then
  if ! (cd "$REPO/$MS" && python3 check.py) >> "$RUNLOG" 2>&1; then
    echo "$(date -u +%FT%TZ) ACHTUNG: check.py durchgefallen, .tex/.pdf dieses Laufs verworfen" >> "$RUNLOG"
    git checkout -- "$MS/MartingaleProblem.tex" "$MS/MartingaleProblem.pdf" >/dev/null 2>&1
    status "teilweise" "check.py durchgefallen -- Manuskriptaenderungen verworfen, der Rest ist behalten"
  fi
fi

# Logs klein halten: nur die letzten 60 Laeufe behalten
ls -1t "$LOGDIR"/run_*.log 2>/dev/null | tail -n +61 | xargs -r rm -f

publish "Facts $STAMP (rc=$RC)"
