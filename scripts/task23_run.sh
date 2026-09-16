#!/usr/bin/env bash
# Ein Lauf an Task 23 (rein atomare Uhr, Dualitaet).  Wird per Cron alle 6 h
# aufgerufen.  Bauform uebernommen von scripts/run_iteration.sh des
# ratchet-Projekts; die dort teuer gelernten Punkte sind hier kommentiert.
#
# Jeder Lauf ist unabhaengig; das Gedaechtnis liegt in Task23/PROTOKOLL.md und
# in den Commits auf dem Branch.  Gearbeitet wird in einem git-Worktree, damit
# der Hauptcheckout des Nutzers nie angefasst wird.

set -uo pipefail

# Cron hat einen minimalen PATH -- claude liegt in ~/.local/bin, lake/lean/elan
# liegen in ~/.elan/bin.  Ohne den elan-Pfad ist "Bash(lake:*)" zwar erlaubt,
# aber `lake` nicht auffindbar (so geschehen am 2026-09-05).
export PATH="$HOME/.local/bin:$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"

REPO="${TASK23_REPO:-$HOME/Code/lean/journal-task23}"
BRANCH="${TASK23_BRANCH:-task23-atomic-duality}"
TIMEOUT_MIN="${TASK23_TIMEOUT_MIN:-120}"
LOCK="$REPO/.task23.lock"
LOGDIR="$REPO/logs"
LIMITFILE="$LOGDIR/limit_until"   # liegt unter logs/, also von git ignoriert
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

# --- Sitzungsgrenze: nicht gegen dieselbe Wand laufen ---------------------
# Die Grenze, die hier zuschlaegt, ist die des KONTOS und nicht die des
# Modells: am 2026-09-16 starben die Slots 08:03 und 16:03 daran, Runlog je
# 60 Bytes, ohne eine Sekunde zu rechnen.  Ein Ausweichmodell hilft nicht, es
# traefe dieselbe Grenze.  Steht der Ruecksetzzeitpunkt fest, wird bis dahin
# gar nicht erst gestartet -- das spart den Aufruf, den Logeintrag und den
# leeren STATUS-Commit.
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
# "You've hit your session limit - resets 9am (Europe/Berlin)".
# ACHTUNG, hier weicht diese Fassung von der in facts_run.sh ab und muss es:
# jene verlangt "resets H:MM" und trifft damit "resets 9am" NICHT -- und genau
# diese Form hatten beide Ausfaelle vom 2026-09-16.  Die Minuten sind optional.
merke_sitzungsgrenze() {  # merke_sitzungsgrenze <logdatei>
  local t e
  t="$(grep -oiE 'resets [0-9]{1,2}(:[0-9]{2})? ?(am|pm)?' "$1" 2>/dev/null | tail -1 \
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
    echo "# Task 23 — Status"
    echo
    echo "- **Letzter Lauf (UTC):** $STAMP"
    echo "- **Zustand:** $1"
    echo "- **Notiz:** $2"
    echo "- **Host:** $(hostname)"
    echo "- **Laeufe bisher:** $(git log --oneline --grep='^Task23 [0-9]\{8\}T' 2>/dev/null | wc -l | tr -d ' ')"
    echo
    echo "Logs unter \`logs/\`. Der inhaltliche Stand steht in"
    echo "\`Journal/Blog/MartingaleProblem/Task23/PROTOKOLL.md\`."
  } > "$REPO/Journal/Blog/MartingaleProblem/Task23/STATUS.md"
}

publish() {  # committen und pushen, auch im Fehlerfall
  git add -A >/dev/null 2>&1
  if ! git diff --cached --quiet 2>/dev/null; then
    git commit -q -m "$1" >/dev/null 2>&1
  fi
  git push -q origin "$BRANCH" >/dev/null 2>&1 || echo "PUSH FEHLGESCHLAGEN" >> "$RUNLOG"
}

git pull -q --rebase origin "$BRANCH" >/dev/null 2>&1
status "laeuft" "Lauf gestartet"
publish "Task23 STATUS: Lauf $STAMP gestartet"

# Der Auftrag ist umstellbar, ohne die stehende Datei anzufassen -- gebraucht
# fuer Sonderlaeufe wie den Abschlusslauf (task23_close_prompt.md).
PROMPT_FILE="${TASK23_PROMPT:-$REPO/scripts/task23_prompt.md}"
[ -r "$PROMPT_FILE" ] || { echo "Auftragsdatei $PROMPT_FILE fehlt"; status "fehler" "Auftragsdatei $PROMPT_FILE fehlt"; publish "Task23 $STAMP (Auftragsdatei fehlt)"; exit 1; }
PROMPT="$(cat "$PROMPT_FILE")"

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
)

# Modell: Opus 5.  Fable stirbt nachweislich an der modellspezifischen
# Kontingentgrenze, ohne eine Sekunde zu rechnen (Erfahrung des
# ratchet-Projekts, dokumentiert in dessen run_iteration.sh).  Der Fallback
# muss ein ANDERES Modell sein als $MODEL, sonst ist er wirkungslos.
MODEL="${TASK23_MODEL:-claude-opus-5}"
FALLBACK="${TASK23_FALLBACK_MODEL:-sonnet}"

# Der Prompt geht ueber stdin, nicht als Argument, aus zwei Gruenden.  Erstens
# begrenzt Linux ein einzelnes Argument auf MAX_ARG_STRLEN = 128 KiB -- daran
# sind am 2026-09-10 zwei Faktenlaeufe gestorben, als deren Prompt darueber
# wuchs.  Zweitens ist --allowedTools variadisch und verschluckt ein folgendes
# positionales Argument als weiteren Werkzeugnamen; der Lauf endet dann mit
# einer Fehlermeldung, die nach etwas ganz anderem aussieht (gemessen
# 2026-09-15).
timeout "${TIMEOUT_MIN}m" claude -p \
    --model "$MODEL" \
    --fallback-model "$FALLBACK" \
    --allowedTools "${ALLOWED[@]}" \
    >> "$RUNLOG" 2>&1 <<< "$PROMPT"
RC=$?

case "$RC" in
  0)   status "ok" "Lauf regulaer beendet" ;;
  124) status "timeout" "nach ${TIMEOUT_MIN} min abgebrochen -- Zwischenstand ist committet" ;;
  *)   # Nutzungsgrenze von einem echten Fehler unterscheiden, sonst sucht man
       # den Fehler im Repo, obwohl nur das Kontingent erschoepft war.
       if grep -qiE 'session limit' "$RUNLOG" 2>/dev/null; then
         # Kontoweit: Ruecksetzzeit merken und bis dahin aussetzen.
         if merke_sitzungsgrenze "$RUNLOG"; then
           status "limit-sitzung" "Sitzungsgrenze des Kontos erreicht; kein Ausweichmodell, es traefe dieselbe Grenze. Naechster Versuch ab $(date -d "@$(cat "$LIMITFILE")" '+%F %H:%M %Z')"
         else
           status "limit-sitzung" "Sitzungsgrenze des Kontos erreicht; Ruecksetzzeit nicht erkennbar, naechster Slot versucht es erneut"
         fi
       elif grep -qiE 'rate limit|usage limit|limit reached|reached your .*limit|hit your .*limit|manage usage credits|quota|too many requests' "$RUNLOG" 2>/dev/null; then
         status "limit" "Nutzungsgrenze erreicht (Code $RC) -- Lauf nicht gelaufen, naechster Cron-Slot versucht es erneut"
       else
         status "fehler" "claude endete mit Code $RC (siehe logs/run_$STAMP.log)"
       fi ;;
esac

# Logs klein halten: nur die letzten 60 Laeufe behalten
ls -1t "$LOGDIR"/run_*.log 2>/dev/null | tail -n +61 | xargs -r rm -f

publish "Task23 $STAMP (rc=$RC)"
