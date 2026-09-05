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

PROMPT="$(cat "$REPO/scripts/task23_prompt.md")"

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

timeout "${TIMEOUT_MIN}m" claude -p "$PROMPT" \
    --model "$MODEL" \
    --fallback-model "$FALLBACK" \
    --allowedTools "${ALLOWED[@]}" \
    >> "$RUNLOG" 2>&1
RC=$?

case "$RC" in
  0)   status "ok" "Lauf regulaer beendet" ;;
  124) status "timeout" "nach ${TIMEOUT_MIN} min abgebrochen -- Zwischenstand ist committet" ;;
  *)   # Nutzungsgrenze von einem echten Fehler unterscheiden, sonst sucht man
       # den Fehler im Repo, obwohl nur das Kontingent erschoepft war.
       if grep -qiE 'rate limit|usage limit|limit reached|reached your .*limit|hit your .*limit|session limit|manage usage credits|quota|too many requests' "$RUNLOG" 2>/dev/null; then
         status "limit" "Nutzungsgrenze erreicht (Code $RC) -- Lauf nicht gelaufen, naechster Cron-Slot versucht es erneut"
       else
         status "fehler" "claude endete mit Code $RC (siehe logs/run_$STAMP.log)"
       fi ;;
esac

# Logs klein halten: nur die letzten 60 Laeufe behalten
ls -1t "$LOGDIR"/run_*.log 2>/dev/null | tail -n +61 | xargs -r rm -f

publish "Task23 $STAMP (rc=$RC)"
