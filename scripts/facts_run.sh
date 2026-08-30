#!/usr/bin/env bash
# Ein Lauf am Formalisierungs-Inventar (Fact-Aussagen des Manuskripts).
# aufgerufen.  Bauform uebernommen von scripts/run_iteration.sh des
# ratchet-Projekts; die dort teuer gelernten Punkte sind hier kommentiert.
#
# Jeder Lauf ist unabhaengig; das Gedaechtnis liegt in Facts/INVENTAR.md und
# in den Commits auf dem Branch.  Gearbeitet wird in einem git-Worktree, damit
# der Hauptcheckout des Nutzers nie angefasst wird.

set -uo pipefail

# Cron hat einen minimalen PATH -- claude liegt in ~/.local/bin.
export PATH="$HOME/.local/bin:/usr/local/bin:/usr/bin:/bin"

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
      git merge --abort >/dev/null 2>&1
      status "konflikt" "Merge von origin/master schlug fehl -- bitte von Hand aufloesen; dieser Slot wurde ausgelassen"
      publish "Facts $STAMP (Merge-Konflikt mit master, ausgelassen)"
      exit 0
    fi
  else
    git merge --abort >/dev/null 2>&1
    status "konflikt" "Merge von origin/master schlug fehl -- bitte von Hand aufloesen; dieser Slot wurde ausgelassen"
    publish "Facts $STAMP (Merge-Konflikt mit master, ausgelassen)"
    exit 0
  fi
fi
status "laeuft" "Lauf gestartet"
publish "Facts STATUS: Lauf $STAMP gestartet"

PROMPT="$(cat "$REPO/scripts/facts_prompt.md")"

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
)

# Der Worktree hat kein .lake -- Mathlib liegt nur im Hauptcheckout.  Ohne
# diese Lesepfade kann der Lauf keinen einzigen Deklarationsnamen belegen.
# Ein nicht vorhandenes --add-dir laesst claude sofort abbrechen, daher geprueft.
ADDDIRS=()
for d in "${FACTS_MATHLIB:-$HOME/Code/lean/journal/.lake/packages/mathlib}" \
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

timeout "${TIMEOUT_MIN}m" claude -p "$PROMPT" \
    --model "$MODEL" \
    --fallback-model "$FALLBACK" \
    --allowedTools "${ALLOWED[@]}" \
    "${ADDDIRS[@]}" \
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

publish "Facts $STAMP (rc=$RC)"
