#!/bin/sh
# Baut die drei `Suggested.lean` in Abhängigkeitsordnung in einen eigenen
# `.olean`-Baum unter `scratch/_probe`, damit ein Entwurf gegen sie übersetzt
# werden kann, ohne die große Datei jedesmal neu zu übersetzen.
#
# Es ist dieselbe Kette und dasselbe Modulpräfix wie in
# `scripts/check_suggested.py`; dieses Skript ersetzt jene Prüfung **nicht**,
# es beschleunigt nur das Entwerfen.  Was zählt, ist `check_suggested.py`.
set -e
ROOT=/home/pfaffelh/Code/lean/journal-facts
JOURNAL=/home/pfaffelh/Code/lean/journal
BUILD="$ROOT/scratch/_probe"
SRC="$ROOT/Journal/Blog/MartingaleProblem/TauCeti"

for f in WeakConvergence SkorokhodSpace MartingaleProblems; do
  mkdir -p "$BUILD/TauCetiRoadmap/$f"
  echo "=== $f"
  lake --dir="$JOURNAL" env sh -c \
    "LEAN_PATH=\"\$LEAN_PATH:$BUILD\" exec lean -DautoImplicit=false -DrelaxedAutoImplicit=false -o $BUILD/TauCetiRoadmap/$f/Suggested.olean $SRC/$f/Suggested.lean"
done
echo "=== fertig"
