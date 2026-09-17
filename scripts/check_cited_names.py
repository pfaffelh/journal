#!/usr/bin/env python3
"""Prüft die in den Roadmaps zitierten **Mathlib-Deklarationsnamen** gegen
`upstream/master`.

Aufruf (aus dem Worktree-Wurzelverzeichnis):

    python3 scripts/check_cited_names.py

Gelesen wird nur; gesucht wird mit `git -C ~/Code/lean/mathlib4 grep` gegen
`upstream/master`, ohne Auschecken.

**Was das Skript kann und was nicht.**  Es sammelt aus den Roadmaps jeden in
Rückwärtsanführungszeichen gesetzten Bezeichner und vergleicht dessen
*letzte Namenskomponente* mit den auf `master` deklarierten Namen.  Das ist
absichtlich grob:

* Ein Treffer heißt **nicht**, daß der volle Namensraum stimmt — nur daß es
  irgendwo eine Deklaration dieses Kurznamens gibt.  Ein Treffer ist also
  kein Beleg, sondern bloß die Abwesenheit des interessanten Falls.
* Ein Fehlschlag heißt **nicht**, daß der Name verschwunden ist — er kann
  auch unsere eigene Roadmap-Vokabel sein, ein Taktikname oder eine Notation.
  Die Ausgabe ist deshalb eine **Prüfliste**, die von Hand durchzugehen ist,
  und keine Befundliste.

Was es zuverlässig leistet: die Liste der von Hand zu prüfenden Namen von
einigen hundert auf wenige Dutzend zu verkürzen, und jeden zitierten Namen zu
melden, der auf `master` als `deprecated` markiert ist.
"""

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TAUCETI = ROOT / "Journal" / "Blog" / "MartingaleProblem" / "TauCeti"
MATHLIB = pathlib.Path.home() / "Code" / "lean" / "mathlib4"
REF = "upstream/master"

DECL_RE = re.compile(
    r"^(?P<kw>theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|alias)"
    r"\s+(?P<name>[A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)")
MODIFIERS = re.compile(
    r"^(protected|private|nonrec|noncomputable|partial|unsafe|scoped|local)\s+")
#  Ein Zitat ist ein Bezeichner in Backticks, ohne Leerzeichen, mit einem
#  Buchstaben am Anfang.  Notationen (`ℝ≥0`, `→ᵇ`) fallen dadurch heraus.
CITE_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)`")


def run(args: list[str]) -> str:
    return subprocess.run(args, capture_output=True, text=True, check=True).stdout


def mathlib_declarations() -> tuple[dict[str, bool], set[str]]:
    """(voll qualifizierter Name -> ist deprecated, alle Kurznamen).

    Der Namensraum wird aus `namespace`/`end` mitgeführt, damit ein Zitat
    gegen den vollen Namen geprüft werden kann und nicht bloß gegen die
    letzte Komponente.  `section`s werden mitgezählt, weil `end` beide
    schließt.
    """
    out = run(["git", "-C", str(MATHLIB), "grep", "-n", "-E",
               r"^\s*(@\[[^]]*\]\s*)?(protected |private |nonrec |noncomputable "
               r"|partial |unsafe |scoped |local )*"
               r"(theorem|lemma|def|abbrev|instance|structure|class|inductive"
               r"|opaque|alias)\s|^\s*@\[deprecated|^namespace |^end( |$)"
               r"|^section( |$)",
               REF, "--", "Mathlib/"])
    full: dict[str, bool] = {}
    shorts: set[str] = set()
    stack: list[tuple[str, str | None]] = []   # ("namespace"|"section", Name)
    cur_path: str | None = None
    dep_line: int | None = None
    for line in out.splitlines():
        parts = line.split(":", 3)
        if len(parts) < 4:
            continue
        _, path, lineno_s, text = parts
        try:
            lineno = int(lineno_s)
        except ValueError:
            continue
        if path != cur_path:
            cur_path, stack, dep_line = path, [], None
        stripped = text.strip()

        if stripped.startswith("namespace "):
            stack.append(("namespace", stripped.split()[1]))
            continue
        if stripped == "section" or stripped.startswith("section "):
            stack.append(("section",
                          stripped.split()[1] if " " in stripped else None))
            continue
        if stripped == "end" or stripped.startswith("end "):
            want = stripped.split()[1] if " " in stripped else None
            if want is None:
                if stack:
                    stack.pop()
            else:
                for i in range(len(stack) - 1, -1, -1):
                    if stack[i][1] == want:
                        del stack[i:]
                        break
                else:
                    if stack:
                        stack.pop()
            continue

        is_dep = stripped.startswith("@[deprecated")
        if is_dep:
            dep_line = lineno
        stripped = re.sub(r"^@\[[^]]*\]\s*", "", stripped)
        if not stripped:
            continue
        while MODIFIERS.match(stripped):
            stripped = MODIFIERS.sub("", stripped)
        m = DECL_RE.match(stripped)
        if not m:
            continue
        prefix = ".".join(n for kind, n in stack if kind == "namespace" and n)
        name = m.group("name")
        qualified = f"{prefix}.{name}" if prefix else name
        deprecated_here = is_dep or (dep_line is not None
                                     and 0 <= lineno - dep_line <= 2)
        #  Ein Name, der irgendwo nicht deprecated deklariert ist, gilt als
        #  nicht deprecated.
        full[qualified] = full.get(qualified, True) and deprecated_here
        shorts.add(name.split(".")[-1])
        dep_line = None
    return full, shorts


def our_declarations() -> set[str]:
    ours: set[str] = set()
    for src in TAUCETI.glob("*/Suggested.lean"):
        for line in src.read_text(encoding="utf-8").splitlines():
            stripped = re.sub(r"^@\[[^]]*\]\s*", "", line.strip())
            while MODIFIERS.match(stripped):
                stripped = MODIFIERS.sub("", stripped)
            m = DECL_RE.match(stripped)
            if m:
                ours.add(m.group("name"))
                ours.add(m.group("name").split(".")[-1])
    return ours


def main() -> int:
    full, shorts = mathlib_declarations()
    ours = our_declarations()

    #  Zu jedem Zitat die vollen Mathlib-Namen, die auf es enden.
    by_tail: dict[str, list[str]] = {}
    for q in full:
        parts = q.split(".")
        for i in range(len(parts)):
            by_tail.setdefault(".".join(parts[i:]), []).append(q)

    cited: dict[str, set[str]] = {}
    for src in sorted(TAUCETI.glob("*/README.md")):
        label = src.parent.name
        for m in CITE_RE.finditer(src.read_text(encoding="utf-8")):
            cited.setdefault(m.group(1), set()).add(label)

    unknown, dep_hits = [], []
    for name in sorted(cited):
        short = name.split(".")[-1]
        matches = by_tail.get(name, [])
        #  Ein Zitat gilt nur dann als deprecated, wenn **jede** Deklaration,
        #  auf die es passt, deprecated ist — und nur bei qualifizierten
        #  Namen, weil ein Kurzname wie `mono` auf Hunderte passt.
        if "." in name and matches and all(full[q] for q in matches):
            dep_hits.append((name, matches))
        if matches or short in shorts:
            continue
        if name in ours or short in ours:
            continue
        unknown.append(name)

    print(f"# Zitierte Bezeichner in den vier README.md, gegen {REF}")
    print()
    print(f"{len(cited)} verschiedene Bezeichner zitiert; "
          f"{len(cited) - len(unknown)} davon sind entweder auf `master` "
          f"deklariert oder in unseren eigenen `Suggested.lean`.")
    print()
    print("## Auf `master` als `deprecated` markiert "
          f"({len(dep_hits)}) — jeder davon ist ein Befund")
    for name, matches in dep_hits:
        print(f"* `{name}` -> {', '.join(sorted(matches)[:3])} "
              f"(zitiert in {', '.join(sorted(cited[name]))})")
    print()
    print(f"## Weder auf `master` noch bei uns deklariert ({len(unknown)})"
          " — von Hand zu prüfen")
    for name in unknown:
        print(f"* `{name}` (zitiert in {', '.join(sorted(cited[name]))})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
