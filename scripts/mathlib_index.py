#!/usr/bin/env python3
"""Baut aus einer Mathlib-Quelle einen Index aller Deklarationsnamen.

Quelle ist entweder ein Git-Revision-Ausdruck im Checkout `~/Code/lean/mathlib4`
(dann wird `git grep <rev>` benutzt, ohne irgendetwas auszuchecken) oder ein
Verzeichnis im Dateisystem (der v4.33.1-Release unter
`~/Code/lean/journal/.lake/packages/mathlib`).

    python3 scripts/mathlib_index.py master   -> scripts/_citations/index_master.json
    python3 scripts/mathlib_index.py v4331    -> scripts/_citations/index_v4331.json

Der Index ist ein Dict `voller Name -> "Datei:Zeile"`.  Namespaces werden
mitgeführt, `deprecated` wird an der Deklaration vermerkt (Präfix `!` im Wert).
"""
import re, os, sys, json, subprocess

# Alle Pfade relativ zur Wurzel des Worktrees, damit das Skript aus jedem
# Verzeichnis heraus lauffähig ist.
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

MATHLIB4 = '/home/pfaffelh/Code/lean/mathlib4'
V4331 = '/home/pfaffelh/Code/lean/journal/.lake/packages/mathlib'
OUT = 'scripts/_citations'

DECL = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\b"
    r"(?:\s+([A-Za-z_α-ωΓ-Ω][^\s:({\[]*))?")
NS = re.compile(r'^\s*(namespace|end)\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$')
DEPR = re.compile(r'@\[[^\]]*deprecated')
# `@[to_dual foo]`, `@[to_additive bar]`, `@[to_fun baz]` erzeugen eine
# Deklaration namens `foo` usw., die in keiner Quellzeile als `theorem` steht.
TRANS = re.compile(r"\b(?:to_dual|to_additive|to_fun)\s+([a-zA-Z_][A-Za-z0-9_.'₀-₉]*)")
TRANS_STOP = {'existing', 'attr', 'self', 'reorder', 'relabel', 'dont_translate'}


def emit_lines(source):
    """Yield (path, lineno, text) for every Mathlib/*.lean line of interest."""
    # POSIX ERE: `git grep -E` kennt weder `\s` noch `(?:`.
    pat = ('^[[:space:]]*(@\\[|private |protected |noncomputable |nonrec |partial '
           '|unsafe |scoped |local |theorem |lemma |def |abbrev |structure |class '
           '|instance|inductive |opaque |axiom |namespace |end |alias )')
    if source == 'master':
        cmd = ['git', '-C', MATHLIB4, 'grep', '-n', '-E', pat,
               'upstream/master', '--', 'Mathlib/']
        out = subprocess.run(cmd, capture_output=True, text=True).stdout
        for line in out.splitlines():
            try:
                rev, path, no, text = line.split(':', 3)
            except ValueError:
                continue
            yield path, int(no), text
    else:
        cmd = ['grep', '-rn', '-E', pat, '--include=*.lean', 'Mathlib/']
        out = subprocess.run(cmd, capture_output=True, text=True, cwd=V4331).stdout
        for line in out.splitlines():
            try:
                path, no, text = line.split(':', 2)
            except ValueError:
                continue
            yield path, int(no), text


def build(source):
    index = {}
    cur_file, stack, pending_depr = None, [], False
    for path, no, text in emit_lines(source):
        if path != cur_file:
            cur_file, stack, pending_depr = path, [], False
        m = NS.match(text)
        if m:
            if m.group(1) == 'namespace':
                stack.extend(m.group(2).split('.'))
            else:
                parts = m.group(2).split('.')
                if stack[-len(parts):] == parts:
                    del stack[-len(parts):]
            continue
        # `@[deprecated ...] alias foo := bar` betrifft `foo`, nicht die nächste
        # richtige Deklaration; ein Attribut ohne eigene Deklaration in derselben
        # Zeile gilt nur, wenn die nächste Zeile die Deklaration ist.
        for t in TRANS.findall(text):
            if t in TRANS_STOP:
                continue
            full = '.'.join(stack + [t]) if stack else t
            index.setdefault(full, f'{path}:{no} (to_dual/to_additive)')
        if re.match(r'^\s*alias\b', text):
            for a in re.findall(r"[A-Za-z_][A-Za-z0-9_.'₀-₉]*",
                                text.split(':=')[0].replace('alias', '', 1)):
                full = '.'.join(stack + [a]) if stack else a
                index.setdefault(full, ('!' if pending_depr else '') + f'{path}:{no} (alias)')
            pending_depr = False   # das `deprecated` galt dem Alias
            continue
        if DEPR.search(text):
            if re.search(r'\balias\b', text):
                continue
            pending_depr = True
            if not re.search(r'\b(theorem|lemma|def|abbrev|instance)\b', text):
                continue
        elif re.match(r'^\s*@\[', text) and not re.search(
                r'\b(theorem|lemma|def|abbrev|instance|structure|class)\b', text):
            # ein anderes Attribut auf eigener Zeile hebt ein hängendes
            # `deprecated` nicht auf, unterbricht es aber auch nicht
            continue
        m = DECL.match(text.split('@[')[-1] if text.lstrip().startswith('@[') else text)
        if not m:
            continue
        name = m.group(2)
        if not name:
            pending_depr = False
            continue
        name = name.strip().rstrip(',')
        if not re.match(r"^[A-Za-z_][A-Za-z0-9_.'!?₁-₉]*$", name):
            pending_depr = False
            continue
        full = '.'.join(stack + [name]) if stack else name
        val = ('!' if pending_depr else '') + f'{path}:{no}'
        index.setdefault(full, val)
        pending_depr = False
    return index


if __name__ == '__main__':
    src = sys.argv[1] if len(sys.argv) > 1 else 'master'
    idx = build(src)
    os.makedirs(OUT, exist_ok=True)
    json.dump(idx, open(f'{OUT}/index_{src}.json', 'w'))
    print(src, 'declarations:', len(idx))
