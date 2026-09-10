#!/usr/bin/env python3
"""Prüft die aus den Roadmaps extrahierten Zitate gegen die beiden
Mathlib-Indizes (`index_master.json`, `index_v4331.json`).

Voraussetzung: `scripts/extract_citations.py` und `scripts/mathlib_index.py`
(einmal mit `master`, einmal mit `v4331`) sind gelaufen.

Ausgabe nach `scripts/_citations/report.md`.
"""
import json, os, re, subprocess

# Alle Pfade relativ zur Wurzel des Worktrees, damit das Skript aus jedem
# Verzeichnis heraus lauffähig ist.
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

OUT = 'scripts/_citations'
MATHLIB4 = '/home/pfaffelh/Code/lean/mathlib4'

cands = json.load(open(f'{OUT}/cands.json'))
paths = json.load(open(f'{OUT}/paths.json'))
im = json.load(open(f'{OUT}/index_master.json'))
iv = json.load(open(f'{OUT}/index_v4331.json'))

# Nachschlagen: voller Name, oder ein Name, dessen Suffix der Kandidat ist.
short_m, short_v = {}, {}
for idx, short in ((im, short_m), (iv, short_v)):
    for full, loc in idx.items():
        short.setdefault(full.split('.')[-1], []).append((full, loc))


def look(name, idx, short):
    if name in idx:
        return ('exact', name, idx[name])
    hits = [(f, l) for f, l in short.get(name.split('.')[-1], [])
            if f == name or f.endswith('.' + name)]
    if hits:
        return ('suffix', hits[0][0], hits[0][1])
    return (None, None, None)


# --- Dateipfade ---
master_files = set(subprocess.run(
    ['git', '-C', MATHLIB4, 'ls-tree', '-r', '--name-only', 'upstream/master', 'Mathlib/'],
    capture_output=True, text=True).stdout.split())
V4331 = '/home/pfaffelh/Code/lean/journal/.lake/packages/mathlib'
v_files = set()
for root, _, fs in os.walk(os.path.join(V4331, 'Mathlib')):
    for f in fs:
        if f.endswith('.lean'):
            v_files.add(os.path.relpath(os.path.join(root, f), V4331))

lines = ['# Zitatprüfung der Roadmaps', '']
lines.append('## Dateipfade')
bad_paths = []
for p in sorted(paths):
    m, v = p in master_files, p in v_files
    if not (m and v):
        bad_paths.append((p, m, v, paths[p]))
lines.append(f'{len(paths)} zitierte Pfade, davon {len(bad_paths)} auffällig.')
for p, m, v, where in bad_paths:
    lines.append(f'* `{p}` — master: {"ja" if m else "**NEIN**"}, '
                 f'v4.33.1: {"ja" if v else "**NEIN**"} — {", ".join(sorted(set(where)))}')

# --- Namen ---
NOISE = re.compile(r"^(sorry|by|fun|let|have|show|exact|simp|rw|omega|ring|this|"
                   r"true|false|id|Type|Prop|Sort)$")
res = {'both': [], 'only_v': [], 'only_m': [], 'neither': [], 'depr': []}
for name in sorted(cands):
    if NOISE.match(name):
        continue
    km, fm, lm = look(name, im, short_m)
    kv, fv, lv = look(name, iv, short_v)
    entry = (name, fm, lm, fv, lv, sorted(set(cands[name])))
    if km and kv:
        if (lm or '').startswith('!') or (lv or '').startswith('!'):
            res['depr'].append(entry)
        else:
            res['both'].append(entry)
    elif kv and not km:
        res['only_v'].append(entry)
    elif km and not kv:
        res['only_m'].append(entry)
    else:
        res['neither'].append(entry)

lines += ['', '## Namen', '',
          f"geprüft: {sum(len(v) for v in res.values())} | "
          f"beide: {len(res['both'])} | nur v4.33.1: {len(res['only_v'])} | "
          f"nur master: {len(res['only_m'])} | keiner: {len(res['neither'])} | "
          f"deprecated: {len(res['depr'])}"]

for key, title in [('only_v', 'Auf v4.33.1, aber **nicht mehr auf master** (verschwunden oder umbenannt)'),
                   ('depr', 'Als `deprecated` markiert'),
                   ('only_m', 'Nur auf master (die Roadmap darf sie nicht als v4.33.1-Beleg führen)'),
                   ('neither', 'In keinem Index gefunden — von Hand zu klären')]:
    lines += ['', f'### {title}', '']
    for name, fm, lm, fv, lv, where in res[key]:
        lines.append(f'* `{name}` — master: `{lm or "—"}` | v4.33.1: `{lv or "—"}` — '
                     + ', '.join(where[:4]))

lines += ['', '### Dateiwechsel (auf beiden vorhanden, aber in verschiedenen Dateien)', '']
for name, fm, lm, fv, lv, where in res['both']:
    if lm.split(':')[0] != lv.split(':')[0]:
        lines.append(f'* `{name}` — master `{lm}` vs. v4.33.1 `{lv}` — ' + ', '.join(where[:3]))

open(f'{OUT}/report.md', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines[:12]))
print('...  ->', f'{OUT}/report.md')
