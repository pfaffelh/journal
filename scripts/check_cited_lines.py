#!/usr/bin/env python3
"""Prüft die in den Roadmaps zitierten **Zeilennummern** gegen einen
Mathlib-Stand.

    python3 scripts/check_cited_lines.py [REV] [--fix]
    -> scripts/_citations/cited_lines.md

`check_cited_names.py` prüft, ob ein zitierter **Name** auf `master` existiert.
Dieses Skript prüft das andere Stück derselben Angabe: ob er auf der zitierten
**Zeile** steht.  Beides zusammen ist das, was ein Leser der Roadmap nachschlägt.

**Warum es nicht paart, sondern prüft.**  Die Roadmaps schreiben Name und
Fundstelle nicht in einem festen Muster; die Fundstelle steht mal hinter dem
Namen in derselben Zeile, mal am Anfang der nächsten, und eine zweite Fundstelle
desselben Satzes wird als bloßes `` `:90` `` angehängt.  Eine Fassung, die zu
jeder Fundstelle den *letzten davorstehenden* Bezeichner nimmt, ist deshalb
falsch, wo zwei Namen und zwei Zeilen in einem Satz stehen — gemessen am
2026-09-19: von 122 so erzeugten „Abweichungen" waren mehrere reine
Fehlpaarungen.

Das Skript geht deshalb umgekehrt vor.  Es baut aus dem Index die Umkehrung
`Datei:Zeile -> Namen` und fragt zu jeder Fundstelle: steht **irgendeiner** der
Bezeichner des Umfelds genau dort?  Dann ist die Angabe richtig, gleichgültig
welcher es war.  Erst wenn keiner dort steht, wird gepaart, und zwar nur, wenn
**genau ein** Bezeichner des Umfelds in der zitierten *Datei* deklariert ist.
Alles andere ist „ungepaart" und von Hand anzusehen.

**Was ein Befund ist und was nicht.**  Ein Pfad gilt als übereinstimmend, wenn
der Pfad des Index auf den zitierten endet — die Roadmaps kürzen `Mathlib/` und
manchmal mehr weg.  Gemeldet wird nur die **Zeile**.  Es schreibt nichts an den
Roadmaps; was zu ändern ist, entscheidet der Lauf.
"""
import json
import os
import re
import subprocess
import sys

os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

BASE = 'Journal/Blog/MartingaleProblem/TauCeti'
OUT = 'scripts/_citations'
MATHLIB4 = '/home/pfaffelh/Code/lean/mathlib4'
FIX = False
PINNED = '94ef6b89544e58e90f119da869f3fb48d1da0f4c'

#  `(`Probability/Martingale/Basic.lean:281`)` und die Fortsetzung `` `:90` ``.
CITE = re.compile(r'`((?:[A-Za-z][A-Za-z0-9_/]*/)?[A-Z][A-Za-z0-9_]*\.lean):(\d+)`')
CONT = re.compile(r'`:(\d+)`')
IDENT = re.compile(r"`([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)`")
LOOKBACK = 400


def index_for(rev):
    path = f'{OUT}/index_{rev}.json'
    if not os.path.exists(path):
        subprocess.run([sys.executable, 'scripts/mathlib_index.py', rev], check=True)
    return json.load(open(path))


def sources():
    for d in sorted(os.listdir(BASE)):
        for f in ['README.md', 'Suggested.lean']:
            p = os.path.join(BASE, d, f)
            if os.path.exists(p):
                yield p


def locations(name, index, by_tail):
    """Alle "Datei:Zeile", unter denen dieser Bezeichner stehen kann."""
    pairs = ([(name, index[name])] if name in index else [])
    pairs += [(q, index[q]) for q in by_tail.get(name, ())]
    return [(q, loc.lstrip('!').split(' ')[0]) for q, loc in pairs]


_FILES = {}


def source_line(rev, path, no):
    """Die Zeile `no` der Datei `path` im Stand `rev`, oder ''."""
    if path not in _FILES:
        r = subprocess.run(['git', '-C', MATHLIB4, 'show', f'{rev}:{path}'],
                           capture_output=True, text=True)
        _FILES[path] = r.stdout.splitlines() if r.returncode == 0 else []
    body = _FILES[path]
    return body[no - 1].strip() if 0 < no <= len(body) else ''


def main():
    global FIX
    args = [a for a in sys.argv[1:] if a != '--fix']
    FIX = '--fix' in sys.argv
    rev = args[0] if args else PINNED
    index = index_for(rev)
    by_tail = {}
    for q in index:
        parts = q.split('.')
        for i in range(1, len(parts)):
            by_tail.setdefault('.'.join(parts[i:]), []).append(q)

    #  Datei -> [(Zeile, Name)], aufsteigend: damit zu einer zitierten Zeile
    #  gesagt werden kann, in welcher Deklaration sie liegt.
    by_file = {}
    for q, loc in index.items():
        p, _, l = loc.lstrip('!').split(' ')[0].rpartition(':')
        try:
            by_file.setdefault(p, []).append((int(l), q))
        except ValueError:
            pass
    for p in by_file:
        by_file[p].sort()

    def owner(path, line):
        """Die Deklaration, in deren Rumpf die Zeile liegt (oder '')."""
        entries = by_file.get(path, [])
        lo, hi, best = 0, len(entries) - 1, ''
        while lo <= hi:
            mid = (lo + hi) // 2
            if entries[mid][0] <= line:
                best = entries[mid][1]
                lo = mid + 1
            else:
                hi = mid - 1
        return best

    ok, moved, unpaired, spans = [], [], [], {}
    for src in sources():
        text = open(src, encoding='utf-8').read()

        def lineno(pos):
            return text.count('\n', 0, pos) + 1

        last_path, last_pos = None, -10 ** 9
        for m in re.finditer(r'`(?:(?:[A-Za-z][A-Za-z0-9_/]*/)?[A-Z][A-Za-z0-9_]*\.lean)?:\d+`',
                             text):
            full = CITE.match(m.group(0))
            if full:
                cpath, cline = full.group(1), int(full.group(2))
                last_path, last_pos = cpath, m.end()
            else:
                cont = CONT.match(m.group(0))
                #  Ein bloßes `` `:154` `` erbt die Datei der vorigen
                #  Fundstelle — aber nur, wenn die nah genug steht.  Am
                #  2026-09-19 hat eine Fassung ohne diese Schranke eine
                #  Fundstelle in `LevyConvergence.lean` der Datei eines
                #  Absatzes weiter oben zugeschlagen und daraus einen Befund
                #  gemacht, der keiner war.
                if not cont or last_path is None or m.start() - last_pos > 300:
                    continue
                cpath, cline = last_path, int(cont.group(1))

            where = f'{src}:{lineno(m.start())}'
            tail = cpath.split('/')[-1]
            #  Das Umfeld: der Text davor und der Rest derselben Zeile.
            eol = text.find('\n', m.end())
            window = (text[max(0, m.start() - LOOKBACK):m.start()]
                      + text[m.end():eol if eol >= 0 else len(text)])
            #  Kandidaten: jeder Bezeichner des Umfelds, der in der zitierten
            #  Datei deklariert ist.
            in_file = []
            hit = None
            for im in IDENT.finditer(window):
                for qname, loc in locations(im.group(1), index, by_tail):
                    ipath, _, iline_s = loc.rpartition(':')
                    if not ipath.endswith(tail):
                        continue
                    try:
                        iline = int(iline_s)
                    except ValueError:
                        continue
                    if iline == cline:
                        hit = (qname, ipath)
                    in_file.append((qname, ipath, iline))
            if hit:
                ok.append((where, hit[0], cpath, cline))
                continue
            names = {q for q, _, _ in in_file}
            if len(names) == 1:
                qname, ipath, iline = in_file[0]
                moved.append((where, qname, cpath, cline, ipath, iline))
                spans.setdefault(src, []).append((m.start(), m.end(), m.group(0),
                                                  cline, iline, where))
            else:
                unpaired.append((where, cpath, cline, sorted(names)))

    #  Eine Fundstelle, die genau auf die erste Zeile *irgendeiner*
    #  Deklaration zeigt, ist nicht veraltet, sondern auf etwas anderes
    #  gemünzt als auf den Namen, den die Paarung gewählt hat — meist auf
    #  eine Nachbarschaft, ein `variable`-Bündel oder die zweite von zwei
    #  Aussagen desselben Satzes.  Sie wird getrennt geführt und **nicht**
    #  umgeschrieben.
    exact_lines = {(p, l) for p, es in by_file.items() for l, _ in es}

    def header_owner(path, line):
        """Die Deklaration, deren Kopf (Doc-Kommentar, Attribute) die Zeile
        `line` ist — leer, wenn dazwischen etwas anderes steht."""
        entries = by_file.get(path, [])
        for l, q in entries:
            if l < line:
                continue
            for k in range(line, l):
                t = source_line(rev, path, k)
                if t and not (t.startswith(('/-', '-/', '--', '*', '@[', ')'))
                              or t.endswith('-/')):
                    return ''
            return q
        return ''

    def deliberate(e):
        """Wahr, wenn die zitierte Zeile nicht veraltet, sondern gemeint ist."""
        where, name, _, cline, ipath, _ = e
        if (ipath, cline) in exact_lines:
            return True
        text = source_line(rev, ipath, cline)
        if text.startswith(('variable', 'section', 'namespace', 'open ')):
            return True
        #  Der Kopf einer Deklaration — Doc-Kommentar oder Attribut — ist eine
        #  richtige Fundstelle, und manchmal die gemeinte: eine Roadmap zitiert
        #  das `@[instance_reducible]`, nicht die Zeile mit `def`.
        if header_owner(ipath, cline):
            return True
        #  Eine Angabe, die sich ausdrücklich auf v4.33.1 beruft, ist ein
        #  **Versionsvergleich** und kein veraltetes Zitat.  Sie zu berichtigen
        #  hieße, den Vergleich zu zerstören, um den es dort geht.
        src, _, ln = where.rpartition(':')
        body = open(src, encoding='utf-8').read().splitlines()
        near = ' '.join(body[max(0, int(ln) - 2):int(ln) + 1])
        return 'v4.33.1' in near

    aimed = [e for e in moved if deliberate(e)]
    moved = [e for e in moved if not deliberate(e)]

    #  Die Datei selbst — unabhängig von jeder Paarung.  Eine Fundstelle in
    #  einer Datei, die es nicht mehr gibt, die nur noch ein
    #  `deprecated_module`-Rumpf ist, oder deren Zeile hinter dem Ende liegt,
    #  ist tot, und der Leser merkt es sofort.  Am 2026-09-19 fand dieser
    #  Test drei Zitate in `MeasureTheory/Measure/MeasureSpace.lean`, das auf
    #  `master` seit dem 2026-08-19 vierzehn Zeilen hat und nichts enthält.
    tree = subprocess.run(['git', '-C', MATHLIB4, 'ls-tree', '-r', '--name-only',
                           rev, '--', 'Mathlib/'], capture_output=True, text=True).stdout
    files = tree.splitlines()
    dead = []
    for src in sources():
        text = open(src, encoding='utf-8').read()
        for m in CITE.finditer(text):
            cpath, cline = m.group(1), int(m.group(2))
            #  Der zitierte Pfad ist gekürzt; er muß auf **ganze
            #  Wegbestandteile** passen.  Eine Fassung, die auch den
            #  Dateinamen allein nehmen ließ, hielt am 2026-09-19
            #  `Topology/Closure.lean` für `Analysis/Convex/Cone/Closure.lean`
            #  und meldete vierzehn Befunde, von denen einer echt war.
            cands = [f for f in files if f == cpath or f.endswith('/' + cpath)]
            where = f'{src}:{text.count("\n", 0, m.start()) + 1}'
            if not cands:
                continue          # unbekannt: das prüft `check_cited_names.py`
            #  Ein gekürzter Pfad paßt oft auf mehrere Dateien
            #  (`Order/Disjointed.lean` auch auf `Algebra/Order/Disjointed.lean`).
            #  Gemeldet wird nur, wenn **keine** von ihnen die Fundstelle
            #  tragen kann.
            why = []
            for cand in cands:
                body = _FILES.get(cand)
                if body is None:
                    r = subprocess.run(['git', '-C', MATHLIB4, 'show', f'{rev}:{cand}'],
                                       capture_output=True, text=True)
                    body = _FILES[cand] = r.stdout.splitlines()
                if any(l.startswith('deprecated_module') for l in body):
                    why.append(f'`{cand}` ist ein `deprecated_module`-Rumpf')
                elif cline > len(body):
                    why.append(f'`{cand}` hat nur {len(body)} Zeilen')
                else:
                    why = []
                    break
            #  Eine Angabe, die sich selbst auf v4.33.1 beruft, ist ein
            #  Versionsvergleich und kein toter Verweis.
            body = text.splitlines()
            ln = text.count('\n', 0, m.start())
            if why and 'v4.33.1' not in ' '.join(body[max(0, ln - 2):ln + 2]):
                dead.append((where, cpath, cline, '; '.join(why)))

    lines = []
    lines.append(f'# Zitierte Zeilennummern gegen `{rev}`')
    lines.append('')
    lines.append(f'* geprüft: {len(ok) + len(moved)} gepaarte Fundstellen')
    lines.append(f'* **stimmt: {len(ok)}**')
    lines.append(f'* **verschoben: {len(moved)}**')
    lines.append(f'* zielt auf eine andere Deklaration (von Hand): {len(aimed)}')
    lines.append(f'* ungepaart (von Hand): {len(unpaired)}')
    lines.append(f'* **tote Fundstelle: {len(dead)}**')
    lines.append('')
    lines.append(f'## Tote Fundstellen ({len(dead)})')
    lines.append('')
    for where, cpath, cline, why in dead:
        lines.append(f'* `{where}` -> `{cpath}:{cline}`: {why}')
    lines.append('')
    lines.append(f'## Zielt auf eine andere Deklaration ({len(aimed)})')
    lines.append('')
    lines.append('Die zitierte Zeile ist die erste Zeile einer anderen Deklaration, ihr '
                 'Kopf, oder ein `variable`-Bündel. Nicht umzuschreiben, ohne den Satz '
                 'zu lesen.')
    lines.append('')
    for where, name, cpath, cline, ipath, iline in aimed:
        at = source_line(rev, ipath, cline)[:60]
        tgt = owner(ipath, cline) if (ipath, cline) in exact_lines \
            else (header_owner(ipath, cline) or f'`{at}`')
        lines.append(f'* `{where}`: `{cpath}:{cline}` ist {tgt}; '
                     f'gepaart wurde `{name}` (`{iline}`)')
    lines.append('')
    lines.append(f'## Verschoben ({len(moved)})')
    lines.append('')
    if moved:
        lines.append('| Stelle | Name | zitiert | steht auf | die zitierte Zeile liegt in '
                     '| und lautet |')
        lines.append('| --- | --- | ---: | ---: | --- | --- |')
        for where, name, cpath, cline, ipath, iline in moved:
            at = source_line(rev, ipath, cline).replace('|', '¦')[:70]
            own = owner(ipath, cline)
            lines.append(f'| `{where}` | `{name}` | `{cpath}:{cline}` '
                         f'| `{ipath}:{iline}` | `{own}` | `{at}` |')
    else:
        lines.append('keine')
    lines.append('')
    lines.append(f'## Ungepaart ({len(unpaired)})')
    lines.append('')
    for where, cpath, cline, names in unpaired:
        cand = ', '.join(f'`{n}`' for n in names[:4]) if names else 'kein Kandidat'
        lines.append(f'* `{where}` -> `{cpath}:{cline}` ({cand})')
    lines.append('')
    if FIX:
        keep = {(w, c, i) for w, _, _, c, _, i in moved}
        changed = 0
        for src, entries in spans.items():
            entries = [e for e in entries if (e[5], e[3], e[4]) in keep]
            if not entries:
                continue
            text = open(src, encoding='utf-8').read()
            for start, end, token, cline, iline, _ in sorted(entries, reverse=True):
                assert text[start:end] == token, (src, token)
                text = text[:start] + token.replace(f':{cline}`', f':{iline}`') + text[end:]
                changed += 1
            open(src, 'w', encoding='utf-8').write(text)
        lines.insert(1, '')
        lines.insert(2, f'**{changed} Zeilennummern umgeschrieben** (`--fix`).')

    os.makedirs(OUT, exist_ok=True)
    open(f'{OUT}/cited_lines.md', 'w', encoding='utf-8').write('\n'.join(lines))
    print('\n'.join(lines[:8]))
    print(f'-> {OUT}/cited_lines.md')
    return 1 if (moved or dead) else 0


if __name__ == '__main__':
    sys.exit(main())
