import re, sys, json, os

# Usage: map_errors.py <experiment.lean> <output.txt> <revert.json (in+out)>
exp_file, out_file, revert_file = sys.argv[1], sys.argv[2], sys.argv[3]

lines = open(exp_file).read().splitlines()
decl_re = re.compile(r"^(?:noncomputable\s+)?(?:theorem|def|lemma|abbrev|structure|inductive|class|instance)\s+([A-Za-z_À-῿Ⰰ-퟿][A-Za-z0-9_.'!?À-῿Ⰰ-퟿]*)")
decls = []
cd = 0
for i, line in enumerate(lines, 1):
    if cd > 0:
        cd += line.count('/-') - line.count('-/')
        continue
    if line.count('/-') > line.count('-/'):
        cd = line.count('/-') - line.count('-/')
        continue
    m = decl_re.match(line)
    if m:
        decls.append((i, m.group(1)))

omit_line_re = re.compile(r'^omit .* in\s*$')

def decl_at(lineno):
    # a "cannot omit" error points at the omit line itself or at the doc
    # comment / attribute right after it; in both cases the culprit is the
    # NEXT declaration below
    for k in (lineno - 1, lineno - 2, lineno - 3):
        if 0 <= k < len(lines) and omit_line_re.match(lines[k]):
            cand = [(l, nm) for (l, nm) in decls if l > lineno]
            if cand:
                return cand[0][1]
    cand = [(l, nm) for (l, nm) in decls if l <= lineno]
    return cand[-1][1] if cand else '???'

err_lines = set()
for line in open(out_file):
    m = re.search(r'\.lean:(\d+):\d+: error', line)
    if m:
        err_lines.add(int(m.group(1)))

bad = sorted(set(decl_at(l) for l in err_lines))
try:
    revert = set(json.load(open(revert_file)))
except FileNotFoundError:
    revert = set()
new = [b for b in bad if b not in revert]
revert |= set(bad)
json.dump(sorted(revert), open(revert_file, 'w'))
print('neue Reverts:', new)
print('gesamt Reverts:', sorted(revert))
