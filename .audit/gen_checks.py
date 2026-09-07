import re, os, sys

# Append a '#check @name' block to a lean file, for every named declaration.
# Usage: gen_checks.py <src.lean> <dst.lean> [namespace-mode]
src_path, dst_path = sys.argv[1], sys.argv[2]

decl_re = re.compile(r"^(?:noncomputable\s+)?(?:theorem|def|lemma|abbrev|structure|inductive|class|instance)\s+([A-Za-z_À-῿Ⰰ-퟿][A-Za-z0-9_.'!?À-῿Ⰰ-퟿]*)")
omit_skip = {'tendsto_map_of_measure_setOf_continuousAt_eq_one'}

lines = open(src_path).read().splitlines()
ns = []
names = []
cd = 0
for line in lines:
    if cd > 0:
        cd += line.count('/-') - line.count('-/')
        continue
    if line.count('/-') > line.count('-/'):
        cd = line.count('/-') - line.count('-/')
        continue
    m = re.match(r'^namespace\s+(\S+)', line)
    if m:
        ns.append(m.group(1)); continue
    m = re.match(r'^end\s+(\S+)', line)
    if m and ns and ns[-1] == m.group(1):
        ns.pop(); continue
    m = decl_re.match(line)
    if m and m.group(1) not in omit_skip:
        names.append('.'.join(ns + [m.group(1)]))

out = open(src_path).read() + '\n\nsection SigDump\n'
for nm in names:
    out += '#check @' + nm + '\n'
out += 'end SigDump\n'
open(dst_path, 'w').write(out)
print(dst_path, len(names))
