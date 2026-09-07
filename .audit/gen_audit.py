import re, os

base = '/home/pfaffelh/Code/lean/journal-facts/Journal/Blog/MartingaleProblem/TauCeti'
out_dir = '/home/pfaffelh/Code/lean/journal-facts/.audit'
files = {
 'WeakConvergence': 'WeakConvergence/Suggested.lean',
 'MartingaleProblems': 'MartingaleProblems/Suggested.lean',
 'SkorokhodSpace': 'SkorokhodSpace/Suggested.lean',
}

decl_re = re.compile(r"^(?:noncomputable\s+)?(theorem|def|lemma|abbrev|structure|inductive|class|instance)\s+([A-Za-z_À-῿Ⰰ-퟿][A-Za-z0-9_.'!?À-῿Ⰰ-퟿]*)")

skip = {('WeakConvergence', 'tendsto_map_of_measure_setOf_continuousAt_eq_one')}

for key, path in files.items():
    full_path = os.path.join(base, path)
    src = open(full_path).read().splitlines()
    ns = []
    names = []
    in_comment = 0
    for line in src:
        stripped = line.strip()
        in_comment += line.count('/-') - line.count('-/')
        if in_comment > 0 or stripped.startswith('--'):
            continue
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)', line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); continue
        m = decl_re.match(line)
        if m:
            kind, name = m.groups()
            if (key, name) in skip:
                continue
            full = '.'.join(ns + [name])
            names.append((kind, full))
    out = ['-- AUDIT: #print axioms fuer jede Deklaration', 'section AxiomAudit']
    for kind, full in names:
        out.append('#print axioms ' + full)
    out.append('end AxiomAudit')
    audit = open(full_path).read() + '\n\n' + '\n'.join(out) + '\n'
    dst = os.path.join(out_dir, 'audit_' + key + '.lean')
    open(dst, 'w').write(audit)
    print(key, len(names), '->', dst)
