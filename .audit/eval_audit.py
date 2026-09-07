import re, os, sys

task_dir = '/tmp/claude-1000/-home-pfaffelh-Code-lean-journal-facts/933c1392-78e2-4a4f-975a-07822bb0e1f8/tasks'
outs = {
 'WeakConvergence': os.path.join(task_dir, 'byl8n92wj.output'),
 'MartingaleProblems': os.path.join(task_dir, 'bllm77p0x.output'),
 'SkorokhodSpace': os.path.join(task_dir, 'b9et0gi1u.output'),
}
base = '/home/pfaffelh/Code/lean/journal-facts/.audit'

for key, path in outs.items():
    text = open(path).read()
    # join wrapped lines: axiom lists may span lines until ']'
    entries = {}  # name -> axioms string
    cur_name = None
    cur_ax = []
    sorry_warn_lines = []
    for line in text.splitlines():
        m = re.search(r"declaration uses .sorry.", line)
        if m:
            lm = re.search(r'\.lean:(\d+):', line)
            if lm:
                sorry_warn_lines.append(int(lm.group(1)))
        m = re.match(r"'([^']+)' depends on axioms: \[(.*)", line)
        if m:
            if cur_name is not None:
                entries[cur_name] = ' '.join(cur_ax)
            cur_name = m.group(1)
            cur_ax = [m.group(2)]
            if line.rstrip().endswith(']'):
                entries[cur_name] = ' '.join(cur_ax)
                cur_name = None
                cur_ax = []
            continue
        if cur_name is not None:
            cur_ax.append(line.strip())
            if line.rstrip().endswith(']'):
                entries[cur_name] = ' '.join(cur_ax)
                cur_name = None
                cur_ax = []
    if cur_name is not None:
        entries[cur_name] = ' '.join(cur_ax)

    # map warning line numbers to declaration names in the audit lean file
    audit_lean = os.path.join(base, 'audit_' + key + '.lean')
    src = open(audit_lean).read().splitlines()
    decl_re = re.compile(r"^(?:noncomputable\s+)?(?:theorem|def|lemma|abbrev|structure|inductive|class|instance)\s+([A-Za-z_À-῿Ⰰ-퟿][A-Za-z0-9_.'!?À-῿Ⰰ-퟿]*)")
    decl_lines = []  # (lineno, name)
    for i, line in enumerate(src, 1):
        m = decl_re.match(line)
        if m:
            decl_lines.append((i, m.group(1)))
    def decl_at(lineno):
        cand = [(l, n) for (l, n) in decl_lines if l <= lineno]
        return cand[-1][1] if cand else '???'
    own_sorry = set(decl_at(l) for l in sorry_warn_lines)

    print('==== ' + key + ' ====')
    print('deklarationen mit #print axioms:', len(entries))
    n_sorry = 0
    bad = []
    for name, ax in entries.items():
        has = 'sorryAx' in ax
        if has:
            n_sorry += 1
            short = name.split('.')[-1]
            if short not in own_sorry and name not in own_sorry:
                bad.append(name)
    print('davon sorryAx:', n_sorry)
    print('own-sorry-deklarationen (aus warnings):', sorted(own_sorry))
    print('VERDAECHTIG (sorryAx ohne eigenes sorry):')
    for b in bad:
        print('  ', b)
    print()
