import re, os, sys, json

# Parse a Suggested.lean into blocks; for chosen declarations, add omit-candidates.
# Usage: gen_omit_experiment.py <key> <revert.json>
# revert.json: list of declaration names whose omits must stay as in the original.

base = '/home/pfaffelh/Code/lean/journal-facts/Journal/Blog/MartingaleProblem/TauCeti'
out_dir = '/home/pfaffelh/Code/lean/journal-facts/.audit'

CONF = {
  'SkorokhodSpace': {
    'path': 'SkorokhodSpace/Suggested.lean',
    'candidates': ['[OrderTopology ι]', '[AdditiveDist ι]', '[ProperSpace ι]'],
    # declarations whose proof is sorry, or which do not bind iota, or anonymous: never touch
    'skip': ['exists_orderIso_isometry_real', 'SkorokhodSpace.continuousAt_eval',
             'SkorokhodSpace.measurableEmbedding_piDense', 'SkorokhodSpace.borel_eq_iSup_comap_eval',
             'SkorokhodSpace.modulus', 'SkorokhodSpace.tendsto_modulus',
             'SkorokhodSpace.isCompact_closure_iff', 'SkorokhodSpace.metricSpace',
             'AdditiveDist', 'instAdditiveDistSubtype', 'Real.instAdditiveDist',
             'Function.RightContinuous', 'IsCadlag',
             'strictMono_steepFun', 'rightInverse_steepFun', 'lipschitzWith_steepFun',
             'lipschitzWith_steepInvFun', 'TimeChange.steep', 'strictMono_doubleFun',
             'rightInverse_doubleFun', 'lipschitzWith_doubleFun', 'lipschitzWith_doubleInvFun',
             'TimeChange.double', 'mem_exhaustion_real_iff', 'TimeChange.normOn_steep_le',
             'TimeChange.normOn_double_le', 'TimeChange.le_normOn_steep_mul_double',
             'TimeChange.not_normOn_mul_le', 'exhaustion'],
    'first_line': 140,   # only touch declarations after the variable bundle
  },
  'MartingaleProblems': {
    'path': 'MartingaleProblems/Suggested.lean',
    'candidates': ['[OrderBot ι]', '[TopologicalSpace ι]', '[OrderTopology ι]'],
    'skip': ['isMPSolution_iff_forall_fdd', 'isMPSolution_iff_forall_fdd_continuous',
             'restart', 'restart_canonical', 'exists_cadlag_modification_of_isRegularizingClass',
             'isQuasiLeftContinuous_of_isRegularizingClass', 'isQuasiLeftContinuous_of_isMPSolutionFor',
             'mpSolution_of_tendsto', 'isMPSolution_of_forall_condExp_eq_of_dense',
             'Clock.Conv', 'Clock', 'TendstoLaw'],
    'first_line': 415,   # only the Regularizing section carries these binders
    'last_line': 945,
  },
}

key = sys.argv[1]
revert = set(json.load(open(sys.argv[2]))) if len(sys.argv) > 2 else set()
conf = CONF[key]
full_path = os.path.join(base, conf['path'])
lines = open(full_path).read().splitlines()

decl_re = re.compile(r"^(?:noncomputable\s+)?(?:theorem|def|lemma|abbrev|structure|inductive|class|instance)\s+([A-Za-z_À-῿Ⰰ-퟿][A-Za-z0-9_.'!?À-῿Ⰰ-퟿]*)")
omit_re = re.compile(r"^omit (.*) in\s*$")

out = []
i = 0
n = len(lines)
touched = []
next_decl_handled = False
comment_depth = 0
while i < n:
    line = lines[i]
    if comment_depth > 0:
        comment_depth += line.count('/-') - line.count('-/')
        out.append(line)
        i += 1
        continue
    if line.count('/-') > line.count('-/'):
        comment_depth = line.count('/-') - line.count('-/')
        out.append(line)
        i += 1
        continue
    m = omit_re.match(line)
    if m:
        next_decl_handled = True
        # find the declaration this omit belongs to (skip doc comments)
        j = i + 1
        cd = 0
        while j < n:
            t = lines[j]
            if cd > 0:
                cd += t.count('/-') - t.count('-/')
                j += 1
                continue
            if t.count('/-') > t.count('-/'):
                cd = t.count('/-') - t.count('-/')
                j += 1
                continue
            if decl_re.match(t):
                break
            j += 1
        name = decl_re.match(lines[j]).group(1) if j < n else None
        lineno = i + 1
        ok_range = lineno >= conf.get('first_line', 0) and lineno <= conf.get('last_line', 10**9)
        if name and ok_range and name not in conf['skip'] and name not in revert:
            existing = m.group(1)
            add = [c for c in conf['candidates'] if c not in existing]
            if add:
                out.append('omit ' + existing + ' ' + ' '.join(add) + ' in')
                touched.append((name, lineno))
                i += 1
                continue
        out.append(line)
        i += 1
        continue
    dm = decl_re.match(line)
    if dm:
        if next_decl_handled:
            next_decl_handled = False
            out.append(line)
            i += 1
            continue
        name = dm.group(1)
        lineno = i + 1
        ok_range = lineno >= conf.get('first_line', 0) and lineno <= conf.get('last_line', 10**9)
        # declaration without a preceding omit (the omit case is handled above,
        # because the omit line comes first in the token stream)
        prev = i - 1
        # check whether an omit already handled: look back over doc comment to see 'omit ... in'
        k = len(out) - 1
        has_omit = False
        while k >= 0:
            t = out[k]
            if omit_re.match(t):
                has_omit = True
                break
            if t.strip() == '' or t.strip().startswith('/--') or t.strip().startswith('--') or not decl_re.match(t):
                # crude: stop at previous declaration-looking line
                if decl_re.match(t):
                    break
                k -= 1
                continue
            break
        # simpler check: scan backwards in ORIGINAL lines from i-1 while in doc comment
        has_omit = False
        k = i - 1
        depth = 0
        while k >= 0:
            t = lines[k]
            if t.strip() == '':
                break
            if omit_re.match(t):
                has_omit = True
                break
            k -= 1
            if i - k > 40:
                break
        if (not has_omit) and ok_range and name not in conf['skip'] and name not in revert and ('ι' in ''.join(lines[i:i+3])):
            # insert the omit BEFORE the attached doc comment, not between it
            # and the declaration
            ins = len(out)
            if out and out[-1].rstrip().endswith('-/'):
                depth = 0
                k = len(out) - 1
                while k >= 0:
                    t = out[k]
                    depth += t.count('-/') - t.count('/-')
                    if depth <= 0:
                        break
                    k -= 1
                ins = k
            out.insert(ins, 'omit ' + ' '.join(conf['candidates']) + ' in')
            touched.append((name, lineno))
        out.append(line)
        i += 1
        continue
    out.append(line)
    i += 1

dst = os.path.join(out_dir, 'omit_' + key + '.lean')
open(dst, 'w').write('\n'.join(out) + '\n')
json.dump(touched, open(os.path.join(out_dir, 'touched_' + key + '.json'), 'w'))
print(key, 'touched', len(touched), 'declarations ->', dst)
for t in touched:
    print('  ', t[0], t[1])
