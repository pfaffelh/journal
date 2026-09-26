import re
p = 'Journal/Blog/MartingaleProblem/Facts/INVENTAR.md'
s = open(p).read()
start = s.index('### 2026-09-26, Lauf 18:03 UTC')
head, body = s[:start], s[start:]
new = {
    'LocalMixWitness.Outcome': 49046, 'LocalMixWitness.T': 49079,
    'instance : filt.IsRightContinuous': 49118,
    'LocalMixWitness.eq_empty_of_Q_eq_zero': 49209, 'LocalMixWitness.isLocalMPSolution_P': 49223,
    'LocalMixWitness.martingale_D': '49294, 49377', "LocalMixWitness.isLocalMPSolution_P'": 49401,
    'LocalMixWitness.le_of_isStoppingTime': 49411, 'LocalMixWitness.not_integrable_of': 49445,
    'LocalMixWitness.not_isLocalMPSolution_Q': 49459, 'LocalMixWitness.not_convex': 49475,
    'setIntegral_eq_kernel_of_restart': 50268, 'condExp_eq_kernel_of_restart': 50343,
    'isStrongMarkov_kernel_of_unique_onedim': 50389, 'semigroup_of_unique_onedim': 50451,
    'condExp_eq_kernel': 50487, 'isStrongMarkov_kernel_of_countable_range_of_bounded': 50527,
    'IsShiftSystem.IsConsistent': 50590, 'IsShiftSystem.IsConsistent.isShiftSystem': 50595,
    'IsShiftSystem.isConsistent_const': 50602, 'chapmanKolmogorov_of_isConsistent': 50623,
    'isFiniteMeasure_map_withDensity_ofReal': '`MartingaleProblems`, 50873',
    'isMPSolution_map_withDensity_of_tendsto': '`MartingaleProblems`, 50891',
    'isStrongMarkov_mpFamily_coordinate_of_finite': '`MartingaleProblems`, 50957',
    'MeasureTheory.measurable_cadlag_eval_stoppingTime': 48814,
    'MeasureTheory.measurable_cadlagShift_randomTime': 48868,
    'MeasureTheory.measurable_cadlagShift_stoppingTime': 48878,
    'MeasureTheory.isStrongMarkov_mpFamily_cadlag': 51207,
}
out = []
cnt = 0
for line in body.split('\n'):
    if line.startswith('|'):
        cells = line.split('|')
        if len(cells) >= 5:
            nm = cells[2].strip()
            m = re.match(r'`([^`]+)`', nm)
            key = m.group(1) if m else None
            if key in new:
                cells[-2] = ' ' + str(new[key]) + ' '
                line = '|'.join(cells)
                cnt += 1
    out.append(line)
body = '\n'.join(out)
rep = [
    ('`isStrongMarkov_of_unique_onedim` (Z. 50102', '`isStrongMarkov_of_unique_onedim` (Z. 50207'),
    ('`isStrongMarkov_kernel_of_unique_onedim` (50284', '`isStrongMarkov_kernel_of_unique_onedim` (50389'),
    ('`semigroup_of_unique_onedim` (50346)', '`semigroup_of_unique_onedim` (50451)'),
    ('`chapmanKolmogorov_of_unique_onedim` (49704', '`chapmanKolmogorov_of_unique_onedim` (49809'),
    ('`isStrongMarkov_mpFamily_coordinate` (50674)', '`isStrongMarkov_mpFamily_coordinate` (50779)'),
    ('`isStrongMarkov_kernel_of_countable_range` (49627', '`isStrongMarkov_kernel_of_countable_range` (49732'),
    ('`isStrongMarkov_kernel_of_countable_range_of_bounded` (50422)',
     '`isStrongMarkov_kernel_of_countable_range_of_bounded` (50527)'),
    ('`chapmanKolmogorov_of_isConsistent`\n(50518', '`chapmanKolmogorov_of_isConsistent`\n(50623'),
]
for a, b in rep:
    if a in body:
        body = body.replace(a, b)
    else:
        print('miss', a[:60])
open(p, 'w').write(head + body)
print(cnt)
