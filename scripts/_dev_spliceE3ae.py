#!/usr/bin/env python3
"""Einmalig: setzt die Sätze aus `_dev_E3ae.lean` in die Roadmap-Dateien."""
import os
R = os.path.dirname(os.path.abspath(__file__))
B = os.path.join(R, '../Journal/Blog/MartingaleProblem/TauCeti')
dev = open(os.path.join(R, '_dev_E3ae.lean')).read()

a = dev.index('section StrongMarkovAeFinite')
b = dev.index('end StrongMarkovAeFinite') + len('end StrongMarkovAeFinite')
mp_block = dev[a:b]
c = dev.index('open RightContinuousPath in\n/-- **`isStrongMarkov_jumpOperator_coordinate` at every almost')
d = dev.index('end JumpDev')
jp_block = dev[c:d].rstrip() + '\n'

p = os.path.join(B, 'MartingaleProblems/Suggested.lean')
s = open(p).read()
anchor = 'end StrongMarkovFinite\n'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + '\n' + mp_block + '\n')
open(p, 'w').write(s)

p = os.path.join(B, 'JumpProcesses/Suggested.lean')
s = open(p).read()
anchor = '      R R\' hR hR\' hs hs\' h0 u) hf hfb t\n\nend JumpUniqueness\n'
assert s.count(anchor) == 1, s.count(anchor)
s = s.replace(anchor, '      R R\' hR hR\' hs hs\' h0 u) hf hfb t\n\n' + jp_block
              + '\nend JumpUniqueness\n')
open(p, 'w').write(s)
print('ok')
