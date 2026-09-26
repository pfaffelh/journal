#!/usr/bin/env python3
"""Einmalig: setzt den Abschnitt aus `_dev_E2c.lean` in `MartingaleProblems/Suggested.lean`."""
import os
R = os.path.dirname(os.path.abspath(__file__))
p = os.path.join(R, '../Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')
dev = open(os.path.join(R, '_dev_E2c.lean')).read()
a = dev.index('section ShiftSystemInhomogeneous')
b = dev.index('end ShiftSystemInhomogeneous') + len('end ShiftSystemInhomogeneous')
block = dev[a:b]
s = open(p).read()
anchor = 'end ChapmanKolmogorovInhomogeneous\n'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + '\n' + block + '\n')
open(p, 'w').write(s)
print('ok')
