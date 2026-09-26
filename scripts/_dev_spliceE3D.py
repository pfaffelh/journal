#!/usr/bin/env python3
"""Einmalig: setzt den Abschnitt aus `_dev_E3D.lean` in `MartingaleProblems/Suggested.lean`."""
import os
R = os.path.dirname(os.path.abspath(__file__))
p = os.path.join(R, '../Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean')
dev = open(os.path.join(R, '_dev_E3D.lean')).read()
a = dev.index('section StrongMarkovCadlagAeFinite')
b = dev.index('end StrongMarkovCadlagAeFinite') + len('end StrongMarkovCadlagAeFinite')
block = dev[a:b]
s = open(p).read()
anchor = 'end StrongMarkovCadlagFinite\n'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + '\n' + block + '\n')
open(p, 'w').write(s)
print('ok')
