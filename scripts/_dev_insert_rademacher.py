"""Einmaliges Hilfsskript des siebten Laufs vom 2026-09-25.

Fügt die beiden Deklarationen aus `scripts/_dev_ceil_insert.lean` in
`MartingaleProblems/Suggested.lean` ein; bricht ab, wenn sie schon dastehen.
"""
p = 'Journal/Blog/MartingaleProblem/TauCeti/MartingaleProblems/Suggested.lean'
s = open(p).read()
d = open('scripts/_dev_ceil_insert.lean').read()
if 'measure_exists_le_sum_eq_of_rademacher_ceil' in s:
    print("steht schon da")
    raise SystemExit(0)
k = d.index("/-- **The law of the running maximum")
first, second = d[:k].rstrip() + "\n", d[k:].rstrip() + "\n"
m1 = "/-- **The running maximum of a step path is attained at a jump.**"
assert s.count(m1) == 1
s = s.replace(m1, first + "\n" + m1)
m2 = "\nend RademacherData\n"
assert s.count(m2) == 1
s = s.replace(m2, "\n" + second + m2)
open(p, 'w').write(s)
print("eingefügt")
