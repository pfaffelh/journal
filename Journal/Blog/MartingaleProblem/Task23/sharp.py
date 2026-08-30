r"""Wo genau faellt die Dualitaet im Halbordnungsfall?

`diamond.py` zeigt: auf dem Diamanten 0 < a,b < 1 faellt sie bei m_a + m_b = 0,
also bei q(T_{<1}) = 0.  Dieses Skript prueft, ob das die ganze Wahrheit ist:
fuer jede Halbordnung mit kleinstem Element auf bis zu fuenf Punkten und alle
Massenvektoren aus einem kleinen Gitter wird verglichen

    (A)  faellt die Dualitaet bei irgendeinem t?
    (B)  gibt es ein s mit q(T_{<s}) = 0 und mindestens einem Atom unter s?

Die Vermutung ist (A) <=> (B).  Faellt sie, so wird das Gegenbeispiel gedruckt.
"""
import itertools
import sys
from fractions import Fraction

from posetsearch import duality_holds, is_chain, posets_with_bottom


def sweep(n, grid, verbose=False):
    a_not_b = []          # Dualitaet faellt, aber alle Abwaertsmassen != 0
    b_not_a = []          # ein Abwaertsmass ist 0, Dualitaet gilt trotzdem
    tested = fails = 0
    for pts, down, lt in posets_with_bottom(n):
        chain = is_chain(pts, lt)
        for vals in itertools.product(grid, repeat=n - 1):
            m = {0: Fraction(0)}
            m.update({x: Fraction(v) for x, v in zip(pts[1:], vals)})
            tested += 1
            t = duality_holds(pts, down, m, 0)
            degen = [s for s in pts
                     if down[s] and sum(m[x] for x in down[s]) == 0]
            if t is not None:
                fails += 1
                if chain:
                    print('  ALARM: Ausfall auf einer Kette! down=%s m=%s'
                          % (down, m))
                    return False
                if not degen:
                    a_not_b.append((dict(down), dict(m), t))
            elif degen:
                b_not_a.append((dict(down), dict(m), degen))
    print('n = %d, Massen aus %s: %d Faelle, %d Ausfaelle der Dualitaet'
          % (n, list(grid), tested, fails))
    print('    Ausfall trotz q(T_{<s}) != 0 ueberall: %d' % len(a_not_b))
    for w in a_not_b[:3]:
        print('        down=%s m=%s t=%s' % w)
    print('    q(T_{<s}) = 0 irgendwo, Dualitaet gilt trotzdem: %d'
          % len(b_not_a))
    for w in b_not_a[:3]:
        print('        down=%s m=%s degeneriert bei %s' % w)
    return not a_not_b


if __name__ == '__main__':
    ok = True
    ok &= sweep(4, (-2, -1, 1, 2))
    ok &= sweep(5, (-1, 1, 2))
    sys.exit(0 if ok else 1)
