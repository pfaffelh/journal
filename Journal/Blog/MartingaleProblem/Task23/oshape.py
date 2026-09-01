"""Wie duenn ist der Ausfall der o-Konvention?

`ocounter` zeigt, dass die o-Fassung des Halbordnungssatzes falsch ist.  Dieses
Skript fragt, wie gross die Ausnahmemenge ist: fuer welche Massenvektoren auf
einer festen Halbordnung faellt sie, und ist das eine duenne (algebraische)
Bedingung oder der generische Fall?

Aufruf:  python3 oshape.py
"""

import itertools
import random
from fractions import Fraction

import posetsearch
from oconvention import down_o

WITNESS_DOWN = {0: [], 1: [0, 2, 3, 4], 2: [0], 3: [0, 4], 4: [0]}


def fails(down, m):
    pts = sorted(down)
    return posetsearch.duality_holds(pts, down_o(pts, down), m, 0)


def generic(down, trials=40, hi=97, seed=20260831):
    """Zufaellige positive Massen: faellt es generisch oder nur speziell?"""
    rng = random.Random(seed)
    pts = sorted(down)
    bad = 0
    for _ in range(trials):
        m = {x: Fraction(rng.randint(1, hi)) for x in pts}
        m[0] = Fraction(0)
        if fails(down, m) is not None:
            bad += 1
    return bad, trials


def mass_pattern(down, grid):
    """Alle Massenvektoren aus dem Gitter: welche fallen?"""
    pts = sorted(down)
    out = []
    for vals in itertools.product(grid, repeat=len(pts) - 1):
        m = {0: Fraction(0)}
        m.update({x: Fraction(v) for x, v in zip(pts[1:], vals)})
        t = fails(down, m)
        if t is not None:
            out.append(({x: int(m[x]) for x in pts[1:]}, t))
    return out


def sweep_random(n, trials, hi=200, seed=20260831):
    """Alle Halbordnungen mit kleinstem Element, Massen in allgemeiner Lage:
    paarweise verschieden und zufaellig gezogen.  Hier faellt nichts."""
    rng = random.Random(seed)
    tot = bad = 0
    for pts, down, lt in posetsearch.posets_with_bottom(n):
        do = down_o(pts, down)
        for _ in range(trials):
            m = {0: Fraction(0)}
            m.update({x: Fraction(v)
                      for x, v in zip(pts[1:], rng.sample(range(1, hi + 1),
                                                          n - 1))})
            tot += 1
            if posetsearch.duality_holds(pts, do, m, 0) is not None:
                bad += 1
                if bad < 4:
                    print('    AUSFALL: down=%s m=%s'
                          % (dict(down), {k: int(v) for k, v in m.items()}))
    print('n = %d, zufaellige paarweise verschiedene Massen aus 1..%d: '
          '%d Faelle, %d Ausfaelle' % (n, hi, tot, bad))
    return bad == 0


def minimal_failures(nmax=5, grid=(0, 1, 2, 3)):
    """Die kleinsten Ausfaelle: wenigste Punkte, dann wenigste Massen != 0."""
    for n in range(3, nmax + 1):
        found = []
        for pts, down, lt in posetsearch.posets_with_bottom(n):
            for vals in itertools.product(grid, repeat=n - 1):
                m = {0: Fraction(0)}
                m.update({x: Fraction(v) for x, v in zip(pts[1:], vals)})
                t = fails(down, m)
                if t is not None:
                    found.append((sum(1 for x in pts if m[x]), dict(down),
                                  {x: int(m[x]) for x in pts}, t))
        found.sort(key=lambda w: w[0])
        print('n = %d, Massen aus %s: %d Ausfaelle' % (n, list(grid), len(found)))
        for w in found[:4]:
            print('    %d Atome: down=%s m=%s t=%s' % w)
        if found:
            return n, found
    return None, []


if __name__ == '__main__':
    print('Der Zeuge, Halbordnung fest, Massen variabel.')
    bad, tot = generic(WITNESS_DOWN)
    print('  zufaellige positive Massen aus 1..97: %d von %d fallen' % (bad, tot))
    pat = mass_pattern(WITNESS_DOWN, (1, 2, 3, 4))
    print('  Massen aus {1,2,3,4}^4: %d Ausfaelle' % len(pat))
    for w in pat[:12]:
        print('     m=%s  t=%s' % w)
    print()
    print('Massen in allgemeiner Lage, ueber alle Halbordnungen:')
    sweep_random(4, 6)
    sweep_random(5, 3)
    print()
    minimal_failures(5, (0, 1, 2, 3))
