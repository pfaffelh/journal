r"""Halbordnungen der Hoehe 2: der Fall, der sich von Hand schliessen laesst.

Bewiesen wird im PROTOKOLL (Abschnitt "Die Antikette unter der Spitze"):  hat
T ein kleinstes Element 0 und keine Kette 0 < a < b < t, so gilt die Dualitaet,
und zwar fuer m_a > 0 (a != 0) und m_0 >= 0.  Der Beweis rechnet in der
Idealreduktion: es genuegt

    T = {0} + M + {z},   M eine nichtleere Antikette, 0 < c < z fuer c in M,

und dort geben die Relationen an (c,z), c in M, gewichtet mit m_c summiert,
sofort R := sum_c m_c kappa(c,z) = 0, weil sum_{c,c'} m_c m_{c'} kappa(c',c) = 0
und q(M) > 0 ist; die Relationen an (0,c) geben m_0 kappa(0,c) = 0, und die
Relation an (0,z) macht daraus m_0 kappa(0,z) = 0.  Das ist zugleich (C4+):
Psi(c,z) = m_0 kappa(0,z) = 0.

Dieses Skript prueft die Behauptung exakt nach -- ueber ALLE Halbordnungen der
Hoehe <= 2 mit kleinstem Element auf bis zu sechs Punkten, wo die vollstaendige
Aufzaehlung von `posetsearch.py` nicht mehr hinreicht.  Geprueft wird beides:
dass delta(t) auf dem Loesungsraum verschwindet und dass Psi(a,x) fuer a < x
verschwindet.
"""
import itertools
import sys
from fractions import Fraction

from antisym import psi_row, system
from posetsearch import rank
from c5 import kappa_row, forced_zeros

from antisym import kappa_index, vanishes


def flat_posets(n):
    """Alle Halbordnungen auf {0,..,n-1} mit 0 als kleinstem Element und ohne
    Kette 0 < a < b < t.  Die Punkte 1..n-1 zerfallen in Atome und Spitzen;
    jede Spitze traegt eine nichtleere Menge von Atomen unter sich."""
    rest = list(range(1, n))
    for k in range(len(rest) + 1):                  # k = Zahl der Spitzen
        for tops in itertools.combinations(rest, k):
            atoms = [x for x in rest if x not in tops]
            if k and not atoms:
                continue
            subsets = [s for r in range(1, len(atoms) + 1)
                       for s in itertools.combinations(atoms, r)]
            for choice in itertools.product(subsets, repeat=k):
                down = {0: []}
                for a in atoms:
                    down[a] = [0]
                for b, s in zip(tops, choice):
                    down[b] = sorted((0,) + s)
                yield list(range(n)), down


def check(pts, down, m):
    """(delta-Ausfall, C4-Ausfall) oder (None, None)."""
    rows, idx, ncol = system(pts, down, m)
    base = rank(rows, ncol)
    dfail = c4fail = None
    for t in pts:
        if not vanishes(rows, base, ncol, psi_row(t, t, down, m, idx, ncol)):
            dfail = t
            break
    for x in pts:
        for a in down[x]:
            if not vanishes(rows, base, ncol,
                            psi_row(a, x, down, m, idx, ncol)):
                c4fail = (a, x)
                break
        if c4fail:
            break
    return dfail, c4fail


def sweep(n, grid):
    tested = dfails = c4fails = 0
    bad = []
    for pts, down in flat_posets(n):
        for vals in itertools.product(grid, repeat=n - 1):
            for m0 in (Fraction(0), Fraction(1), Fraction(3)):
                m = {0: m0}
                m.update({x: Fraction(v) for x, v in zip(pts[1:], vals)})
                tested += 1
                d, c = check(pts, down, m)
                if d is not None:
                    dfails += 1
                    if len(bad) < 3:
                        bad.append(('delta', dict(down), dict(m), d))
                if c is not None:
                    c4fails += 1
                    if len(bad) < 3:
                        bad.append(('C4+', dict(down), dict(m), c))
    print('Hoehe <= 2, n = %d, Massen aus %s, m_0 in {0,1,3}: %d Faelle, '
          'Dualitaet %d Ausfaelle, (C4+) %d Ausfaelle'
          % (n, list(grid), tested, dfails, c4fails))
    for what, down, m, w in bad:
        print('    AUSFALL (%s): down=%s m=%s bei %s'
              % (what, down, {k: str(v) for k, v in m.items()}, w))
    return dfails == 0 and c4fails == 0


# ------------------------------------------------------- die scharfe Fassung

def flat_at(t, down):
    """Ist T_{<t} ohne 0 eine Antikette aus Atomen?  Das ist die Hypothese des
    Satzes, punktweise an t statt global."""
    return all(down[c] == [0] for c in down[t] if c != 0)


def sharp_sweep(n, grid, samples=None, seed=20260831):
    """Der Satz behauptet mehr als Positivitaet: gebraucht wird allein
    q(M_t) = sum_{c in M_t} m_c != 0 fuer M_t = T_{<t} ohne 0.  Geprueft mit
    Massen beider Vorzeichen ueber alle Halbordnungen mit kleinstem Element."""
    import random
    from posetsearch import posets_with_bottom
    random.seed(seed)
    tested = fails = 0
    bad = []
    for pts, down, lt in posets_with_bottom(n):
        if samples is None:
            mass_iter = itertools.product(grid, repeat=n)
        else:
            mass_iter = (tuple(random.choice(grid) for _ in range(n))
                         for _ in range(samples))
        for vals in mass_iter:
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            targets = [t for t in pts if flat_at(t, down)
                       and sum(m[c] for c in down[t] if c != 0) != 0]
            if not targets:
                continue
            rows, idx, ncol = system(pts, down, m)
            base = rank(rows, ncol)
            for t in targets:
                tested += 1
                bads = []
                if not vanishes(rows, base, ncol,
                                psi_row(t, t, down, m, idx, ncol)):
                    bads.append('delta(%s)' % t)
                for a in down[t]:
                    if not vanishes(rows, base, ncol,
                                    psi_row(a, t, down, m, idx, ncol)):
                        bads.append('Psi(%s,%s)' % (a, t))
                if bads:
                    fails += 1
                    if len(bad) < 3:
                        bad.append((dict(down), dict(m), bads))
    print('scharfe Fassung, n = %d, Massen aus %s%s: %d Stellen t geprueft, '
          '%d Ausfaelle' % (n, list(grid),
                            '' if samples is None else ' (%d Stichproben je '
                            'Halbordnung)' % samples, tested, fails))
    for down, m, w in bad:
        print('    AUSFALL: down=%s m=%s bei %s'
              % (down, {k: str(v) for k, v in m.items()}, w))
    return fails == 0


if __name__ == '__main__':
    ok = True
    plan = ((4, (1, 2, 3)), (5, (1, 2, 3)), (6, (1, 2)))
    sharp = ((4, (-2, -1, 0, 1, 2), None), (5, (-2, -1, 0, 1, 2), 20))
    if '--quick' in sys.argv:
        plan = ((4, (1, 2)), (5, (1, 2)))
        sharp = ((4, (-1, 0, 1), None),)
    for n, grid in plan:
        ok &= sweep(n, grid)
    for n, grid, samples in sharp:
        ok &= sharp_sweep(n, grid, samples)
    sys.exit(0 if ok else 1)
