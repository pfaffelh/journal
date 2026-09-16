r"""Vermutung C(K) (Lauf 32, Nachtrag): der endliche Kern der Klasse
"endlicher Kern K plus omega-Kette ueber jedem maximalen Element von K".

K endliche Halbordnung mit kleinstem Element 0, m >= 0, m_0 = 0, kappa
antisymmetrisch auf K x K mit (diamondsuit) an allen Paaren von K.  X_0 = minimale
Atome (T_{<x} = {0}), Max = maximale Elemente.  Zusaetzliche Relationen, die
im unendlichen System aus den Ketten kommen (Relation (c_1, x), T_{<c_1} = T_{<=k}):

   (H)   sum_{v <= k} m_v kappa(v,x) = 0    fuer alle x in X_0, k in Max.

Behauptung C(K):  aus (diamondsuit) und (H) und  phi_x(K) = phi_{x'}(K) fuer alle
x, x' in X_0  (phi_x(K) = sum_{v in K} m_v kappa(v,x); das sind die Relationen
(x,t*) des unendlichen Systems, deren gemeinsamer Wert delta(t*) ist) folgt
phi_x(K) = 0.

Gilt C(K) fuer alle endlichen K, so gilt die Dualitaet auf jeder Halbordnung
der Klasse (alle Relationen von C(K) sind Relationen des unendlichen Systems;
phi_x(W) = phi_x(K), weil phi_x auf Kettenpunkten verschwindet).

Erschoepfend geprueft: alle Halbordnungen mit kleinstem Element auf n <= 5
Punkten, zwei Massenvektoren; Stichprobe auf 6 und 7 Punkten; erschoepfend auf
6 Punkten (4231 Halbordnungen, ein Massenvektor) in `core_conjecture_n6.txt`.
"""
import itertools
import random
import sys
from fractions import Fraction

from posetsearch import posets_with_bottom, rank
from antisym import kappa_index, psi_row, system as diamond_system


def conjecture_holds(pts, down, m):
    n = len(pts)
    rows, idx, ncol = diamond_system(pts, down, m)
    X0 = [x for x in pts if down[x] == [0]]
    Max = [k for k in pts if not any(k in down[s] for s in pts)]
    def phi_row(S, x):
        r = [Fraction(0)] * ncol
        for v in S:
            if v == x or not m[v]:
                continue
            if v < x:
                r[idx[(v, x)]] += m[v]
            else:
                r[idx[(x, v)]] -= m[v]
        return r
    for x in X0:
        for k in Max:
            r = phi_row(list(down[k]) + [k], x)
            if any(r):
                rows.append(r)
    if not X0:
        return True, 0
    x1 = X0[0]
    base_target = phi_row(pts, x1)
    for x in X0[1:]:
        r = [a - b for a, b in zip(phi_row(pts, x), base_target)]
        if any(r):
            rows.append(r)
    base = rank(rows, ncol)
    forced = (not any(base_target)) or rank(rows + [base_target], ncol) == base
    return forced, ncol - base


def main():
    rng = random.Random(23)
    rc = 0
    for n in (2, 3, 4, 5):
        total = fails = 0
        for pts, down, lt in posets_with_bottom(n):
            for trial in range(2):
                m = [Fraction(0)] + [Fraction(rng.randint(1, 9), rng.randint(1, 5)) for _ in range(1, n)]
                ok, kd = conjecture_holds(pts, down, m)
                total += 1
                if not ok:
                    fails += 1
                    if fails <= 5:
                        print("  AUSFALL n=%d down=%s m=%s" % (n, down, m))
        print("n=%d: %d Konfigurationen, %d Ausfaelle" % (n, total, fails))
        rc |= bool(fails)
    # Stichprobe n=6,7: zufaellige Halbordnungen
    for n in (6, 7):
        total = fails = 0
        for trial in range(150 if n == 6 else 60):
            edges = set()
            for i in range(1, n):
                for j in range(i + 1, n):
                    if rng.random() < rng.choice((0.2, 0.35, 0.5)):
                        edges.add((i, j))
            # transitiver Abschluss
            lt = set(edges)
            changed = True
            while changed:
                changed = False
                for (a, b) in list(lt):
                    for (c, d) in list(lt):
                        if b == c and (a, d) not in lt:
                            lt.add((a, d)); changed = True
            lt |= {(0, x) for x in range(1, n)}
            down = {x: sorted(y for y in range(n) if (y, x) in lt) for x in range(n)}
            m = [Fraction(0)] + [Fraction(rng.randint(1, 9), rng.randint(1, 5)) for _ in range(1, n)]
            ok, kd = conjecture_holds(list(range(n)), down, m)
            total += 1
            if not ok:
                fails += 1
                if fails <= 5:
                    print("  AUSFALL n=%d down=%s m=%s" % (n, down, m))
        print("n=%d (Stichprobe): %d Konfigurationen, %d Ausfaelle" % (n, total, fails))
        rc |= bool(fails)
    # die drei Schleifen des Laufs, explizit
    from ideal_exhaustion import closure
    named = {
        'Doppelschleife': (7, [(0, i) for i in range(1, 7)] + [(1, 5), (2, 5), (3, 5), (1, 6), (2, 6), (4, 6)]),
        'haengende Doppelschleife': (9, [(0, i) for i in range(1, 9)] + [(3, 4), (5, 6), (1, 7), (2, 7), (4, 7), (1, 8), (2, 8), (6, 8)]),
        'doppelt haengende Doppelschleife': (11, [(0, i) for i in range(1, 11)] + [(1, 2), (3, 4), (5, 6), (7, 8), (2, 9), (4, 9), (6, 9), (2, 10), (4, 10), (8, 10)]),
        'A+B': (20, [(0, i) for i in range(1, 20)] + [(3, 4), (5, 6), (1, 7), (2, 7), (4, 7), (1, 8), (2, 8), (6, 8)]
                + [(11, 12), (13, 14), (15, 16), (9, 17), (10, 17), (12, 17), (9, 18), (10, 18), (14, 18), (9, 19), (10, 19), (16, 19)]),
    }
    for label, (N, edges) in named.items():
        lt, down = closure(N, edges)
        for m in ([Fraction(0)] + [Fraction(1, 2 ** i) for i in range(1, N)],
                  [Fraction(0)] + [Fraction(1)] * (N - 1)):
            ok, kd = conjecture_holds(list(range(N)), {x: down[x] for x in range(N)}, m)
            print("  %-34s C(K): %s (Kerndim %d)" % (label, ok, kd))
            rc |= (not ok)
    print("rc =", rc)
    return rc


if __name__ == '__main__':
    sys.exit(main())
