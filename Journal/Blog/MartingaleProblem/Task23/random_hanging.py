r"""Zufallssuche (Lauf 32, Nachtrag): zufaellige endliche Kerne K mit kleinstem
Element 0, ueber JEDEM maximalen Element von K haengt eine omega-Kette (dann
hat W keine maximalen Elemente, alle Ideale endlich).  Auf der Trunkierung
W_n ohne Spitze wird exakt geprueft:
  (a) gibt es ein minimales Atom x, fuer das phi_x(W_n \ max \ {x}) erzwungen ist?
      (dann folgt delta(t*) = 0 rigoros, falls das fuer alle n gilt);
  (b) ist g(W_n \ max) erzwungen (Theorem 38, X = leer)?
Gezaehlt werden die Kerne, bei denen (a) fuer KEIN x gilt -- das waeren die
Kandidaten fuer ein Gegenbeispiel bzw. fuer einen weiteren Mechanismus.
Aufruf: python3 random_hanging.py [Anzahl] [n] [seed]
"""
import random
import sys
from fractions import Fraction

from posetsearch import rank
from antisym import system as diamond_system
from ideal_exhaustion import closure, is_forced, maximal, g_row, psi_row_single
from bowties import with_chains, phi_of, sum_rows

def random_core(rng, k, p=None):
    """Kern auf k Punkten (0 Minimum), zufaellige Aufwaertskanten, transitiv."""
    if p is None:
        p = rng.choice((0.15, 0.25, 0.35, 0.5))
    edges = [(0, i) for i in range(1, k)]
    for i in range(1, k):
        for j in range(i + 1, k):
            if rng.random() < p:
                edges.append((i, j))
    return k, edges

def layered_core(rng):
    """Stufenweise gebauter Kern: Stufe 0 minimale Atome, jede hoehere Stufe
    ueberdeckt zufaellige Teilmengen tieferer Punkte (zwillingsfreundlich)."""
    n0 = rng.randint(2, 5)
    pts = list(range(1, n0 + 1))
    edges = []
    levels = [pts[:]]
    k = n0 + 1
    for lev in range(rng.randint(1, 3)):
        new = []
        for _ in range(rng.randint(1, 3)):
            below = rng.sample(pts, rng.randint(1, min(3, len(pts))))
            for b in below:
                edges.append((b, k))
            new.append(k)
            k += 1
        pts += new
    N0 = k
    edges = [(0, i) for i in range(1, N0)] + edges
    return N0, edges


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 32
    rng = random.Random(seed)
    stats = {'kerne': 0, 'a_ok': 0, 'b_ok': 0, 'keins': 0}
    hard = []
    for trial in range(count):
        if trial % 2:
            k = rng.randint(4, 9)
            N0, e0 = random_core(rng, k)
        else:
            N0, e0 = layered_core(rng)
            k = N0
        lt0, down0 = closure(N0, e0)
        hooks = sorted(maximal(N0, lt0))
        N, edges, cp = with_chains(N0, e0, hooks, n)
        m = [Fraction(0)] + [Fraction(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(1, N)]
        lt, down = closure(N, edges)
        pts = list(range(N))
        rows, idx, ncol = diamond_system(pts, down, m)
        base = rank(rows, ncol)
        mx = maximal(N, lt)
        nonmax = [c for c in pts if c not in mx]
        minimal = [c for c in pts if down[c] == [0]]
        a_ok = [x for x in minimal if is_forced(rows, base, ncol, phi_of(x, [d for d in nonmax if d != x], m, idx, ncol))]
        b_ok = is_forced(rows, base, ncol, sum_rows([g_row(c, m, idx, ncol) for c in nonmax], ncol))
        stats['kerne'] += 1
        stats['a_ok'] += bool(a_ok)
        stats['b_ok'] += b_ok
        if not a_ok and not b_ok:
            stats['keins'] += 1
            hard.append((k, sorted(set(e0)), hooks, minimal))
    print("Kerne: %d | (a) ein x erzwungen: %d | (b) g(W_n\\max) erzwungen: %d | weder (a) noch (b): %d   (n=%d, seed=%d)"
          % (stats['kerne'], stats['a_ok'], stats['b_ok'], stats['keins'], n, seed))
    for h in hard[:10]:
        print("  Kandidat: k=%d edges=%s hooks=%s minimal=%s" % h)
    return 0

if __name__ == '__main__':
    sys.exit(main())
