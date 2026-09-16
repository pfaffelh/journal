r"""Werden die kappa-Werte an haengenden Kettenpunkten durch die Relationen
innerhalb der Trunkierung W_n (ohne Spitze) erzwungen?  Exakt, Fraction.
Fuer jeden Kettenpunkt c_i (i <= n-1, also mit Nachfolger in W_n) und jedes
v in W_n wird geprueft, ob kappa(v, c_i) auf dem Loesungsraum verschwindet."""
import sys
from fractions import Fraction
from posetsearch import rank
from antisym import system as diamond_system
from ideal_exhaustion import closure, is_forced, maximal, double_bowtie

def hanging_double_bowtie(n, mass):
    # 0; p=1,q=2,r0=3,r=4,s0=5,s=6,a=7,a'=8; chains c_i=8+i, c'_i=8+n+i
    N = 9 + 2 * n
    edges = [(0, i) for i in range(1, N)]
    edges += [(3, 4), (5, 6), (1, 7), (2, 7), (4, 7), (1, 8), (2, 8), (6, 8)]
    edges += [(7, 9)] + [(8 + i, 9 + i) for i in range(1, n)]
    edges += [(8, 9 + n)] + [(8 + n + i, 9 + n + i) for i in range(1, n)]
    m = [Fraction(0)] + [mass(i) for i in range(1, N)]
    names = ['0','p','q','r0','r','s0','s','a',"a'"] + ['c%d'%i for i in range(1,n+1)] + ["c'%d"%i for i in range(1,n+1)]
    chain_pts = list(range(9, 9 + 2 * n))
    return N, edges, m, names, chain_pts

def report(label, N, edges, m, names, chain_pts):
    lt, down = closure(N, edges)
    pts = list(range(N))
    rows, idx, ncol = diamond_system(pts, down, m)
    base = rank(rows, ncol)
    mx = maximal(N, lt)
    free = []
    for c in chain_pts:
        if c in mx:
            continue
        for v in pts:
            if v == c or v == 0:
                continue
            r = [Fraction(0)] * ncol
            if v < c:
                r[idx[(v, c)]] = Fraction(1)
            else:
                r[idx[(c, v)]] = Fraction(1)
            if not is_forced(rows, base, ncol, r):
                free.append((names[v], names[c]))
    print("%-30s Kerndim %d; nicht erzwungene kappa(v,c) an nicht-maximalen Kettenpunkten: %s"
          % (label, ncol - base, free if free else 'keine'))

for n in (2, 3, 4):
    N, edges, m, names, cp = hanging_double_bowtie(n, lambda i: Fraction(1, 2 ** i))
    report("haengende Doppelschleife n=%d" % n, N, edges, m, names, cp)
for n in (2, 3, 4):
    N, edges, m, names = double_bowtie(n, lambda i: Fraction(1, 2 ** i))
    cp = list(range(7, 7 + 2 * n))
    report("Doppelschleife n=%d" % n, N, edges, m, names, cp)
