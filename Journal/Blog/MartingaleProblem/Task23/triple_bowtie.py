r"""Naechste Rechnung des zweiunddreissigsten Laufs: die Dreifachschleife.

0 < p,q,r,s (minimal); p,q,r < a; p,q,s < a'; r,s < a''; omega-Ketten ueber
a, a', a''.  Endliche Ideale, keine maximalen Elemente.  Frage: erzwingen die
Relationen innerhalb der Trunkierung W_n (ohne Spitze) fuer irgendein
minimales Atom x die Summe phi_x(W_n \ max \ {x}), phi_x(c) = m_c kappa(c,x)?
Und: liegt 1_{W \ X} im Spann der Idealindikatoren fuer irgendeine Menge X
minimaler Atome?  Beides exakt in Fraction.
"""
import itertools
import sys
from fractions import Fraction

from posetsearch import rank
from antisym import system as diamond_system
from ideal_exhaustion import closure, is_forced, maximal, psi_row_single, g_row


def triple_bowtie(n, mass):
    # 0; p=1,q=2,r=3,s=4; a=5,a'=6,a''=7; chains: c_i=7+i, c'_i=7+n+i, c''_i=7+2n+i
    N = 8 + 3 * n
    edges = [(0, i) for i in range(1, N)]
    edges += [(1, 5), (2, 5), (3, 5), (1, 6), (2, 6), (4, 6), (3, 7), (4, 7)]
    for base, top in ((5, 7), (6, 7 + n), (7, 7 + 2 * n)):
        edges.append((base, top + 1))
        for i in range(1, n):
            edges.append((top + i, top + i + 1))
    m = [Fraction(0)] + [mass(i) for i in range(1, N)]
    names = ['0', 'p', 'q', 'r', 's', 'a', "a'", "a''"] + ['c%d' % i for i in range(1, n + 1)] \
        + ["c'%d" % i for i in range(1, n + 1)] + ["c''%d" % i for i in range(1, n + 1)]
    return N, edges, m, names


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for n in range(1, nmax + 1):
        N, edges, m, names = triple_bowtie(n, lambda i: Fraction(1, 2 ** i))
        lt, down = closure(N, edges)
        pts = list(range(N))
        rows, idx, ncol = diamond_system(pts, down, m)
        base = rank(rows, ncol)
        mx = maximal(N, lt)
        nonmax = [c for c in pts if c not in mx]
        print("n=%d  |W_n|=%d  maximal: %s" % (n, N, [names[c] for c in sorted(mx)]))
        # (1) g(c) forced?
        forced = [names[c] for c in pts if c != 0 and is_forced(rows, base, ncol, g_row(c, m, idx, ncol))]
        print("  g(c) erzwungen fuer:", forced)
        # (2) Spann der Idealindikatoren: welche 1_{W\X} (X subset minimaler Atome) liegen drin?
        ideal_vecs = []
        for a in pts:
            v = [Fraction(0)] * N
            for c in down[a]:
                v[c] = Fraction(1)
            ideal_vecs.append(v)
        sr = rank(ideal_vecs, N)
        minimal_atoms = [c for c in pts if down[c] == [0]]
        for k in range(0, len(minimal_atoms) + 1):
            for X in itertools.combinations(minimal_atoms, k):
                v = [Fraction(0)] * N
                for c in nonmax:
                    if c != 0 and c not in X:
                        v[c] = Fraction(1)
                inspan = rank(ideal_vecs + [v], N) == sr
                if inspan:
                    print("  1_{W_n\\max\\X} im Spann fuer X =", [names[c] for c in X])
        # (3) phi_x(W_n \ max \ {x}) erzwungen fuer ein minimales x?
        for x in minimal_atoms:
            r = [Fraction(0)] * ncol
            for c in nonmax:
                if c != x:
                    r = [u + v for u, v in zip(r, psi_row_single(c, x, m, idx, ncol))]
            print("  phi_%s(W_n\\max\\{%s}) erzwungen: %s" % (names[x], names[x], is_forced(rows, base, ncol, r)))
        # (4) g(W_n \ max) erzwungen?
        r = [Fraction(0)] * ncol
        for c in nonmax:
            r = [u + v for u, v in zip(r, g_row(c, m, idx, ncol))]
        print("  g(W_n\\max) erzwungen:", is_forced(rows, base, ncol, r))
        # (5) Kerndimension und: welche Linearkombinationen von g(p),g(q),g(r),g(s) sind erzwungen?
        gp = [g_row(c, m, idx, ncol) for c in (1, 2, 3, 4)]
        # Rang der erzwungenen Funktionale unter span{g(p),g(q),g(r),g(s)}
        free = []
        for coeffs in itertools.product((0, 1, -1), repeat=4):
            if not any(coeffs):
                continue
            r = [Fraction(0)] * ncol
            for cf, row in zip(coeffs, gp):
                r = [u + cf * v for u, v in zip(r, row)]
            if is_forced(rows, base, ncol, r):
                free.append(coeffs)
        print("  erzwungene Kombinationen (p,q,r,s) mit Koeffizienten in {0,1,-1}:", free)


if __name__ == '__main__':
    main()
