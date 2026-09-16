r"""Die lambda-Fassung von Theorem 38 (zweiunddreissigster Lauf, Nachtrag),
exakt an Trunkierungen ohne Spitze geprueft.

Satz 38'':  delta == 0 auf W, und  1_W = h + sum_j lambda_j 1_{X_j}  auf W\{0}
mit h im Abschluss L-bar des Spanns der Idealindikatoren, X_j disjunkte Mengen
minimaler Atome, m_0 = 0, sum_j lambda_j m(X_j) != 0.  Dann delta(t*) = 0.
Mechanik: fuer x in X_i ist delta(t*) = phi_x(W) = sum_j lambda_j phi_x(X_j);
gewichtet mit lambda_i m_x und summiert ueber alle x heben sich die Kreuzterme
B_{ij} = sum m_x m_x' kappa(x',x) durch Antisymmetrie auf.

Endliche Probe (Trunkierung W_n ohne Spitze, Kettenlaenge n):  fuer
h_n := 1_{W_n \ max} - sum_j lambda_j 1_{X_j}  (das ist h auf W_n, wenn die
Kettenpunkte bis n-1 kettenueberdeckt sind) muss
   sum_j lambda_j sum_{x in X_j} m_x  phi_x(h_n)  = 0
erzwungen sein, waehrend phi_x(W_n \ max) fuer einzelne x frei bleibt.

Faelle:
  (1) haengende Doppelschleife: X = {p,q}, lambda = -1.
  (2) A+B (Defizite 2 und 3): X_1 = {p,q}, lambda_1 = -1; X_2 = {p',q'}, lambda_2 = -2.
  (3) doppelt haengende Doppelschleife (p0<p, q0<q, r0<r, s0<s; a>p,q,r; a'>p,q,s):
      dort ist kein 1_W - sum lambda_j 1_{X_j} im Spann (alle minimalen Atome
      sind kettenueberdeckt, die Obstruktion sitzt in p,q,r,s); geprueft wird,
      dass weder g(W_n\max) noch eine der phi_x-Summen erzwungen ist.
"""
import itertools
import sys
from fractions import Fraction

from posetsearch import rank
from antisym import system as diamond_system
from ideal_exhaustion import closure, is_forced, maximal, g_row, psi_row_single


def with_chains(N0, edges0, hooks, n):
    """Haengt an jeden Haken eine Kette der Laenge n."""
    N = N0
    edges = list(edges0)
    chain_pts = []
    for hk in hooks:
        prev = hk
        for i in range(n):
            edges.append((prev, N))
            edges.append((0, N))
            chain_pts.append(N)
            prev = N
            N += 1
    return N, edges, chain_pts


def setup(N, edges, m):
    lt, down = closure(N, edges)
    pts = list(range(N))
    rows, idx, ncol = diamond_system(pts, down, m)
    base = rank(rows, ncol)
    mx = maximal(N, lt)
    nonmax = [c for c in pts if c not in mx]
    return lt, down, pts, rows, idx, ncol, base, mx, nonmax


def phi_of(x, S, m, idx, ncol):
    r = [Fraction(0)] * ncol
    for c in S:
        r = [u + v for u, v in zip(r, psi_row_single(c, x, m, idx, ncol))]
    return r


def check_lambda(label, N, edges, m, Xs, lambdas, n):
    lt, down, pts, rows, idx, ncol, base, mx, nonmax = setup(N, edges, m)
    # h_n = 1_{W_n\max} - sum lambda_j 1_{X_j}  als Koeffizientenvektor
    coef = {c: Fraction(1) for c in nonmax if c != 0}
    for X, lam in zip(Xs, lambdas):
        for x in X:
            coef[x] = coef.get(x, Fraction(0)) - lam
    # Spann-Test: liegt h_n im Spann der Idealindikatoren (ohne die maximalen)?
    ideal_vecs = []
    for a in pts:
        v = [Fraction(0)] * N
        for c in down[a]:
            if c != 0:
                v[c] = Fraction(1)
        ideal_vecs.append(v)
    hv = [Fraction(0)] * N
    for c, cf in coef.items():
        hv[c] = cf
    inspan = rank(ideal_vecs + [hv], N) == rank(ideal_vecs, N)
    # gewichtete Summe sum_j lambda_j sum_{x in X_j} m_x phi_x(h_n) erzwungen?
    tot = [Fraction(0)] * ncol
    for X, lam in zip(Xs, lambdas):
        for x in X:
            for c, cf in coef.items():
                if c == x or cf == 0:
                    continue
                row = psi_row_single(c, x, m, idx, ncol)
                tot = [u + lam * m[x] * cf * v for u, v in zip(tot, row)]
    forced_tot = is_forced(rows, base, ncol, tot)
    # einzelne phi_x(W_n\max) frei?
    singles = {x: is_forced(rows, base, ncol, phi_of(x, [c for c in nonmax if c != x], m, idx, ncol))
               for X in Xs for x in X}
    gW = is_forced(rows, base, ncol, sum_rows([g_row(c, m, idx, ncol) for c in nonmax], ncol))
    print("%-38s n=%d  h_n im Spann: %s | gewichtete phi-Summe erzwungen: %s | einzelne phi_x(W_n\\max) erzwungen: %s | g(W_n\\max) erzwungen: %s"
          % (label, n, inspan, forced_tot, singles, gW))
    return inspan, forced_tot


def sum_rows(rs, ncol):
    t = [Fraction(0)] * ncol
    for r in rs:
        t = [u + v for u, v in zip(t, r)]
    return t


def main():
    rc = 0
    mass = lambda N: [Fraction(0)] + [Fraction(1, 2 ** i) for i in range(1, N)]
    # (1) haengende Doppelschleife: 0; p=1,q=2,r0=3,r=4,s0=5,s=6,a=7,a'=8
    e = [(0, i) for i in range(1, 9)] + [(3, 4), (5, 6), (1, 7), (2, 7), (4, 7), (1, 8), (2, 8), (6, 8)]
    for n in (2, 3, 4):
        N, edges, cp = with_chains(9, e, [7, 8], n)
        ins, ft = check_lambda("(1) haengende Doppelschleife", N, edges, mass(N), [[1, 2]], [Fraction(-1)], n)
        rc |= not (ins and ft)
    # (2) A+B
    e = [(0, i) for i in range(1, 20)]
    e += [(3, 4), (5, 6), (1, 7), (2, 7), (4, 7), (1, 8), (2, 8), (6, 8)]
    e += [(11, 12), (13, 14), (15, 16), (9, 17), (10, 17), (12, 17), (9, 18), (10, 18), (14, 18), (9, 19), (10, 19), (16, 19)]
    for n in (1, 2):
        N, edges, cp = with_chains(20, e, [7, 8, 17, 18, 19], n)
        ins, ft = check_lambda("(2) A+B, lambda=(-1,-2)", N, edges, mass(N), [[1, 2], [9, 10]], [Fraction(-1), Fraction(-2)], n)
        rc |= not (ins and ft)
        # Kontrolle: mit gleichen lambdas (-1,-1) liegt h_n NICHT im Spann
        ins2, ft2 = check_lambda("(2) A+B, Kontrolle lambda=(-1,-1)", N, edges, mass(N), [[1, 2], [9, 10]], [Fraction(-1), Fraction(-1)], n)
        rc |= ins2
    # (3) doppelt haengende Doppelschleife: 0; p0=1,p=2,q0=3,q=4,r0=5,r=6,s0=7,s=8,a=9,a'=10
    e = [(0, i) for i in range(1, 11)] + [(1, 2), (3, 4), (5, 6), (7, 8), (2, 9), (4, 9), (6, 9), (2, 10), (4, 10), (8, 10)]
    for n in (2, 3):
        N, edges, cp = with_chains(11, e, [9, 10], n)
        lt, down, pts, rows, idx, ncol, base, mx, nonmax = setup(N, edges, mass(N))
        m = mass(N)
        minimal = [c for c in pts if down[c] == [0]]
        gW = is_forced(rows, base, ncol, sum_rows([g_row(c, m, idx, ncol) for c in nonmax], ncol))
        phis = {c: is_forced(rows, base, ncol, phi_of(c, [d for d in nonmax if d != c], m, idx, ncol)) for c in minimal}
        # alle Kombinationen sum_x mu_x m_x phi_x(W_n\max) mit mu in {0,1,-1}^4 -- irgendeine erzwungen?
        anyforced = []
        for mus in itertools.product((0, 1, -1), repeat=len(minimal)):
            if not any(mus):
                continue
            tot = [Fraction(0)] * ncol
            for mu, x in zip(mus, minimal):
                if mu:
                    row = phi_of(x, [d for d in nonmax if d != x], m, idx, ncol)
                    tot = [u + mu * m[x] * v for u, v in zip(tot, row)]
            if is_forced(rows, base, ncol, tot):
                anyforced.append(mus)
        # Idealspann-Konstanten an p,q,r,s: liegt irgendein 1_{W_n\max} - sum lambda 1_X im Spann?  (Argument: f(p)=f(q)=f(r)+f(s))
        print("(3) doppelt haengende Doppelschleife n=%d  Kerndim %d | g(W_n\\max) erzwungen: %s | phi_x(W_n\\max\\x) erzwungen: %s | erzwungene Vorzeichenkombinationen der phi_x: %s"
              % (n, ncol - base, gW, phis, anyforced if anyforced else 'keine'))
    print("rc =", rc)
    return rc


if __name__ == '__main__':
    sys.exit(main())
