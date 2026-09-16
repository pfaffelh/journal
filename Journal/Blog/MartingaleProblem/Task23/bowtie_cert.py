r"""Zertifikat: welche Relationen erzwingen phi_{r0}(W_n \ max) auf der doppelt
haengenden Doppelschleife?  Loest  sum_rel lambda_rel * row_rel = target  exakt
und druckt die Relationen mit lambda != 0 (Paar (s,t) und Koeffizient)."""
import sys
from fractions import Fraction
from antisym import kappa_index, psi_row
from ideal_exhaustion import closure, psi_row_single
from bowties import with_chains

def system_labeled(pts, down, m):
    n = len(pts)
    idx, ncol = kappa_index(n)
    rows, labels = [], []
    for s in pts:
        for t in pts:
            if s >= t:
                continue
            a = psi_row(s, t, down, m, idx, ncol); b = psi_row(t, s, down, m, idx, ncol)
            c = psi_row(s, s, down, m, idx, ncol); d = psi_row(t, t, down, m, idx, ncol)
            r = [a[i] + b[i] - c[i] - d[i] for i in range(ncol)]
            if any(r):
                rows.append(r); labels.append((s, t))
    return rows, labels, idx, ncol

def solve_combination(rows, target):
    """Finde lambda mit sum lambda_i rows[i] = target (exakt); Gauss auf dem
    transponierten System.  Gibt lambda (Liste) oder None."""
    R = len(rows); ncol = len(target)
    # Gleichungen: fuer jede Spalte c: sum_i lambda_i rows[i][c] = target[c]
    A = [[rows[i][c] for i in range(R)] + [target[c]] for c in range(ncol)]
    piv_cols = []
    r = 0
    for c in range(R):
        piv = None
        for i in range(r, ncol):
            if A[i][c]:
                piv = i; break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(ncol):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv_cols.append(c); r += 1
    # Konsistenz
    for i in range(r, ncol):
        if A[i][R]:
            return None
    lam = [Fraction(0)] * R
    for i, c in enumerate(piv_cols):
        lam[c] = A[i][R]
    return lam

n = int(sys.argv[1]) if len(sys.argv) > 1 else 2
e = [(0, i) for i in range(1, 11)] + [(1, 2), (3, 4), (5, 6), (7, 8), (2, 9), (4, 9), (6, 9), (2, 10), (4, 10), (8, 10)]
N, edges, cp = with_chains(11, e, [9, 10], n)
names = ['0','p0','p','q0','q','r0','r','s0','s','a',"a'"] + ['c%d' % i for i in range(1, n+1)] + ["c'%d" % i for i in range(1, n+1)]
m = [Fraction(0)] + [Fraction(1, 2 ** i) for i in range(1, N)]
lt, down = closure(N, edges)
pts = list(range(N))
rows, labels, idx, ncol = system_labeled(pts, down, m)
mx = {c for c in pts if not any(lt[c][s] for s in pts)}
x = 5  # r0
target = [Fraction(0)] * ncol
for c in pts:
    if c not in mx and c != x and c != 0:
        target = [u + v for u, v in zip(target, psi_row_single(c, x, m, idx, ncol))]
lam = solve_combination(rows, target)
if lam is None:
    print("nicht im Zeilenraum")
else:
    print("phi_r0(W_n\\max) = Summe ueber Relationen (s,t) mit Koeffizient:")
    for l, (s, t) in zip(lam, labels):
        if l:
            print("   (%s,%s): %s" % (names[s], names[t], l))
