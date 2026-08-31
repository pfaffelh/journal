r"""Der Halbordnungsfall, ganz: (diamondsuit) mit m >= 0 erzwingt delta == 0.

Nachpruefung des Beweises, der im PROTOKOLL unter "Der Halbordnungsfall,
2026-08-31 (sechster Lauf)" steht.  Die Gestalt der Rechnung ist die
kappa-Gestalt von `antisym.py`:

    Psi(s,t) = sum_{a<s} m_a kappa(a,t),   delta(t) = Psi(t,t),
    (diamondsuit):  Psi(s,t) + Psi(t,s) = Psi(s,s) + Psi(t,t).

Mit V_{s,a} = [a<s] m_a und K = (kappa(a,b)) ist Psi = V K, und (diamondsuit)
heisst genau

    sym(VK) = (1/2) (delta 1^T + 1 delta^T).                              (S)

Daraus zwei Zeilen: fuer JEDES symmetrische T ist tr(T V K) = <delta, T 1>
(Spur gegen den symmetrischen Anteil), und ist ausserdem T V symmetrisch, so
ist tr(TVK) = 0, weil K antisymmetrisch ist.  Also

    T symmetrisch, T V symmetrisch  ==>  <delta, T 1> = 0.                (C)

Der ganze Satz haengt damit an der Frage, ob e_t im Bild
L := { T 1 : T = T^T, T V = V^T T } liegt.  Und das tut es fuer m >= 0 immer:
V hat nichtnegative Eintraege, also ist V^k 1 (der Zeilensummenvektor von V^k)
genau dann null, wenn V^k null ist; die Ordnung von 1 im R[x]-Modul (R^T, V)
ist also der Nilpotenzindex r von V, 1 hat maximale Ordnung, und dann ist L
alles.  Die Konstruktion von T ist explizit, siehe `explicit_T`.

Geprueft wird hier:

 (1) das Kriterium selbst -- "delta(t) erzwungen" <=> "e_t in L" -- gegen den
     Rangvergleich von `antisym.py`, auch bei gemischten Vorzeichen, wo beide
     Seiten fallen duerfen;
 (2) das kombinatorische Lemma  V^k 1 = 0 <=> V^k = 0  fuer m >= 0;
 (3) die explizite Formel fuer T: symmetrisch, T 1 = e_t, T V symmetrisch;
 (4) der Satz im ganzen, ueber alle Halbordnungen auf bis zu fuenf Punkten
     (auch ohne kleinstes Element) und viele Massenvektoren.

Alles in exakter Bruchrechnung.
"""
import itertools
import random
import sys
from fractions import Fraction

from antisym import duality_fails_at, psi_row, system as kappa_system
from posetsearch import rank

Q0, Q1 = Fraction(0), Fraction(1)


# ------------------------------------------------------------------ Matrizen

def zeros(n, k=None):
    k = n if k is None else k
    return [[Q0] * k for _ in range(n)]


def matmul(A, B):
    n, p, q = len(A), len(B), len(B[0])
    C = zeros(n, q)
    for i in range(n):
        Ai = A[i]
        Ci = C[i]
        for k in range(p):
            a = Ai[k]
            if a:
                Bk = B[k]
                for j in range(q):
                    Ci[j] += a * Bk[j]
    return C


def transpose(A):
    return [list(col) for col in zip(*A)]


def is_zero(A):
    return not any(any(row) for row in A)


def is_sym(A):
    n = len(A)
    return all(A[i][j] == A[j][i] for i in range(n) for j in range(i + 1, n))


def matV(n, down, m):
    """V_{s,a} = [a < s] m_a."""
    V = zeros(n)
    for s in range(n):
        for a in down[s]:
            V[s][a] = m[a]
    return V


def nilpotency_index(V):
    n = len(V)
    P = [[Q1 if i == j else Q0 for j in range(n)] for i in range(n)]
    for r in range(n + 1):
        if is_zero(P):
            return r
        P = matmul(P, V)
    raise AssertionError('V ist nicht nilpotent')


# ------------------------------------------------------- L = { T 1 } als Raum

def sym_index(n):
    idx, k = {}, 0
    for i in range(n):
        for j in range(i, n):
            idx[(i, j)] = idx[(j, i)] = k
            k += 1
    return idx, k


def selfadjoint_space(V):
    """Basis des Raumes { T symmetrisch : T V = V^T T }, als Liste von Matrizen."""
    n = len(V)
    idx, nvar = sym_index(n)
    rows = []
    # (T V)_{ij} - (T V)_{ji} = 0 fuer i < j; T V - V^T T = T V - (T V)^T.
    for i in range(n):
        for j in range(i + 1, n):
            r = [Q0] * nvar
            for a in range(n):
                r[idx[(i, a)]] += V[a][j]
                r[idx[(j, a)]] -= V[a][i]
            if any(r):
                rows.append(r)
    basis = []
    for vec in nullspace(rows, nvar):
        T = zeros(n)
        for i in range(n):
            for j in range(n):
                T[i][j] = vec[idx[(i, j)]]
        basis.append(T)
    return basis


def nullspace(rows, ncol):
    """Basis des Kerns, exakt (reduzierte Zeilenstufenform)."""
    R = [r[:] for r in rows]
    pivots, r = [], 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(R)) if R[i][c]), None)
        if piv is None:
            continue
        R[r], R[piv] = R[piv], R[r]
        pv = R[r][c]
        R[r] = [x / pv for x in R[r]]
        for i in range(len(R)):
            if i != r and R[i][c]:
                f = R[i][c]
                R[i] = [x - f * y for x, y in zip(R[i], R[r])]
        pivots.append(c)
        r += 1
        if r == len(R):
            break
    free = [c for c in range(ncol) if c not in pivots]
    basis = []
    for c in free:
        v = [Q0] * ncol
        v[c] = Q1
        for i, p in enumerate(pivots):
            v[p] = -R[i][c]
        basis.append(v)
    return basis


def image_of_one(V):
    """L = { T 1 : T symmetrisch, T V = V^T T }, als Liste von Erzeugern."""
    n = len(V)
    return [[sum(T[i]) for i in range(n)] for T in selfadjoint_space(V)]


def in_span(vecs, w, n):
    return rank(list(vecs) + [w], n) == rank(list(vecs), n)


# ------------------------------------------------------- die explizite Formel

def explicit_T(V, t):
    """Symmetrisches T mit T 1 = e_t und T V symmetrisch.

    Setzt voraus, dass 1 maximale Ordnung hat: V^{r-1} 1 != 0 fuer den
    Nilpotenzindex r.  Fuer m >= 0 ist das automatisch (Lemma).
    """
    n = len(V)
    r = nilpotency_index(V)
    # v_k = V^k 1
    one = [Q1] * n
    pw = [[[Q1 if i == j else Q0 for j in range(n)] for i in range(n)]]  # V^0
    for _ in range(r):
        pw.append(matmul(pw[-1], V))                                     # V^k
    v = [[sum(pw[k][i]) for i in range(n)] for k in range(r + 1)]        # v_k
    assert any(v[r - 1]), 'V^{r-1} 1 = 0: 1 hat nicht maximale Ordnung'
    istar = next(i for i in range(n) if v[r - 1][i])
    scale = Q1 / v[r - 1][istar]
    # pi_k(y) = lambda(V^{r-1-k} y), lambda = scale * e_istar^T
    #   als Vektor: p_k = scale * (V^{r-1-k})^T e_istar = scale * Zeile istar
    p = [[scale * pw[r - 1 - k][istar][j] for j in range(n)] for k in range(r)]
    # Einheit u = pi(1) = sum_k pi_k(1) x^k, invertiert in R[x]/(x^r)
    u = [sum(p[k][j] for j in range(n)) for k in range(r)]
    assert u[0] != 0
    w = [Q0] * r
    w[0] = Q1 / u[0]
    for k in range(1, r):
        w[k] = -sum(u[i] * w[k - i] for i in range(1, k + 1)) / u[0]
    # pi~_k = sum_{j<=k} w_{k-j} pi_j
    pt = [[sum(w[k - j] * p[j][col] for j in range(k + 1)) for col in range(n)]
          for k in range(r)]
    # psi_k = (V^k)^T e_t, also die t-te Zeile von V^k
    psi = [[pw[k][t][j] for j in range(n)] for k in range(r)]
    T = zeros(n)
    for k in range(r):
        for i in range(n):
            for j in range(n):
                T[i][j] += pt[k][i] * psi[k][j] + psi[k][i] * pt[k][j]
    for k in range(r):
        for l in range(r):
            c = v[k + l][t] if k + l <= r else Q0
            if c:
                for i in range(n):
                    for j in range(n):
                        T[i][j] -= c * pt[k][i] * pt[l][j]
    return T


# ------------------------------------------------------------------ Prueflaeufe

def all_posets(n):
    """Alle Halbordnungen auf {0,..,n-1} -- ohne die Forderung eines Minimums."""
    pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        lt = {p for p, b in zip(pairs, bits) if b}
        if any((b, a) in lt for (a, b) in lt):
            continue
        if any((a, c) in lt and (c, b) in lt and (a, b) not in lt
               for a in range(n) for b in range(n) for c in range(n)):
            continue
        down = {x: sorted(y for y in range(n) if (y, x) in lt) for x in range(n)}
        yield list(range(n)), down, lt


def check_criterion(nmax=4, grid=(-1, 0, 1, 2)):
    """(1) 'delta(t) erzwungen' <=> 'e_t in L', Rangvergleich gegen Kriterium."""
    tested = bad = 0
    for n in range(2, nmax + 1):
        for pts, down, lt in all_posets(n):
            for vals in itertools.product(grid, repeat=n):
                m = {i: Fraction(x) for i, x in zip(pts, vals)}
                V = matV(n, down, m)
                L = image_of_one(V)
                rows, idx, ncol = kappa_system(pts, down, m)
                base = rank(rows, ncol)
                for t in pts:
                    forced = rank(rows + [psi_row(t, t, down, m, idx, ncol)],
                                  ncol) == base
                    crit = in_span(L, [Q1 if i == t else Q0 for i in range(n)], n)
                    tested += 1
                    if forced != crit:
                        bad += 1
                        if bad <= 3:
                            print('    ABWEICHUNG: down=%s m=%s t=%d '
                                  'erzwungen=%s kriterium=%s'
                                  % (down, vals, t, forced, crit))
    print('(1) Kriterium: %d Stellen geprueft, %d Abweichungen' % (tested, bad))
    return bad == 0


def check_lemma(nmax=5, grid=(0, 1, 2)):
    """(2) Fuer m >= 0 ist V^k 1 = 0 genau dann, wenn V^k = 0."""
    tested = bad = 0
    for n in range(2, nmax + 1):
        for pts, down, lt in all_posets(n):
            for vals in itertools.product(grid, repeat=n):
                m = {i: Fraction(x) for i, x in zip(pts, vals)}
                V = matV(n, down, m)
                P = [[Q1 if i == j else Q0 for j in range(n)] for i in range(n)]
                for k in range(n + 1):
                    tested += 1
                    if is_zero(P) != all(sum(row) == 0 for row in P):
                        bad += 1
                    P = matmul(P, V)
    print('(2) Lemma V^k 1 = 0 <=> V^k = 0 (m >= 0): %d Potenzen, %d Ausfaelle'
          % (tested, bad))
    return bad == 0


def check_explicit(nmax=5, grid=(0, 1, 2, 3), samples=None, seed=20260831):
    """(3) Die explizite Formel liefert wirklich ein zulaessiges T."""
    rnd = random.Random(seed)
    tested = bad = 0
    for n in range(2, nmax + 1):
        for pts, down, lt in all_posets(n):
            vecs = ([tuple(rnd.choice(grid) for _ in range(n))
                     for _ in range(samples)] if samples
                    else list(itertools.product(grid, repeat=n)))
            for vals in vecs:
                m = {i: Fraction(x) for i, x in zip(pts, vals)}
                V = matV(n, down, m)
                VT = transpose(V)
                for t in pts:
                    T = explicit_T(V, t)
                    ok = (is_sym(T)
                          and all(sum(T[i]) == (Q1 if i == t else Q0)
                                  for i in range(n))
                          and is_sym(matmul(T, V))
                          and matmul(T, V) == matmul(VT, T))
                    tested += 1
                    if not ok:
                        bad += 1
                        if bad <= 3:
                            print('    FORMEL FAELLT: down=%s m=%s t=%d'
                                  % (down, vals, t))
    print('(3) explizites T: %d Konstruktionen, %d Ausfaelle' % (tested, bad))
    return bad == 0


def check_theorem(nmax=5, grid=(0, 1, 2), samples=None, seed=20260831):
    """(4) Der Satz: m >= 0 auf beliebiger Halbordnung erzwingt delta == 0."""
    rnd = random.Random(seed)
    tested = bad = 0
    for n in range(2, nmax + 1):
        for pts, down, lt in all_posets(n):
            vecs = ([tuple(rnd.choice(grid) for _ in range(n))
                     for _ in range(samples)] if samples
                    else list(itertools.product(grid, repeat=n)))
            for vals in vecs:
                m = {i: Fraction(x) for i, x in zip(pts, vals)}
                tested += 1
                w = duality_fails_at(pts, down, m)
                if w is not None:
                    bad += 1
                    if bad <= 3:
                        print('    SATZ FAELLT: down=%s m=%s bei %s'
                              % (down, vals, w))
    print('(4) Satz (m >= 0, beliebige Halbordnung): %d Faelle, %d Ausfaelle'
          % (tested, bad))
    return bad == 0


if __name__ == '__main__':
    quick = '--quick' in sys.argv
    ok = check_criterion(3 if quick else 4)
    ok &= check_lemma(4 if quick else 5)
    ok &= check_explicit(4 if quick else 5, samples=None if quick else 12)
    ok &= check_theorem(4 if quick else 5, samples=None if quick else 20)
    print('ALLES BESTANDEN' if ok else 'AUSFAELLE')
    sys.exit(0 if ok else 1)
