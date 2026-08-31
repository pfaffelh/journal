"""Die o-Konvention: die Frage ist die nach der maximalen Ordnung von 1.

Der Satz des sechsten Laufs (2026-08-31) ruht auf zwei Stuecken.  Der Spurteil
ist konventionsfrei (`oconvention.criterion_o`); die Last liegt auf

    L = { T 1 : T = T^T, T V = V^T T }  =  R^F .

Das ist eine Frage der Modultheorie und **kein** Nilpotenzphaenomen: L = R^F
genau dann, wenn 1 im R[x]-Modul (R^F, x = V) **maximale Ordnung** hat, also
Ann(1) = Ann(R^F), d.h. mu_1 = mu_V.  Unter iota = p ist mu_V = x^r und
maximale Ordnung heisst V^{r-1} 1 != 0 -- genau die Gestalt, in der das Lemma
des sechsten Laufs steht.  Unter iota = o ist V = P D mit der Zeta-Matrix P der
Halbordnung und D = diag(m), also nicht nilpotent, und zu pruefen ist dieselbe
Bedingung in ihrer allgemeinen Gestalt.

Dieses Skript prueft drei Dinge in exakter Bruchrechnung:

  1. `check_maxorder`  -- hat 1 unter iota = o maximale Ordnung?
  2. `check_equiv`     -- faellt 'maximale Ordnung' mit 'L = R^F' zusammen?
  3. `check_split`     -- die Reduktion auf den Teil positiver Massen:
     mit Z = {m = 0} (enthaelt 0) und F' = {m > 0} ist V = [[0, A], [0, B]]
     mit B = P' D' invertierbar, und die Behauptung ist
        1 hat maximale Ordnung fuer V   <=>   1_{F'} hat maximale Ordnung fuer B.

Befund (2026-08-31, achter Lauf): (1) faellt.  Auf drei und vier Punkten hat 1
stets maximale Ordnung, auf fuenf nicht mehr, und der erste Ausfall ist zugleich
ein Ausfall der Dualitaet -- siehe `ocounter.py` und `odiamond.py`.  (2) und (3)
tragen ueberall: das Kriterium beschreibt die Lage auch unter iota = o, und die
Frage haengt allein am Teil positiver Massen.

Aufruf:  python3 omaxorder.py
"""

import itertools
import random
from fractions import Fraction

import posetsearch
import selfadjoint
from oconvention import down_o


# --------------------------------------------------------------------------
# Lineare Algebra ueber Q
# --------------------------------------------------------------------------

def flat(A):
    return [x for row in A for x in row]


def matV_o(pts, do, m):
    """V_{s,a} = [a in (0,s]] m_a."""
    return [[m[a] if a in do[s] else Fraction(0) for a in pts] for s in pts]


def identity(n):
    return [[Fraction(1) if i == j else Fraction(0) for j in range(n)]
            for i in range(n)]


def matvec(A, v):
    return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]


def deg_minpoly_matrix(V):
    """Grad des Minimalpolynoms von V: kleinstes k mit V^k in span(I,..,V^{k-1})."""
    n = len(V)
    powers = [identity(n)]
    span = [flat(powers[0])]
    k = 0
    while True:
        k += 1
        nxt = selfadjoint.matmul(powers[-1], V)
        powers.append(nxt)
        if selfadjoint.in_span(span, flat(nxt), n * n):
            return k
        span.append(flat(nxt))


def deg_minpoly_vector(V, v):
    """Grad des Minimalpolynoms von v: kleinstes k mit V^k v in span(v,..,V^{k-1}v)."""
    n = len(V)
    cur = list(v)
    span = [cur]
    k = 0
    while True:
        k += 1
        cur = matvec(V, cur)
        if selfadjoint.in_span(span, cur, n):
            return k
        span.append(cur)


def has_max_order(V, v):
    return deg_minpoly_vector(V, v) == deg_minpoly_matrix(V)


def is_full(V):
    """Ist L = { T 1 : T = T^T, T V = V^T T } ganz R^n?"""
    n = len(V)
    L = selfadjoint.image_of_one(V)
    return posetsearch.rank(L, n) == n


# --------------------------------------------------------------------------
# Die drei Pruefungen
# --------------------------------------------------------------------------

def check_maxorder(n, grid):
    """Hat 1 unter iota = o maximale Ordnung?"""
    tested = fails = 0
    witness = None
    for pts, down, lt in posetsearch.posets_with_bottom(n):
        do = down_o(pts, down)
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            m[0] = Fraction(0)
            V = matV_o(pts, do, m)
            one = [Fraction(1)] * n
            tested += 1
            if not has_max_order(V, one):
                fails += 1
                if witness is None:
                    witness = (dict(down), dict(m))
    print('maximale Ordnung, n = %d, Massen aus %s: %d Faelle, %d Ausfaelle'
          % (n, list(grid), tested, fails))
    if witness:
        print('    AUSFALL: down=%s m=%s' % witness)
    return fails == 0


def check_equiv(n, grid):
    """'maximale Ordnung' gegen 'L = R^F', beide Richtungen."""
    tested = only_order = only_full = 0
    for pts, down, lt in posetsearch.posets_with_bottom(n):
        do = down_o(pts, down)
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            m[0] = Fraction(0)
            V = matV_o(pts, do, m)
            one = [Fraction(1)] * n
            tested += 1
            mo = has_max_order(V, one)
            fl = is_full(V)
            if mo and not fl:
                only_order += 1
            if fl and not mo:
                only_full += 1
    print('Aequivalenz, n = %d, Massen aus %s: %d Faelle; '
          'Ordnung ohne L: %d; L ohne Ordnung: %d (beide muessen 0 sein)'
          % (n, list(grid), tested, only_order, only_full))
    return only_order == 0 and only_full == 0


def check_split(n, grid):
    """Die Reduktion auf den Teil positiver Massen."""
    tested = fails = 0
    witness = None
    for pts, down, lt in posetsearch.posets_with_bottom(n):
        do = down_o(pts, down)
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            m[0] = Fraction(0)
            V = matV_o(pts, do, m)
            one = [Fraction(1)] * n
            pos = [s for s in pts if m[s] > 0]
            B = [[m[a] if a in do[s] else Fraction(0) for a in pos]
                 for s in pos]
            tested += 1
            left = has_max_order(V, one)
            right = (has_max_order(B, [Fraction(1)] * len(pos))
                     if pos else True)
            if left != right:
                fails += 1
                if witness is None:
                    witness = (dict(down), dict(m), left, right)
    print('Reduktion auf F\' = {m > 0}, n = %d, Massen aus %s: %d Faelle, '
          '%d Abweichungen' % (n, list(grid), tested, fails))
    if witness:
        print('    ABWEICHUNG: down=%s m=%s V:%s B:%s' % witness)
    return fails == 0


def check_random(trials=200, n=7, seed=20260831):
    """Jenseits der Aufzaehlung: zufaellige Halbordnungen mit kleinstem Element."""
    rng = random.Random(seed)
    fails = 0
    for _ in range(trials):
        perm = list(range(1, n))
        rng.shuffle(perm)
        order = [0] + perm
        rank_of = {x: i for i, x in enumerate(order)}
        lt = set()
        for x in order:
            for y in order:
                if rank_of[x] < rank_of[y] and (x == 0 or rng.random() < 0.5):
                    lt.add((x, y))
        # transitiv abschliessen
        changed = True
        while changed:
            changed = False
            for (a, b) in list(lt):
                for (c, d) in list(lt):
                    if b == c and (a, d) not in lt:
                        lt.add((a, d))
                        changed = True
        pts = list(range(n))
        down = {x: sorted(a for a in pts if (a, x) in lt) for x in pts}
        do = down_o(pts, down)
        m = {x: Fraction(rng.choice([0, 1, 1, 2, 3, 5])) for x in pts}
        m[0] = Fraction(0)
        V = matV_o(pts, do, m)
        if not has_max_order(V, [Fraction(1)] * n):
            fails += 1
            print('    AUSFALL: down=%s m=%s' % (dict(down), dict(m)))
    print('Zufallstest, %d Halbordnungen auf %d Punkten: %d Ausfaelle'
          % (trials, n, fails))
    return fails == 0


if __name__ == '__main__':
    print('(1) Hat 1 maximale Ordnung?  Auf drei und vier Punkten ja, auf fuenf')
    print('    nicht mehr -- das ist der Zeuge von `ocounter`.')
    for n, grid in ((3, (0, 1, 2)), (4, (0, 1, 2)), (5, (0, 1, 2))):
        check_maxorder(n, grid)
    check_random()
    print()
    print('(2) Das Kriterium: "maximale Ordnung" faellt mit "L = R^F" zusammen.')
    print('    Hier darf nichts abweichen.')
    ok = True
    for n, grid in ((3, (0, 1, 2)), (4, (0, 1, 2)), (5, (0, 1, 2))):
        ok &= check_equiv(n, grid)
    print()
    print('(3) Die Reduktion auf F\' = {m > 0}.  Hier darf nichts abweichen.')
    for n, grid in ((4, (0, 1, 2)), (5, (0, 1, 2))):
        ok &= check_split(n, grid)
    print()
    print('Kriterium und Reduktion:', 'kein Ausfall' if ok else 'AUSFALL')
    raise SystemExit(0 if ok else 1)
