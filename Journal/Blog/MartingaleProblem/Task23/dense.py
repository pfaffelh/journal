r"""Die ordnungsdichte Atommenge: wie teuer ist eine Ausschoepfung?

Der Rueckstau fragt, ob eine ordnungsdichte Atommenge eine Ausschoepfung durch
endliche Teilmengen zulaesst, laengs deren der Defekt stetig ist.  Der Beweis des
sechsten Laufs (PROTOKOLL, "Der Halbordnungsfall") macht daraus eine *rechenbare*
Frage, und zwar ohne jede neue Idee -- man muss ihn nur stoerungsweise lesen.

Die Paarungsidentitaet lautet dort: mit V_{s,a} = [a<s] m_a, K antisymmetrisch,
Psi = VK, delta = diag Psi und

    sym(VK) = (1/2)(delta 1^T + 1 delta^T)                                 (S)

gilt fuer jedes symmetrische T mit symmetrischem TV, dass <delta, T 1> = 0.
Haelt (S) nur bis auf einen Rest E, also sym(VK) = (1/2)(delta 1^T + 1 delta^T)
+ (1/2) E mit E symmetrisch, so wird daraus

    <delta, T 1> = -(1/2) tr(T E),

und mit T 1 = e_t

    |delta(t)| <= (1/2) ||T||_F ||E||_F.                                   (P)

Genau diese Gestalt braucht eine Ausschoepfung.  Sei A die (ordnungsdichte,
abzaehlbare) Atommenge mit q(A) = M < oo und F <= A endlich.  Schneidet man das
System auf F zurueck, so ist der Fehler in (S) der Beitrag der weggelassenen
Atome, also eintragsweise hoechstens 2 ||kappa||_oo eps_F mit
eps_F = q(A \ F), und ebenso |delta(t) - delta_F(t)| <= ||kappa||_oo eps_F.
Mit (P):

    |delta(t)| <= ||kappa||_oo eps_F (1 + 2 |F| ||T_F||_F).

Der Defekt des vollen Systems verschwindet also, sobald **irgendeine** Folge
endlicher F mit  |F| ||T_F||_F eps_F --> 0  existiert.  Die ganze Frage ist das
Wachstum von

    C(V,t) := ||T||_F  fuer  T = T^T,  T V = V^T T,  T 1 = e_t.

Das Gleichungssystem ist quadratisch: N(N+1)/2 Unbekannte gegen
N(N-1)/2 + N = N(N+1)/2 Gleichungen.  Der Kern ist durchweg eindimensional, die
Minimalnorm-Loesung also die richtige Messgroesse.  C ist skaleninvariant --
mit V loest auch cV die Bedingung T V = V^T T, und T 1 = e_t kennt V nicht --,
haengt also nur von der *Gestalt* des Massenvektors ab, nicht von seiner Groesse.

Zwei Voraussetzungen, die das Manuskript nicht liefert und die hier offen
angemeldet sind: kappa muss beschraenkt sein, und eps_F = q(A \ F) faellt nur so
schnell, wie die Massen von A summierbar sind -- beides ist beim Zurueckschneiden
zu bezahlen.

Aufrufe:

    python3 dense.py check     -- (P) und die Loesbarkeit an kleinen Faellen
    python3 dense.py uniform   -- gleiche Massen, Kette wachsender Laenge
    python3 dense.py dyadic    -- die dyadische ordnungsdichte Menge, Level <= n
    python3 dense.py exact     -- dieselben Profile in Bruechen statt Gleitkomma
    python3 dense.py small     -- der Preis EINES kleinen Atoms, nach seinem Ort
    python3 dense.py all
"""
import sys

import numpy as np
from fractions import Fraction


# ------------------------------------------------------------------ Matrizen

def chain_V(m):
    """V_{s,a} = [a < s] m_a fuer die Kette 0 < 1 < ... < n.

    m[0] ist die Masse von 0 und in unserem Modell null: {0} ist kein Atom.
    """
    N = len(m)
    V = np.zeros((N, N))
    for s in range(N):
        V[s, :s] = m[:s]
    return V


def sym_basis(N):
    """Index der symmetrischen Unbekannten (i,j), i <= j."""
    return [(i, j) for i in range(N) for j in range(i, N)]


def solve_T(V, t, rcond=None):
    """Minimalnorm-Loesung von  T = T^T,  T V = V^T T,  T 1 = e_t.

    Gibt (T, residuum, Kerndimension) zurueck.
    """
    N = V.shape[0]
    idx = sym_basis(N)
    pos = {p: k for k, p in enumerate(idx)}
    d = len(idx)

    rows, rhs = [], []

    # (a)  (T V - V^T T)_{ij} = 0 fuer i < j.  Der Ausdruck ist automatisch
    #      antisymmetrisch, der strikt obere Teil genuegt.
    for i in range(N):
        for j in range(i + 1, N):
            row = np.zeros(d)
            for k in range(N):
                # (T V)_{ij} = sum_k T_{ik} V_{kj}
                row[pos[(min(i, k), max(i, k))]] += V[k, j]
                # (V^T T)_{ij} = sum_k V_{ki} T_{kj}
                row[pos[(min(k, j), max(k, j))]] -= V[k, i]
            rows.append(row)
            rhs.append(0.0)

    # (b)  (T 1)_i = [i = t]
    for i in range(N):
        row = np.zeros(d)
        for k in range(N):
            row[pos[(min(i, k), max(i, k))]] += 1.0
        rows.append(row)
        rhs.append(1.0 if i == t else 0.0)

    A = np.array(rows)
    b = np.array(rhs)
    x, _, rank, sv = np.linalg.lstsq(A, b, rcond=rcond)

    T = np.zeros((N, N))
    for (i, j), k in pos.items():
        T[i, j] = T[j, i] = x[k]
    return T, float(np.linalg.norm(A @ x - b)), d - int(rank)


def defect_bound(V, t):
    """C(V,t) = ||T||_F, dazu Residuum und Kerndimension des Systems."""
    T, res, kern = solve_T(V, t)
    return float(np.linalg.norm(T)), res, kern


# ------------------------------------------------------- die Atommengen

# ------------------------------------------------- dasselbe exakt, in Bruechen
#
# Die Gleitkommarechnung bricht zusammen, sobald C gross wird: fuer n = 8 und
# rho = 4 meldet `lstsq` Kerndimension 2 und ein *kleineres* C als bei rho = 3.
# Das ist die rcond-Abschneidung, kein Messwert.  Exakt gerechnet gibt es keine
# solche Falle.

def _solve_exact(rows, rhs, d):
    """Gauss ueber Q; gibt (Partikulaerloesung, Kernbasis) oder None."""
    A = [list(r) + [b] for r, b in zip(rows, rhs)]
    piv = []
    r = 0
    for c in range(d):
        p = next((i for i in range(r, len(A)) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = Fraction(1) / A[r][c]
        A[r] = [x * inv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    for i in range(r, len(A)):
        if A[i][d]:
            return None                      # inkonsistent
    x0 = [Fraction(0)] * d
    for i, c in enumerate(piv):
        x0[c] = A[i][d]
    free = [c for c in range(d) if c not in piv]
    kern = []
    for f in free:
        v = [Fraction(0)] * d
        v[f] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -A[i][f]
        kern.append(v)
    return x0, kern


def defect_bound_exact(m, t):
    """C(V,t)^2 = ||T||_F^2 exakt, als Bruch; T von minimaler Frobeniusnorm.

    Die Frobeniusnorm zaehlt Ausserdiagonalen doppelt -- die Minimierung laeuft
    also gegen die gewichtete Form, nicht gegen die euklidische des
    Koeffizientenvektors.
    """
    m = [Fraction(x) for x in m]
    N = len(m)
    V = [[m[a] if a < s else Fraction(0) for a in range(N)] for s in range(N)]
    idx = sym_basis(N)
    pos = {p: k for k, p in enumerate(idx)}
    d = len(idx)
    w = [Fraction(1) if i == j else Fraction(2) for i, j in idx]   # Gewichte

    rows, rhs = [], []
    for i in range(N):
        for j in range(i + 1, N):
            row = [Fraction(0)] * d
            for k in range(N):
                row[pos[(min(i, k), max(i, k))]] += V[k][j]
                row[pos[(min(k, j), max(k, j))]] -= V[k][i]
            rows.append(row)
            rhs.append(Fraction(0))
    for i in range(N):
        row = [Fraction(0)] * d
        for k in range(N):
            row[pos[(min(i, k), max(i, k))]] += Fraction(1)
        rows.append(row)
        rhs.append(Fraction(1) if i == t else Fraction(0))

    sol = _solve_exact(rows, rhs, d)
    if sol is None:
        return None, 0
    x0, kern = sol

    def ip(u, v):
        return sum(wi * a * b for wi, a, b in zip(w, u, v))

    # Minimiere ||x0 + sum c_j k_j||_w : normale Gleichungen, exakt.
    if kern:
        G = [[ip(a, b) for b in kern] for a in kern]
        rhs2 = [-ip(a, x0) for a in kern]
        c = _solve_exact(G, rhs2, len(kern))
        if c is not None:
            for cj, kj in zip(c[0], kern):
                x0 = [a + cj * b for a, b in zip(x0, kj)]
    return ip(x0, x0), len(kern)


def run_small(ns=(4, 6, 8, 10)):
    """Was kostet EIN kleines Atom, und haengt der Preis von seinem Ort ab?

    Befund: eine Masse eps an der Stelle k einer Kette aus n Atomen (alle
    uebrigen Massen 1, t die Spitze) kostet

        C ~ eps^-(n-2k)   fuer 2k < n,      C = O(1)   fuer 2k >= n.

    Kleine Massen in der *oberen* Haelfte der Kette sind also gratis, kleine
    Massen in der unteren ruinieren die Schranke, und zwar umso mehr, je weiter
    unten sie sitzen.  Der Exponent wird hier aus zwei Dekaden abgelesen.
    """
    print('kleine Masse eps an Stelle k, sonst 1, t = Spitze;'
          ' Exponent p in C ~ eps^-p')
    print(f'{"n":>3} | ' + ' '.join(f'k={k:<2d}' for k in range(1, 11)))
    for n in ns:
        cells = []
        for k in range(1, n + 1):
            vals = []
            for e in (2, 3):
                m = [0] + [Fraction(1)] * n
                m[k] = Fraction(1, 10 ** e)
                C2, _ = defect_bound_exact(m, len(m) - 1)
                vals.append(float(C2) ** 0.5)
            p = round((vals[1] / vals[0] if vals[0] else 1) and
                      __import__('math').log10(vals[1] / vals[0]))
            cells.append(f'{max(p, 0):<4d}')
        print(f'{n:3d} | ' + ' '.join(cells)
              + f'    (n-2k: ' + ','.join(str(max(n - 2 * k, 0))
                                          for k in range(1, n + 1)) + ')')


def run_exact():
    """C^2 exakt fuer die Profile, an denen die Gleitkommarechnung scheitert."""
    print('exakt: C^2 = ||T||_F^2, geometrische Massen m_k = rho^k')
    print(f'{"n":>3} {"rho":>5} {"Kern":>5} {"C":>16} {"C/C(rho=1)":>14}')
    for n in (3, 4, 5, 6, 7):
        base = None
        for rho in (1, 2, 3, 4):
            m = [0] + [Fraction(rho) ** k for k in range(n)]
            C2, kern = defect_bound_exact(m, len(m) - 1)
            C = float(C2) ** 0.5
            base = C if rho == 1 else base
            print(f'{n:3d} {rho:5d} {kern:5d} {C:16.6e} {C / base:14.4e}')
        print()

    print('exakt: eine einzige kleine Masse, m = (1,..,1,eps,1,..,1), n = 6')
    print(f'{"Stelle":>7} {"eps":>10} {"Kern":>5} {"C":>16}')
    n = 6
    for where in (1, 2, 3, 5, 6):
        for eps in (Fraction(1), Fraction(1, 10), Fraction(1, 100),
                    Fraction(1, 1000)):
            m = [0] + [Fraction(1)] * n
            m[where] = eps
            C2, kern = defect_bound_exact(m, len(m) - 1)
            print(f'{where:7d} {float(eps):10.1e} {kern:5d}'
                  f' {float(C2) ** 0.5:16.6e}')
        print()


def dyadic_levels(nmax):
    """Atome k/2^j (k ungerade), Masse 4^-j, nach Ort sortiert; Level <= n.

    Die Menge aller dyadischen Brueche ist ordnungsdicht in [0,1]; die
    Ausschoepfung nach Level ist die natuerliche endliche Approximation, und
    eps_n = sum_{j>n} 2^{j-1} 4^{-j} = 2^{-n-1} faellt geometrisch.
    """
    out = []
    for n in range(1, nmax + 1):
        pts = []
        for j in range(1, n + 1):
            for k in range(1, 2 ** j, 2):
                pts.append((k / 2 ** j, 4.0 ** (-j)))
        pts.sort()
        m = np.array([0.0] + [w for _, w in pts])   # 0 ist kein Atom
        eps = 2.0 ** (-n - 1)
        out.append((n, m, eps))
    return out


# ------------------------------------------------------------------ Laeufe

def run_uniform(ns=(2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30, 40)):
    print('gleiche Massen m_a = 1/n, Kette der Laenge n, t = n (die Spitze)')
    print(f'{"n":>4} {"|F|":>5} {"C = ||T||_F":>16} {"Residuum":>11} {"Kern":>5}'
          f' {"C/vorher":>10}')
    prev = None
    for n in ns:
        m = np.array([0.0] + [1.0 / n] * n)
        V = chain_V(m)
        C, res, kern = defect_bound(V, len(m) - 1)
        ratio = '' if prev is None else f'{C / prev:10.3f}'
        print(f'{n:4d} {len(m):5d} {C:16.4e} {res:11.2e} {kern:5d} {ratio:>10}')
        prev = C


def run_dyadic(nmax=6):
    print('dyadische Atome k/2^j, Masse 4^-j, Level <= n; t = die Spitze')
    print(f'{"n":>3} {"|F|":>5} {"eps_n":>10} {"C = ||T||_F":>16}'
          f' {"Residuum":>11} {"Kern":>5} {"|F| C eps":>14}')
    for n, m, eps in dyadic_levels(nmax):
        V = chain_V(m)
        C, res, kern = defect_bound(V, len(m) - 1)
        print(f'{n:3d} {len(m):5d} {eps:10.3e} {C:16.4e} {res:11.2e}'
              f' {kern:5d} {len(m) * C * eps:14.4e}')


def run_check():
    """(P) an kleinen Faellen: zufaellige K, gestoertes (S), Schranke pruefen."""
    rng = np.random.default_rng(20260901)
    print('Probe auf (P): |delta(t)| <= (1/2) ||T||_F ||E||_F')
    print(f'{"n":>3} {"t":>3} {"|delta(t)|":>12} {"Schranke":>12} {"ok":>4}')
    worst = 0.0
    for n in (2, 3, 4, 5):
        for _ in range(30):
            m = np.array([0.0] + list(rng.uniform(0.2, 2.0, size=n)))
            N = len(m)
            V = chain_V(m)
            X = rng.normal(size=(N, N))
            K = X - X.T
            Psi = V @ K
            delta = np.diag(Psi).copy()
            # E ist der Fehler in (S); fuer eine exakte Loesung ist er null,
            # hier wird (S) kuenstlich gestoert, um die Schranke zu testen.
            E = 2 * (0.5 * (Psi + Psi.T)
                     - 0.5 * (np.outer(delta, np.ones(N))
                              + np.outer(np.ones(N), delta)))
            for t in range(N):
                T, res, _ = solve_T(V, t)
                if res > 1e-8:
                    continue
                lhs = abs(delta[t])
                bound = 0.5 * np.linalg.norm(T) * np.linalg.norm(E)
                worst = max(worst, lhs - bound)
                # Schaerfer: die Identitaet selbst, nicht nur die Schranke.
                ident = delta[t] + 0.5 * np.trace(T @ E)
                assert abs(ident) < 1e-6 * (1 + abs(delta[t])), (n, t, ident)
    print(f'   Identitaet <delta,T1> = -(1/2) tr(TE) haelt in allen Faellen;'
          f' groesste Verletzung der Schranke: {worst:.2e}')


def run_profile():
    """Haengt C von der Laenge ab oder vom Massenverhaeltnis?

    C ist skaleninvariant: mit V ist auch cV eine Loesung derselben Bedingung
    T V = V^T T, und T 1 = e_t kennt V nicht.  C haengt also nur von der
    *Gestalt* des Massenvektors ab.  Hier: geometrische Massen m_k = rho^k bei
    fester Laenge, und wachsende Laenge bei festem rho.
    """
    print('geometrische Massen m_k = rho^k, Kette der Laenge n, t = Spitze')
    print(f'{"n":>3} {"rho":>8} {"Verhaeltnis":>12} {"C = ||T||_F":>14}'
          f' {"C/Verh.":>10} {"Kern":>5}')
    for n in (4, 6, 8):
        for rho in (1.0, 1.5, 2.0, 3.0, 4.0):
            m = np.array([0.0] + [rho ** k for k in range(n)])
            V = chain_V(m)
            C, res, kern = defect_bound(V, len(m) - 1)
            ratio = rho ** (n - 1)
            print(f'{n:3d} {rho:8.2f} {ratio:12.3e} {C:14.4e}'
                  f' {C / ratio:10.4f} {kern:5d}')
        print()

    print('eine einzige kleine Masse: m = (1,...,1,eps,1,...,1), n = 6')
    print(f'{"Stelle":>7} {"eps":>10} {"C":>14} {"C*eps":>12}')
    n = 6
    for where in (1, 3, 5):
        for eps in (1.0, 1e-1, 1e-2, 1e-3):
            m = np.array([0.0] + [1.0] * n)
            m[where] = eps
            V = chain_V(m)
            C, _, _ = defect_bound(V, len(m) - 1)
            print(f'{where:7d} {eps:10.1e} {C:14.4e} {C * eps:12.4e}')
        print()


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if what == 'profile':
        run_profile()
        return
    if what == 'exact':
        run_exact()
        return
    if what == 'small':
        run_small()
        return
    if what in ('check', 'all'):
        run_check()
        print()
    if what in ('uniform', 'all'):
        run_uniform()
        print()
    if what in ('dyadic', 'all'):
        run_dyadic()


if __name__ == '__main__':
    main()
