"""Task 23, zwölfter Lauf: die ordnungsdichte Atommenge als lineares Programm.

Reduktion (hergeleitet in PROTOKOLL.md, zwölfter Lauf): eliminiere gamma
zugunsten seines antisymmetrischen Teils g(x,y) = gamma(x,y) - gamma(y,x) und
setze h(a,t) := g(a,t) - g(a,0). Dann ist die Dualitätsaussage
Phi(t,0) = Phi(0,t) für alle t äquivalent dazu, dass jedes System

  (1) h(a,0) = 0                                       (Definition)
  (2) h(a,b) + h(b,a) = h(a,a) + h(b,b)   (a,b Atome)  (Antisymmetrie von g)
  (3) Sum_{a<s} m_a h(a,t) + Sum_{b<t} m_b h(b,s) = 0  (alle s,t; Antisymmetrie
                                                        des Feldes H)

nur h(a,a) = 0 für alle Atome zulässt; der Eckdefekt ist
Delta(s) = Sum_{a<s} m_a h(a,a).

Trunkierung: behalte die Atome bis Level J der dyadischen Menge. Ein
beschränktes Gegenbeispiel (|h| <= B) des vollen Systems erfüllt auf der
Trunkierung (1),(2) exakt und (3) bis auf 2*B*eps_J, eps_J = Schwanzmasse.
Das LP maximiert Delta_J(1) unter genau diesen Bedingungen mit B = 1.

Lesart: v_J -> 0 (etwa ~ eps_J) => kein beschränktes Gegenbeispiel auf dieser
Uhr, und die Dualvariablen sind die strukturierte Paarung, nach der der elfte
Lauf gefragt hat. v_J -> const > 0 => Richtung Gegenbeispiel.

Kontrolle: eta = 0 muss v_J = 0 geben (der endliche Satz, sechster Lauf).
"""

from fractions import Fraction
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog


def build_instance(J, r):
    """Dyadische Atome k/2^j, j<=J, Masse r^{-j} je Level-j-Atom."""
    atoms = []
    for j in range(1, J + 1):
        mu = float(r) ** (-j)
        for k in range(1, 2 ** j, 2):
            atoms.append((Fraction(k, 2 ** j), mu))
    atoms.sort()
    vals = [a for a, _ in atoms]
    mass = np.array([m for _, m in atoms])
    # Gitter: Dyadische bis Level J+1 (enthält alle Atome und alle
    # Lückenmittelpunkte) samt 0 und 1.
    G = [Fraction(k, 2 ** (J + 1)) for k in range(0, 2 ** (J + 1) + 1)]
    # Schwanzmasse: Sum_{j>J} 2^{j-1} r^{-j} = (1/2) * (2/r)^{J+1} / (1-2/r)
    q = 2.0 / float(r)
    eps = 0.5 * q ** (J + 1) / (1.0 - q)
    return vals, mass, G, eps


def solve(J, r, eta_factor=2.0, objective_at=None, use_eta=True, eta_abs=None):
    vals, mass, G, eps = build_instance(J, r)
    n, m = len(vals), len(G)
    gidx = {g: i for i, g in enumerate(G)}
    aidx_in_grid = [gidx[v] for v in vals]

    def var(a, t):  # h(atoms[a], G[t])
        return a * m + t

    nvar = n * m
    eta = eta_factor * eps if use_eta else 0.0
    if eta_abs is not None:
        eta = eta_abs

    # Schranken: |h| <= 1, h(a,0) = 0.
    lb = -np.ones(nvar)
    ub = np.ones(nvar)
    for a in range(n):
        lb[var(a, gidx[Fraction(0)])] = 0.0
        ub[var(a, gidx[Fraction(0)])] = 0.0

    # Gleichungen (2): h(a,b)+h(b,a)-h(a,a)-h(b,b) = 0 für a<b.
    rows, cols, dat = [], [], []
    nr = 0
    for a in range(n):
        for b in range(a + 1, n):
            ta, tb = aidx_in_grid[a], aidx_in_grid[b]
            for c, coef in ((var(a, tb), 1.0), (var(b, ta), 1.0),
                            (var(a, ta), -1.0), (var(b, tb), -1.0)):
                rows.append(nr); cols.append(c); dat.append(coef)
            nr += 1
    A_eq = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr()
    b_eq = np.zeros(nr)

    # Ungleichungen (3): |expr(s,t)| <= eta für s<=t im Gitter.
    # expr(s,t) = Sum_{a: vals[a]<s} mass[a]*h(a,t) + Sum_{b: vals[b]<t} mass[b]*h(b,s)
    # cnt[s] = Anzahl Atome < s (strikt).
    import bisect
    cnt = [bisect.bisect_left(vals, g) for g in G]
    rows, cols, dat, rhs = [], [], [], []
    nr = 0
    for si in range(m):
        for ti in range(si, m):
            cs, ct = cnt[si], cnt[ti]
            if cs == 0 and ct == 0:
                continue
            coef = {}
            for a in range(cs):
                coef[var(a, ti)] = coef.get(var(a, ti), 0.0) + mass[a]
            for b in range(ct):
                coef[var(b, si)] = coef.get(var(b, si), 0.0) + mass[b]
            for c, v in coef.items():
                rows.append(nr); cols.append(c); dat.append(v)
            nr += 1
            rhs.append(eta)
    A1 = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr()
    from scipy.sparse import vstack
    A_ub = vstack([A1, -A1]).tocsr()
    b_ub = np.concatenate([np.array(rhs), np.array(rhs)])

    # Ziel: maximiere Delta(objective_at) = Sum_{a < s0} m_a h(a,a).
    s0 = Fraction(1) if objective_at is None else objective_at
    c = np.zeros(nvar)
    for a in range(n):
        if vals[a] < s0:
            c[var(a, aidx_in_grid[a])] = -mass[a]  # linprog minimiert

    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=np.stack([lb, ub], axis=1), method="highs")
    val = -res.fun if res.status == 0 else float("nan")
    return val, eps, res


if __name__ == "__main__":
    for r in (2.5, 4.0, 8.0):
        print(f"== Massen r^-j, r={r} ==")
        for J in range(2, 7):
            v0, eps, _ = solve(J, r, use_eta=False)
            v, _, _ = solve(J, r, use_eta=True)
            print(f"  J={J}: eps_J={eps:.3e}  v(eta=0)={v0:.3e}  "
                  f"v(eta=2eps)={v:.3e}  v/eps={v/eps if eps else float('inf'):.3f}")
