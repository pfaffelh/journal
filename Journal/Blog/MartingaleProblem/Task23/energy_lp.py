"""Task 23, dreizehnter Lauf: die Energieschranke adversarial testen.

Vermutung (zwölfter Lauf): für jedes endliche Kettensystem mit
  (1) h(a,0) = 0
  (2) h(a,b)+h(b,a) = h(a,a)+h(b,b)          (a,b Atome)
  (3) |Sum_{a<s} m_a h(a,t) + Sum_{b<t} m_b h(b,s)| <= eta   (alle s,t)
  |h| <= B
gilt Delta^2 <= C*B*M*eta mit C <= 1, Delta = Sum_a m_a h(a,a).

Beide Skalierungen (h -> lam*h mit (eta,B) -> (lam*eta,lam*B); m -> c*m mit
eta -> c*eta) lassen Delta^2/(B*M*eta) fest; o.B.d.A. B = M = 1. Getestet wird
sup ueber Massenprofile und eta von v(eta)^2/eta, v der LP-Wert.

Kette: Atome 1..n an beliebigen Positionen (nur die Ordnung zaehlt); Gitter =
{0} + Atome + alle Lueckenmitten + Top. Das ist dieselbe Kodierung wie
lp_dense.py, nur mit freiem Massenvektor.
"""

import itertools
import numpy as np
from scipy.sparse import coo_matrix, vstack
from scipy.optimize import linprog


def solve_chain(mass, eta, B=1.0, want_dual=False):
    """Max Delta = Sum m_k h(a_k,a_k) unter (1),(2) exakt, (3) <= eta, |h|<=B.

    Gitter (Indices der Zeitpunkte): 0, a_1, s_1, a_2, s_2, ..., a_n, s_n
    mit s_k = Schnitt direkt ueber a_k (s_0 := 0 traegt keine Constraint-Info,
    da H(s_0,.) = 0; der Punkt 0 selbst steht fuer s_0 und fuer h(.,0)=0).
    """
    mass = np.asarray(mass, dtype=float)
    n = len(mass)
    # Gitterpunkte: g = 0 -> t=0 (=s_0); g = 2k-1 -> Atom k; g = 2k -> Schnitt s_k.
    m_grid = 2 * n + 1

    def atoms_below(g):
        # Anzahl Atome strikt unterhalb des Gitterpunkts g.
        if g == 0:
            return 0
        k = (g + 1) // 2  # g=2k-1 (Atom k) oder g=2k (Schnitt s_k)
        return k - 1 if g % 2 == 1 else k

    def var(a, g):  # h(Atom a+1, Gitterpunkt g)
        return a * m_grid + g

    nvar = n * m_grid
    lb = -B * np.ones(nvar)
    ub = B * np.ones(nvar)
    for a in range(n):
        lb[var(a, 0)] = ub[var(a, 0)] = 0.0  # (1)

    # (2): h(a,b)+h(b,a)-h(a,a)-h(b,b)=0, Atomgitterpunkt von Atom k ist 2k-1.
    rows, cols, dat = [], [], []
    nr = 0
    for a in range(n):
        for b in range(a + 1, n):
            ga, gb = 2 * a + 1, 2 * b + 1
            for c, coef in ((var(a, gb), 1.0), (var(b, ga), 1.0),
                            (var(a, ga), -1.0), (var(b, gb), -1.0)):
                rows.append(nr); cols.append(c); dat.append(coef)
            nr += 1
    A_eq = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr() if nr else None
    b_eq = np.zeros(nr) if nr else None

    # (3): |Sum_{k<cnt(s)} m_k h(k,t) + Sum_{k<cnt(t)} m_k h(k,s)| <= eta.
    rows, cols, dat, rhs = [], [], [], []
    nr = 0
    for gs in range(m_grid):
        for gt in range(gs, m_grid):
            cs, ct = atoms_below(gs), atoms_below(gt)
            if cs == 0 and ct == 0:
                continue
            coef = {}
            for k in range(cs):
                coef[var(k, gt)] = coef.get(var(k, gt), 0.0) + mass[k]
            for k in range(ct):
                coef[var(k, gs)] = coef.get(var(k, gs), 0.0) + mass[k]
            for c, v in coef.items():
                rows.append(nr); cols.append(c); dat.append(v)
            rhs.append(eta)
            nr += 1
    A1 = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr()
    A_ub = vstack([A1, -A1]).tocsr()
    b_ub = np.concatenate([rhs, rhs])

    c = np.zeros(nvar)
    for a in range(n):
        c[var(a, 2 * a + 1)] = -mass[a]

    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=np.stack([lb, ub], axis=1), method="highs")
    val = -res.fun if res.status == 0 else float("nan")
    return (val, res) if want_dual else val


def solve_chain_localbudget(mass, eta0, B=1.0):
    """Variante: rhs(s,t) = eta0 * M(<= max(s,t)) / M statt uniform eta.

    Das ist das masse-lokale Residuenbudget einer Trunkierung (Residuum an
    (s,t) <= 2B * fehlende Masse unterhalb max(s,t), hier proportional zur
    praesenten Masse modelliert). Ergebnis des dreizehnten Laufs: der
    Zwei-Atom-Zeuge faellt damit unter 1, die aufsteigend-geometrischen
    Ketten bleiben unbeschraenkt (14.5 / 131 / 8273 fuer n=5/6/8, rho=2).
    """
    mass = np.asarray(mass, dtype=float)
    n = len(mass)
    m_grid = 2 * n + 1
    Mpref = np.concatenate([[0.0], np.cumsum(mass)])
    Mtot = Mpref[-1]

    def atoms_below(g):
        if g == 0:
            return 0
        k = (g + 1) // 2
        return k - 1 if g % 2 == 1 else k

    def atoms_leq(g):
        return 0 if g == 0 else (g + 1) // 2

    def var(a, g):
        return a * m_grid + g

    nvar = n * m_grid
    lb = -B * np.ones(nvar)
    ub = B * np.ones(nvar)
    for a in range(n):
        lb[var(a, 0)] = ub[var(a, 0)] = 0.0

    rows, cols, dat = [], [], []
    nr = 0
    for a in range(n):
        for b in range(a + 1, n):
            ga, gb = 2 * a + 1, 2 * b + 1
            for c, coef in ((var(a, gb), 1.0), (var(b, ga), 1.0),
                            (var(a, ga), -1.0), (var(b, gb), -1.0)):
                rows.append(nr); cols.append(c); dat.append(coef)
            nr += 1
    A_eq = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr() if nr else None
    b_eq = np.zeros(nr) if nr else None

    rows, cols, dat, rhs = [], [], [], []
    nr = 0
    for gs in range(m_grid):
        for gt in range(gs, m_grid):
            cs, ct = atoms_below(gs), atoms_below(gt)
            if cs == 0 and ct == 0:
                continue
            coef = {}
            for k in range(cs):
                coef[var(k, gt)] = coef.get(var(k, gt), 0.0) + mass[k]
            for k in range(ct):
                coef[var(k, gs)] = coef.get(var(k, gs), 0.0) + mass[k]
            for c, v in coef.items():
                rows.append(nr); cols.append(c); dat.append(v)
            rhs.append(eta0 * Mpref[atoms_leq(max(gs, gt))] / Mtot)
            nr += 1
    A1 = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr()
    A_ub = vstack([A1, -A1]).tocsr()
    b_ub = np.concatenate([rhs, rhs])

    c = np.zeros(nvar)
    for a in range(n):
        c[var(a, 2 * a + 1)] = -mass[a]

    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=np.stack([lb, ub], axis=1), method="highs")
    return -res.fun if res.status == 0 else float("nan")


def ratio(mass, eta, B=1.0):
    mass = np.asarray(mass, dtype=float)
    M = mass.sum()
    v = solve_chain(mass, eta, B)
    return v * v / (B * M * eta)


if __name__ == "__main__":
    rng = np.random.default_rng(23)

    print("== Kontrolle: eta=0 gibt v=0 ==")
    for mass in ([1.0], [1.0, 1.0], [0.1, 1.0, 0.3], [1, 2, 3, 4]):
        v = solve_chain(mass, 0.0)
        print(f"  m={mass}: v={v:.2e}")

    print("== n=1..3, Handprofile, eta-Sweep ==")
    profiles = [
        [1.0],
        [0.5, 0.5], [0.01, 0.99], [0.99, 0.01],
        [1 / 3] * 3, [0.01, 0.01, 0.98], [0.98, 0.01, 0.01],
        [0.01, 0.98, 0.01],
    ]
    for mass in profiles:
        worst = 0.0
        arg = None
        for eta in np.geomspace(1e-5, 1.0, 25):
            r = ratio(mass, eta)
            if r > worst:
                worst, arg = r, eta
        print(f"  m={np.round(mass,3)}: max ratio={worst:.4f} bei eta={arg:.2e}")

    print("== zufaellige Profile, n=4..8 ==")
    worst_all = (0.0, None, None)
    for trial in range(40):
        n = int(rng.integers(4, 9))
        # Massen ueber mehrere Groessenordnungen, normiert.
        mass = rng.dirichlet(np.full(n, 0.3))
        mass = np.maximum(mass, 1e-6)
        mass /= mass.sum()
        for eta in np.geomspace(1e-4, 0.5, 12):
            r = ratio(mass, eta)
            if r > worst_all[0]:
                worst_all = (r, mass.copy(), eta)
    r, mass, eta = worst_all
    print(f"  schlimmster Fall: ratio={r:.4f} bei eta={eta:.2e}, "
          f"m={np.round(mass,4)}")
