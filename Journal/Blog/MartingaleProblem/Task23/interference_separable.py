"""Task 23, sechzehnter Lauf, zweiter Teil: die Gestalt des Residuums.

Auf der hierarchischen Motor-Uhr liegt ALLE fehlende Masse unterhalb aller
praesenten Atome.  Ein realisierbares Residuum ist dann separabel:

    R(s,t) = phi(s) + phi(t),   phi(g) = Sum_{a fehlend} m_a h(a,g),
    |phi| <= B*E,  E = fehlende Gesamtmasse,

waehrend die Relaxation der Laeufe 15/16 beliebige R mit |R| <= 2BE zulaesst.
Punkt 3 des dreizehnten Laufs ("nicht die Groesse des Residuums, sondern
seine Gestalt") wird hier zum ersten Mal ins LP eingebaut: Variablen phi(g),
g >= 1, Gleichheitszeilen R(s,t) - phi(s) - phi(t) = 0, Schranke |phi| <= BE.
Das ist immer noch eine Relaxation der echten Trunkierung (phi muss nicht
selbst aus einem global zulaessigen h der fehlenden Atome kommen), aber echt
enger als |R| <= 2BE.  Frage: stirbt die Interferenz-Kaskade darunter --
kollabiert v_i wieder auf die Skala des Einzelmotors lambda_i*B?
"""

import numpy as np
from scipy.sparse import coo_matrix, vstack
from scipy.optimize import linprog

from interference import build_clock, stage


def solve_chain_separable(mass, E, B=1.0):
    """Max Delta unter (1) h(a,0)=0, (2) Symmetrie exakt, |h| <= B, und
    (3') R(s,t) = phi(s)+phi(t) fuer alle Gitterpaare gs,gt >= 1, mit
    |phi| <= B*E.  Setzt voraus, dass alle fehlende Masse unterhalb des
    untersten praesenten Atoms liegt (eps(g) = E fuer alle g >= 1)."""
    mass = np.asarray(mass, dtype=float)
    n = len(mass)
    m_grid = 2 * n + 1

    def atoms_below(g):
        if g == 0:
            return 0
        k = (g + 1) // 2
        return k - 1 if g % 2 == 1 else k

    def var(a, g):
        return a * m_grid + g

    nh = n * m_grid
    def phivar(g):
        return nh + g - 1  # phi(g), g = 1..2n

    nvar = nh + 2 * n
    lb = np.concatenate([-B * np.ones(nh), -B * E * np.ones(2 * n)])
    ub = np.concatenate([B * np.ones(nh), B * E * np.ones(2 * n)])
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
    for gs in range(1, m_grid):
        for gt in range(gs, m_grid):
            cs, ct = atoms_below(gs), atoms_below(gt)
            coef = {}
            for k in range(cs):
                coef[var(k, gt)] = coef.get(var(k, gt), 0.0) + mass[k]
            for k in range(ct):
                coef[var(k, gs)] = coef.get(var(k, gs), 0.0) + mass[k]
            coef[phivar(gs)] = coef.get(phivar(gs), 0.0) - 1.0
            coef[phivar(gt)] = coef.get(phivar(gt), 0.0) - 1.0
            for c, v in coef.items():
                rows.append(nr); cols.append(c); dat.append(v)
            nr += 1
    A_eq = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr()
    b_eq = np.zeros(nr)

    c = np.zeros(nvar)
    for a in range(n):
        c[var(a, 2 * a + 1)] = -mass[a]
    res = linprog(c, A_eq=A_eq, b_eq=b_eq,
                  bounds=np.stack([lb, ub], axis=1), method="highs")
    return -res.fun if res.status == 0 else float("nan")


if __name__ == "__main__":
    N, k, lam1, B = 14, 4, 0.4, 1.0
    atoms, lamN = build_clock(N, lam1, k)
    lam = [lam1 / k ** (i - 1) for i in range(0, N + 2)]
    print("== Kontrolle: E = 0 gibt v = 0 ==", flush=True)
    for i in (1, 2):
        mass, eps, _ = stage(atoms, i, lamN, k)
        v = solve_chain_separable(mass, 0.0, B)
        print(f"  Stufe {i}: v={v:.2e}", flush=True)
    print("== separables Residuum, natuerliche Ausschoepfung ==", flush=True)
    prev = None
    for i in range(1, 11):
        mass, eps, eps_tot = stage(atoms, i, lamN, k)
        v = solve_chain_separable(mass, eps_tot, B)
        r = f"  v_i/v_(i-1)={v / prev:.4f}" if prev else ""
        print(f"  Stufe {i:2d}: n={len(mass)} E={eps_tot:.3e} v={v:.6f}  "
              f"v/(lam_i B)={v / (lam[i] * B):.3f}  v/E={v / eps_tot:.2f}{r}",
              flush=True)
        prev = v
