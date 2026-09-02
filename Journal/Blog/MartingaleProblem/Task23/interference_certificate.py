"""Task 23, sechzehnter Lauf: exakte Zertifikate fuer den Interferenztest.

Die LP-Messung (interference.py) zeigt auf der hierarchischen Motor-Uhr
(k=4, lambda_1=2/5) einen langsamen Abfall von v_i bei geometrisch
kollabierendem eps_i -- Amplifikation ~5e4 auf Stufe 10.  Weil das die
Kollaps-Narrative der Laeufe 12 und 15 umkehrt, wird hier wie im dreizehnten
Lauf zertifiziert: LP-Loesung auf rationale Zahlen gerundet, Bedingungen 1
und 2 per Konstruktion exakt erzwungen, dann in fractions.Fraction exakt
nachgerechnet: Delta, B_used = max|h| und maxratio = max |R(s,t)|/(eps(s)+
eps(t)) ueber alle Gitterpaare.  Skalieren mit c = max(B_used, maxratio)
gibt ein unter B=1 zulaessiges h mit Gewinn Delta/c: ein Zertifikat
v_Stufe >= Delta/c, unabhaengig von LP-Toleranzen.

Auf dieser Uhr liegt alle fehlende Masse unterhalb aller praesenten Atome;
eps(g) ist also fuer jedes g >= a_1 die exakte Gesamtmasse E der fehlenden
Bloecke (Fraction), und die Zeilen mit gs=0 sind wegen h(.,0)=0 trivial.
"""

from fractions import Fraction
import numpy as np
from scipy.sparse import coo_matrix, vstack
from scipy.optimize import linprog


def solve_return_x(mass, eps_grid, B=1.0):
    """Wie summable_lp.solve_chain_missing, gibt aber (v, x) zurueck."""
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
            rhs.append(B * (eps_grid[gs] + eps_grid[gt]))
            nr += 1
    A1 = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr()
    c = np.zeros(nvar)
    for a in range(n):
        c[var(a, 2 * a + 1)] = -mass[a]
    res = linprog(c, A_ub=vstack([A1, -A1]).tocsr(),
                  b_ub=np.concatenate([rhs, rhs]), A_eq=A_eq, b_eq=b_eq,
                  bounds=np.stack([lb, ub], axis=1), method="highs")
    assert res.status == 0
    return -res.fun, res.x


def certify_stage(i, N=14, k=4, denom=10 ** 9):
    """Exaktes Zertifikat fuer Stufe i der hierarchischen Motor-Uhr."""
    lam1 = Fraction(2, 5)
    # praesente Atome, aufsteigend nach Position = Bloecke i..1 von unten
    masses = []          # exakte Massen, aufsteigend sortiert nach Position
    for blk in range(i, 0, -1):
        lam = lam1 / k ** (blk - 1)
        masses += [lam / k] * k + [lam]
    n = len(masses)
    # fehlende Masse: Bloecke i+1..N exakt, Schwanz j>N geometrisch exakt
    E = sum(2 * lam1 / k ** (j - 1) for j in range(i + 1, N + 1)) \
        + 2 * (lam1 / k ** (N - 1)) / (k - 1)
    m_grid = 2 * n + 1

    v_float, x = solve_return_x(np.array([float(m) for m in masses]),
                                np.full(m_grid, float(E)))
    # runden, Bedingungen 1 und 2 exakt erzwingen
    h = [[Fraction(round(x[a * m_grid + g] * denom), denom)
          for g in range(m_grid)] for a in range(n)]
    for a in range(n):
        h[a][0] = Fraction(0)
    for a in range(n):
        for b in range(a + 1, n):
            ga, gb = 2 * a + 1, 2 * b + 1
            h[b][ga] = h[a][ga] + h[b][gb] - h[a][gb]

    def atoms_below(g):
        if g == 0:
            return 0
        q = (g + 1) // 2
        return q - 1 if g % 2 == 1 else q

    B_used = max(abs(v) for row in h for v in row)
    maxres = Fraction(0)
    for gs in range(1, m_grid):
        for gt in range(gs, m_grid):
            cs, ct = atoms_below(gs), atoms_below(gt)
            R = sum(masses[a] * h[a][gt] for a in range(cs)) \
                + sum(masses[a] * h[a][gs] for a in range(ct))
            maxres = max(maxres, abs(R))
    maxratio = maxres / (2 * E)
    delta = sum(masses[a] * h[a][2 * a + 1] for a in range(n))
    c = max(B_used, maxratio)
    return v_float, delta, B_used, maxratio, delta / c, E


if __name__ == "__main__":
    for i in (4, 6, 8):
        v, d, B_used, mr, cert, E = certify_stage(i)
        print(f"Stufe {i}: LP v={v:.6f}  Delta_exakt={float(d):.6f}  "
              f"B_used={float(B_used):.6f}  maxratio={float(mr):.6f}  "
              f"zertifiziert v>={float(cert):.6f}  (eps={float(E):.3e})",
              flush=True)
