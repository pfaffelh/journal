"""Task 23, siebzehnter Lauf: die Adjudikation der Kollision, numerischer Teil.

Papierbefund dieses Laufs (PROTOKOLL, siebzehnter Lauf): das exakte h-System
1-3 ist auf jeder intervallendlichen Kette starr.  Der Beweis braucht keine
Rekonstruktion: w(s,t) := H(s,t) + Delta(t) - Delta(s) erfuellt (C3-exakt)
die Kreuzrelation (*) des vierzehnten Laufs --

  Erstschritt   w(u_{k+1},t) - w(u_k,t) =  m_k kappa(u_k,t)   (definitorisch),
  Zweitschritt  w(s,u_{k+1}) - w(s,u_k) = -m_k kappa(u_k,s)   (C3 zweimal),
  kappa(a,t) := h(a,t) - h(a,a),  kappa antisymmetrisch auf Atompaaren (C2)

-- also laeuft die Zwei-Diagonalen-Induktion, w == 0 auf dem Gitter, und die
Schwanzlimiten (C3 macht den Zweitkoordinatenlimes zum Schnittschwanz) geben
Delta == 0, d.h. h(a,a) = 0.  Folgerung fuer die LPs (Residuen phi statt 0):
der (*)-Defekt ist exakt -m_i * (phi(u_{j+1}) - phi(u_j)), und mit festem
Fenster oberhalb u_l gilt  v_i <= 2B*M(<u_l) + K_l*E_i  mit
stufenUNabhaengigem (aber gewaltigem) K_l.  Wegen M(<u_l) -> 0 folgt
v_i -> 0: das Plateau 1/24 + E_i ist praeasymptotisch.

Dieses Skript prueft am LP-Optimum:
  (a) die exakt erzwungene Identitaet h(a_j, a_{j+1}) = h(a_j, a_j)
      (drei C3-Zeilen, phi kuerzt sich);
  (b) die Randzerlegung v = H(t*,u) + Delta(u) - w(t*,u) je Blockboden;
  (d) den (*)-Defekt: D(i,j) := m_j[w(i+1,j)-w(i,j)] - m_i[w(i,j+1)-w(i,j)]
      muss exakt -m_i*(phi(u_{j+1}) - phi(u_j)) sein, phi(g) = H(g,g).

LP-Formulierung: phi ist durch die Diagonalzeile bestimmt, phi(s) = H(s,s);
eingesetzt lautet Bedingung (3') exakt

  H(s,t) + H(t,s) - H(s,s) - H(t,t) = 0,     |H(t,t)| <= B*E,

ohne phi-Variablen.  Das ist dieselbe zulaessige Menge wie in
interference_separable.py, aber besser konditioniert (die einzigen
E-skaligen Zeilen sind die Ungleichungen |H(t,t)| <= BE).
"""

import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog

from interference import build_clock, stage


def solve_sep2(mass, E, B=1.0, return_x=False):
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

    # Gleichungen: (2) exakt; (3') H(s,t)+H(t,s)-H(s,s)-H(t,t)=0, gs<gt.
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
        for gt in range(gs + 1, m_grid):
            cs, ct = atoms_below(gs), atoms_below(gt)
            coef = {}
            for k in range(cs):
                coef[var(k, gt)] = coef.get(var(k, gt), 0.0) + mass[k]
                coef[var(k, gs)] = coef.get(var(k, gs), 0.0) - mass[k]
            for k in range(ct):
                coef[var(k, gs)] = coef.get(var(k, gs), 0.0) + mass[k]
                coef[var(k, gt)] = coef.get(var(k, gt), 0.0) - mass[k]
            coef = {c: v for c, v in coef.items() if v != 0.0}
            if not coef:
                continue
            scale = max(abs(v) for v in coef.values())
            for c, v in coef.items():
                rows.append(nr); cols.append(c); dat.append(v / scale)
            nr += 1
    A_eq = coo_matrix((dat, (rows, cols)), shape=(nr, nvar)).tocsr()
    b_eq = np.zeros(nr)

    # Ungleichungen: |H(g,g)| <= B*E fuer alle Gitter-g >= 1.
    urows, ucols, udat = [], [], []
    unr = 0
    for g in range(1, m_grid):
        cg = atoms_below(g)
        if cg == 0:
            continue  # H = 0, nichts zu beschraenken
        sc = mass[:cg].max()
        for k in range(cg):
            urows.append(unr); ucols.append(var(k, g)); udat.append(mass[k] / sc)
        unr += 1
        for k in range(cg):
            urows.append(unr); ucols.append(var(k, g)); udat.append(-mass[k] / sc)
        unr += 1
        # b_ub je Zeile: B*E/sc — unten gesammelt
    A_ub = coo_matrix((udat, (urows, ucols)), shape=(unr, nvar)).tocsr()
    b_ub = np.empty(unr)
    unr = 0
    for g in range(1, m_grid):
        cg = atoms_below(g)
        if cg == 0:
            continue
        sc = mass[:cg].max()
        b_ub[unr] = B * E / sc; unr += 1
        b_ub[unr] = B * E / sc; unr += 1

    c = np.zeros(nvar)
    for a in range(n):
        c[var(a, 2 * a + 1)] = -mass[a]
    res = linprog(c, A_eq=A_eq, b_eq=b_eq, A_ub=A_ub, b_ub=b_ub,
                  bounds=np.stack([lb, ub], axis=1), method="highs",
                  options={"presolve": False})
    v = -res.fun if res.status == 0 else float("nan")
    if not return_x:
        return v
    return v, (res.x if res.status == 0 else None), res.status


def inspect(mass, E, B=1.0):
    mass = np.asarray(mass, dtype=float)
    n = len(mass)
    m_grid = 2 * n + 1
    v, x, st = solve_sep2(mass, E, B, return_x=True)
    if x is None:
        return v, None, None, None
    h = x.reshape(n, m_grid)

    # (a) max_j |h(j, a_{j+1}) - h(j, a_j)|
    ident = max(abs(h[j, 2 * (j + 1) + 1] - h[j, 2 * j + 1])
                for j in range(n - 1))

    # Bausteine: Atomgitter u_0..u_{n-1} (Gitter 2j+1) plus Deckel t* (2n).
    # H(u_i, t) mit Schnitt i Atome; phi(u_j) := H(u_j,u_j).
    gpt = [2 * j + 1 for j in range(n)] + [2 * n]      # Gitterindex von u_j, t*
    cut = [j for j in range(n)] + [n]                   # Atome unterhalb
    diag = np.array([mass[a] * h[a, 2 * a + 1] for a in range(n)])
    csum = np.concatenate([[0.0], np.cumsum(diag)])     # Delta an Schnitten

    def H(i, j):  # H(u_i, u_j), Indizes in 0..n (n = Deckel)
        return sum(mass[a] * h[a, gpt[j]] for a in range(cut[i]))

    def w(i, j):
        return H(i, j) + csum[cut[j]] - csum[cut[i]]

    phi = np.array([H(j, j) for j in range(n + 1)])

    # (d) (*)-Defekt gegen Vorhersage -m_i*(phi(j+1)-phi(j)), i,j <= n-1.
    ddef = 0.0
    for i in range(min(n - 1, 12)):
        for j in range(min(n - 1, 12)):
            D = mass[j] * (w(i + 1, j) - w(i, j)) \
                - mass[i] * (w(i, j + 1) - w(i, j))
            pred = -mass[i] * (phi[j + 1] - phi[j])
            ddef = max(ddef, abs(D - pred))
    # dieselbe Probe an den obersten Paaren
    for i in range(max(0, n - 13), n - 1):
        for j in range(max(0, n - 13), n - 1):
            D = mass[j] * (w(i + 1, j) - w(i, j)) \
                - mass[i] * (w(i, j + 1) - w(i, j))
            pred = -mass[i] * (phi[j + 1] - phi[j])
            ddef = max(ddef, abs(D - pred))

    # (b) Randzerlegung an Blockboeden: v = H(t*,u) + Delta(u) - w(t*,u).
    dec = [(cs, H(n, cs), csum[cs], w(n, cs)) for cs in range(0, n, 5)]
    return v, ident, ddef, dec


if __name__ == "__main__":
    N, k, lam1, B = 16, 4, 0.4, 1.0
    atoms, lamN = build_clock(N, lam1, k)
    print("== (a)+(b)+(d): Stufen 4..9 ==", flush=True)
    for i in range(4, 10):
        mass, eps, E = stage(atoms, i, lamN, k)
        v, ident, ddef, dec = inspect(mass, E, B)
        if ident is None:
            print(f"Stufe {i}: LP-Status != 0, v={v}", flush=True)
            continue
        print(f"Stufe {i}: v={v:.8f} v-1/24={v - 1/24:.3e} E={E:.3e} "
              f"(a)={ident:.2e} (d)={ddef:.2e}", flush=True)
        for cs, Htu, dlt, wv in dec:
            print(f"    Schnitt {cs:2d} Atome unten: H(t*,u)={Htu:+.6f} "
                  f"Delta(u)={dlt:+.6f} w(t*,u)={wv:+.6f}", flush=True)
    print("== (c): Stufen 10..14 ==", flush=True)
    for i in range(10, 15):
        mass, eps, E = stage(atoms, i, lamN, k)
        v = solve_sep2(mass, E, B)
        print(f"Stufe {i}: n={len(mass)} E={E:.3e} v={v:.8f} "
              f"v-1/24={v - 1/24:.3e}", flush=True)
