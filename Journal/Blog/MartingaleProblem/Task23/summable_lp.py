"""Task 23, fuenfzehnter Lauf (Teil b der Aufgabe vom 2026-09-01): die
Summierbarkeit als tragende Struktur.

Neuformulierung. Die Relaxation der Laeufe 11-13 quantifizierte ueber beliebige
endliche Massenvektoren mit freiem Slack eta und ist dreifach gescheitert. Eine
Uhr hat aber q(T_<=t) < infty: die Massen sind ein fest gewaehltes summierbares
Profil, und eine Trunkierung ist GESCHACHTELT -- Stufe J+1 fuegt Atome hinzu,
aendert keine Masse. Das Residuum der Stufe J am Paar (s,t) ist dann nicht frei,
sondern

    |R(s,t)| <= B * (eps(s) + eps(t)),   eps(g) = fehlende Masse unterhalb g.

Frage (S): gilt v_J -> 0 fuer jede summierbare Uhr laengs jeder Ausschoepfung
mit eps_J -> 0?  Die Laeufe 12/13 haben das nur fuer geometrische Schwaenze
(eps_J ~ q^J) gemessen. Der freie Parameter, den die Summierbarkeit NICHT
kontrolliert, ist die Schwanzgeschwindigkeit: m_(k) ~ 1/(k log^2 k) gibt
eps_n ~ 1/log n, und die profilfreie lineare Schranke v <= (n+1/2)*eta des
zwoelften Laufs wird dann nutzlos ((n+1/2)*eps_n -> infty). Dieses Skript
testet deshalb langsame Schwaenze (eps_J ~ 1/J und ~ 1/log J) gegen die
geometrische Kontrolle, jeweils flach und mit steigendem Positionsprofil x^p
(der realisierbare Rest des Verstaerkungsmotors der Laeufe 11-13).

Konservativ zugunsten des Gegenspielers: eps(Schnitt s_k) zaehlt alle
fehlenden Atome der ganzen Luecke (x_k, x_{k+1}) als unterhalb, und der
analytische Schwanz jenseits von Jdeep wird JEDEM Gitterpunkt zugeschlagen.
Kollabiert v_J trotzdem, ist der Befund belastbar.
"""

import numpy as np
from scipy.sparse import coo_matrix, vstack
from scipy.optimize import linprog


def solve_chain_missing(mass, eps_grid, B=1.0):
    """Max Delta = Sum m_k h(a_k,a_k) unter
    (1) h(a,0)=0, (2) Symmetrierelation exakt,
    (3) |Sum_{a<s} m_a h(a,t) + Sum_{b<t} m_b h(b,s)| <= B*(eps(s)+eps(t)),
    |h| <= B.  Gitter wie energy_lp.solve_chain; eps_grid hat Laenge 2n+1."""
    mass = np.asarray(mass, dtype=float)
    n = len(mass)
    m_grid = 2 * n + 1
    assert len(eps_grid) == m_grid

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
    A_ub = vstack([A1, -A1]).tocsr()
    b_ub = np.concatenate([rhs, rhs])

    c = np.zeros(nvar)
    for a in range(n):
        c[var(a, 2 * a + 1)] = -mass[a]

    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=np.stack([lb, ub], axis=1), method="highs")
    return -res.fun if res.status == 0 else float("nan")


def dyadic_nested(J, massfun, Jdeep, tailbound):
    """Stufe J der geschachtelten dyadischen Uhr: Atome k/2^j, j<=J, Masse
    massfun(x, j).  eps(g) exakt aus den Levels J+1..Jdeep (Prefixsummen je
    Level, Binaersuche je Gitterpunkt), plus tailbound (Levels > Jdeep) auf
    jedem Gitterpunkt.  Rueckgabe: mass (sortiert), eps_grid, eps_total."""
    atoms = []
    for j in range(1, J + 1):
        for k in range(1, 2 ** j, 2):
            atoms.append((k / 2 ** j, float(massfun(k / 2 ** j, j))))
    atoms.sort()
    pos = np.array([x for x, _ in atoms])
    mass = np.array([m for _, m in atoms])
    n = len(atoms)
    # Gitterpositionen: 0, a_1, s_1, ..., a_n, s_n. eps am Schnitt s_k zaehlt
    # die ganze Luecke (x_k, x_{k+1}): nimm als Vergleichsposition x_{k+1}
    # (bzw. 1.0 + fuer s_n), am Atom a_k die Position x_k (strikt darunter).
    grid_pos = np.empty(2 * n + 1)
    grid_strict = np.empty(2 * n + 1, dtype=bool)  # strikt-unterhalb-Vergleich?
    grid_pos[0] = 0.0; grid_strict[0] = True
    for k in range(n):
        grid_pos[2 * k + 1] = pos[k]; grid_strict[2 * k + 1] = True
        if k + 1 < n:
            grid_pos[2 * k + 2] = pos[k + 1]; grid_strict[2 * k + 2] = True
        else:
            grid_pos[2 * k + 2] = 2.0; grid_strict[2 * k + 2] = True
    eps = np.full(2 * n + 1, tailbound)
    eps_total = tailbound
    for j in range(J + 1, Jdeep + 1):
        ks = np.arange(1, 2 ** j, 2, dtype=np.int64)
        xs = ks / 2.0 ** j
        ms = np.asarray(massfun(xs, j), dtype=float)
        pref = np.concatenate([[0.0], np.cumsum(ms)])
        idx = np.searchsorted(xs, grid_pos, side="left")
        eps += pref[idx]
        eps_total += ms.sum()
    return mass, eps, eps_total


def levelnorm(j, p):
    """Summe von x^p ueber die neuen Atome des Levels j (exakt)."""
    ks = np.arange(1, 2 ** j, 2, dtype=float)
    return ((ks / 2 ** j) ** p).sum()


def make_profiles():
    """(Name, massfun, tailbound(Jdeep)).  Levelgesamtmasse c_j, verteilt
    flach oder mit Positionsfaktor x^p (levelnormiert, Gesamtmasse bleibt c_j).
    Schwaenze: geometrisch (Kontrolle), 1/j^2 (eps_J ~ 1/J), 1/(j log^2 j)
    (eps_J ~ 1/log J)."""
    profs = []

    def flat(cfun):
        return lambda x, j: cfun(j) / 2 ** (j - 1) * np.ones_like(np.asarray(x, dtype=float))

    def shaped(cfun, p):
        return lambda x, j: cfun(j) * np.asarray(x, dtype=float) ** p / levelnorm(j, p)

    c_geo = lambda j: 2.0 ** (-j)
    c_sq = lambda j: 1.0 / j ** 2
    c_log = lambda j: 1.0 / (j * np.log(j + 1.0) ** 2)
    # Schwanz Sum_{j>Jd} c_j, obere Schranken analytisch:
    t_geo = lambda Jd: 2.0 ** (-Jd)
    t_sq = lambda Jd: 1.0 / Jd          # Sum_{j>Jd} 1/j^2 <= 1/Jd
    t_log = lambda Jd: 1.0 / np.log(Jd + 1.0)  # Integralvergleich

    profs.append(("geometrisch flach", flat(c_geo), t_geo))
    profs.append(("1/j^2 flach", flat(c_sq), t_sq))
    profs.append(("1/j^2 * x^4", shaped(c_sq, 4), t_sq))
    profs.append(("1/(j log^2 j) flach", flat(c_log), t_log))
    profs.append(("1/(j log^2 j) * x^4", shaped(c_log, 4), t_log))
    return profs


if __name__ == "__main__":
    Jdeep = 20
    print("== Kontrolle: eps = 0 ueberall gibt v = 0 ==", flush=True)
    for J in (2, 3):
        mass, eps, et = dyadic_nested(J, lambda x, j: 4.0 ** (-j) * np.ones_like(np.asarray(x, dtype=float)), J, 0.0)
        v = solve_chain_missing(mass, np.zeros_like(eps))
        print(f"  J={J}: v={v:.2e}", flush=True)

    for name, f, tb in make_profiles():
        print(f"== {name} ==", flush=True)
        for J in range(2, 7):
            mass, eps, eps_total = dyadic_nested(J, f, Jdeep, tb(Jdeep))
            M = mass.sum()
            v = solve_chain_missing(mass, eps)
            print(f"  J={J}: n={len(mass)} M_J={M:.4f} eps_J={eps_total:.3e} "
                  f"v_J={v:.5f}  v/M={v / M:.4f}  v/eps={v / eps_total:.3f}  "
                  f"v/sqrt(M eps)={v / np.sqrt(M * eps_total):.3f}", flush=True)
