"""Task 23, sechzehnter Lauf: der Interferenztest der Massenbilanz-Heuristik.

Die Heuristik des fuenfzehnten Laufs: der einzige gemessene Mechanismus traegt
Gewinn v ~ lambda*B mit lambda = Masse eines leichten Praefixes unter einem
schweren Atom, und anhaltender Gewinn laengs einer Ausschoepfung braeuchte
unendlich viele Motoren mit lambda_i >= c/B -- unendliche Masse. Ihre Luecke:
dass Motoren verschiedener Skalen keine Praefixmasse teilen koennen
(Interferenz), ist unbewiesen. Dieses Skript baut den adversarialen Fall:

    Block i = schweres Atom M_i ueber einem Praefix aus k leichten Atomen
    der Gesamtmasse lambda_i, M_i = lambda_i, Blocks absteigend geschachtelt
    (Block i+1 liegt ganz unterhalb des Praefixes von Block i), und
    lambda_{i+1} = lambda_i / k.

Damit ist die Wolke der Skala i (= die auf Stufe i fehlenden Bloecke >= i+1)
genau der Praefix der Skala i+1 samt allem Tieferen, und ihre Masse
eps_i ~ (8/3) lambda_{i+1} deckt den Budgetbedarf des Motors i
(~ (2/3) m_i = (2/3) lambda_{i+1}) mit Faktor 4. Die Pointe der Konstruktion:
weil die rechte Seite der Bedingung 3 an JEDEM Paar B*(eps(s)+eps(t)) lautet,
verbraucht ein Motor kein Budget -- dieselbe fehlende Masse steht allen Skalen
zugleich zur Verfuegung. Rechnet man die Motoren einzeln, so gibt Skala j < i
auf Stufe i den anteiligen Gewinn min(1, eps_i/budget_j) * lambda_j * B, und
diese Anteile sind fuer alle j nahezu GLEICH (die Konversionsrate
Budget -> Gewinn ist skalenfrei); additive Interferenz hiesse also
v_i ~ i * lambda_i * B statt lambda_i * B, und das Energiegesetz
v ~ sqrt(M eps) ~ sqrt(lambda_i) waere noch einmal groesser.

Gemessen wird laengs der natuerlichen Ausschoepfung (Stufe i = Bloecke 1..i
praesent, alles Tiefere fehlt, analytischer Schwanz jenseits von N wie in
summable_lp.py jedem Gitterpunkt zugeschlagen). Kontrolle: eps = 0 gibt v = 0.
"""

import numpy as np
from summable_lp import solve_chain_missing


def build_clock(N, lam1=0.4, k=4):
    """Alle N Bloecke der Uhr: Liste (Position, Masse, Blockindex).
    Block i in (2^-i, 2^-i+1]: Praefix bei (1.2..1.6)*2^-i, schwer bei
    1.75*2^-i.  lambda_i = lam1 / k^(i-1), m_i = lambda_i/k, M_i = lambda_i."""
    atoms = []
    lam = lam1
    for i in range(1, N + 1):
        scale = 2.0 ** (-i)
        for r in range(1, k + 1):
            atoms.append(((1.2 + 0.4 * r / (k + 1)) * scale, lam / k, i))
        atoms.append((1.75 * scale, lam, i))
        lam /= k
    return atoms, lam1 / k ** (N - 1)


def stage(atoms, i, lamN, k):
    """Stufe i: Bloecke 1..i praesent.  Rueckgabe mass (aufsteigend sortiert),
    eps_grid (Konvention von solve_chain_missing: Gitter 0,a_1,s_1,...,a_n,s_n,
    eps am Schnitt s_j zaehlt die ganze Luecke bis zum naechsten Atom),
    eps_total."""
    present = sorted((x, m) for x, m, b in atoms if b <= i)
    missing = [(x, m) for x, m, b in atoms if b > i]
    tail = 2.0 * lamN / (k - 1)  # Sum_{j>N} (lambda_j + M_j), exakt geometrisch
    pos = np.array([x for x, _ in present])
    mass = np.array([m for _, m in present])
    n = len(present)
    grid_pos = np.empty(2 * n + 1)
    grid_pos[0] = 0.0
    for j in range(n):
        grid_pos[2 * j + 1] = pos[j]
        grid_pos[2 * j + 2] = pos[j + 1] if j + 1 < n else 2.0
    mx = np.array([x for x, _ in missing])
    mm = np.array([m for _, m in missing])
    order = np.argsort(mx)
    mx, mm = mx[order], mm[order]
    pref = np.concatenate([[0.0], np.cumsum(mm)])
    eps = tail + pref[np.searchsorted(mx, grid_pos, side="left")]
    return mass, eps, eps.max()


if __name__ == "__main__":
    N, k, lam1, B = 12, 4, 0.4, 1.0
    atoms, lamN = build_clock(N, lam1, k)
    Mtot = sum(m for _, m, _ in atoms) + 2.0 * lamN / (k - 1)
    print(f"Uhr: N={N} Bloecke, k={k}, lambda_1={lam1}, Gesamtmasse={Mtot:.6f}")

    print("== Kontrolle: eps = 0 gibt v = 0 ==", flush=True)
    for i in (1, 2):
        mass, eps, _ = stage(atoms, i, lamN, k)
        v = solve_chain_missing(mass, np.zeros_like(eps), B)
        print(f"  Stufe {i}: v={v:.2e}", flush=True)

    print("== Interferenztest, natuerliche Ausschoepfung ==", flush=True)
    lam = [lam1 / k ** (i - 1) for i in range(0, N + 2)]  # lam[i] = lambda_i
    for i in range(1, 7):
        mass, eps, eps_tot = stage(atoms, i, lamN, k)
        M = mass.sum()
        v = solve_chain_missing(mass, eps, B)
        # Einzelmotor-Vorhersagen: budget_j ~ (2/3)*m_j = (2/3)*lambda_{j+1},
        # anteiliger Gewinn min(1, eps/budget_j)*lambda_j*B, additiv summiert.
        additive = sum(min(1.0, eps_tot / ((2.0 / 3.0) * lam[j + 1])) * lam[j] * B
                       for j in range(1, i + 1))
        print(f"  Stufe {i}: n={len(mass)} eps={eps_tot:.3e} v={v:.6f}  "
              f"v/(lam_i B)={v / (lam[i] * B):.3f}  "
              f"v/additiv={v / additive:.3f}  "
              f"v/sqrt(M eps)={v / np.sqrt(M * eps_tot):.3f}", flush=True)
