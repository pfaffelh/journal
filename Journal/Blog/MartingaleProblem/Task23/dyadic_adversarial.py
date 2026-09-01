"""Task 23, dreizehnter Lauf, Folgeexperiment: realisierbare steigende Profile.

Der zwoelfte Lauf mass die dyadische Uhr nur mit levelweise konstanten,
geometrisch fallenden Massen und fand v_J -> 0. Der Verstaerkungsmechanismus
dieses Laufs (leichte Atome unter schweren) legt Profile nahe, die nach rechts
wachsen: m(k/2^j) = (k/2^j)^p * r^{-j}, summierbar fuer r > 2. Das Residuum ist
das echte Trunkierungsresiduum eta_J = 2*B*(Schwanzmasse ueber Level J).

Frage: kollabiert v_J auch dort? Wenn nein, ist das Richtung Gegenbeispiel zur
Dualitaet selbst (nicht nur zur Energieschranke).
"""

import numpy as np
from fractions import Fraction
from energy_lp import solve_chain


def dyadic_instance(J, massfun, levelbound, Jtail=22):
    """Atome k/2^j, j<=J; Masse massfun(x, j). Schwanz vektorisiert bis Jtail
    summiert; die Level darueber sind durch levelbound(j) (obere Schranke der
    Levelmasse) abgeschaetzt, geometrisch aufsummiert via Quotient 1/2."""
    atoms = []
    for j in range(1, J + 1):
        for k in range(1, 2 ** j, 2):
            x = k / 2 ** j
            atoms.append((Fraction(k, 2 ** j), massfun(x, j)))
    atoms.sort()
    mass = np.array([m for _, m in atoms])
    tail = 0.0
    for j in range(J + 1, Jtail + 1):
        ks = np.arange(1, 2 ** j, 2, dtype=float)
        tail += massfun(ks / 2 ** j, j).sum()
    # Rest: Levelmassen fallen bei r >= 3 mindestens mit Quotient 2/3; nach
    # oben: Summe ueber die Level > Jtail <= 3 * levelbound(Jtail+1).
    tail += 3.0 * levelbound(Jtail + 1)
    return mass, tail


# (Name, massfun(x,j), obere Schranke der Masse von Level j)
PROFILES = [
    ("x^4 * 4^-j", lambda x, j: x ** 4 * 4.0 ** (-j), lambda j: 0.5 ** j / 2),
    ("x^8 * 3^-j", lambda x, j: x ** 8 * 3.0 ** (-j),
     lambda j: (2.0 / 3.0) ** j / 2),
    ("Kontrolle 1 * 4^-j", lambda x, j: 0 * x + 4.0 ** (-j),
     lambda j: 0.5 ** j / 2),
]


if __name__ == "__main__":
    for name, f, lb in PROFILES:
        print(f"== {name} ==", flush=True)
        for J in range(2, 7):
            mass, tail = dyadic_instance(J, f, lb)
            M = mass.sum()
            eta = 2.0 * tail
            v = solve_chain(list(mass), eta)
            print(f"  J={J}: n={len(mass)} M_J={M:.4f} eta_J={eta:.3e} "
                  f"v_J={v:.5f}  v/M_J={v / M:.4f}  "
                  f"v^2/(M eta)={v * v / (M * eta):.2f}", flush=True)
