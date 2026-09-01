"""Fensterprobe zur omega*-Skizze (zwölfter Lauf).

Eine ZZ-Kette hat keinen Boden; jedes Atom hat Nachbarn. Trunkiert man auf ein
Fenster von n Indizes, so stehen die Relationen (*) nur an (i,j) mit
i,j <= n-2 zur Verfügung (kein Index ist "erster", der Rand ist frei). Die
Behauptung der Skizze: die Zwei-Diagonalen-Induktion braucht keinen Boden,
also ist w = 0 auf allen inneren Paaren erzwungen, obwohl die Randpaare frei
bleiben. Genau das prüft dieses Skript symbolisch (Massen frei, nur != 0).
"""

import sympy as sp


def check(n):
    m = sp.symbols(f"m0:{n}", nonzero=True)
    w = {}
    for i in range(n):
        for j in range(n):
            if i == j:
                w[i, j] = sp.Integer(0)
            elif i > j:
                w[i, j] = sp.Symbol(f"w_{i}_{j}")
            else:
                w[i, j] = -sp.Symbol(f"w_{j}_{i}")
    eqs = []
    for i in range(n - 1):
        for j in range(n - 1):
            eqs.append(m[j] * (w[i + 1, j] - w[i, j])
                       - m[i] * (w[i, j + 1] - w[i, j]))
    unknowns = [w[i, j] for i in range(n) for j in range(n) if i > j]
    sol = sp.solve(eqs, unknowns, dict=True)
    assert len(sol) == 1, f"erwartet eindeutige Loesung, gefunden {len(sol)}"
    s = sol[0]
    inner = [(i, j) for i in range(n - 1) for j in range(n - 1) if i > j]
    inner_zero = all(sp.simplify(w[i, j].subs(s)) == 0 for i, j in inner)
    nonzero = [(i, j) for i in range(n) for j in range(n)
               if i > j and sp.simplify(w[i, j].subs(s)) != 0]
    return inner_zero, nonzero


if __name__ == "__main__":
    for n in (5, 6, 7):
        inner_zero, nonzero = check(n)
        print(f"n={n}: w=0 auf allen inneren Paaren: {inner_zero}; "
              f"nicht erzwungene Paare: {nonzero}")
