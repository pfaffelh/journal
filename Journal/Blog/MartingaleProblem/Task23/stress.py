r"""Stichprobe jenseits der vollstaendigen Aufzaehlung: zufaellige Halbordnungen
auf sechs bis acht Punkten mit nichtnegativen Massen.

`selfadjoint.py` zaehlt vollstaendig auf, kommt damit aber nur bis fuenf Punkte.
Ein Fehler, der erst bei groesseren Halbordnungen auftraete -- etwa in der
Konstruktion von T, wo die Laenge r der Potenzkette eingeht --, bliebe dort
unsichtbar.  Dieses Skript prueft beides an zufaelligen Halbordnungen: dass die
Dualitaet nie faellt und dass die explizite Formel liefert, was sie soll.
"""
import random
import sys
from fractions import Fraction

from antisym import duality_fails_at
from selfadjoint import matV, explicit_T, transpose, matmul, is_sym


def rand_poset(rnd, n):
    """Zufaellige Halbordnung auf {0,..,n-1}: Kanten nur aufwaerts, dann
    transitive Huelle -- Antisymmetrie und Transitivitaet sind damit gratis."""
    lt = set()
    for a in range(n):
        for b in range(a + 1, n):
            if rnd.random() < 0.35:
                lt.add((a, b))
    changed = True
    while changed:
        changed = False
        for (a, b) in list(lt):
            for (c, d) in list(lt):
                if b == c and (a, d) not in lt:
                    lt.add((a, d))
                    changed = True
    down = {x: sorted(y for y in range(n) if (y, x) in lt) for x in range(n)}
    return list(range(n)), down


def run(sizes=(6, 7, 8), trials=40, seed=20260831):
    rnd = random.Random(seed)
    tot = dual_bad = formula_bad = 0
    for n in sizes:
        for _ in range(trials):
            pts, down = rand_poset(rnd, n)
            m = {i: Fraction(rnd.choice([0, 1, 2, 5, 7])) for i in pts}
            tot += 1
            if duality_fails_at(pts, down, m) is not None:
                dual_bad += 1
            V = matV(n, down, m)
            VT = transpose(V)
            for t in pts:
                T = explicit_T(V, t)
                ok = (is_sym(T)
                      and all(sum(T[i]) == (1 if i == t else 0) for i in range(n))
                      and matmul(T, V) == matmul(VT, T))
                if not ok:
                    formula_bad += 1
    print('Halbordnungen auf %s Punkten, je %d zufaellige, m >= 0: %d Faelle, '
          '%d Dualitaetsausfaelle, %d Formelausfaelle'
          % (list(sizes), trials, tot, dual_bad, formula_bad))
    return dual_bad == 0 and formula_bad == 0


if __name__ == '__main__':
    sys.exit(0 if run() else 1)
