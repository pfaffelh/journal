r"""Der Zeuge, nicht nur die Antwort: welche Linearkombination der Relationen
(diamondsuit) liefert das Funktional, das verschwinden soll?

Der Rangvergleich von `antisym.py` sagt *dass* ein Funktional auf dem
Loesungsraum verschwindet.  Fuer einen Beweis braucht man *wie*: die Koeffizienten
der Linearkombination, mit symbolischen Massen, denn an ihnen liest sich das
Argument ab (am Diamanten etwa ist es der Faktor 1/(m_a+m_b), und genau dort
sitzt die Positivitaet).

Aufgestellt wird das System in kappa (antisymmetrisch, Unbekannte die Paare
i<j).  Relation zu (s,t):

    Psi(s,t) + Psi(t,s) - Psi(s,s) - Psi(t,t) = 0,   Psi(s,t) = sum_{a<s} m_a kappa(a,t).

Gesucht: lambda mit  sum_{(s,t)} lambda_{s,t} * Zeile(s,t) = Zielzeile.
"""
import sys

import sympy as sp


def kappa_index(n):
    idx, k = {}, 0
    for i in range(n):
        for j in range(i + 1, n):
            idx[(i, j)] = k
            k += 1
    return idx, k


def psi_row(s, t, down, m, idx, ncol):
    r = [sp.Integer(0)] * ncol
    for a in down[s]:
        if a == t:
            continue
        if a < t:
            r[idx[(a, t)]] += m[a]
        else:
            r[idx[(t, a)]] -= m[a]
    return r


def relations(pts, down, m, idx, ncol):
    rows, labels = [], []
    for i, s in enumerate(pts):
        for t in pts[i + 1:]:
            r = [a + b - c - d for a, b, c, d in
                 zip(psi_row(s, t, down, m, idx, ncol),
                     psi_row(t, s, down, m, idx, ncol),
                     psi_row(s, s, down, m, idx, ncol),
                     psi_row(t, t, down, m, idx, ncol))]
            if any(x != 0 for x in r):
                rows.append(r)
                labels.append((s, t))
    return rows, labels


def certificate(pts, down, m, target, name):
    """target: Zeile (Liste); sucht lambda mit lambda^T * Relationen = target."""
    n = len(pts)
    idx, ncol = kappa_index(n)
    rows, labels = relations(pts, down, m, idx, ncol)
    A = sp.Matrix(rows).T                       # ncol x nrel
    b = sp.Matrix(target)
    lam = sp.symbols('l0:%d' % len(rows))
    sol = sp.solve(list(A * sp.Matrix(lam) - b), lam, dict=True)
    if not sol:
        print('%s: kein Zeuge -- das Funktional ist auf dem Loesungsraum frei.'
              % name)
        return None
    s = sol[0]
    print('%s:' % name)
    for lb, v in zip(labels, lam):
        val = sp.simplify(s.get(v, v))
        if val != 0:
            print('    Relation %-8s * %s' % (str(lb), sp.factor(val)))
    return s


def show(pts, down, mvals, targets, title):
    print('=' * 70)
    print(title, ' down =', {k: v for k, v in down.items() if v})
    m = dict(zip(pts, mvals))
    n = len(pts)
    idx, ncol = kappa_index(n)
    for kind, a, x in targets:
        if kind == 'psi':
            tgt = psi_row(a, x, down, m, idx, ncol)
            name = 'Psi(%s,%s)' % (a, x)
        else:
            tgt = [sp.Integer(0)] * ncol
            if a < x:
                tgt[idx[(a, x)]] = sp.Integer(1)
            else:
                tgt[idx[(x, a)]] = sp.Integer(-1)
            name = 'kappa(%s,%s)' % (a, x)
        certificate(pts, down, m, tgt, name)
    print()


if __name__ == '__main__':
    m0, m1, m2, m3, m4 = sp.symbols('m0 m1 m2 m3 m4', positive=True)

    # Diamant: 0 < 1,2 < 3
    show([0, 1, 2, 3], {0: [], 1: [0], 2: [0], 3: [0, 1, 2]},
         [m0, m1, m2, m3],
         [('kappa', 1, 2), ('kappa', 0, 3), ('psi', 1, 3), ('psi', 0, 3)],
         'Diamant')

    # Kette 0 < 1 < 2
    show([0, 1, 2], {0: [], 1: [0], 2: [0, 1]}, [m0, m1, m2],
         [('kappa', 0, 2), ('kappa', 0, 1), ('psi', 1, 2)],
         'Kette')

    # W = Diamant, z darueber:  0 < 1,2 < 3 < 4
    show([0, 1, 2, 3, 4], {0: [], 1: [0], 2: [0], 3: [0, 1, 2],
                           4: [0, 1, 2, 3]}, [m0, m1, m2, m3, m4],
         [('kappa', 3, 4), ('kappa', 1, 4), ('kappa', 0, 4), ('psi', 3, 4)],
         'Diamant mit Spitze')

    # 0 < 1 < 3, 0 < 2 < 3, 0 < 1 < 4? -- N-Form: 0<1,2 ; 1<3 ; 2<3 nein:
    # W = {0,1,2} Antikette ueber 0, z = 3, und 4 ueber 3 -- Kette von Diamanten
    show([0, 1, 2, 3], {0: [], 1: [0], 2: [0, 1], 3: [0, 1, 2]},
         [m0, m1, m2, m3],
         [('kappa', 0, 3), ('kappa', 1, 3), ('psi', 2, 3)],
         'Kette mit vier Punkten')

    # drei unvergleichbare unter der Spitze
    show([0, 1, 2, 3, 4], {0: [], 1: [0], 2: [0], 3: [0],
                           4: [0, 1, 2, 3]}, [m0, m1, m2, m3, m4],
         [('kappa', 1, 2), ('kappa', 0, 4), ('psi', 1, 4)],
         'Drei Atome unter der Spitze')

    # gemischt: 0 < 1 < 2, 0 < 3, alles unter 4
    show([0, 1, 2, 3, 4], {0: [], 1: [0], 2: [0, 1], 3: [0],
                           4: [0, 1, 2, 3]}, [m0, m1, m2, m3, m4],
         [('kappa', 0, 4), ('kappa', 1, 4), ('kappa', 2, 3), ('psi', 2, 4)],
         'Kette und Atom unter der Spitze')
