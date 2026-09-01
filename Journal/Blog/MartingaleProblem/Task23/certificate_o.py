"""Ausgeschriebene Zeugen gegen die o-Fassung des Halbordnungssatzes.

Nicht ein Rangvergleich, sondern ein hingeschriebenes Paar (Phi, gamma): es
erfuellt beide Zuwachsdarstellungen \\eqref{eq:incrementrep} unter iota = o auf
allen vergleichbaren Paaren und hat Phi(t*,0) != Phi(0,t*).  Wer den Zeugen
nachrechnen will, braucht dieses Skript nicht -- er braucht die Tabelle, die es
druckt.

Zwei Zeugen:

  * der **Diamant** 0 < a, b < c mit m_a = 1, m_b = 4, m_c = 2, der kleinste
    ueberhaupt (vier Punkte, drei Atome; siehe `odiamond.py` fuer die Bedingung
    m_c^2 = m_a m_b, die ihn erzeugt), und
  * der Zeuge auf fuenf Punkten mit Massen aus {0,1,2}, den `ocounter.sweep_o_full`
    beim erschoepfenden Durchgang zuerst findet.

Aufruf:  python3 certificate_o.py
"""

from fractions import Fraction

import posetsearch
import selfadjoint
from oconvention import down_o

DIAMOND = ('Diamant 0 < a, b < c  (a=1, b=2, c=3)',
           {0: [], 1: [0], 2: [0], 3: [0, 1, 2]},
           {0: 0, 1: 1, 2: 4, 3: 2})

FIVE = ('4 < 3 < 1,  2 < 1,  4 < 1',
        {0: [], 1: [0, 2, 3, 4], 2: [0], 3: [0, 4], 4: [0]},
        {0: 0, 1: 1, 2: 1, 3: 1, 4: 2})


def build(pts, down, m):
    do = down_o(pts, down)
    rows, idx, ncol = posetsearch.system(pts, do, m, 0)
    ker = selfadjoint.nullspace(rows, ncol)

    def defect(v, t):
        return sum(m[a] * (v[idx[(a, 0)]] - v[idx[(0, a)]]) for a in do[t])

    for v in ker:
        if any(defect(v, t) for t in pts):
            return do, {(s, t): v[idx[(s, t)]] for s in pts for t in pts}
    return do, None


def phi_from(pts, do, m, gamma):
    """Phi(s,t) = sum_{a in (0,s]} m_a gamma(a,t) + sum_{b in (0,t]} m_b gamma(0,b);
    das ist (I) mit Phi(0,t) aus (II) und der Normierung Phi(0,0) = 0."""
    return {(s, t): sum(m[a] * gamma[(a, t)] for a in do[s])
                    + sum(m[b] * gamma[(0, b)] for b in do[t])
            for s in pts for t in pts}


def check(pts, down, do, m, gamma, phi):
    """Beide Zuwachsdarstellungen, auf jedem vergleichbaren Paar."""
    leq = {(a, b) for b in pts for a in [b] + list(down[b])}
    bad = []
    for s in pts:
        for s2 in pts:
            if (s, s2) not in leq:
                continue
            iv = sorted(set(do[s2]) - set(do[s]))
            for t in pts:
                if phi[(s2, t)] - phi[(s, t)] != sum(m[a] * gamma[(a, t)]
                                                     for a in iv):
                    bad.append(('erste', s, s2, t))
                if phi[(t, s2)] - phi[(t, s)] != sum(m[a] * gamma[(t, a)]
                                                     for a in iv):
                    bad.append(('zweite', s, s2, t))
    return bad


def show(label, down, mass):
    pts = sorted(down)
    m = {x: Fraction(v) for x, v in mass.items()}
    print('=== %s' % label)
    print('    Massen %s,  (0,s] = %s'
          % ({k: str(v) for k, v in m.items()},
             {s: down_o(pts, down)[s] for s in pts}))
    do, gamma = build(pts, down, m)
    if gamma is None:
        print('    kein Zeuge')
        return False
    phi = phi_from(pts, do, m, gamma)
    print('    gamma (Zeile s, Spalte t):')
    for s in pts:
        print('       ', [str(gamma[(s, t)]) for t in pts])
    print('    Phi (Zeile s, Spalte t):')
    for s in pts:
        print('       ', [str(phi[(s, t)]) for t in pts])
    bad = check(pts, down, do, m, gamma, phi)
    print('    Zuwachsdarstellungen auf allen vergleichbaren Paaren: %s'
          % ('erfuellt' if not bad else 'VERLETZT bei %s' % bad[:3]))
    for t in pts:
        d = phi[(t, 0)] - phi[(0, t)]
        if d:
            print('    Defekt bei t = %s:  Phi(t,0) - Phi(0,t) = %s - %s = %s'
                  % (t, phi[(t, 0)], phi[(0, t)], d))
    ok = (not bad) and any(phi[(t, 0)] != phi[(0, t)] for t in pts)
    print('    Zeuge gueltig:', ok)
    return ok


def main():
    ok = True
    for label, down, mass in (DIAMOND, FIVE):
        ok &= show(label, down, mass)
        print()
    print('Alle Zeugen gueltig:', ok)
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
