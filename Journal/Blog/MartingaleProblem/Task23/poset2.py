r"""Der Fall unvergleichbarer Atome, systematisch: welche Hypothese traegt ihn?

`poset.py` prueft den einen Index {0,1,2}^2.  Dieses Skript prueft eine Familie
kleiner Halbordnungen gegen eine Familie von Massenvektoren -- darunter solche
mit **negativen** Massen --, und es tut das auf zwei unabhaengigen Wegen:

  (A) das volle homogene System in (Phi, gamma), wie `verify.py` und `poset.py`
      es bauen, und
  (B) das auf gamma reduzierte System (siehe unten), das Phi eliminiert.

Stimmen (A) und (B) ueberall ueberein, so ist die Reduktion mitgeprueft.

Die Reduktion.  Da T ein kleinstes Element 0 hat, ist T_{<0} leer, und
(eq:incrementrep) mit s = 0 bzw. t = 0 loest Phi auf:

    Phi(s,t) = Phi(0,t) + sum_{a < s} m_a gamma(a,t)              (I)
    Phi(s,t) = Phi(s,0) + sum_{b < t} m_b gamma(s,b)              (II)

Die Vertraeglichkeit von (I) und (II) ist genau

    sum_{a<s} m_a (gamma(a,t) - gamma(a,0))
        = sum_{b<t} m_b (gamma(s,b) - gamma(0,b))    fuer alle s,t    (*)

und der Defekt der Dualitaet ist

    Phi(t,0) - Phi(0,t) = sum_{a<t} m_a (gamma(a,0) - gamma(0,a)) =: delta(t).

Zu pruefen ist also: erzwingt (*) das Verschwinden von delta?

Befund, siehe __main__: fuer eine **Kette** ja, und ohne jede Bedingung an die
Vorzeichen der Massen (das ist lem:atomgrid).  Fuer eine Halbordnung mit einer
Antikette gilt es fuer positive Massen, faellt aber, sobald eine Antikette die
Gesamtmasse 0 hat.  Der kleinste Zeuge ist der Diamant {0,a,b,1} mit
m_a + m_b = 0.
"""
import itertools
import sys

import sympy as sp

# ---------------------------------------------------------------- Halbordnungen


class Poset:
    def __init__(self, name, pts, leq, bottom):
        self.name = name
        self.pts = list(pts)
        self._leq = leq
        self.bottom = bottom
        assert all(leq(bottom, x) for x in pts), 'kein kleinstes Element'

    def le(self, a, b):
        return self._leq(a, b)

    def down(self, s):                       # T_{<s} = {u <= s} \ {u : s <= u}
        return [u for u in self.pts if self.le(u, s) and not self.le(s, u)]

    def interval(self, s, s2):               # [s,s') = T_{<s'} \ T_{<s}
        d = set(self.down(s))
        return [u for u in self.down(s2) if u not in d]

    def is_chain(self):
        return all(self.le(a, b) or self.le(b, a)
                   for a in self.pts for b in self.pts)


def chain(n):
    return Poset('Kette 0..%d' % n, list(range(n + 1)),
                 lambda a, b: a <= b, 0)


def diamond():
    pts = ['0', 'a', 'b', '1']
    rel = {('0', '0'), ('a', 'a'), ('b', 'b'), ('1', '1'),
           ('0', 'a'), ('0', 'b'), ('0', '1'), ('a', '1'), ('b', '1')}
    return Poset('Diamant 0<a,b<1', pts, lambda a, b: (a, b) in rel, '0')


def vee():
    pts = ['0', 'a', 'b']
    rel = {('0', '0'), ('a', 'a'), ('b', 'b'), ('0', 'a'), ('0', 'b')}
    return Poset('V 0<a,b', pts, lambda a, b: (a, b) in rel, '0')


def grid(k):
    pts = [(i, j) for i in range(k) for j in range(k)]
    return Poset('Gitter {0..%d}^2' % (k - 1), pts,
                 lambda a, b: a[0] <= b[0] and a[1] <= b[1], (0, 0))


def cube():
    pts = list(itertools.product((0, 1), repeat=3))
    return Poset('Wuerfel {0,1}^3', pts,
                 lambda a, b: all(x <= y for x, y in zip(a, b)), (0, 0, 0))


def bowtie():
    # 0 < a,b < c,d : zwei Antiketten uebereinander
    pts = ['0', 'a', 'b', 'c', 'd']
    rel = {(x, x) for x in pts}
    rel |= {('0', x) for x in pts}
    rel |= {('a', 'c'), ('a', 'd'), ('b', 'c'), ('b', 'd')}
    return Poset('Doppelantikette', pts, lambda a, b: (a, b) in rel, '0')


# ------------------------------------------------------------------ die Systeme


def full_system(P, m):
    """(A) Volles homogenes System in (Phi, gamma); gibt (Kernbasis, Index)."""
    idx = {}
    for kind in ('P', 'g'):
        for s in P.pts:
            for t in P.pts:
                idx[(kind, s, t)] = len(idx)
    rows = []
    for s in P.pts:
        for s2 in P.pts:
            if not P.le(s, s2) or s == s2:
                continue
            iv = P.interval(s, s2)
            for t in P.pts:
                r = [sp.Integer(0)] * len(idx)
                r[idx[('P', s2, t)]] += 1
                r[idx[('P', s, t)]] -= 1
                for a in iv:
                    r[idx[('g', a, t)]] -= m[a]
                rows.append(r)
                r = [sp.Integer(0)] * len(idx)
                r[idx[('P', t, s2)]] += 1
                r[idx[('P', t, s)]] -= 1
                for a in iv:
                    r[idx[('g', t, a)]] -= m[a]
                rows.append(r)
    return sp.Matrix(rows).nullspace(), idx


def reduced_system(P, m):
    """(B) System (*) in gamma allein; gibt (Kernbasis, Index)."""
    idx = {}
    for s in P.pts:
        for t in P.pts:
            idx[(s, t)] = len(idx)
    rows = []
    for s in P.pts:
        for t in P.pts:
            r = [sp.Integer(0)] * len(idx)
            for a in P.down(s):
                r[idx[(a, t)]] += m[a]
                r[idx[(a, P.bottom)]] -= m[a]
            for b in P.down(t):
                r[idx[(s, b)]] -= m[b]
                r[idx[(P.bottom, b)]] += m[b]
            rows.append(r)
    return sp.Matrix(rows).nullspace(), idx


def check(P, m, label):
    z = P.bottom
    basis, idx = full_system(P, m)
    badA = sorted({str(t) for v in basis for t in P.pts
                   if v[idx[('P', t, z)]] != v[idx[('P', z, t)]]})
    basisB, idxB = reduced_system(P, m)
    badB = sorted({str(t) for v in basisB for t in P.pts
                   if sum(m[a] * (v[idxB[(a, z)]] - v[idxB[(z, a)]])
                          for a in P.down(t)) != 0})
    agree = (not badA) == (not badB)
    print('  %-24s voll: %-28s reduziert: %-28s %s'
          % (label,
             'Dualitaet gilt' if not badA else 'FAELLT bei ' + ','.join(badA),
             'Dualitaet gilt' if not badB else 'FAELLT bei ' + ','.join(badB),
             'ok' if agree else 'WEGE UNEINIG'))
    return (not badA), agree


MASSVEC = [
    ('gleich',            lambda n: [sp.Integer(1)] * n),
    ('positiv verschieden', lambda n: [sp.Integer(p) for p in
                                       [2, 3, 5, 7, 11, 13, 17, 19, 23][:n]]),
    ('Stammbrueche',      lambda n: [sp.Rational(1, k) for k in
                                     [1, 2, 3, 5, 7, 11, 13, 17, 19][:n]]),
    ('Vorzeichen wechselnd', lambda n: [sp.Integer(v) for v in
                                        [1, -1, 2, -2, 3, -3, 4, -4, 5][:n]]),
]


def run(P, m0_zero=True):
    print('%s  (%s)' % (P.name, 'Kette' if P.is_chain() else 'keine Kette'))
    ok = True
    for label, gen in MASSVEC:
        vals = gen(len(P.pts))
        m = dict(zip(P.pts, vals))
        if m0_zero:
            m[P.bottom] = sp.Integer(0)
        good, agree = check(P, m, label)
        ok &= agree
        if P.is_chain() and not good:
            ok = False                       # Ketten muessen immer tragen
    return ok


if __name__ == '__main__':
    ok = True
    for P in (chain(3), chain(4), vee(), diamond(), bowtie(), grid(3)):
        ok &= run(P)

    print('\nDer scharfe Zeuge: Diamant mit m_a + m_b = 0')
    D = diamond()
    for ma, mb in ((1, -1), (2, -2), (1, 1)):
        m = {'0': sp.Integer(0), 'a': sp.Integer(ma), 'b': sp.Integer(mb),
             '1': sp.Integer(1)}
        check(D, m, 'm_a=%d, m_b=%d' % (ma, mb))

    print('\nZum Vergleich: dieselben Vorzeichen auf einer Kette')
    C = chain(3)
    for v in ((1, -1, 1), (1, -1, -1), (-1, 1, 2)):
        m = dict(zip(C.pts, [sp.Integer(0)] + [sp.Integer(x) for x in v]))
        check(C, m, 'm = %s' % (v,))

    sys.exit(0 if ok else 1)
