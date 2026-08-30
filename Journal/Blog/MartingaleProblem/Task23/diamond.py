r"""Der Diamant 0 < a,b < 1: der kleinste Index mit unvergleichbaren Atomen.

`rem:atomicdual` sagt zu diesem Index: "the three relations along [0,t*),
[a,t*) and [b,t*) force m_a gamma(a,t) = m_b gamma(b,t) = 0 and the conclusion
is immediate".  Dieses Skript prueft beides nach, und zwar ohne jede Annahme
ueber die Gestalt der Loesung: es baut das volle homogene System, das
(eq:incrementrep) den Unbekannten (Phi, gamma) auferlegt, und rechnet in dessen
Kern.

  (1) Bei positiven Massen gilt die Dualitaet -- aber m_a gamma(a,t) ist NICHT
      Null erzwungen.  Die im Manuskript genannte Begruendung traegt also nicht;
      die Behauptung tut es.
  (2) Bei m_a + m_b = 0 faellt die Dualitaet.  Das ist keine Uhr (eine Uhr ist
      ein Mass, ihre Atome haben positive Masse), aber es zeigt, dass der
      Halbordnungsfall mehr braucht als `lem:atomgrid`: dort genuegt m_i != 0.

Die Relationen werden am Schluss Zeile fuer Zeile nachgerechnet, unabhaengig von
der linearen Algebra, die den Zeugen geliefert hat.
"""
import sys

import sympy as sp

PTS = ['0', 'a', 'b', '1']
LE = {('0', '0'), ('a', 'a'), ('b', 'b'), ('1', '1'),
      ('0', 'a'), ('0', 'b'), ('0', '1'), ('a', '1'), ('b', '1')}


def le(x, y):
    return (x, y) in LE


def down(s):                                  # T_{<s}
    return [u for u in PTS if le(u, s) and not le(s, u)]


def interval(s, s2):                          # [s,s') = T_{<s'} \ T_{<s}
    d = set(down(s))
    return [u for u in down(s2) if u not in d]


def build(m):
    idx = {}
    for kind in ('P', 'g'):
        for s in PTS:
            for t in PTS:
                idx[(kind, s, t)] = len(idx)
    rows = []
    for s in PTS:
        for s2 in PTS:
            if not le(s, s2) or s == s2:
                continue
            iv = interval(s, s2)
            for t in PTS:
                r = [sp.Integer(0)] * len(idx)
                r[idx[('P', s2, t)]] += 1
                r[idx[('P', s, t)]] -= 1
                for x in iv:
                    r[idx[('g', x, t)]] -= m[x]
                rows.append(r)
                r = [sp.Integer(0)] * len(idx)
                r[idx[('P', t, s2)]] += 1
                r[idx[('P', t, s)]] -= 1
                for x in iv:
                    r[idx[('g', t, x)]] -= m[x]
                rows.append(r)
    return sp.Matrix(rows).nullspace(), idx


def recheck(m, Phi, gam):
    """Alle Relationen aus (eq:incrementrep) direkt nachrechnen."""
    bad = []
    for s in PTS:
        for s2 in PTS:
            if not le(s, s2) or s == s2:
                continue
            iv = interval(s, s2)
            for t in PTS:
                lhs = Phi[(s2, t)] - Phi[(s, t)]
                rhs = sum(m[x] * gam[(x, t)] for x in iv)
                if sp.simplify(lhs - rhs) != 0:
                    bad.append(('1.', s, s2, t))
                lhs = Phi[(t, s2)] - Phi[(t, s)]
                rhs = sum(m[x] * gam[(t, x)] for x in iv)
                if sp.simplify(lhs - rhs) != 0:
                    bad.append(('2.', s, s2, t))
    return bad


def table(name, f):
    print('    %s:' % name)
    print('        ' + ' '.join('%6s' % t for t in PTS))
    for s in PTS:
        print('     %2s ' % s + ' '.join('%6s' % f[(s, t)] for t in PTS))


def masses(ma, mb, m1=1):
    return {'0': sp.Integer(0), 'a': sp.Integer(ma),
            'b': sp.Integer(mb), '1': sp.Integer(m1)}


def report(ma, mb):
    m = masses(ma, mb)
    basis, idx = build(m)
    print('m_a = %s, m_b = %s   (m_0 = 0, m_1 spielt keine Rolle)' % (ma, mb))
    print('    Dimension des Loesungsraums: %d' % len(basis))

    free_dual = [v for v in basis
                 if v[idx[('P', '1', '0')]] != v[idx[('P', '0', '1')]]]
    free_gam = [v for v in basis if any(v[idx[('g', 'a', t)]] for t in PTS)]
    print('    Phi(1,0) - Phi(0,1) frei?   %s' % ('JA' if free_dual else 'nein'))
    print('    m_a gamma(a,.) = 0 erzwungen? %s'
          % ('nein' if free_gam else 'ja'))
    return basis, idx, m, free_dual, free_gam


def main():
    print(__doc__.strip().splitlines()[0])
    print()
    print('(1) Positive Massen.')
    basis, idx, m, free_dual, free_gam = report(1, 2)
    ok = (not free_dual) and bool(free_gam)
    if free_gam:
        v = free_gam[0]
        Phi = {(s, t): v[idx[('P', s, t)]] for s in PTS for t in PTS}
        gam = {(s, t): v[idx[('g', s, t)]] for s in PTS for t in PTS}
        print('    Ein Kernvektor mit gamma(a,.) != 0:')
        table('Phi', Phi)
        table('gamma', gam)
        bad = recheck(m, Phi, gam)
        print('    Relationen nachgerechnet: %s'
              % ('alle erfuellt' if not bad else 'VERLETZT bei %s' % bad[:3]))
        print('    Phi(1,0) = %s, Phi(0,1) = %s  -- Dualitaet gilt trotzdem.'
              % (Phi[('1', '0')], Phi[('0', '1')]))
        ok &= not bad

    print()
    print('(2) m_a + m_b = 0.')
    basis, idx, m, free_dual, free_gam = report(1, -1)
    ok &= bool(free_dual)
    if free_dual:
        v = free_dual[0]
        Phi = {(s, t): v[idx[('P', s, t)]] for s in PTS for t in PTS}
        gam = {(s, t): v[idx[('g', s, t)]] for s in PTS for t in PTS}
        print('    Ein Gegenbeispiel zur Dualitaet:')
        table('Phi', Phi)
        table('gamma', gam)
        bad = recheck(m, Phi, gam)
        print('    Relationen nachgerechnet: %s'
              % ('alle erfuellt' if not bad else 'VERLETZT bei %s' % bad[:3]))
        print('    Phi(1,0) = %s, Phi(0,1) = %s  -- Defekt %s.'
              % (Phi[('1', '0')], Phi[('0', '1')],
                 Phi[('1', '0')] - Phi[('0', '1')]))
        ok &= not bad
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
