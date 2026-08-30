r"""Der Fall unvergleichbarer Atome: T = {0,1,2}^2 mit der Produktordnung.

`prop:atomicdual` verlangt, dass die Atome unter t^* eine Kette bilden.  Das
Manuskript hatte den zweidimensionalen Index {0,1,2}^2 als symbolisch geprueft
vermerkt; dieses Skript prueft ihn nach, und zwar ohne Annahme ueber die Gestalt
der Loesung.

Anders als im Kettenfall werden ALLE Relationen aus (eq:incrementrep)
aufgestellt, also fuer jedes vergleichbare Paar s <= s', nicht nur fuer
Einschrittintervalle: in einem Verband folgen die uebrigen nicht durch
Teleskopieren entlang einer einzigen Kette.

    T_{<s}  = {u : u <= s, u != s}          (Halbordnung, also ohne Aequivalente)
    [s,s')  = T_{<s'} \ T_{<s}
    Phi(s',t) - Phi(s,t) = sum_{a in [s,s')} m_a gamma(a,t)
    Phi(s,t') - Phi(s,t) = sum_{a in [t,t')} m_a gamma(s,a)

Befund (2026-08-30).  Die Dualitaetsidentitaet Phi(t,0) = Phi(0,t) gilt fuer
jedes t und fuer alle drei Massenwahlen -- die Notiz des Manuskripts stimmt.
Die **Symmetrie** Phi(s,t) = Phi(t,s) gilt hier jedoch **nicht**; sie faellt an
den unvergleichbaren und den maximalen Punkten aus.  Ein Beweis fuer den
allgemeinen Praeordnungsfall kann also nicht ueber die Symmetrie laufen, die im
Kettenfall (lem:atomgrid) das ganze Argument traegt.
"""
import sympy as sp

K = 3
PTS = [(i, j) for i in range(K) for j in range(K)]
ZERO = (0, 0)


def le(a, b):
    return a[0] <= b[0] and a[1] <= b[1]


def lt_set(s):                       # T_{<s}
    return [u for u in PTS if le(u, s) and u != s]


def interval(s, s2):                 # [s,s')
    return sorted(set(lt_set(s2)) - set(lt_set(s)))


def run(masses, label):
    m = dict(zip(PTS, masses))
    m[ZERO] = sp.Integer(0)          # das kleinste Element traegt kein Atom
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
            for t in PTS:
                r = [sp.Integer(0)] * len(idx)
                r[idx[('P', s2, t)]] += 1
                r[idx[('P', s, t)]] -= 1
                for a in interval(s, s2):
                    r[idx[('g', a, t)]] -= m[a]
                rows.append(r)
                r = [sp.Integer(0)] * len(idx)
                r[idx[('P', t, s2)]] += 1
                r[idx[('P', t, s)]] -= 1
                for a in interval(s, s2):
                    r[idx[('g', t, a)]] -= m[a]
                rows.append(r)
    basis = sp.Matrix(rows).nullspace()
    val = lambda v, kind, s, t: v[idx[(kind, s, t)]]
    bad_dual = sorted({t for v in basis for t in PTS
                       if val(v, 'P', t, ZERO) != val(v, 'P', ZERO, t)})
    bad_sym = sorted({(s, t) for v in basis for s in PTS for t in PTS
                      if val(v, 'P', s, t) != val(v, 'P', t, s)})
    print('%s: dim=%d\n    Phi(t,0) = Phi(0,t) verletzt bei: %s\n'
          '    Phi unsymmetrisch bei:            %s'
          % (label, len(basis), bad_dual or 'nirgends', bad_sym or 'nirgends'))
    return not bad_dual


if __name__ == '__main__':
    import sys
    ok = True
    ok &= run([sp.Integer(1)] * 9, 'gleiche Massen        ')
    ok &= run([sp.Integer(k) for k in [1, 3, 5, 2, 7, 11, 4, 13, 6]],
              'ganzzahlig verschieden')
    ok &= run([sp.Rational(1, k) for k in [1, 2, 5, 3, 7, 11, 4, 9, 13]],
              'Stammbrueche          ')
    sys.exit(0 if ok else 1)
