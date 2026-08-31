"""Die o-Konvention faellt auf einer Halbordnung: der Zeuge, im vollen System.

Der siebte Lauf (2026-08-31) hielt die o-Fassung des Halbordnungssatzes fuer
"verified, not proved": `oconvention.sweep_o` fand auf bis zu fuenf Punkten
keinen Ausfall.  Auf fuenf Punkten lief der Sweep aber nur ueber Massen aus
{0,1}, und genau dort liegt der Zeuge nicht.  Dieses Skript stellt ihn
unabhaengig fest -- nicht im reduzierten System (*) in gamma allein, sondern im
**vollen** homogenen System in (Phi, gamma), wie `poset2.full_system` es baut,
nur mit dem Intervall (s,s'] statt [s,s').

Aufruf:  python3 ocounter.py
"""

import itertools
from fractions import Fraction

import posetsearch
from oconvention import down_o


# --------------------------------------------------------------- das volle System

def full_rows_o(pts, down, m):
    """Zeilen des vollen Systems zu (eq:incrementrep) unter iota = o.

    Fuer s <= s' und jedes t:
        Phi(s',t) - Phi(s,t) = sum_{a in (s,s']} m_a gamma(a,t)
        Phi(t,s') - Phi(t,s) = sum_{a in (s,s']} m_a gamma(t,a)
    """
    n = len(pts)
    idx = {}
    for kind in ('P', 'g'):
        for s in pts:
            for t in pts:
                idx[(kind, s, t)] = len(idx)
    ncol = len(idx)
    do = down_o(pts, down)
    leq = {(a, b) for b in pts for a in ([b] + list(down[b]))}
    rows = []
    for s in pts:
        for s2 in pts:
            if s == s2 or (s, s2) not in leq:
                continue
            iv = sorted(set(do[s2]) - set(do[s]))
            for t in pts:
                r = [Fraction(0)] * ncol
                r[idx[('P', s2, t)]] += 1
                r[idx[('P', s, t)]] -= 1
                for a in iv:
                    r[idx[('g', a, t)]] -= m[a]
                rows.append(r)
                r = [Fraction(0)] * ncol
                r[idx[('P', t, s2)]] += 1
                r[idx[('P', t, s)]] -= 1
                for a in iv:
                    r[idx[('g', t, a)]] -= m[a]
                rows.append(r)
    return rows, idx, ncol


def duality_full_o(pts, down, m, bottom=0):
    """Erstes t, an dem Phi(t,0) = Phi(0,t) im vollen System nicht erzwungen
    ist; None, wenn die Dualitaet ueberall gilt."""
    rows, idx, ncol = full_rows_o(pts, down, m)
    base = posetsearch.rank(rows, ncol)
    for t in pts:
        d = [Fraction(0)] * ncol
        d[idx[('P', t, bottom)]] += 1
        d[idx[('P', bottom, t)]] -= 1
        if posetsearch.rank(rows + [d], ncol) != base:
            return t
    return None


# ----------------------------------------------------------------- der Zeuge

WITNESS_DOWN = {0: [], 1: [0, 2, 3, 4], 2: [0], 3: [0, 4], 4: [0]}
WITNESS_M = {0: 0, 1: 1, 2: 1, 3: 1, 4: 2}


def show_witness():
    pts = sorted(WITNESS_DOWN)
    m = {x: Fraction(v) for x, v in WITNESS_M.items()}
    print('Zeuge: 4 < 3 < 1, 2 < 1, 4 < 1; 0 kleinstes Element')
    print('Massen: m_0 = 0, m_1 = m_2 = m_3 = 1, m_4 = 2')
    t_full = duality_full_o(pts, WITNESS_DOWN, m)
    t_red = posetsearch.duality_holds(pts, down_o(pts, WITNESS_DOWN), m, 0)
    print('  volles System in (Phi, gamma): %s'
          % ('Dualitaet gilt' if t_full is None else 'FAELLT bei t = %s' % t_full))
    print('  reduziertes System (*):        %s'
          % ('Dualitaet gilt' if t_red is None else 'FAELLT bei t = %s' % t_red))
    print('  beide Wege einig:', (t_full is None) == (t_red is None))
    # Zum Vergleich: unter iota = p traegt derselbe Fall.
    t_p = posetsearch.duality_holds(pts, WITNESS_DOWN, m, 0)
    print('  dieselbe Uhr unter iota = p:   %s'
          % ('Dualitaet gilt' if t_p is None else 'FAELLT bei t = %s' % t_p))
    return t_full is not None and t_red is not None


def sweep_o_full(n, grid):
    """Alle Halbordnungen mit kleinstem Element, alle nichtnegativen Massen aus
    dem Gitter -- beide Wege, und wo sie ausfallen."""
    tested = fails = 0
    bad = []
    for pts, down, lt in posetsearch.posets_with_bottom(n):
        do = down_o(pts, down)
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            tested += 1
            t = posetsearch.duality_holds(pts, do, m, 0)
            if t is not None:
                fails += 1
                if len(bad) < 5:
                    bad.append((dict(down), dict(m), t))
    print('o-Konvention, n = %d, Massen aus %s: %d Faelle, %d Ausfaelle'
          % (n, list(grid), tested, fails))
    for w in bad:
        print('    AUSFALL: down=%s m=%s t=%s' % w)
    return fails


def smallest_failures(n, grid):
    """Die Ausfaelle, nach Zahl der Punkte mit m > 0 geordnet."""
    out = []
    for pts, down, lt in posetsearch.posets_with_bottom(n):
        do = down_o(pts, down)
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            m[0] = Fraction(0)
            t = posetsearch.duality_holds(pts, do, m, 0)
            if t is not None:
                out.append((sum(1 for x in pts if m[x]), dict(down), dict(m), t))
    out.sort(key=lambda w: w[0])
    return out


if __name__ == '__main__':
    ok = show_witness()
    print()
    for n, grid in ((3, (0, 1, 2)), (4, (0, 1, 2, 3)), (5, (0, 1, 2))):
        sweep_o_full(n, grid)
    print()
    small = smallest_failures(4, (0, 1, 2, 3))
    print('Ausfaelle auf vier Punkten, Massen aus 0..3: %d' % len(small))
    for w in small[:5]:
        print('    %d Massen != 0: down=%s m=%s t=%s' % w)
    print()
    print('Zeuge bestaetigt:', ok)
