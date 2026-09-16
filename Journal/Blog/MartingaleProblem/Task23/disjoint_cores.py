r"""Lauf 33, Nachtrag: die unendliche disjunkte Vereinigung endlicher Kerne.

Theorem 41 (Protokoll): m_0 = 0, delta = 0 auf W.  Gibt es unendlich viele
v_n in W mit Psi(t*, v_n) = 0 und paarweise disjunkten T_{<v_n} \ {0}, so ist
delta(t*) = 0 -- denn (diamondsuit) an (v_n, t*) gibt psi(T_{<v_n}) = theta fuer
psi(a) = m_a kappa(a, t*), und sum_n theta muss konvergieren.

Lemma C: sind alle nicht-minimalen Punkte von W kettenueberdeckt, so ist
kappa(u, z) = 0 fuer nicht-minimale u und minimale z, und fuer jeden Punkt v
der Hoehe eins (T_{<v} in M + {0}) ist Psi(t*, v) = sum_a m_a kappa(a, v) = 0.

Geprueft wird die endliche Mechanik auf Trunkierungen W_n OHNE Spitze der
disjunkten Vereinigung von k Doppelschleifen mit Ketten (auch mit resonanten
Massen m_r = m_s), exakt in Fraction:

  (A)  kappa(u, z) erzwungen 0 fuer alle nicht-minimalen, in W_n
       kettenueberdeckten u (d.h. u nicht maximal in W_n) und minimalen z;
  (B)  fuer jedes v der Hoehe eins (die a_n, a'_n):  sum_{a in D_n} m_a
       kappa(a, v) erzwungen 0, wobei D_n die minimalen Atome und die
       nicht-minimalen a umfasst, deren Ueberdecker a' in W_n selbst
       ueberdeckt ist (der Beweisschritt m_a kappa(a,v) = Psi(a',v) - Psi(a,v)
       = -Psi(v,a') + Psi(v,a) braucht Lemma A fuer a' und a).  Im unendlichen
       W ist D = W; in W_n fehlen die obersten zwei Kettenpunkte je Kette.
       Eine erste Fassung der Probe hatte D_n = W_n \ max und fiel genau an
       den vorletzten Kettenpunkten -- erwartet, nicht ein Fehler des Lemmas;
  (C)  Kontrolle: fuer v = ein Kettenpunkt c_1 (Hoehe > 1) ist dieselbe Summe
       i.a. NICHT erzwungen -- die Hoehe-eins-Bedingung ist nicht leer.
  (D)  Kontrolle des Orakels: antisym.check_diamond.
"""
import random
import sys
from fractions import Fraction

from posetsearch import rank
from antisym import system as diamond_system, check_diamond
from ideal_exhaustion import closure, is_forced, maximal, psi_row_single
from bowties import with_chains


def disjoint_bowties(k, n, resonant, rng):
    """k Doppelschleifen (p,q,r < a; p,q,s < a'), je Ketten der Laenge n ueber a, a'."""
    N0 = 1
    edges = []
    hooks = []
    cores = []
    for _ in range(k):
        p, q, r, s, a, a2 = range(N0, N0 + 6)
        edges += [(0, x) for x in (p, q, r, s, a, a2)]
        edges += [(p, a), (q, a), (r, a), (p, a2), (q, a2), (s, a2)]
        hooks += [a, a2]
        cores.append((p, q, r, s, a, a2))
        N0 += 6
    N, edges, chain_pts = with_chains(N0, edges, hooks, n)
    m = [Fraction(0)]
    for (p, q, r, s, a, a2) in cores:
        mp, mq, mr = (Fraction(rng.randint(1, 9), rng.randint(1, 7)) for _ in range(3))
        ms = mr if resonant else mr + Fraction(rng.randint(1, 5))
        ma, ma2 = (Fraction(rng.randint(1, 9), rng.randint(1, 7)) for _ in range(2))
        m += [mp, mq, mr, ms, ma, ma2]
    m += [Fraction(rng.randint(1, 9), rng.randint(1, 7)) for _ in chain_pts]
    return N, edges, m, cores, chain_pts


def run(k, n, resonant, rng):
    N, edges, m, cores, chain_pts = disjoint_bowties(k, n, resonant, rng)
    lt, down = closure(N, edges)
    pts = list(range(N))
    rows, idx, ncol = diamond_system(pts, down, m)
    base = rank(rows, ncol)
    mx = maximal(N, lt)
    M = [z for z in pts if z != 0 and down[z] == [0]]
    Nn = [u for u in pts if u != 0 and u not in M]
    def covered(u):
        return any(sorted(down[w]) == sorted(down[u] + [u]) for w in pts)
    ok = True
    cntA = 0
    for u in Nn:
        if not covered(u):
            continue
        for z in M:
            r = psi_row_single(u, z, m, idx, ncol)
            if not is_forced(rows, base, ncol, r):
                ok = False
                print('   AUSFALL (A): kappa(%d,%d) frei' % (u, z))
            cntA += 1
    height1 = [v for v in Nn if all(a == 0 or a in M for a in down[v])]
    def doubly_covered(a):
        if a in M:
            return True
        for w in pts:
            if sorted(down[w]) == sorted(down[a] + [a]) and covered(w):
                return True
        return False
    D = [a for a in pts if a != 0 and doubly_covered(a)]
    cntB = 0
    for v in height1:
        r = [Fraction(0)] * ncol
        for a in D:
            r = [x + y for x, y in zip(r, psi_row_single(a, v, m, idx, ncol))]
        if not is_forced(rows, base, ncol, r):
            ok = False
            print('   AUSFALL (B): Summe fuer v=%d frei' % v)
        cntB += 1
    free_ctrl = 0
    ctrl = [c for c in chain_pts if c not in mx]
    for v in ctrl:
        r = [Fraction(0)] * ncol
        for a in pts:
            if a in mx or a == 0:
                continue
            r = [x + y for x, y in zip(r, psi_row_single(a, v, m, idx, ncol))]
        if not is_forced(rows, base, ncol, r):
            free_ctrl += 1
    print('  k=%d Kerne, n=%d, %s: (A) %d Paare erzwungen: %s; (B) %d Hoehe-eins-Punkte, |D_n|=%d von %d, Summe erzwungen: %s;'
          ' (C) Kontrolle Kettenpunkte: frei in %d/%d' % (k, n, 'resonant' if resonant else 'generisch',
                                                         cntA, ok, cntB, len(D), N - 1, ok, free_ctrl, len(ctrl)))
    return ok


def main():
    rng = random.Random(41)
    rc = 0
    print('== (D) Kontrolle des Orakels')
    if not check_diamond():
        rc = 1
    for k in (1, 2, 3):
        for n in (2, 3):
            for resonant in (False, True):
                if k == 3 and n == 3:
                    continue
                if not run(k, n, resonant, rng):
                    rc = 1
    print('rc =', rc)
    return rc


if __name__ == '__main__':
    sys.exit(main())
