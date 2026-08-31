r"""Die Reduktion auf beschraenkte Halbordnungen, und zwei Gegenproben.

**Der Satz.**  Ist I eine Unterhalbordnung von T, die *abwaertsabgeschlossen*
ist (ein Ordnungsideal) und das kleinste Element enthaelt, so erfuellt die
Einschraenkung von kappa auf I dieselbe Bedingung (diamondsuit), denn fuer
s in I ist T_{<s} in I enthalten, also Psi_I(s,t) = Psi(s,t) fuer s,t in I,
und die Relationen an Paaren aus I sind eine Teilmenge der Relationen auf T.
Insbesondere ist d_I(t) = d(t) fuer t in I.

Daraus folgt: eine Loesung auf T mit d(t) != 0 schraenkt sich zu einer Loesung
auf I = T_{<=t} mit demselben d(t) != 0 ein.  Also

    d(t) = 0 ist auf T erzwungen, sobald es auf T_{<=t} erzwungen ist,

und T_{<=t} hat sowohl ein kleinstes (0) als auch ein groesstes Element (t).
Der Fall unvergleichbarer Atome ist damit auf **beschraenkte** Halbordnungen
zurueckgefuehrt, und dort ist nur der Defekt an der Spitze offen: fuer jedes
s < t ist T_{<=s} echt kleiner, also greift die Induktion ueber |T|.

Dieses Skript prueft zweierlei exakt in Bruchrechnung:

 (1) Die Richtung, die der Satz behauptet -- faellt d(t) auf T, so faellt es
     auch auf T_{<=t}.  Ein Ausfall waere ein Fehler im Beweis oben.

 (2) Ob die Reduktion **verlustfrei** ist, also ob umgekehrt jedes auf T_{<=t}
     freie d(t) auch auf T frei bleibt.  Das behauptet der Satz nicht; die
     Antwort sagt, wie viel die Reduktion wegwirft.

Dazu die Verschaerfung der widerlegten Vermutung (C4) aus `antisym.py`:
Psi(a,x) = 0 fuer a < x ist bei nichtnegativen Massen falsch (Zeuge dort),
und hier wird nachgesehen, ob sie bei **strikt positiven** Massen haelt.
"""
import itertools
import random
import sys
from fractions import Fraction

from antisym import (posets_with_bottom, psi_row, rank, support_fails_at,
                     system, vanishes)


def sweep(n, grid, probe, label, m0=None):
    tested = fails = 0
    bad = []
    for pts, down, _ in posets_with_bottom(n):
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            if m0 is not None:
                m[0] = Fraction(m0)
            tested += 1
            w = probe(pts, down, m)
            if w is not None:
                fails += 1
                if len(bad) < 3:
                    bad.append((dict(down), dict(m), w))
    print('n = %d, %s, Massen aus %s: %d Faelle, %d Ausfaelle'
          % (n, label, list(grid), tested, fails))
    for d_, m_, w_ in bad:
        print('    AUSFALL: down=%s m=%s bei %s'
              % (d_, {k: str(v) for k, v in m_.items()}, w_))
    return fails


def free_in(pts, down, m, t):
    """Bleibt d(t) auf dem Loesungsraum von (diamondsuit) frei?"""
    rows, idx, ncol = system(pts, down, m)
    base = rank(rows, ncol)
    return not vanishes(rows, base, ncol, psi_row(t, t, down, m, idx, ncol))


def ideal_below(down, m, t):
    """Das Ideal T_{<=t}, auf 0..k-1 umbenannt (die Indizierung von kappa in
    `antisym.py` setzt zusammenhaengende Nummern voraus).  Die Umbenennung ist
    ordnungserhaltend, laesst also 0 kleinstes und t groesstes Element."""
    I = sorted(set(down[t]) | {t})
    ren = {x: i for i, x in enumerate(I)}
    pts = list(range(len(I)))
    downI = {ren[x]: sorted(ren[y] for y in down[x] if y in I) for x in I}
    return pts, downI, {ren[x]: m[x] for x in I}, ren[t]


def check_reduction(ns=(4, 5), reps=3, seed=7):
    random.seed(seed)
    viol = lossy = tot = 0
    witness = None
    for n in ns:
        for pts, down, _ in posets_with_bottom(n):
            for _ in range(reps):
                m = {x: Fraction(random.randint(-3, 3)) for x in pts}
                for t in pts:
                    ptsI, downI, mI, tI = ideal_below(down, m, t)
                    fT = free_in(pts, down, m, t)
                    fI = free_in(ptsI, downI, mI, tI)
                    tot += 1
                    if fT and not fI:
                        viol += 1
                    if fI and not fT:
                        lossy += 1
                        if witness is None:
                            witness = (dict(down), dict(m), t)
    print('Reduktion, n in %s, zufaellige Massen mit Vorzeichen: %d Paare (T,t)'
          % (list(ns), tot))
    print('    frei auf T, aber nicht auf T_{<=t}: %d   (muss 0 sein)' % viol)
    print('    frei auf T_{<=t}, aber nicht auf T: %d   (Verlust der Reduktion)'
          % lossy)
    if witness:
        d_, m_, t_ = witness
        print('    Verlustzeuge: down=%s m=%s t=%s'
              % (d_, {k: str(v) for k, v in m_.items()}, t_))
    return viol == 0


def check_residual(n, grid):
    """Die Restgestalt (R') auf beschraenkten Halbordnungen.

    Ist z groesstes und 0 kleinstes Element und verschwindet d auf
    W = T \\ {z}, so geben die Relationen an (0,a) sofort Psi(a,0) = d(a) = 0
    fuer a in W und an (0,z) sofort Psi(z,0) = d(z).  Der Defekt ist damit

        d(z) = sum_{c in W} g(c),   g(c) := m_c kappa(c,0),

    und g summiert sich ueber jedes Hauptideal T_{<a}, a in W, zu null.
    Geprueft wird, dass diese drei Identitaeten auf dem Loesungsraum wirklich
    erzwungen sind -- eine Gegenprobe zur Rechnung, nicht zur Vermutung.
    """
    tested = bad = 0
    for pts, down, lt in posets_with_bottom(n):
        z = max(pts)
        if len(down[z]) != n - 1:                 # z muss groesstes Element sein
            continue
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            rows, idx, ncol = system(pts, down, m)
            base = rank(rows, ncol)
            tested += 1
            for a in pts:
                if a == z:
                    continue
                if not vanishes(rows, base, ncol,
                                psi_row(a, 0, down, m, idx, ncol)):
                    bad += 1
                    break
            else:
                r = [x - y for x, y in
                     zip(psi_row(z, 0, down, m, idx, ncol),
                         psi_row(z, z, down, m, idx, ncol))]
                if not vanishes(rows, base, ncol, r):
                    bad += 1
    print('n = %d, beschraenkte Halbordnungen, Massen aus %s: %d Faelle, '
          '%d Abweichungen von (R\')' % (n, list(grid), tested, bad))
    return bad == 0


if __name__ == '__main__':
    ok = check_reduction()
    print()
    grids = ((4, (1, 2, 3)), (5, (1, 2)))
    if '--quick' in sys.argv:
        grids = ((4, (1, 2)),)
    for n, grid in grids:
        sweep(n, grid, support_fails_at, 'support (C4), strikt positive Massen')
    print()
    # Der Fall, den die Streichung der Nullmassen uebriglaesst: alle Massen
    # ausser der am kleinsten Punkt sind positiv, und m_0 = 0.
    for n, grid in grids:
        sweep(n, grid, support_fails_at,
              'support (C4), m_0 = 0 und sonst positiv', m0=0)
    print()
    for n, grid in grids:
        ok &= check_residual(n, grid)
    sys.exit(0 if ok else 1)
