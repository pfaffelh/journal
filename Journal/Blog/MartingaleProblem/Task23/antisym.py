r"""Der Halbordnungsfall in der reinen kappa-Gestalt, und die Frage nach dem
Traeger von Psi.

Ausgangspunkt ist die in `PROTOKOLL.md` festgehaltene Entkopplung: (**) zerfaellt
in eine Bedingung an den symmetrischen und eine an den antisymmetrischen Anteil
von gamma, und der Dualitaetsdefekt haengt nur am antisymmetrischen.  Mit
kappa antisymmetrisch und

    Psi(s,t) = sum_{a<s} m_a kappa(a,t),      d(t) = Psi(t,t)

lautet die Bedingung

    Psi(s,t) + Psi(t,s) = Psi(s,s) + Psi(t,t)   fuer alle s,t.   (diamondsuit)

Zu zeigen ist d == 0.  Dieses Skript prueft zweierlei exakt in Bruchrechnung:

 (1) Kontrolle.  Die kappa-Gestalt liefert dieselben Antworten wie das volle
     System in (Phi,gamma) aus `posetsearch.py`: auf Ketten nie ein Ausfall,
     am Diamanten mit m_a = 1, m_b = -1, m_0 = 0 ein Ausfall, bei
     nichtnegativen Massen nie einer.

 (2) Die Vermutung (C4).  Psi(a,x) = 0, sobald a < x -- also: Psi ist auf
     vergleichbaren Paaren null und lebt allein auf der Unvergleichbarkeit.
     Das ist echt staerker als d == 0 und der Grund, aus dem es hier steht:
     unter (C4) folgt d == 0 in vier Zeilen (siehe PROTOKOLL.md).

Getestet wird jeweils, ob das lineare Funktional auf dem Loesungsraum von
(diamondsuit) verschwindet -- ein Rangvergleich, kein Kern.
"""
import itertools
import sys
from fractions import Fraction

from posetsearch import posets_with_bottom, rank


# ------------------------------------------------------------------ das System

def kappa_index(n):
    """kappa ist antisymmetrisch: Unbekannte sind die Paare i<j (Indexordnung)."""
    idx = {}
    k = 0
    for i in range(n):
        for j in range(i + 1, n):
            idx[(i, j)] = k
            k += 1
    return idx, k


def psi_row(s, t, down, m, idx, ncol):
    """Die Zeile des Funktionals kappa |-> Psi(s,t) = sum_{a<s} m_a kappa(a,t)."""
    r = [Fraction(0)] * ncol
    for a in down[s]:
        if a == t:
            continue                      # kappa(t,t) = 0
        if a < t:
            r[idx[(a, t)]] += m[a]
        else:
            r[idx[(t, a)]] -= m[a]
    return r


def add(r1, r2):
    return [x + y for x, y in zip(r1, r2)]


def sub(r1, r2):
    return [x - y for x, y in zip(r1, r2)]


def system(pts, down, m):
    n = len(pts)
    idx, ncol = kappa_index(n)
    rows = []
    for s in pts:
        for t in pts:
            if s >= t:
                continue                  # die Bedingung ist symmetrisch in s,t
            r = sub(add(psi_row(s, t, down, m, idx, ncol),
                        psi_row(t, s, down, m, idx, ncol)),
                    add(psi_row(s, s, down, m, idx, ncol),
                        psi_row(t, t, down, m, idx, ncol)))
            if any(r):
                rows.append(r)
    return rows, idx, ncol


def vanishes(rows, base, ncol, r):
    """Verschwindet das Funktional r auf allen Loesungen des Systems?"""
    if not any(r):
        return True
    return rank(rows + [r], ncol) == base


def duality_fails_at(pts, down, m):
    """Erstes t, an dem d(t) auf dem Loesungsraum frei bleibt; sonst None."""
    rows, idx, ncol = system(pts, down, m)
    base = rank(rows, ncol)
    for t in pts:
        if not vanishes(rows, base, ncol,
                        psi_row(t, t, down, m, idx, ncol)):
            return t
    return None


def support_fails_at(pts, down, m):
    """Erstes Paar a < x, an dem Psi(a,x) frei bleibt; sonst None."""
    rows, idx, ncol = system(pts, down, m)
    base = rank(rows, ncol)
    for x in pts:
        for a in down[x]:
            if not vanishes(rows, base, ncol,
                            psi_row(a, x, down, m, idx, ncol)):
                return (a, x)
    return None


# ------------------------------------------------------------------ Kontrolle

def is_chain(pts, lt):
    return all(a == b or (a, b) in lt or (b, a) in lt for a in pts for b in pts)


def check_diamond():
    """Der Zeuge aus `diamond.py`, in der kappa-Gestalt nachgerechnet."""
    pts = [0, 1, 2, 3]                      # 0 < a=1, b=2 < t*=3
    down = {0: [], 1: [0], 2: [0], 3: [0, 1, 2]}
    m = {0: Fraction(0), 1: Fraction(1), 2: Fraction(-1), 3: Fraction(0)}
    t = duality_fails_at(pts, down, m)
    print('Diamant, m = (0,1,-1,0): Dualitaet faellt bei t = %s '
          '(erwartet: 3)' % t)
    m2 = {0: Fraction(0), 1: Fraction(1), 2: Fraction(1), 3: Fraction(0)}
    t2 = duality_fails_at(pts, down, m2)
    print('Diamant, m = (0,1, 1,0): Dualitaet faellt bei t = %s '
          '(erwartet: None)' % t2)
    return t == 3 and t2 is None


def check_chains(nmax=5):
    """Auf Ketten faellt die Dualitaet nie, auch bei gemischten Vorzeichen."""
    ok = True
    for n in range(2, nmax + 1):
        down = {i: list(range(i)) for i in range(n)}
        pts = list(range(n))
        for vals in itertools.product((-2, -1, 0, 1, 3), repeat=n):
            m = {i: Fraction(v) for i, v in zip(pts, vals)}
            if duality_fails_at(pts, down, m) is not None:
                ok = False
                print('    KETTE FAELLT: n=%d m=%s' % (n, vals))
    print('Ketten bis n = %d, alle Massenvektoren aus {-2,-1,0,1,3}: %s'
          % (nmax, 'kein Ausfall' if ok else 'AUSFAELLE'))
    return ok


# ------------------------------------------------------------------ die Suche

def sweep(n, grid, what):
    """what = 'duality' oder 'support'."""
    probe = duality_fails_at if what == 'duality' else support_fails_at
    tested = fails = 0
    bad = []
    for pts, down, lt in posets_with_bottom(n):
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            tested += 1
            w = probe(pts, down, m)
            if w is not None:
                fails += 1
                if len(bad) < 3:
                    bad.append((dict(down), dict(m), w))
    print('n = %d, %s, Massen aus %s: %d Faelle, %d Ausfaelle'
          % (n, what, list(grid), tested, fails))
    for down, m, w in bad:
        print('    AUSFALL: down=%s m=%s bei %s'
              % (down, {k: str(v) for k, v in m.items()}, w))
    return fails == 0


if __name__ == '__main__':
    ok = check_diamond()
    ok &= check_chains()
    print()
    grids = ((4, (0, 1, 2, 3)), (5, (0, 1, 2)))
    if '--quick' in sys.argv:
        grids = ((4, (0, 1, 2)),)
    for n, grid in grids:
        ok &= sweep(n, grid, 'duality')
        sweep(n, grid, 'support')           # Vermutung, kein Abbruchkriterium
    sys.exit(0 if ok else 1)
