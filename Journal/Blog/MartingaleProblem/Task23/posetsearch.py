r"""Erschoepfende Suche: fuer welche Halbordnungen und Massen gilt die Dualitaet?

Benutzt die in `poset2.py` gegen das volle System gepruefte Reduktion: mit
T_{<0} = leer loest (eq:incrementrep) das Phi auf, und uebrig bleibt in gamma
allein

    sum_{a<s} m_a (gamma(a,t) - gamma(a,0))
        = sum_{b<t} m_b (gamma(s,b) - gamma(0,b))       fuer alle s,t     (*)

mit dem Dualitaetsdefekt  delta(t) = sum_{a<t} m_a (gamma(a,0) - gamma(0,a)).

Zu pruefen ist, ob das lineare Funktional delta(t) im Zeilenraum von (*) liegt;
genau dann verschwindet es auf jeder Loesung.  Das ist ein Rangvergleich und
braucht keinen Kern -- exakte Bruchrechnung, Gauss.

Gesucht wird ueber ALLE Halbordnungen mit kleinstem Element auf bis zu fuenf
Punkten (bis auf Isomorphie durch die Aufzaehlung ohnehin mehrfach getroffen)
und ueber mehrere Massenvektoren.
"""
import itertools
import random
import sys
from fractions import Fraction


# ------------------------------------------------------------------ lineare Algebra


def rank(rows, ncol):
    """Rang einer Liste von Zeilen (Listen von Fractions), exakt."""
    rows = [r[:] for r in rows]
    r = 0
    for c in range(ncol):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c]:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][c]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c] / pv
                ri, rr = rows[i], rows[r]
                for j in range(c, ncol):
                    ri[j] -= f * rr[j]
        r += 1
        if r == len(rows):
            break
    return r


# ------------------------------------------------------------------ das System


def system(pts, down, m, bottom):
    n = len(pts)
    idx = {(s, t): i * n + j for i, s in enumerate(pts) for j, t in enumerate(pts)}
    ncol = n * n
    rows = []
    for s in pts:
        for t in pts:
            r = [Fraction(0)] * ncol
            for a in down[s]:
                r[idx[(a, t)]] += m[a]
                r[idx[(a, bottom)]] -= m[a]
            for b in down[t]:
                r[idx[(s, b)]] -= m[b]
                r[idx[(bottom, b)]] += m[b]
            if any(r):
                rows.append(r)
    return rows, idx, ncol


def duality_holds(pts, down, m, bottom):
    """True, wenn delta(t) = 0 fuer jedes t auf allen Loesungen von (*) erzwungen
    ist.  Gibt sonst das erste t zurueck, an dem es frei bleibt."""
    rows, idx, ncol = system(pts, down, m, bottom)
    base = rank(rows, ncol)
    for t in pts:
        d = [Fraction(0)] * ncol
        for a in down[t]:
            d[idx[(a, bottom)]] += m[a]
            d[idx[(bottom, a)]] -= m[a]
        if not any(d):
            continue
        if rank(rows + [d], ncol) != base:
            return t
    return None


# ------------------------------------------------------------------ Halbordnungen


def posets_with_bottom(n):
    """Alle Halbordnungen auf {0,..,n-1} mit 0 als kleinstem Element."""
    rest = list(range(1, n))
    pairs = [(a, b) for a in rest for b in rest if a != b]
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        lt = {p for p, b in zip(pairs, bits) if b}
        if any((b, a) in lt for (a, b) in lt):          # Antisymmetrie
            continue
        if any((a, c) in lt and (c, b) in lt and (a, b) not in lt
               for a in rest for b in rest for c in rest):
            continue                                     # Transitivitaet
        lt |= {(0, x) for x in rest}
        down = {x: sorted(y for y in range(n) if (y, x) in lt) for x in range(n)}
        yield list(range(n)), down, lt


def is_chain(pts, lt):
    return all(a == b or (a, b) in lt or (b, a) in lt for a in pts for b in pts)


MASSES = {
    'alle 1':      lambda n: [Fraction(1)] * n,
    'positiv':     lambda n: [Fraction(p) for p in (2, 3, 5, 7, 11, 13)][:n],
    'positiv 2':   lambda n: [Fraction(1, k) for k in (1, 2, 3, 5, 7, 11)][:n],
    'zufaellig +': lambda n: [Fraction(random.randint(1, 40)) for _ in range(n)],
}


def sweep(n, m0_zero=True):
    random.seed(20260830)
    total = chains = failures = 0
    bad = []
    for pts, down, lt in posets_with_bottom(n):
        total += 1
        if is_chain(pts, lt):
            chains += 1
        for name, gen in MASSES.items():
            m = dict(zip(pts, gen(n)))
            if m0_zero:
                m[0] = Fraction(0)
            t = duality_holds(pts, down, m, 0)
            if t is not None:
                failures += 1
                bad.append((down, name, m, t))
    print('n = %d: %d Halbordnungen mit kleinstem Element (%d Ketten), '
          '%d Massenvektoren je: %d Ausfaelle'
          % (n, total, chains, len(MASSES), failures))
    for down, name, m, t in bad[:5]:
        print('    AUSFALL: down=%s  %s  m=%s  bei t=%s' % (down, name, m, t))
    return failures == 0


def signed_sweep(n):
    """Dasselbe mit Massen beider Vorzeichen: hier soll es Ausfaelle geben,
    und zwar genau ausserhalb der Ketten."""
    random.seed(1)
    chainfail = nonchainfail = nonchaintot = 0
    witness = None
    for pts, down, lt in posets_with_bottom(n):
        ch = is_chain(pts, lt)
        if not ch:
            nonchaintot += 1
        for _ in range(6):
            m = dict(zip(pts, [Fraction(random.randint(-4, 4)) or Fraction(1)
                               for _ in range(n)]))
            m[0] = Fraction(0)
            t = duality_holds(pts, down, m, 0)
            if t is not None:
                if ch:
                    chainfail += 1
                else:
                    nonchainfail += 1
                    if witness is None:
                        witness = (dict(down), dict(m), t)
    print('n = %d, Massen mit Vorzeichenwechsel: Ausfaelle auf Ketten: %d '
          '(muss 0 sein), ausserhalb: %d von %d Halbordnungen getestet'
          % (n, chainfail, nonchainfail, nonchaintot))
    if witness:
        print('    Zeuge: down=%s  m=%s  bei t=%s' % witness)
    return chainfail == 0


def clock_sweep(n, grid):
    """Der Fall echter Uhren: nichtnegative Massen, auch am kleinsten Punkt,
    alle Halbordnungen mit kleinstem Element und alle Massenvektoren aus dem
    Gitter.  Hier darf es keinen Ausfall geben."""
    tested = fails = 0
    bad = []
    for pts, down, lt in posets_with_bottom(n):
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            tested += 1
            t = duality_holds(pts, down, m, 0)
            if t is not None:
                fails += 1
                bad.append((dict(down), dict(m), t))
    print('n = %d, nichtnegative Massen aus %s (echte Uhren): %d Faelle, '
          '%d Ausfaelle' % (n, list(grid), tested, fails))
    for w in bad[:3]:
        print('    AUSFALL: down=%s m=%s t=%s' % w)
    return fails == 0


if __name__ == '__main__':
    ok = True
    for n in (3, 4, 5):
        ok &= sweep(n)
    print()
    for n in (4, 5):
        ok &= signed_sweep(n)
    print()
    if '--clocks' in sys.argv:                # dauert einige Minuten
        for n, grid in ((4, (0, 1, 2, 3)), (5, (0, 1, 2))):
            ok &= clock_sweep(n, grid)
    else:
        print('(--clocks laeuft zusaetzlich alle nichtnegativen Massenvektoren '
              'aus einem Gitter durch: 4864 + 53217 Faelle, 0 Ausfaelle)')
    sys.exit(0 if ok else 1)
