r"""Wo lebt kappa?  Die Suche nach der lokalen Fassung von (C4).

Ausgangspunkt ist der Stand des vierten Laufs vom 2026-08-31 (PROTOKOLL.md):
mit kappa antisymmetrisch, Psi(s,t) = sum_{a<s} m_a kappa(a,t) und

    Psi(s,t) + Psi(t,s) = Psi(s,s) + Psi(t,t)      fuer alle s,t     (diamondsuit)

bleibt vom Halbordnungsfall genau die Vermutung

    (C4+)  m_a > 0 fuer a != 0, m_0 >= 0  ==>  Psi(a,x) = 0, sobald a < x.

Dieses Skript prueft eine **lokale** Verschaerfung, aus der (C4+) in einer Zeile
folgt, weil in Psi(a,x) = sum_{c<a} m_c kappa(c,x) jeder Summand ein c mit
c < a < x hat:

    (C5)  m_c kappa(c,x) = 0, sobald es ein b mit c < b < x gibt.

Geprueft wird wie ueberall hier durch Rangvergleich: verschwindet das lineare
Funktional kappa |-> kappa(c,x) auf dem ganzen Loesungsraum von (diamondsuit)?

Zusaetzlich schreibt `--muster` fuer kleine Halbordnungen die volle Liste der
erzwungenen Nullen von kappa heraus -- die Datengrundlage, an der sich ablesen
laesst, ob (C5) die richtige Fassung ist oder ob mehr gilt.
"""
import itertools
import sys
from fractions import Fraction

from antisym import kappa_index, psi_row, system, vanishes
from posetsearch import posets_with_bottom, rank


def kappa_row(c, x, idx, ncol):
    """Die Zeile des Funktionals kappa |-> kappa(c,x)."""
    r = [Fraction(0)] * ncol
    if c == x:
        return r
    if c < x:
        r[idx[(c, x)]] += 1
    else:
        r[idx[(x, c)]] -= 1
    return r


def middle(c, x, down):
    """Gibt es ein b mit c < b < x?"""
    return any(c in down[b] for b in down[x])


def forced_zeros(pts, down, m):
    """Menge der Paare (c,x), c != x, an denen kappa(c,x) = 0 erzwungen ist."""
    rows, idx, ncol = system(pts, down, m)
    base = rank(rows, ncol)
    out = set()
    for c in pts:
        for x in pts:
            if c == x:
                continue
            if vanishes(rows, base, ncol, kappa_row(c, x, idx, ncol)):
                out.add((c, x))
    return out


def c5_fails_at(pts, down, m):
    """Erstes Paar (c,x) mit c < b < x und m_c != 0, an dem kappa(c,x) frei
    bleibt; sonst None."""
    rows, idx, ncol = system(pts, down, m)
    base = rank(rows, ncol)
    for x in pts:
        for c in down[x]:
            if m[c] == 0 or not middle(c, x, down):
                continue
            if not vanishes(rows, base, ncol, kappa_row(c, x, idx, ncol)):
                return (c, x)
    return None


def c4_fails_at(pts, down, m):
    """Erstes Paar a < x, an dem Psi(a,x) frei bleibt; sonst None."""
    rows, idx, ncol = system(pts, down, m)
    base = rank(rows, ncol)
    for x in pts:
        for a in down[x]:
            if not vanishes(rows, base, ncol,
                            psi_row(a, x, down, m, idx, ncol)):
                return (a, x)
    return None


# ------------------------------------------------------------------ die Suche

def sweep(n, grid, m0_zero):
    """grid: Massen fuer a != 0, strikt positiv.  m0_zero: auch m_0 = 0 testen."""
    tested = c5f = c4f = 0
    bad5, bad4 = [], []
    for pts, down, lt in posets_with_bottom(n):
        for vals in itertools.product(grid, repeat=n - 1):
            for m0 in ((Fraction(0),) + tuple(Fraction(g) for g in grid)
                       if m0_zero else tuple(Fraction(g) for g in grid)):
                m = {0: m0}
                m.update({x: Fraction(v) for x, v in zip(pts[1:], vals)})
                tested += 1
                w5 = c5_fails_at(pts, down, m)
                if w5 is not None:
                    c5f += 1
                    if len(bad5) < 3:
                        bad5.append((dict(down), dict(m), w5))
                w4 = c4_fails_at(pts, down, m)
                if w4 is not None:
                    c4f += 1
                    if len(bad4) < 3:
                        bad4.append((dict(down), dict(m), w4))
    print('n = %d, Massen aus %s (m_0 auch 0: %s): %d Faelle, '
          '(C5) %d Ausfaelle, (C4+) %d Ausfaelle'
          % (n, list(grid), m0_zero, tested, c5f, c4f))
    for down, m, w in bad5:
        print('    (C5) AUSFALL: down=%s m=%s bei %s'
              % (down, {k: str(v) for k, v in m.items()}, w))
    for down, m, w in bad4:
        print('    (C4+) AUSFALL: down=%s m=%s bei %s'
              % (down, {k: str(v) for k, v in m.items()}, w))
    # (C5) ist am 2026-08-31 widerlegt; ihre Ausfaelle sind der Befund, nicht
    # ein Fehler des Skripts.  Ueber den Rueckgabewert entscheidet allein
    # (C4+), die weiterhin ohne Ausfall dasteht.
    return c4f == 0


def muster(n, m0):
    """Die erzwungenen Nullen von kappa, gegen die Vorhersage von (C5)."""
    seen = set()
    for pts, down, lt in posets_with_bottom(n):
        key = tuple(tuple(down[x]) for x in pts)
        if key in seen:
            continue
        seen.add(key)
        m = {x: Fraction(1) for x in pts}
        m[0] = Fraction(m0)
        z = forced_zeros(pts, down, m)
        pred = {(c, x) for c in pts for x in pts
                if c != x and middle(c, x, down) and m[c] != 0}
        extra = sorted(z - pred)
        miss = sorted(pred - z)
        print('down=%s  erzwungen=%s  (C5) sagt %s  darueber hinaus=%s  fehlt=%s'
              % ({k: v for k, v in down.items() if v}, sorted(z), sorted(pred),
                 extra, miss))


if __name__ == '__main__':
    if '--muster' in sys.argv:
        n = int(sys.argv[sys.argv.index('--muster') + 1])
        muster(n, 1)
        print()
        muster(n, 0)
        sys.exit(0)
    ok = True
    grids = ((4, (1, 2, 3)), (5, (1, 2)))
    if '--quick' in sys.argv:
        grids = ((4, (1, 2)),)
    for n, grid in grids:
        ok &= sweep(n, grid, True)
    sys.exit(0 if ok else 1)
