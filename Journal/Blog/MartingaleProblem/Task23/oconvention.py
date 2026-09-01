"""Die o-Konvention auf einer Halbordnung.

Der Satz des sechsten Laufs (2026-08-31) ist fuer iota = p bewiesen: dort ist
[0,s) = T_{<s}, und die Matrix V_{s,a} = [a < s] m_a ist nilpotent.  Unter
iota = o ist das Intervall (0,s] = T_{<=s} \\ {0}, also V_{s,a} = [a <= s, a != 0]
m_a mit nichtverschwindender Diagonale -- der Nilpotenzschluss faellt aus.

Dieses Skript prueft, ob die Aussage trotzdem gilt.  Es benutzt dieselbe
Systemkonstruktion wie `posetsearch`, nur mit dem anderen Intervall, und
vergleicht ausserdem den Raum L = {T e : T = T^T, TV = V^T T} mit den
tatsaechlich erzwungenen Stellen.

Befund (2026-08-31, achter Lauf): sie gilt **nicht**.  `sweep_o` faellt auf fuenf
Punkten, sobald das Massengitter die Bedingung m_c^2 = m_a m_b treffen kann; der
kleinste Zeuge steht auf vier Punkten und heisst `odiamond`.  `criterion_o`
dagegen traegt auch dort, wo L echt kleiner ist als R^T, und erklaert den
Ausfall: L beschreibt die erzwungenen Stellen genau.

Aufruf:  python3 oconvention.py
"""

import itertools
from fractions import Fraction

import posetsearch
import selfadjoint


def down_o(pts, down, bottom=0):
    """(0,x] = T_{<=x} ohne den kleinsten Punkt."""
    return {x: sorted((set(down[x]) | {x}) - {bottom}) if x != bottom else []
            for x in pts}


def sweep_o(n, grid):
    """Alle Halbordnungen mit kleinstem Element, nichtnegative Massen."""
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
                bad.append((dict(down), dict(m), t))
    print('o-Konvention, n = %d, Massen aus %s: %d Faelle, %d Ausfaelle'
          % (n, list(grid), tested, fails))
    for w in bad[:5]:
        print('    AUSFALL: down=%s m=%s t=%s' % w)
    return fails == 0


def forced_at(pts, down, m, bottom, t):
    """Ist delta(t) = 0 auf allen Loesungen von (*) erzwungen?"""
    rows, idx, ncol = posetsearch.system(pts, down, m, bottom)
    base = posetsearch.rank(rows, ncol)
    d = [Fraction(0)] * ncol
    for a in down[t]:
        d[idx[(a, bottom)]] += m[a]
        d[idx[(bottom, a)]] -= m[a]
    if not any(d):
        return True
    return posetsearch.rank(rows + [d], ncol) == base


def criterion_o(n, grid):
    """Beschreibt L auch unter iota = o genau die erzwungenen Stellen?  Wenn ja,
    ist der Spurteil des Beweises konventionsfrei und nur die Konstruktion von T
    ist zu ersetzen; wenn nein, traegt L die Lage hier nicht."""
    tested = only_L = only_forced = 0
    witness = None
    for pts, down, lt in posetsearch.posets_with_bottom(n):
        do = down_o(pts, down)
        for vals in itertools.product(grid, repeat=n):
            m = {x: Fraction(v) for x, v in zip(pts, vals)}
            V = [[m[a] if a in do[s] else Fraction(0) for a in pts]
                 for s in pts]
            L = selfadjoint.image_of_one(V)
            for t in pts:
                e = [Fraction(1) if i == t else Fraction(0)
                     for i in range(len(pts))]
                in_L = selfadjoint.in_span(L, e, len(pts))
                forced = forced_at(pts, do, m, 0, t)
                tested += 1
                if in_L and not forced:
                    only_L += 1                      # darf nie vorkommen
                if forced and not in_L:
                    only_forced += 1                 # L ist dann zu klein
                    if witness is None:
                        witness = (dict(down), dict(m), t)
    print('o-Konvention, Kriterium, n = %d, Massen aus %s: %d Stellen; '
          'in L aber nicht erzwungen: %d (muss 0 sein); '
          'erzwungen aber nicht in L: %d'
          % (n, list(grid), tested, only_L, only_forced))
    if witness:
        print('    L zu klein bei: down=%s m=%s t=%s' % witness)
    return only_L == 0


if __name__ == '__main__':
    # Der Sweep lief hier bis zum 2026-08-31 auf fuenf Punkten nur ueber Massen
    # aus {0,1} und meldete "kein Ausfall".  Das war die Luecke: {0,1} und
    # {0,1,2} koennen die Ausnahmebedingung m_c^2 = m_a m_b mit m_a != m_b gar
    # nicht treffen.  Mit {0,1,2} auf fuenf Punkten fallen 144 Faelle -- siehe
    # `ocounter.py` und `odiamond.py`.  Ausfaelle sind hier also erwartet.
    for n, grid in ((3, (0, 1, 2)), (4, (0, 1, 2)), (5, (0, 1, 2))):
        sweep_o(n, grid)
    # Das Kriterium dagegen traegt ueberall, auch auf fuenf Punkten, wo L echt
    # kleiner wird als R^T; hier darf nichts abweichen.
    ok = True
    for n, grid in ((3, (0, 1, 2)), (4, (0, 1, 2)), (5, (0, 1, 2))):
        ok &= criterion_o(n, grid)
    print('Kriterium:', 'kein Ausfall' if ok else 'AUSFALL')
    raise SystemExit(0 if ok else 1)
