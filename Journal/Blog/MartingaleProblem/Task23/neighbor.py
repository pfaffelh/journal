r"""Gegenprobe zur Nachbaratom-Skizze (zwoelfter Lauf), nachgerechnet im
vierzehnten Lauf.

Die Skizze behauptet: hat jedes Atom beidseits ein Nachbaratom, so laeuft die
Zwei-Diagonalen-Induktion von `lem:atomgrid` ohne Boden.  Die Nachrechnung
(PROTOKOLL, vierzehnter Lauf) ergibt: die Induktion braucht weder Boden noch
Deckel, aber sie traegt nur, wenn **je zwei Atome endlich viele Atome zwischen
sich haben** (Intervallendlichkeit); "beidseits ein Nachbaratom" ist echt
schwaecher (Beispiel: zwei omega*-Bloecke).  Dieses Skript prueft die zwei
mechanischen Kernaussagen an endlichen Systemen, exakt rational:

    (R)  RANDFREIHEIT.  Eine endliche Kette von Gitterpunkten g_0 > ... > g_M,
         nur die Einschrittrelationen aus (eq:incrementrep) -- keine Relation
         nach oben aus g_0 hinaus, keine nach unten aus g_M hinaus, kein
         Punkt 0, kein t* jenseits der Kette.  Behauptung: der Kern erzwingt
         Phi(i,j) = Phi(j,i) auf dem ganzen Quadrat.  Das ist die Gestalt, in
         der die Induktion im omega*- und im zeta-Fall laeuft (dort ist jedes
         Fenster [a_j, a_i] eine solche Kette).

    (X)  KREUZBLOCK.  Zwei solche Ketten ohne verbindende Einschrittrelation
         (das endliche Abbild zweier Bloecke, zwischen denen sich Atome
         haeufen).  Behauptung: innerhalb jedes Blocks erzwingt der Kern die
         Symmetrie, auf den Kreuzpaaren NICHT.  Die lokalen Relationen allein
         schliessen den Fall "diskret in sich, aber nicht intervallendlich"
         also nicht; dort muessten die Schwanzrelationen arbeiten, und ob sie
         es tun, ist offen.

(X) ist kein Gegenbeispiel zur Dualitaet -- das unendliche System hat
Relationen (unendliche Summen), die das endliche Abbild weglaesst; siehe den
dreizehnten Lauf zu der Falle, eine Relaxation fuer das System zu halten.

Konventionen wie in `verify.py`: iota = p legt die Dichte an den unteren
Endpunkt des Einschrittintervalls, iota = o an den oberen.  Bei iota = o
traegt der oberste Punkt der Kette die Masse seines Schritts; die Kette ohne
Rand ist unter Spiegelung selbstdual, beide Konventionen werden dennoch
getrennt gebaut und geprueft.
"""
import sympy as sp

MASSVECTORS = [
    [sp.Integer(1)] * 12,
    [sp.Integer(k) for k in [3, 1, 7, 2, 11, 5, 4, 13, 6, 1, 9, 8]],
    [sp.Rational(1, k) for k in [2, 5, 3, 7, 1, 11, 4, 9, 13, 6, 8, 10]],
]


def chain_rows(points, steps, idx, nvar):
    """Einschrittrelationen einer Kette, fuer alle zweiten Argumente.

    points: Liste der Gitterindizes (absteigend gedacht: points[0] am
    groessten).  steps: Liste (oben, unten, masse, traeger) -- die Relation
    Phi(oben, y) - Phi(unten, y) = masse * gamma(traeger, y) und ihr Spiegel
    im zweiten Argument, fuer jedes y aus dem Gesamtgitter.
    """
    rows = []
    for oben, unten, masse, traeger in steps:
        for y in range(nvar):
            r = [sp.Integer(0)] * len(idx)
            r[idx[('P', oben, y)]] += 1
            r[idx[('P', unten, y)]] -= 1
            r[idx[('g', traeger, y)]] -= masse
            rows.append(r)
            r = [sp.Integer(0)] * len(idx)
            r[idx[('P', y, oben)]] += 1
            r[idx[('P', y, unten)]] -= 1
            r[idx[('g', y, traeger)]] -= masse
            rows.append(r)
    return rows


def build(blocks, mass, iota):
    """System aus disjunkten Ketten-Bloecken ohne Randrelationen.

    blocks: Liste von Blocklaengen; Block b hat so viele Gitterpunkte, die
    global durchnummeriert werden.  Zwischen den Bloecken gibt es keine
    Relation.  Rueckgabe: Matrix, Index, Blockzugehoerigkeit je Punkt.
    """
    pts = []
    zug = []
    for b, n in enumerate(blocks):
        start = len(zug)
        pts.append(list(range(start, start + n)))
        zug += [b] * n
    nvar = len(zug)
    idx = {}
    for kind in ('P', 'g'):
        for s in range(nvar):
            for t in range(nvar):
                idx[(kind, s, t)] = len(idx)
    rows, mi = [], 0
    for block in pts:
        steps = []
        for k in range(1, len(block)):
            m = mass[mi]
            mi += 1
            # absteigende Kette: block[k-1] > block[k]; iota = p: das
            # Intervall [g_k, g_{k-1}) traegt g_k, iota = o: (g_k, g_{k-1}]
            # traegt g_{k-1}.
            traeger = block[k] if iota == 'p' else block[k - 1]
            steps.append((block[k - 1], block[k], m, traeger))
        rows += chain_rows(block, steps, idx, nvar)
    return sp.Matrix(rows), idx, zug


def check(blocks, mass, iota):
    A, idx, zug = build(blocks, mass, iota)
    basis = A.nullspace()
    nvar = len(zug)
    val = lambda v, s, t: v[idx[('P', s, t)]]
    asym_in = sorted({(s, t) for v in basis for s in range(nvar)
                      for t in range(nvar) if zug[s] == zug[t]
                      and val(v, s, t) != val(v, t, s)})
    asym_x = sorted({(s, t) for v in basis for s in range(nvar)
                     for t in range(nvar) if zug[s] != zug[t]
                     and val(v, s, t) != val(v, t, s)})
    return len(basis), asym_in, asym_x


def report():
    ok = True
    print('-- (R) Randfreiheit: eine Kette, keine Randrelation --')
    for iota in ('p', 'o'):
        for M in range(2, 8):
            for v_i, mass in enumerate(MASSVECTORS):
                dim, asym_in, asym_x = check([M + 1], mass, iota)
                gut = not asym_in and not asym_x
                ok &= gut
                print('iota=%s M=%d Massen#%d: dim=%2d  (S) %s'
                      % (iota, M, v_i, dim,
                         'ja' if gut else 'NEIN bei %s' % (asym_in + asym_x)))
    print('-- (R) symbolische Massen --')
    # iota = o nur bis M = 3: sympys Nullraum ueber Q(m_1..m_4) braucht in
    # dieser Orientierung Stunden.  Das kostet nichts an Aussagekraft: das
    # o-System der Kette ist wortgleich das p-System der gespiegelten Kette
    # (Spiegelung von Punkten und Massenliste), und p ist bis M = 4 geprueft.
    for iota, Ms in (('p', (2, 3, 4)), ('o', (2, 3))):
        for M in Ms:
            mass = list(sp.symbols('m1:%d' % (M + 1), positive=True))
            A, idx, zug = build([M + 1], mass, iota)
            basis = A.nullspace()
            nvar = len(zug)
            bad = sorted({(s, t) for v in basis for s in range(nvar)
                          for t in range(nvar)
                          if sp.cancel(v[idx[('P', s, t)]]
                                       - v[idx[('P', t, s)]]) != 0})
            ok &= not bad
            print('iota=%s M=%d symbolisch: dim=%2d  (S) %s'
                  % (iota, M, len(basis), 'ja' if not bad else 'NEIN bei %s' % bad))
    print('-- (X) Kreuzblock: zwei Ketten ohne Verbindung --')
    for iota in ('p', 'o'):
        for blocks in ([3, 3], [4, 3], [3, 4]):
            for v_i, mass in enumerate(MASSVECTORS):
                dim, asym_in, asym_x = check(blocks, mass, iota)
                # erwartet: blockintern symmetrisch, Kreuzpaare frei
                gut = (not asym_in) and bool(asym_x)
                ok &= gut
                print('iota=%s Bloecke=%s Massen#%d: dim=%2d  intern %s,'
                      ' Kreuz %s'
                      % (iota, blocks, v_i, dim,
                         'ja' if not asym_in else 'NEIN bei %s' % asym_in,
                         'frei (wie erwartet)' if asym_x else
                         'ERZWUNGEN -- unerwartet'))
    return ok


if __name__ == '__main__':
    import sys
    sys.exit(0 if report() else 1)
