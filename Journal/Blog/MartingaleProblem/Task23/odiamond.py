"""Der kleinste Zeuge gegen die o-Konvention: der Diamant mit m_c^2 = m_a m_b.

Auf dem Diamanten  0 < a, b < c  mit nichtnegativen Massen ist die Matrix des
iota = o-Systems

    B = [[m_a, 0, 0], [0, m_b, 0], [m_a, m_b, m_c]]      (Basis a, b, c)

Ihre Eigenwerte sind m_a, m_b, m_c.  Sind sie verschieden, so hat 1 genau dann
**nicht** maximale Ordnung, wenn 1 auf dem Linkseigenvektor zu m_c verschwindet;
dessen Gestalt ist w = (m_a/(m_c-m_a), m_b/(m_c-m_b), 1), und

    <w, 1> = 0   <=>   m_c^2 = m_a m_b .

Das ist die ganze Bedingung: die Masse der Spitze ist das **geometrische Mittel**
der beiden unvergleichbaren Massen.  Der kleinste ganzzahlige Fall ist
m_a = 1, m_b = 4, m_c = 2.

Aufruf:  python3 odiamond.py
"""

from fractions import Fraction

import ocounter
import posetsearch
from oconvention import down_o

PTS = [0, 1, 2, 3]                       # 0 < 1, 2 < 3
DOWN = {0: [], 1: [0], 2: [0], 3: [0, 1, 2]}

CASES = [(1, 4, 2), (1, 9, 3), (4, 9, 6), (2, 8, 4), (1, 16, 4),
         (Fraction(1), Fraction(1, 4), Fraction(1, 2)),
         (1, 1, 1), (3, 3, 3), (1, 4, 3), (1, 4, 1), (1, 4, 4), (2, 3, 5)]


def run_case(ma, mb, mc):
    m = {0: Fraction(0), 1: Fraction(ma), 2: Fraction(mb), 3: Fraction(mc)}
    red = posetsearch.duality_holds(PTS, down_o(PTS, DOWN), m, 0)
    full = ocounter.duality_full_o(PTS, DOWN, m)
    pdual = posetsearch.duality_holds(PTS, DOWN, m, 0)
    return red, full, pdual


def main():
    print('Diamant 0 < a, b < c,  Konvention iota = o.')
    print('%-22s %-14s %-12s %-12s %s'
          % ('(m_a, m_b, m_c)', 'm_c^2 - m_a m_b', 'reduziert', 'voll',
             'dieselbe Uhr, iota = p'))
    ok = True
    for ma, mb, mc in CASES:
        red, full, pdual = run_case(ma, mb, mc)
        disc = Fraction(mc) ** 2 - Fraction(ma) * Fraction(mb)
        geo = (disc == 0 and Fraction(ma) != Fraction(mb))
        print('%-22s %-14s %-12s %-12s %s'
              % ('(%s, %s, %s)' % (ma, mb, mc), disc,
                 'faellt' if red is not None else 'gilt',
                 'faellt' if full is not None else 'gilt',
                 'faellt' if pdual is not None else 'gilt'))
        if (red is not None) != geo or (full is not None) != geo:
            ok = False
    print()
    print('Vorhersage "faellt genau dann, wenn m_c^2 = m_a m_b und m_a != m_b":',
          'bestaetigt' if ok else 'WIDERLEGT')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
