r"""Die Spitzenzeile jedes Zertifikats einer endlichen Halbordnung ist erzwungen:
T_{t* a} = m_a e_{r-2}(up a) / e_{r-1}(T)  -- der massengewichtete Anteil der
laengsten Ketten, die in a beginnen.  Beweis: V^{r-1} 1 = c_{r-1} e_{t*}, also
T e_{t*} = T V^{r-1} 1 / c_{r-1} = (V^T)^{r-1} e_{t*} / c_{r-1} = psi_{r-1}/c_{r-1}.

PROTOKOLL, dreissigster Lauf.  Geprueft: (a) der Nullraum {D sym, DV=V^T D,
D1=0} verschwindet in der Zeile t*;  (b) die Krylow-Spitzenzeile ist die
Kettenformel;  (c) auf der Leiter: T_{t* b_1} = 1 / sum_{i=0}^n prod_{l<=i}
alpha_l/beta_l, T_{t* a_1} = 1 - das.  Exakt in Fractions.

    python3 toprow.py
"""
import random, sys
from fractions import Fraction as Fr
import mpmath as mp
import spectral as S
import ladder_lp as L

FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


def maxchain_weight_from(P, a):
    """Summe der Massenprodukte ueber alle Ketten a=c_0<c_1<...<c_{h-1} von
    Atomen maximaler Laenge h(a) mit kleinstem Element a; gibt (h, Gewicht)."""
    from functools import lru_cache

    @lru_cache(None)
    def f(a):
        best_h, best_w = 1, P.masses[a]
        for s in P.atoms:
            if P.less(a, s):
                h, w = f(s)
                if h + 1 > best_h:
                    best_h, best_w = h + 1, P.masses[a] * w
                elif h + 1 == best_h:
                    best_w += P.masses[a] * w
        return best_h, best_w
    return f(a)


def toprow_formula(P):
    hw = {a: maxchain_weight_from(P, a) for a in P.atoms}
    d = max(h for h, w in hw.values())
    tot = sum((w for h, w in hw.values() if h == d), Fr(0))
    return {a: (w / tot if h == d else Fr(0)) for a, (h, w) in hw.items()}, d


def test(P, tag):
    TK, b, r, c = S.hankel_certificate(P)
    form, d = toprow_formula(P)
    check(d == r - 1, f'{tag}: Hoehe d={d} = r-1={r-1}')
    check(all(TK[P.t][a] == form[a] for a in P.atoms) and TK[P.t][0] == 0 and TK[P.t][P.t] == 0,
          f'{tag}: Krylow-Spitzenzeile = Kettenformel')
    tk, basis, wt, idx = L.certificate_space(P)
    mxt = max((abs(D[idx[(min(a, P.t), max(a, P.t))]]) for D in basis for a in range(P.n + 2)), default=mp.mpf(0))
    check(mxt < mp.mpf(10) ** -40, f'{tag}: Nullraum (dim {len(basis)}) verschwindet in Zeile t* (max {mp.nstr(mxt, 3)})')


def main():
    rng = random.Random(30)
    for k in range(8):
        n = rng.randint(3, 7)
        P = S.random_poset(n, rng)
        test(P, f'zufaellig #{k} n={n}')
    test(S.chain([Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(1, 16)]), 'Kette')
    test(S.antichain([Fr(1, 2), Fr(1, 3), Fr(1, 6)]), 'Antikette')
    test(S.crown([Fr(1, 2), Fr(1, 4), Fr(1, 8)], [Fr(1, 3), Fr(1, 9), Fr(1, 27)]), 'Krone')
    for alpha, beta in ((Fr(1, 2), Fr(1, 3)), (Fr(1, 3), Fr(1, 2)), (Fr(1, 2), Fr(2, 3)), (Fr(1, 4), Fr(1, 2))):
        Minf = alpha / (1 - alpha) + beta / (1 - beta)
        for n in (3, 5, 8):
            alF = [alpha ** i / Minf for i in range(1, n + 1)]
            beF = [beta ** j / Minf for j in range(1, n + 1)]
            P = S.ladder(alF, beF)
            test(P, f'Leiter ({alpha},{beta}) n={n}')
            TK, *_ = S.hankel_certificate(P)
            pi_n = 1 / sum((alpha / beta) ** (i * (i + 1) // 2) for i in range(n + 1))
            check(TK[P.t][n + 1] == pi_n and TK[P.t][1] == 1 - pi_n,
                  f'Leiter ({alpha},{beta}) n={n}: T_(t*,b1) = 1/sum_i (alpha/beta)^(i(i+1)/2) = {pi_n}')
        # Limes
        if alpha < beta:
            mp.mp.dps = 30
            q = mp.mpf(alpha.numerator) / alpha.denominator / (mp.mpf(beta.numerator) / beta.denominator)
            s = mp.nsum(lambda i: q ** (i * (i + 1) / 2), [0, mp.inf])
            print(f'  Limes fuer ({alpha},{beta}): T_(t*,a1) -> 1 - 1/sum = {mp.nstr(1 - 1/s, 12)}   (Lauf 29 misst 0.51704641 bei (1/3,1/2))')
    print('\nFEHL:', FAIL if FAIL else 'keine')
    return 1 if FAIL else 0


if __name__ == '__main__':
    sys.exit(main())
