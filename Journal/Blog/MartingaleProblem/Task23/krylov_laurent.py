r"""Das Krylow-Zertifikat als Laurent-Koeffizient (Lauf 30): fuer Atome s,u
    T_K[s,u] / (m_s m_u) = + [c^{-2}] ( P_{up s}(c) P_{up u}(c) / P_T(c) )
(Entwicklung bei c = oo), aus Theorem 28(ii) / Lemma 27.3.  Exakt geprueft;
Vermutung 34 lautet damit: |[c^{-2}] P_{up s} P_{up u} / P_T| <= kappa_n/alpha_2
fuer alle Atome s,u der Leiter mit beta/alpha <= 1/2.
    python3 krylov_laurent.py
"""
import sys
from fractions import Fraction as Fr
import spectral as S


def laurent_coeff_minus2(num, den, extra=8):
    """[c^{-2}] von num(c)/den(c) bei c=oo; num, den aufsteigende Koeffizienten."""
    # Division absteigend: num/den = sum_{k} r_k c^{k}, k <= deg num - deg den
    dn, dd = len(num) - 1, len(den) - 1
    # Arbeite mit x = 1/c: num(c)/den(c) = c^{dn-dd} * Num(x)/Den(x), Num(x)=sum num[dn-i] x^i
    Num = [num[dn - i] for i in range(dn + 1)]
    Den = [den[dd - i] for i in range(dd + 1)]
    # Potenzreihe Num/Den in x bis Ordnung K
    K = dn - dd + 2 + extra
    if K < 0:
        return Fr(0)
    ser = []
    rem = Num[:] + [Fr(0)] * (K + 1)
    for k in range(K + 1):
        coef = rem[k] / Den[0]
        ser.append(coef)
        for i in range(len(Den)):
            if k + i < len(rem):
                rem[k + i] -= coef * Den[i]
    # c^{dn-dd} x^k = c^{dn-dd-k}; wir wollen Exponent -2: k = dn-dd+2
    k = dn - dd + 2
    return ser[k] if 0 <= k < len(ser) else Fr(0)


def main():
    ok = True
    for alpha, beta, n in ((Fr(1, 2), Fr(1, 3), 5), (Fr(1, 2), Fr(1, 4), 6), (Fr(1, 3), Fr(1, 2), 5)):
        Minf = alpha / (1 - alpha) + beta / (1 - beta)
        alF = [alpha ** i / Minf for i in range(1, n + 1)]
        beF = [beta ** j / Minf for j in range(1, n + 1)]
        P = S.ladder(alF, beF)
        TK, *_ = S.hankel_certificate(P)
        PT = P.chain_poly()
        worst = Fr(0)
        for s in P.atoms:
            Ps = S.up_poset(P, s).chain_poly()
            for u in P.atoms:
                if u < s:
                    continue
                Pu = S.up_poset(P, u).chain_poly()
                prod = [Fr(0)] * (len(Ps) + len(Pu) - 1)
                for i, x in enumerate(Ps):
                    for j, y in enumerate(Pu):
                        prod[i + j] += x * y
                val = laurent_coeff_minus2(prod, PT)
                lhs = TK[s][u] / (P.masses[s] * P.masses[u])
                if lhs != val:
                    ok = False
                worst = max(worst, abs(val))
        print(f'({alpha},{beta}), n={n}: Identitaet T_K/(m m) = +[c^-2] P_up P_up / P_T {"exakt" if ok else "FEHL"}; max |[c^-2]| ueber Atome = {float(worst):.8f}')
    print('rc', 0 if ok else 1)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
