r"""Untere Schranke fuer jedes Zertifikat der Leiter-Trunkierung (Lauf 30,
Theorem 31): mit p_n = T_{t* a_1} (Korollar 29.1) und
    kappa_n := p_n/alpha_1 - (1-p_n)/beta_1
gilt fuer JEDES Zertifikat exakt
    (E1) T_{a_2 b_n} = kappa_n beta_n,    T_{a_i b_n} = 0  (i>=3),
    (E2) T_{b_2 b_n} = (1-p_n) beta_n/beta_1,   T_{b_l b_n} = 0  (l>=3),
    (E3) T_{a_2 a_n} + T_{a_2 b_n}... nein: T_{a_n a_2} + T_{a_n b_2} = p_n alpha_n/alpha_1,
         T_{a_n a_k} + T_{a_n b_k} = 0  (k>=3),
also ||T||_m >= max(|kappa_n|/alpha_2, (1-p_n)/(beta_1 beta_2)).
Geprueft: (E1)-(E3) exakt am Krylow-Zertifikat und am Krylow-Zertifikat plus
zufaelligen Nullraumrichtungen (mpmath); dann LP-Minimum gegen die Schranke.

    python3 ladder_lowerbound.py            (Standardprofile)
    python3 ladder_lowerbound.py 1/2 1/3 6 8 10 12
"""
import sys, random
from fractions import Fraction as Fr
import mpmath as mp
import spectral as S
import ladder_lp as L

FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


def bound(alpha, beta, n, alF, beF):
    pi_n = 1 / sum((alpha / beta) ** (i * (i + 1) // 2) for i in range(n + 1))
    p = 1 - pi_n
    kappa = p / alF[0] - (1 - p) / beF[0]
    return p, kappa, max(abs(kappa) / alF[1], (1 - p) / (beF[0] * beF[1]))


def identities(T, n, alF, beF, p, kappa, eq):
    A = lambda i: i
    B = lambda j: n + j
    ok = eq(T(A(2), B(n)), kappa * beF[n - 1])
    ok &= all(eq(T(A(i), B(n)), 0) for i in range(3, n + 1))
    ok &= eq(T(B(2), B(n)), (1 - p) * beF[n - 1] / beF[0])
    ok &= all(eq(T(B(l), B(n)), 0) for l in range(3, n))
    ok &= eq(T(A(n), A(2)) + T(A(n), B(2)), p * alF[n - 1] / alF[0])
    ok &= all(eq(T(A(n), A(k)) + T(A(n), B(k)), 0) for k in range(3, n))
    return ok


def run(alpha, beta, ns, lp=True):
    Minf = alpha / (1 - alpha) + beta / (1 - beta)
    print(f'\nLeiter ({alpha},{beta}), M_oo = {Minf}')
    rng = random.Random(31)
    for n in ns:
        alF = [alpha ** i / Minf for i in range(1, n + 1)]
        beF = [beta ** j / Minf for j in range(1, n + 1)]
        P = S.ladder(alF, beF)
        TK, *_ = S.hankel_certificate(P)
        p, kappa, lb = bound(alpha, beta, n, alF, beF)
        check(TK[P.t][1] == p, f'n={n}: p_n = {float(p):.10f} (Korollar 29.1)')
        check(identities(lambda i, j: TK[i][j], n, alF, beF, p, kappa, lambda x, y: x == y),
              f'n={n}: (E1)-(E3) exakt am Krylow-Zertifikat')
        tk, basis, wt, idx = L.certificate_space(P)
        pos = {k: ij for ij, k in idx.items()}
        # Krylow + zufaellige Nullraumkombination
        lam = [mp.mpf(rng.uniform(-3, 3)) for _ in basis]
        Tr = {ij: S.fr(TK[ij[0]][ij[1]]) + sum(l * D[k] for l, D in zip(lam, basis)) for k, ij in pos.items()}
        Tf = lambda i, j: Tr[(min(i, j), max(i, j))]
        tol = mp.mpf(10) ** -40
        check(identities(Tf, n, [S.fr(x) for x in alF], [S.fr(x) for x in beF], S.fr(p), S.fr(kappa),
                         lambda x, y: abs(x - y) <= tol),
              f'n={n}: (E1)-(E3) an Krylow + zufaelliger Nullraumrichtung (dim {len(basis)})')
        if lp:
            val, (cmax, lam2, resid) = L.chebyshev_lp(tk, basis, wt)
            rel = abs(val - S.fr(lb)) / S.fr(lb)
            print(f'      LP-Minimum = {mp.nstr(val, 14)},  Schranke max(|kappa_n|/alpha_2, (1-p_n)/(beta_1 beta_2)) = {mp.nstr(S.fr(lb), 14)},  |kappa_n|/alpha_2 = {mp.nstr(S.fr(abs(kappa)/alF[1]), 14)},  rel. Abstand {mp.nstr(rel, 3)}')
            check(rel < mp.mpf(10) ** -9, f'n={n}: LP-Minimum = Schranke auf 1e-9')


def main(argv):
    if len(argv) > 3:
        run(Fr(argv[1]), Fr(argv[2]), [int(x) for x in argv[3:]])
    else:
        for a, b, ns in ((Fr(1, 2), Fr(1, 3), [4, 6, 8, 10]), (Fr(1, 3), Fr(1, 2), [6, 8, 10]),
                         (Fr(1, 2), Fr(2, 3), [6, 8, 10]), (Fr(1, 4), Fr(1, 2), [6, 8, 10]),
                         (Fr(2, 3), Fr(1, 2), [6, 8, 10]), (Fr(1, 5), Fr(1, 2), [6, 8])):
            run(a, b, ns)
    print('\nFEHL:', FAIL if FAIL else 'keine')
    return 1 if FAIL else 0


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    sys.exit(main(sys.argv))
