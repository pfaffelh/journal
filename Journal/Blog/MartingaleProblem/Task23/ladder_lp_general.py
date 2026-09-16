r"""LP-Minimum gegen die Schranke von Theorem 31 an nicht-geometrischen
Profilen (Lauf 30).   python3 ladder_lp_general.py
"""
import sys
from fractions import Fraction as Fr
import mpmath as mp
import spectral as S
import toprow as TR
import ladder_lp as L


def run(alF, beF, tag):
    n = len(alF)
    P = S.ladder(alF, beF)
    form, d = TR.toprow_formula(P)
    p = form[1]
    kappa = p / alF[0] - (1 - p) / beF[0]
    lb = max(abs(kappa) / alF[1], (1 - p) / (beF[0] * beF[1]))
    tk, basis, wt, idx = L.certificate_space(P)
    val, (cmax, lam, resid) = L.chebyshev_lp(tk, basis, wt)
    pos = {k: ij for ij, k in idx.items()}
    N = P.n + 2
    names = {0: '0', P.t: 't*'}
    for i in range(1, N - 1):
        names[i] = f'a{i}' if i <= n else f'b{i - n}'
    act = sorted(((abs(r), j) for j, r in enumerate(resid)), reverse=True)
    active = [f'({names[pos[j][0]]},{names[pos[j][1]]})' for a, j in act if a > cmax * (1 - mp.mpf(10) ** -8)]
    print(f'{tag}, n={n}: Schranke {mp.nstr(S.fr(lb), 10)}, LP-Minimum {mp.nstr(val, 10)}, Quotient {mp.nstr(val / S.fr(lb), 8)}')
    print('      aktiv:', ', '.join(active))


def main():
    for n in (4, 6, 8):
        run([Fr(1, i * (i + 1)) for i in range(1, n + 1)], [Fr(1, 3 ** j) for j in range(1, n + 1)], 'alpha=1/(i(i+1)), beta=3^-j')
        run([Fr(1, 2 ** i) for i in range(1, n + 1)], [Fr(1, j * (j + 1)) for j in range(1, n + 1)], 'alpha=2^-i, beta=1/(j(j+1))')
        run([Fr(1, 2 ** i) for i in range(1, n + 1)], [Fr(1, 3 ** j) * (1 + Fr((-1) ** j, 5)) for j in range(1, n + 1)], 'alpha=2^-i, beta=3^-j(1+(-1)^j/5)')
        run([Fr(1, 2 ** i) * (1 + Fr((-1) ** i, 5)) for i in range(1, n + 1)], [Fr(1, 3 ** j) for j in range(1, n + 1)], 'alpha=2^-i(1+(-1)^i/5), beta=3^-j')


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    main()
