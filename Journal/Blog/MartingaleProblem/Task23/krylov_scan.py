r"""Satz 34 zu groesserem n und feinerem Skalenverhaeltnis (Lauf 30):
||T_K||_m gegen |kappa_n|/alpha_2, exakt, Leiter alpha=1/2, beta=q/2.
    python3 krylov_scan.py
"""
import sys
from fractions import Fraction as Fr
import spectral as S
import toprow as TR


def one(alpha, beta, n):
    Minf = alpha / (1 - alpha) + beta / (1 - beta)
    alF = [alpha ** i / Minf for i in range(1, n + 1)]
    beF = [beta ** j / Minf for j in range(1, n + 1)]
    P = S.ladder(alF, beF)
    TK, *_ = S.hankel_certificate(P)
    form, d = TR.toprow_formula(P)
    p = form[1]
    kappa = p / alF[0] - (1 - p) / beF[0]
    lb = max(abs(kappa) / alF[1], (1 - p) / (beF[0] * beF[1]))
    N = P.n + 2
    w = [P.masses[i] + (1 if i in (0, P.t) else 0) for i in range(N)]
    norm = max(abs(TK[i][j]) / (w[i] * w[j]) for i in range(N) for j in range(i, N))
    return norm == lb, float(norm / lb)


def main():
    for alpha, q in ((Fr(1, 2), Fr(1, 3)), (Fr(1, 2), Fr(2, 5)), (Fr(1, 2), Fr(1, 2)), (Fr(1, 2), Fr(11, 20)),
                     (Fr(1, 2), Fr(3, 5)), (Fr(1, 2), Fr(5, 8)), (Fr(1, 2), Fr(2, 3)), (Fr(1, 2), Fr(3, 2)),
                     (Fr(1, 4), Fr(2)), (Fr(1, 6), Fr(3))):
        beta = alpha * q
        res = []
        for n in (10, 16, 22, 28):
            eq, r = one(alpha, beta, n)
            res.append(f'n={n}: {"=" if eq else f"{r:.4g}x"}')
            if not eq and r > 1e3:
                break
        print(f'({alpha},{beta}) beta/alpha={float(q):.3f}: ' + ', '.join(res), flush=True)


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    main()
