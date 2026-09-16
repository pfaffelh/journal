r"""Krylow-Zertifikat gegen die Schranke von Theorem 31, exakt (Lauf 30).
Bei stark getrennten Skalen ist das Krylow-Zertifikat gemessen optimal
(LP = Krylow); hier: ist ||T_K||_m = |kappa_n|/alpha_2 EXAKT, und bis zu
welchem n?      python3 krylov_vs_bound.py
"""
import sys
from fractions import Fraction as Fr
import spectral as S
import toprow as TR


def run(alpha, beta, ns):
    Minf = alpha / (1 - alpha) + beta / (1 - beta)
    out = []
    for n in ns:
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
        out.append((n, norm == lb, float(norm / lb)))
    print(f'({alpha},{beta}), beta/alpha={float(beta/alpha):.3f}: ' + ', '.join(f'n={n}: {"=" if eq else f"{q:.6g}x"}' for n, eq, q in out))


def main():
    ns = list(range(4, 17, 2))
    for a, b in ((Fr(1, 2), Fr(1, 4)), (Fr(1, 3), Fr(1, 9)), (Fr(1, 2), Fr(1, 5)), (Fr(1, 2), Fr(1, 3)),
                 (Fr(1, 4), Fr(1, 2)), (Fr(1, 5), Fr(1, 2)), (Fr(1, 9), Fr(1, 3)), (Fr(1, 3), Fr(1, 2))):
        run(a, b, ns)


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    main()
