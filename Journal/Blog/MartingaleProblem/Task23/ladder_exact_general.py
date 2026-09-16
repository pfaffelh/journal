r"""Satz 32 / Lemma 33 an NICHT-geometrischen Profilen (Lauf 30).  p_n aus der
Kettenzaehlung (Proposition 29, toprow.toprow_formula), C_n = kappa_n/alpha_2,
Saettigungssystem wie in ladder_exact_opt.py, exakt.

    python3 ladder_exact_general.py
"""
import sys
from fractions import Fraction as Fr
import spectral as S
import toprow as TR
import ladder_exact_opt as LE


def run(alF, beF, tag, mode_b=False):
    n = len(alF)
    P = S.ladder(alF, beF)
    N = P.n + 2
    m = P.masses
    idx = {}
    for i in range(N):
        for j in range(i, N):
            idx[(i, j)] = len(idx)
    E = len(idx)
    var = lambda i, j: idx[(min(i, j), max(i, j))]
    rows = []
    for s in range(N):
        for u in range(s + 1, N):
            row = [Fr(0)] * E
            for a in range(N):
                if P.less(u, a):
                    row[var(s, a)] += m[u]
                if P.less(s, a):
                    row[var(a, u)] -= m[s]
            if any(row):
                rows.append(row)
    for s in range(N):
        row = [Fr(0)] * E
        for a in range(N):
            row[var(s, a)] += 1
        rows.append(row)
    basis = LE.nullspace_exact(rows, E)
    TK, *_ = S.hankel_certificate(P)
    tk = [TK[i][j] for (i, j) in idx]
    form, d = TR.toprow_formula(P)
    p = form[1]
    assert TK[P.t][1] == p
    kappa = p / alF[0] - (1 - p) / beF[0]
    C = abs(kappa) / alF[1]
    lb = max(C, (1 - p) / (beF[0] * beF[1]))
    if mode_b:
        targets = [((n + 1, n + 1), -C * beF[0] ** 2)] + [((i, n + 1), -C * alF[i - 1] * beF[0]) for i in range(1, n + 1)] + [((1, 1), -C * alF[0] ** 2)]
    else:
        targets = [((1, 1), -C * alF[0] ** 2)] + [((1, n + j), -C * alF[0] * beF[j - 1]) for j in range(1, n + 1)] + [((n + 1, n + 1), -C * beF[0] ** 2)]
    A = [[D[var(*ij)] for D in basis] for ij, _ in targets]
    b = [t - tk[var(*ij)] for ij, t in targets]
    lam, cons, defect = LE.solve_exact(A, b)
    print(f'{tag}, n={n}: p_n={float(p):.6f}, C_n=|kappa_n|/alpha_2={float(C):.8f}, Schranke={float(lb):.8f}; System konsistent={cons}, Rangdefekt={defect}', end='')
    if not cons:
        print()
        return
    T = [tk[k] + sum(l * D[k] for l, D in zip(lam, basis)) for k in range(E)]
    w = [m[i] + (1 if i in (0, P.t) else 0) for i in range(N)]
    norm = max(abs(T[var(i, j)]) / (w[i] * w[j]) for i in range(N) for j in range(i, N))
    print(f'; ||T||_m = {float(norm):.8f} = C_n? {norm == C}')
    if not mode_b:
        sig = lambda l: sum(beF[l:], Fr(0))
        base = C * alF[0] - p / alF[0]
        ok33 = all(T[var(n + 1, n + l)] == beF[l - 1] * (base + C * sig(l)) for l in range(2, n + 1)) and T[var(0, n + 1)] == beF[0] * (base + C * sig(0))
        print(f'      Lemma 33: {"exakt" if ok33 else "FEHL"}')


def main():
    for n in (4, 6, 8):
        # alpha langsam (harmonisch), beta geometrisch
        run([Fr(1, i * (i + 1)) for i in range(1, n + 1)], [Fr(1, 3 ** j) for j in range(1, n + 1)], 'alpha=1/(i(i+1)), beta=3^-j')
        # alpha geometrisch 1/2, beta = 1/(j(j+1)) langsamer -> Fall alpha<beta (Spiegel)
        run([Fr(1, 2 ** i) for i in range(1, n + 1)], [Fr(1, j * (j + 1)) for j in range(1, n + 1)], 'alpha=2^-i, beta=1/(j(j+1)) [--b]', mode_b=True)
        # zwei geometrische mit Stoerung: beta_j = 3^-j (1 + (-1)^j/5)
        run([Fr(1, 2 ** i) for i in range(1, n + 1)], [Fr(1, 3 ** j) * (1 + Fr((-1) ** j, 5)) for j in range(1, n + 1)], 'alpha=2^-i, beta=3^-j(1+(-1)^j/5)')
        # alpha gestoert
        run([Fr(1, 2 ** i) * (1 + Fr((-1) ** i, 5)) for i in range(1, n + 1)], [Fr(1, 3 ** j) for j in range(1, n + 1)], 'alpha=2^-i(1+(-1)^i/5), beta=3^-j')


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    main()
