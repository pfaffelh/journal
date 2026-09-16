r"""Exakte Kandidaten fuer das optimale Zertifikat der Leiter-Trunkierung
(Lauf 30).  Vermutung aus den LP-Daten bei alpha > beta:  das Optimum ist das
EINZIGE Zertifikat mit
    T_{a_1 u} = -C alpha_1 m_u   fuer u in {a_1} u B          (n+1 Gleichungen)
    T_{b_1 b_1} = -C beta_1^2                                  (1 Gleichung)
mit C = kappa_n/alpha_2 (rational).  Das sind n+2 Gleichungen auf dem
(n+2)-dimensionalen Zertifikatsraum T_K + span(D_k).  Geprueft: eindeutig
loesbar?  ||T||_m = C exakt?  Und die Eintraege als Brueche.

    python3 ladder_exact_opt.py 1/2 1/3 4 6 8 10
    python3 ladder_exact_opt.py 1/3 1/2 4 6 8 --b     (alpha < beta: Zeile b_1 gesaettigt)
    python3 ladder_exact_opt.py 1/2 1/4 4 6 8 --bb    (beta/alpha <= 1/2: Zeile b_1 auf B gesaettigt)
"""
import sys
from fractions import Fraction as Fr
import spectral as S


def nullspace_exact(rows, ncols):
    rows = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        bi = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if bi is None:
            continue
        rows[r], rows[bi] = rows[bi], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
        if r == len(rows):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [Fr(0)] * ncols
        v[fc] = Fr(1)
        for i, pc in enumerate(piv):
            v[pc] = -rows[i][fc]
        basis.append(v)
    return basis


def solve_exact(A, b):
    """Loest A x = b exakt; gibt (x, konsistent, rangdefekt)."""
    m, k = len(A), len(A[0])
    M = [A[i][:] + [b[i]] for i in range(m)]
    piv = []
    r = 0
    for c in range(k):
        bi = next((i for i in range(r, m) if M[i][c] != 0), None)
        if bi is None:
            continue
        M[r], M[bi] = M[bi], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    consistent = all(M[i][-1] == 0 for i in range(r, m))
    x = [Fr(0)] * k
    for i, pc in enumerate(piv):
        x[pc] = M[i][-1]
    return x, consistent, k - len(piv)


def main(argv):
    alpha, beta = Fr(argv[1]), Fr(argv[2])
    ns = [int(x) for x in argv[3:] if not x.startswith('--')] or [4, 6]
    Minf = alpha / (1 - alpha) + beta / (1 - beta)
    for n in ns:
        alF = [alpha ** i / Minf for i in range(1, n + 1)]
        beF = [beta ** j / Minf for j in range(1, n + 1)]
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
        basis = nullspace_exact(rows, E)
        TK, *_ = S.hankel_certificate(P)
        tk = [Fr(0)] * E
        for (i, j), k in idx.items():
            tk[k] = TK[i][j]
        # Schranke
        pi_n = 1 / sum((alpha / beta) ** (i * (i + 1) // 2) for i in range(n + 1))
        p = 1 - pi_n
        kappa = p / alF[0] - (1 - p) / beF[0]
        C = abs(kappa) / alF[1]
        # Saettigungsgleichungen: T_{a1,u} = -C alpha_1 m_u (u in {a1} u B), T_{b1 b1} = -C beta_1^2
        if '--bb' in argv:
            # stark getrennte Skalen (beta/alpha <= 1/2): Zeile b_1 auf B gesaettigt
            # (-C an (b_1,b_1), +C an (b_1,b_j), j>=2), dazu (a_1,a_1) = (a_1,b_1) = -C
            targets = [((n + 1, n + 1), -C * beF[0] ** 2)] + [((n + 1, n + j), C * beF[0] * beF[j - 1]) for j in range(2, n + 1)] + [((1, 1), -C * alF[0] ** 2), ((1, n + 1), -C * alF[0] * beF[0])]
        elif '--b' in argv:
            # alpha < beta: gesaettigte Zeile b_1 auf A u {b_1}, dazu Ecke (a_1,a_1)
            targets = [((n + 1, n + 1), -C * beF[0] ** 2)] + [((i, n + 1), -C * alF[i - 1] * beF[0]) for i in range(1, n + 1)] + [((1, 1), -C * alF[0] ** 2)]
        else:
            targets = [((1, 1), -C * alF[0] ** 2)] + [((1, n + j), -C * alF[0] * beF[j - 1]) for j in range(1, n + 1)] + [((n + 1, n + 1), -C * beF[0] ** 2)]
        A = [[D[var(*ij)] for D in basis] for ij, _ in targets]
        b = [t - tk[var(*ij)] for ij, t in targets]
        lam, cons, defect = solve_exact(A, b)
        print(f'n={n}: dim Nullraum {len(basis)}, {len(targets)} Saettigungsgleichungen: konsistent={cons}, Rangdefekt={defect}')
        if not cons:
            continue
        T = [tk[k] + sum(l * D[k] for l, D in zip(lam, basis)) for k in range(E)]
        w = [m[i] + (1 if i in (0, P.t) else 0) for i in range(N)]
        norm = max(abs(T[var(i, j)]) / (w[i] * w[j]) for i in range(N) for j in range(i, N))
        print(f'      ||T||_m = {norm} = C? {norm == C}   (C = {C} = {float(C):.12f})')
        # Lemma 33: aus der Saettigung der Zeile a_1 folgt ueber (AB) bei i=1 und (3b)
        #   T_{b_1 b_l} = beta_l (C alpha_1 - p/alpha_1 + C sigma_l)     (2 <= l <= n),
        #   T_{0 b_1}   = beta_1 (C alpha_1 - p/alpha_1 + C M_beta),      sigma_l = sum_{l<j<=n} beta_j
        if '--b' not in argv and '--bb' not in argv:
            sig = lambda l: sum(beF[l:], Fr(0))
            base = C * alF[0] - p / alF[0]
            ok33 = all(T[var(n + 1, n + l)] == beF[l - 1] * (base + C * sig(l)) for l in range(2, n + 1))
            ok33 &= T[var(0, n + 1)] == beF[0] * (base + C * sig(0))
            print(f'      Lemma 33 (Zeile b_1 und T_(0,b_1) geschlossen): {"exakt" if ok33 else "FEHL"}')
        names = {0: '0', P.t: 't*'}
        for i in range(1, N - 1):
            names[i] = f'a{i}' if i <= n else f'b{i - n}'
        def show(i, j):
            v = T[var(i, j)] / (w[i] * w[j])
            return f'{names[i]},{names[j]}: {v} = {float(v):.8f}'
        for pair in ((0, 0), (0, 1), (0, n + 1), (1, 2), (1, 3), (2, 2), (2, 3), (n + 1, n + 2), (n + 1, n + 3), (n + 2, n + 2), (n + 2, n + 3), (2, n + 1), (3, n + 1), (3, n + 2), (2, n + 2)):
            print('      ', show(*pair))


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    main(sys.argv)
