r"""Lauf 31: jedes Zertifikat ist auf dem Krylow-Raum von 1 festgelegt.

Proposition 35 (endlich oder unendlich, beschraenkt):  T V^k 1 = psi_k := (V^T)^k e_{t*}
fuer alle k >= 0, denn T V^k 1 = (V^T)^k T 1 = (V^T)^k e_{t*}.  Bilinear:
(V^k 1)^T T (V^l 1) = c_{k+l} mit c_j = (V^j 1)_{t*} = e_j (Ketten aus j Atomen).

Theorem 36 (Spitzenzeile im Unendlichen):  auf einer abzaehlbaren Halbordnung mit
Maximum t*, m_0 = m_{t*} = 0, M = sum m_a < oo, hat jedes unendliche Zertifikat
in der Gewichtsklasse {0, t*} die Spalte
    T e_{t*} = lim_k psi_k / e_k,      d.h.   T_{t* a} = m_a lim_k e_{k-1}(up a) / e_k(T),
und der Limes existiert, sobald ein Zertifikat existiert.  Beweis: V^k 1 / e_k -> e_{t*}
in der gewichteten l^1-Norm, denn sum_a m_a (V^k 1)_a = e_{k+1} und
e_{k+1}/e_k <= M/(k+1).

Teil A prueft Proposition 35 exakt (Krylow) und auf 1e-40 (Krylow + zufaellige
Nullraumrichtung) an endlichen Halbordnungen.  Teil B berechnet den Limes auf der
unendlichen Leiter und vergleicht mit dem Trunkierungslimes 1 - pi_oo (Korollar 29.1).

    python3 krylov_moments.py
"""
import random, sys
from fractions import Fraction as Fr
import mpmath as mp
import spectral as S
import ladder_lp as L

mp.mp.dps = 60
FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


def matvec(A, v):
    return [sum((A[i][j] * v[j] for j in range(len(v))), type(v[0])(0)) for i in range(len(A))]


def krylov_ones(P):
    """V^k 1, k = 0..r (bis Null), exakt."""
    N = P.n + 2
    v = [Fr(1)] * N
    out = [v]
    while any(v):
        v = matvec(P.V, v)
        out.append(v)
    return out


def psis(P):
    N = P.n + 2
    Vt = [[P.V[j][i] for j in range(N)] for i in range(N)]
    v = [Fr(1) if i == P.t else Fr(0) for i in range(N)]
    out = [v]
    while any(v):
        v = matvec(Vt, v)
        out.append(v)
    return out


def full_matrix(vec, idx, N):
    T = [[mp.mpf(0)] * N for _ in range(N)]
    for (i, j), k in idx.items():
        T[i][j] = vec[k]
        T[j][i] = vec[k]
    return T


def test_finite(P, tag, rng):
    N = P.n + 2
    TK, b, r, c = S.hankel_certificate(P)
    K1 = krylov_ones(P)
    Ps = psis(P)
    check(len(K1) == len(Ps), f'{tag}: V^k 1 und psi_k verschwinden ab demselben k (r={r})')
    # exakt am Krylow-Zertifikat
    ok = True
    for k in range(len(K1)):
        lhs = matvec(TK, K1[k])
        if lhs != Ps[k]:
            ok = False
    check(ok, f'{tag}: T_K V^k 1 = psi_k exakt, k=0..{len(K1)-1}')
    # Hankel: (V^k 1)^T T (V^l 1) = c_{k+l}
    e = P.chain_moments()
    ok = True
    for k in range(len(K1)):
        for l in range(len(K1)):
            val = sum((K1[k][i] * x for i, x in enumerate(matvec(TK, K1[l]))), Fr(0))
            want = e[k + l] if k + l < len(e) else Fr(0)
            if val != want:
                ok = False
    check(ok, f'{tag}: (V^k 1)^T T_K (V^l 1) = e_{{k+l}} exakt')
    # Krylow + Nullraum
    tk, basis, wt, idx = L.certificate_space(P)
    lam = [mp.mpf(rng.uniform(-3, 3)) for _ in basis]
    vec = [tk[i] + sum(lam[j] * basis[j][i] for j in range(len(basis))) for i in range(len(tk))]
    T = full_matrix(vec, idx, N)
    worst = mp.mpf(0)
    for k in range(len(K1)):
        lhs = matvec(T, [mp.mpf(S.fr(x)) for x in K1[k]])
        for i in range(N):
            worst = max(worst, abs(lhs[i] - mp.mpf(S.fr(Ps[k][i]))))
    check(worst < mp.mpf(10) ** -40, f'{tag}: T V^k 1 = psi_k fuer Krylow + Nullraum (dim {len(basis)}), max Abw. {mp.nstr(worst, 3)}')
    # Gegenprobe: eine Nullraumrichtung allein hat D V^k 1 = 0
    if basis:
        D = full_matrix(basis[0], idx, N)
        worst = max(abs(x) for k in range(len(K1)) for x in matvec(D, [mp.mpf(S.fr(y)) for y in K1[k]]))
        check(worst < mp.mpf(10) ** -40, f'{tag}: D V^k 1 = 0 fuer Nullraumrichtung, max {mp.nstr(worst, 3)}')


# ---------------------------------------------------------------- Teil B

def poly_mul_trunc(p, q, K):
    out = [mp.mpf(0)] * (K + 1)
    for i, x in enumerate(p):
        if i > K or x == 0:
            continue
        for j, y in enumerate(q):
            if i + j > K:
                break
            out[i + j] += x * y
    return out


def ladder_ek(alphas, betas, K):
    """e_0..e_K der Leiter mit Stufen (alphas[i], betas[i]), a_i<b_j iff i<j.
    Z_n = (1 + x beta_n) Z_{n-1} + x alpha_n A_{n-1},  A_n = (1 + x alpha_n) A_{n-1}."""
    Z = [mp.mpf(1)] + [mp.mpf(0)] * K
    A = [mp.mpf(1)] + [mp.mpf(0)] * K
    for al, be in zip(alphas, betas):
        Zn = Z[:]
        for k in range(1, K + 1):
            Zn[k] += be * Z[k - 1] + al * A[k - 1]
        An = A[:]
        for k in range(1, K + 1):
            An[k] += al * A[k - 1]
        Z, A = Zn, An
    return Z


def esym(ms, K):
    e = [mp.mpf(1)] + [mp.mpf(0)] * K
    for m in ms:
        for k in range(K, 0, -1):
            e[k] += m * e[k - 1]
    return e


def infinite_ladder(alpha, beta, K, N):
    alpha, beta = S.fr(alpha), S.fr(beta)
    al = [alpha ** i for i in range(1, N + 1)]
    be = [beta ** j for j in range(1, N + 1)]
    e = ladder_ek(al, be, K + 1)                # ganze Leiter
    e_up_a1 = ladder_ek(al[1:], be[1:], K + 1)  # Stufen >= 2 = up a_1
    e_B2 = esym(be[1:], K + 1)                  # b_j, j >= 2 = up b_1
    e_up_a2 = ladder_ek(al[2:], be[2:], K + 1)
    rows = []
    for k in range(1, K + 1):
        pa = al[0] * e_up_a1[k - 1] / e[k]
        pb = be[0] * e_B2[k - 1] / e[k]
        rest = e_up_a1[k] / e[k]
        pa2 = al[1] * e_up_a2[k - 1] / e[k]
        rows.append((k, pa, pb, rest, pa2, e[k + 1] / e[k]))
    return rows


def theta_limit(alpha, beta, terms=400):
    q = S.fr(alpha) / S.fr(beta)
    if q >= 1:
        return mp.mpf(0)
    return 1 / mp.nsum(lambda i: q ** (i * (i + 1) / 2), [0, mp.inf])


def part_b():
    print('Teil B: die Spitzenzeile auf der unendlichen Leiter, p_a = alpha_1 e_{k-1}(up a_1)/e_k, p_b = beta_1 e_{k-1}(B_{>=2})/e_k')
    for alpha, beta in ((Fr(1, 2), Fr(1, 3)), (Fr(1, 3), Fr(1, 2)), (Fr(1, 2), Fr(2, 3)), (Fr(1, 4), Fr(1, 2)), (Fr(1, 2), Fr(1, 2)), (Fr(1, 2), Fr(49, 100))):
        pi_inf = theta_limit(alpha, beta)
        K = 40
        rows_N1 = infinite_ladder(alpha, beta, K, 200)
        rows_N2 = infinite_ladder(alpha, beta, K, 400)
        stab = max(abs(r1[1] - r2[1]) + abs(r1[2] - r2[2]) for r1, r2 in zip(rows_N1, rows_N2))
        print(f'  ({alpha},{beta}): 1-pi_oo = {mp.nstr(1 - pi_inf, 15)}, pi_oo = {mp.nstr(pi_inf, 15)};  Stabilitaet N=200 vs 400: {mp.nstr(stab, 3)}')
        for (k, pa, pb, rest, pa2, ratio) in rows_N2:
            if k in (1, 2, 3, 5, 8, 12, 16, 20, 30, 40):
                print(f'     k={k:2d}  p_a={mp.nstr(pa, 15)}  p_b={mp.nstr(pb, 15)}  1-p_a-p_b={mp.nstr(rest, 3)}  T_(t*,a_2)-Kandidat={mp.nstr(pa2, 3)}  e_(k+1)/e_k={mp.nstr(ratio, 3)}')
        k, pa, pb, rest, pa2, ratio = rows_N2[-1]
        M = S.fr(alpha / (1 - alpha) + beta / (1 - beta))
        # bewiesene Raten: 1-p_a-p_b = e_k(up a_1)/e_k <= M/(k alpha_1);  e_(k+1)/e_k <= M/(k+1)
        check(all(r[3] <= M / (r[0] * S.fr(alpha)) and r[5] <= M / (r[0] + 1) for r in rows_N2),
              f'({alpha},{beta}): Raten e_k(up a_1)/e_k <= M/(k alpha_1) und e_(k+1)/e_k <= M/(k+1) fuer alle k<=40')
        if alpha < beta:
            tol = max(mp.mpf(10) ** -12, 4 * rest)   # Abweichung darf den nicht abgeklungenen Rest nicht uebersteigen
            check(abs(pa - (1 - pi_inf)) < tol and abs(pb - pi_inf) < tol,
                  f'({alpha},{beta}): lim_k = Trunkierungslimes 1-pi_oo (Abw. {mp.nstr(abs(pa - (1 - pi_inf)), 3)}, Rest {mp.nstr(rest, 3)})')
        elif alpha == beta:
            check(all(abs(r[2] - (1 - S.fr(beta) ** r[0]) / (r[0] + 1)) < mp.mpf(10) ** -50 for r in rows_N2),
                  f'({alpha},{beta}): p_b(k) = (1-beta^k)/(k+1) exakt (Lemma 36.2), also p = 1')
        else:
            bound = [(S.fr(beta) / S.fr(alpha)) ** (r[0] * (r[0] + 1) / 2) / mp.qp(S.fr(beta)) for r in rows_N2]
            check(all(r[2] <= b for r, b in zip(rows_N2, bound)), f'({alpha},{beta}): p_b(k) <= (beta/alpha)^(k(k+1)/2)/(beta;beta)_oo (Korollar 36.1(c)), also p = 1')
    # omega-Ketten-Gegenprobe: m_1 e_{k-1}(m_{>=2}) / e_k -> 1
    for prof in ((lambda i: mp.mpf(2) ** -i), (lambda i: mp.mpf(1) / (i * (i + 1))), (lambda i: mp.mpf(i) ** mp.mpf(-1.5))):
        ms = [prof(i) for i in range(1, 401)]
        K = 40
        e = esym(ms, K)
        e2 = esym(ms[1:], K)
        vals = [ms[0] * e2[k - 1] / e[k] for k in range(1, K + 1)]
        Mm = sum(ms)
        check(all(1 - vals[k - 1] <= Mm / (k * ms[0]) for k in range(1, K + 1)),
              f'omega-Kette {mp.nstr(ms[0],3)},{mp.nstr(ms[1],3)},...: 1 - m_1 e_(k-1)(m_>=2)/e_k <= M/(k m_1) (k=40: Wert {mp.nstr(vals[-1], 12)})')


def main():
    rng = random.Random(31)
    print('Teil A: T V^k 1 = psi_k fuer jedes Zertifikat endlicher Halbordnungen')
    for k in range(6):
        n = rng.randint(3, 7)
        P = S.random_poset(n, rng)
        test_finite(P, f'zufaellig #{k} n={n}', rng)
    test_finite(S.chain([Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(1, 16)]), 'Kette', rng)
    test_finite(S.antichain([Fr(1, 2), Fr(1, 3), Fr(1, 6)]), 'Antikette', rng)
    test_finite(S.crown([Fr(1, 2), Fr(1, 4), Fr(1, 8)], [Fr(1, 3), Fr(1, 9), Fr(1, 27)]), 'Krone', rng)
    for alpha, beta in ((Fr(1, 2), Fr(1, 3)), (Fr(1, 3), Fr(1, 2))):
        Minf = alpha / (1 - alpha) + beta / (1 - beta)
        for n in (3, 5, 7):
            P = S.ladder([alpha ** i / Minf for i in range(1, n + 1)], [beta ** j / Minf for j in range(1, n + 1)])
            test_finite(P, f'Leiter ({alpha},{beta}) n={n}', rng)
    part_b()
    print('FEHLER:', len(FAIL))
    for f in FAIL:
        print('  ', f)
    return 1 if FAIL else 0


if __name__ == '__main__':
    sys.exit(main())
