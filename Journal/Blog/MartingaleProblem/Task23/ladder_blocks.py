r"""Die Leiter blockweise: Potentiale, erzwungene Spitzenzeile, und der Test
"A-Block des optimalen Zertifikats = Kettenzertifikat der alpha-Kette".

PROTOKOLL, dreissigster Lauf.  Leiter a_i<b_j iff i<j, Massen alpha^i/M,
beta^j/M (M = M_oo wie in ladder_lp.py).  Fuer ein Zertifikat T (Krylow exakt
oder LP-optimal, mpmath) werden gebildet

    p        = T_{t* a_1},  1-p = T_{t* b_1}      (Spitzenzeile)
    H(j,l)   = (1/beta_j) ( sum_{j'>l} T_{b_j b_j'} + T_{b_j t*} ),  l>=0
    J(i,l)   = (1/alpha_i)( sum_{j>l}  T_{a_i b_j}  + T_{a_i t*} ),  l>=0
    K(l,i)   = (1/beta_l) sum_{i'>i} T_{a_i' b_l},                    i>=0
    Phi(i,k) = (1/alpha_i) sum_{i'>k} T_{a_i a_i'},                    k>=0

und geprueft:  (P1) Spitzen- und Nullzeile auf {0,a_1,b_1} getragen;
(P2) H symmetrisch (Bed. 2 an (b_j,b_l));  (P3) J(i,l) = K(l,i) + H(l,i)
(Bed. 2 an (a_i,b_l));  (P4) F := Phi + J symmetrisch (Bed. 2 an (a_i,a_k));
(P5) F(i,0) = 0 (Bed. 3 an a_i, bei T_{0 a_i}=0);  (P6) beta_l H(l,0) =
-sum_i T_{a_i b_l} (Bed. 3 an b_l).  Dann: ist p im Nullraum frei?  Und:
stimmt der A-Block des LP-Optimums mit dem Krylow-Zertifikat der alpha-Kette
(gleiche Massen, eigener Gipfel) ueberein?

    python3 ladder_blocks.py 1/2 1/3 6 8 10        (exakt: Krylow;  LP: mpmath)
"""
import sys
from fractions import Fraction as Fr
import mpmath as mp
import spectral as S
import ladder_lp as L

FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


def blocks(P, T, n, tol=None):
    """T als Funktion (i,j)->Zahl auf Indizes 0..2n+1. a_i = i, b_j = n+j."""
    t = P.t
    m = P.masses
    A = lambda i: i            # 1..n
    B = lambda j: n + j        # 1..n
    al = lambda i: m[A(i)]
    be = lambda j: m[B(j)]
    zero = Fr(0) if tol is None else mp.mpf(0)
    eq = (lambda x, y: x == y) if tol is None else (lambda x, y: abs(x - y) <= tol)
    p = T(t, A(1))
    # (P1)
    top_ok = all(eq(T(t, x), zero) for x in range(2 * n + 2) if x not in (0, A(1), B(1)))
    zero_ok = all(eq(T(0, x), zero) for x in range(2 * n + 2) if x not in (0, A(1), B(1)))
    check(top_ok and eq(T(t, 0) + T(t, A(1)) + T(t, B(1)), 1), 'P1 Spitzenzeile auf {0,a1,b1}, Summe 1')
    check(zero_ok and eq(T(0, 0) + T(0, A(1)) + T(0, B(1)), zero), 'P1 Nullzeile auf {0,a1,b1}, Summe 0')
    H = lambda j, l: (sum((T(B(j), B(jj)) for jj in range(l + 1, n + 1)), zero) + T(B(j), t)) / be(j)
    J = lambda i, l: (sum((T(A(i), B(jj)) for jj in range(l + 1, n + 1)), zero) + T(A(i), t)) / al(i)
    K = lambda l, i: sum((T(A(ii), B(l)) for ii in range(i + 1, n + 1)), zero) / be(l)
    Phi = lambda i, k: sum((T(A(i), A(ii)) for ii in range(k + 1, n + 1)), zero) / al(i)
    check(all(eq(H(j, l), H(l, j)) for j in range(1, n + 1) for l in range(1, n + 1)), 'P2 H symmetrisch')
    check(all(eq(J(i, l), K(l, i) + H(l, i)) for i in range(1, n + 1) for l in range(1, n + 1)), 'P3 J(i,l) = K(l,i) + H(l,i)')
    F = lambda i, k: Phi(i, k) + J(i, k)
    check(all(eq(F(i, k), F(k, i)) for i in range(1, n + 1) for k in range(1, n + 1)), 'P4 F = Phi + J symmetrisch')
    check(all(eq(F(i, 0) + T(A(i), 0) / al(i), zero) for i in range(1, n + 1)), 'P5 F(i,0) = -T_{a_i 0}/alpha_i')
    check(all(eq(be(l) * H(l, 0) + sum((T(A(i), B(l)) for i in range(1, n + 1)), zero) + T(B(l), 0), zero) for l in range(1, n + 1)), 'P6 beta_l H(l,0) = -sum_i T_{a_i b_l} - T_{b_l 0}')
    return dict(p=p, H=H, J=J, K=K, Phi=Phi, F=F)


def main(argv):
    alpha, beta = Fr(argv[1]), Fr(argv[2])
    ns = [int(x) for x in argv[3:] if not x.startswith('--')] or [6, 8]
    Minf = alpha / (1 - alpha) + beta / (1 - beta)
    print(f'Leiter ({alpha},{beta}), M_oo = {Minf}')
    for n in ns:
        alF = [alpha ** i / Minf for i in range(1, n + 1)]
        beF = [beta ** j / Minf for j in range(1, n + 1)]
        P = S.ladder(alF, beF)
        TK, b, r, c = S.hankel_certificate(P)
        print(f'\n== n={n}: Krylow-Zertifikat, exakt ==')
        bl = blocks(P, lambda i, j: TK[i][j], n)
        print(f'  p = T_(t*,a1) = {bl["p"]},  1-p = {TK[P.t][n+1]}')
        # Nullraum: ist p frei?
        tk, basis, wt, idx = L.certificate_space(P)
        k_ta1 = idx[(1, P.t)]
        k_tb1 = idx[(n + 1, P.t)]
        k_0a1 = idx[(0, 1)]
        k_0b1 = idx[(0, n + 1)]
        mx = lambda k: max(abs(D[k]) for D in basis)
        print(f'  dim Nullraum = {len(basis)};  max|D| an (t*,a1) = {mp.nstr(mx(k_ta1), 5)}, (t*,b1) = {mp.nstr(mx(k_tb1), 5)}, (0,a1) = {mp.nstr(mx(k_0a1), 5)}, (0,b1) = {mp.nstr(mx(k_0b1), 5)}')
        # alpha-Kette allein, gleiche Massen, eigener Gipfel
        C = S.chain(alF)
        TC, _, _, _ = S.hankel_certificate(C)
        diffA = max(abs(TK[i][j] - TC[i][j]) for i in range(1, n + 1) for j in range(1, n + 1))
        print(f'  max |T_K[A,A] - T_chain(alpha)[A,A]| = {float(diffA):.3e}   (Krylow der Leiter gegen Krylow der Kette)')
        if '--lp' in argv:
            val, (cmax, lam, resid) = L.chebyshev_lp(tk, basis, wt)
            # T_opt Eintraege: resid[k] = T_opt/w  ->  T_opt = resid*wt
            pos = {k: ij for ij, k in idx.items()}
            Topt = {}
            for k, ij in pos.items():
                Topt[ij] = resid[k] * wt[k]
            Tf = lambda i, j: Topt[(min(i, j), max(i, j))]
            print(f'== n={n}: LP-optimales Zertifikat, mpmath ({mp.mp.dps} Stellen), C = {mp.nstr(val, 12)} ==')
            tol = mp.mpf(10) ** (-30)
            blo = blocks(P, Tf, n, tol=tol)
            print(f'  p = T_opt(t*,a1) = {mp.nstr(blo["p"], 12)}')
            w = [S.fr(P.masses[i]) + (1 if i in (0, P.t) else 0) for i in range(2 * n + 2)]
            dA = max(abs(Tf(i, j) - S.fr(TC[i][j])) / (w[i] * w[j]) for i in range(1, n + 1) for j in range(1, n + 1))
            print(f'  max |T_opt[A,A] - T_chain(alpha)[A,A]| / (w w) = {mp.nstr(dA, 6)}')
            # gewichtete Normen der Bloecke
            nAA = max(abs(Tf(i, j)) / (w[i] * w[j]) for i in range(1, n + 1) for j in range(1, n + 1))
            nAB = max(abs(Tf(i, n + j)) / (w[i] * w[n + j]) for i in range(1, n + 1) for j in range(1, n + 1))
            nBB = max(abs(Tf(n + i, n + j)) / (w[n + i] * w[n + j]) for i in range(1, n + 1) for j in range(1, n + 1))
            nCh = max(abs(S.fr(TC[i][j])) / (w[i] * w[j]) for i in range(1, n + 1) for j in range(1, n + 1))
            print(f'  ||T_opt||_m auf AA / AB / BB = {mp.nstr(nAA, 8)} / {mp.nstr(nAB, 8)} / {mp.nstr(nBB, 8)};   ||T_chain(alpha)||_m auf AA = {mp.nstr(nCh, 8)}')
            # Zeilensummen von Q = T_opt[A,B]
            qs = [sum(Tf(i, n + j) for j in range(1, n + 1)) for i in range(1, n + 1)]
            print(f'  Zeilensummen von Q=T_opt[A,B]: {[mp.nstr(q, 6) for q in qs[:5]]} ...')
            ps = [sum(Tf(i, j) for j in range(1, n + 1)) for i in range(1, n + 1)]
            print(f'  Zeilensummen von P=T_opt[A,A]: {[mp.nstr(q, 6) for q in ps[:5]]} ...')
            if '--dump' in argv:
                import pickle
                with open(f'ladder_opt_{alpha.numerator}_{alpha.denominator}_{beta.numerator}_{beta.denominator}_n{n}.pkl', 'wb') as f:
                    pickle.dump({(i, j): str(v) for (i, j), v in Topt.items()}, f)
    print('\nFEHL:', FAIL if FAIL else 'keine')
    return 1 if FAIL else 0


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    sys.exit(main(sys.argv))
