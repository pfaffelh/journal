r"""LP-optimales Zertifikat der Leiter in Potentialform (Lauf 30).
    python3 ladder_opt_view.py 1/2 1/3 10
"""
import sys
from fractions import Fraction as Fr
import mpmath as mp
import spectral as S
import ladder_lp as L

def main(argv):
    alpha, beta = Fr(argv[1]), Fr(argv[2])
    n = int(argv[3])
    Minf = alpha / (1 - alpha) + beta / (1 - beta)
    alF = [alpha ** i / Minf for i in range(1, n + 1)]
    beF = [beta ** j / Minf for j in range(1, n + 1)]
    P = S.ladder(alF, beF)
    tk, basis, wt, idx = L.certificate_space(P)
    val, (cmax, lam, resid) = L.chebyshev_lp(tk, basis, wt)
    pos = {k: ij for ij, k in idx.items()}
    Topt = {ij: resid[k] * wt[k] for k, ij in pos.items()}
    T = lambda i, j: Topt[(min(i, j), max(i, j))]
    m = [S.fr(x) for x in P.masses]
    t = P.t
    A = lambda i: i; B = lambda j: n + j
    al = lambda i: m[A(i)]; be = lambda j: m[B(j)]
    print(f'Leiter ({alpha},{beta}) n={n}: C = {mp.nstr(val, 12)}')
    print('T/(w w) an der Ecke: (a1,a1) =', mp.nstr(T(1,1)/al(1)**2, 8), ' (b1,b1) =', mp.nstr(T(B(1),B(1))/be(1)**2, 8), ' (a1,b1) =', mp.nstr(T(1,B(1))/(al(1)*be(1)), 8))
    print('Zeile a1 gegen b:  T_(a1,bj)/(alpha1 beta_j):', [mp.nstr(T(1, B(j))/(al(1)*be(j)), 6) for j in range(1, n+1)])
    print('Zeile a2 gegen b:  T_(a2,bj)/(alpha2 beta_j):', [mp.nstr(T(2, B(j))/(al(2)*be(j)), 6) for j in range(1, n+1)])
    print('Zeile a3 gegen b:  T_(a3,bj)/(alpha3 beta_j):', [mp.nstr(T(3, B(j))/(al(3)*be(j)), 6) for j in range(1, n+1)])
    print('Spalte b1 gegen a: T_(ai,b1)/(alpha_i beta1):', [mp.nstr(T(i, B(1))/(al(i)*be(1)), 6) for i in range(1, n+1)])
    print('Spalte b2 gegen a: T_(ai,b2)/(alpha_i beta2):', [mp.nstr(T(i, B(2))/(al(i)*be(2)), 6) for i in range(1, n+1)])
    print('Diagonale AA: T_(ai,ai)/alpha_i^2:', [mp.nstr(T(i,i)/al(i)**2, 6) for i in range(1, n+1)])
    print('Diagonale BB: T_(bj,bj)/beta_j^2:', [mp.nstr(T(B(j),B(j))/be(j)**2, 6) for j in range(1, n+1)])
    print('Zeile a1 in AA: T_(a1,ai)/(alpha1 alpha_i):', [mp.nstr(T(1,i)/(al(1)*al(i)), 6) for i in range(1, n+1)])
    print('Zeile b1 in BB: T_(b1,bj)/(beta1 beta_j):', [mp.nstr(T(B(1),B(j))/(be(1)*be(j)), 6) for j in range(1, n+1)])
    # Potentiale
    H = lambda j, l: (sum(T(B(j), B(jj)) for jj in range(l + 1, n + 1)) + T(B(j), t)) / be(j)
    J = lambda i, l: (sum(T(A(i), B(jj)) for jj in range(l + 1, n + 1)) + T(A(i), t)) / al(i)
    K = lambda l, i: sum(T(A(ii), B(l)) for ii in range(i + 1, n + 1)) / be(l)
    Phi = lambda i, k: sum(T(A(i), A(ii)) for ii in range(k + 1, n + 1)) / al(i)
    print('H(j,0) (Rand des b-Blocks):', [mp.nstr(H(j,0), 6) for j in range(1, n+1)])
    print('J(i,0) = -Phi(i,0) (Rand des a-Blocks):', [mp.nstr(J(i,0), 6) for i in range(1, n+1)])
    print('Spaltensummen von Q, sum_i Q_il / beta_l:', [mp.nstr(sum(T(i,B(l)) for i in range(1,n+1))/be(l), 6) for l in range(1, n+1)])
    print('Zeilensummen von Q, sum_j Q_ij / alpha_i:', [mp.nstr(sum(T(i,B(j)) for j in range(1,n+1))/al(i), 6) for i in range(1, n+1)])
    print('H-Tabelle (j,l), j,l=1..5:')
    for j in range(1, 6):
        print('   ', [mp.nstr(H(j,l), 6) for l in range(1, 6)])
    print('F=Phi+J Tabelle (i,k), 1..5:')
    for i in range(1, 6):
        print('   ', [mp.nstr(Phi(i,k)+J(i,k), 6) for k in range(1, 6)])
    print('Phi Tabelle (i,k), 1..5:')
    for i in range(1, 6):
        print('   ', [mp.nstr(Phi(i,k), 6) for k in range(1, 6)])
    print('J Tabelle (i,l), 1..5:')
    for i in range(1, 6):
        print('   ', [mp.nstr(J(i,l), 6) for l in range(1, 6)])
    print('K Tabelle (l,i), 1..5:')
    for l in range(1, 6):
        print('   ', [mp.nstr(K(l,i), 6) for i in range(1, 6)])

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    main(sys.argv)
