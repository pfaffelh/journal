import sys
from fractions import Fraction as Fr
import mpmath as mp
import spectral as S
import ladder_lp as L
alpha, beta, n = Fr(sys.argv[1]), Fr(sys.argv[2]), int(sys.argv[3])
Minf = alpha / (1 - alpha) + beta / (1 - beta)
alF = [alpha ** i / Minf for i in range(1, n + 1)]
beF = [beta ** j / Minf for j in range(1, n + 1)]
P = S.ladder(alF, beF)
tk, basis, wt, idx = L.certificate_space(P)
val, (cmax, lam, resid) = L.chebyshev_lp(tk, basis, wt)
pos = {k: ij for ij, k in idx.items()}
N = P.n + 2
names = {0: '0', P.t: 't*'}
for i in range(1, N - 1):
    names[i] = f'a{i}' if i <= n else f'b{i - n}'
R = [[None] * N for _ in range(N)]
for k, (i, j) in pos.items():
    R[i][j] = R[j][i] = resid[k]
print(f'T_opt/(w w), ({alpha},{beta}), n={n}, C={mp.nstr(val, 10)}')
print('       ' + ''.join(f'{names[j]:>9}' for j in range(N)))
for i in range(N):
    print(f'{names[i]:>6} ' + ''.join(f'{mp.nstr(R[i][j], 4):>9}' for j in range(N)))
