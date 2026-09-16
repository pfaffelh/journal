r"""Lauf 31, Theorem 37: eine fundierte Halbordnung ohne beschraenktes Zertifikat.

T = {0} u {a_1<a_2<...} u {b_1<b_2<...} u {t*}, zwei disjunkte omega-Ketten
(a_i || b_j fuer alle i,j), alpha_i = B^-i, beta_j = B^-j * (2 falls j ungerade,
1/2 falls j gerade), Basis B >= 8 (sortiert fallend; B=2 waere nur eine Umordnung von {1} u {2^-j : j>=2}).  Alle Massen positiv, summierbar, A fundiert.

Nach Theorem 36 hat jedes beschraenkte Zertifikat T_{t* a_1} = lim_k alpha_1
e_{k-1}(alpha_{>=2}) / (e_k(alpha) + e_k(beta)).  Mit q = 1/B gilt exakt
    e_k(beta)/e_k(alpha) = 2^[k ungerade] * R_k * (q;q)_k,
    R_k = sum_{0<=t_1<=...<=t_k} q^{sum t} prod_{l: t_l ungerade} 4^{(-1)^l},
also 1 <= R_k <= 1/(4q;4q)_oo, und fuer B >= 16 ist
    limsup_{k gerade} <= 1/(4q;4q)_oo  <  2 (q;q)_oo <= liminf_{k ungerade}
(B=16: 1.4524 < 1.8672).  Der Limes existiert nicht -- also gibt es kein
unendliches Zertifikat, in keiner endlichen Gewichtsklasse (Theorem 37).
Bei B=8 ist die grobe Schranke nicht trennend (3.46 gegen 1.72), gemessen sind
die Limiten 1.3315 / 1.8440 aber ebenfalls verschieden.  Konsequenz: sup_n ||T_n||_m = oo fuer JEDE Wahl von
Trunkierungszertifikaten (sonst gaebe ein Teilfolgenlimes ein beschraenktes
Zertifikat), also ist auch Proposition 19.3 dort unanwendbar.

Teil (i): der oszillierende Quotient, mpmath;  Teil (ii): Proposition 29 auf den
Trunkierungen, exakt: T_{t* a_1} = 1/(1 + prod_{l<=n} beta_l/alpha_l) in {1/2, 1/3};
Teil (iii): LP-Minimum ueber alle Zertifikate der Trunkierung, n = 3..8, zum
Vergleich dieselben Ketten unperturbiert (2^-i, 3^-j) und identisch (2^-i, 2^-i).

    python3 two_chains.py [B] [n ...]
"""
import sys
from fractions import Fraction as Fr
import mpmath as mp
import spectral as S
import ladder_lp as L

mp.mp.dps = 80
FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


def two_chains(alpha, beta):
    n = len(alpha)

    def lt(x, y):
        return (x < n) == (y < n) and x < y
    return S.Poset('ZweiKetten', list(alpha) + list(beta), lt)


def esym(ms, K):
    e = [mp.mpf(1)] + [mp.mpf(0)] * K
    for m in ms:
        for k in range(K, 0, -1):
            e[k] += m * e[k - 1]
    return e


def profile(kind, N):
    base = Fr(1, 2)
    if kind.startswith('gestoert'):
        base = Fr(1, int(kind[8:]))
    al = [base ** i for i in range(1, N + 1)]
    if kind.startswith('gestoert'):
        # sortiert fallend, Quotienten beta_j/alpha_j = 2, 1/2, 2, 1/2, ...
        be = [base ** j * (Fr(2) if j % 2 else Fr(1, 2)) for j in range(1, N + 1)]
        assert all(be[i] > be[i + 1] for i in range(N - 1))
    elif kind == 'drittel':
        be = [Fr(1, 3) ** j for j in range(1, N + 1)]
    else:
        be = al[:]
    return al, be


def part_i(kind):
    print(f'Teil (i), {kind}: q_k = alpha_1 e_(k-1)(alpha_>=2) / (e_k(alpha)+e_k(beta)), N=400 Stufen')
    al, be = profile(kind, 400)
    K = 80
    alm = [S.fr(x) for x in al]
    bem = [S.fr(x) for x in be]
    ea, ea2, eb = esym(alm, K), esym(alm[1:], K), esym(bem, K)
    q = [alm[0] * ea2[k - 1] / (ea[k] + eb[k]) for k in range(1, K + 1)]
    rat = [eb[k] / ea[k] for k in range(1, K + 1)]
    for k in (1, 2, 3, 4, 9, 10, 19, 20, 39, 40, 59, 60, 79, 80):
        print(f'     k={k:2d}  q_k={mp.nstr(q[k - 1], 20)}   e_k(beta)/e_k(alpha)={mp.nstr(rat[k - 1], 12)}')
    return q


def part_ii(kind):
    print(f'Teil (ii), {kind}: Spitzenzeile der Trunkierungen (Proposition 29), exakt')
    vals = []
    for n in range(2, 11):
        al, be = profile(kind, n)
        P = two_chains(al, be)
        TK, b, r, c = S.hankel_certificate(P)
        pa = TK[P.t][1]
        want = 1 / (1 + Fr(1) * (lambda p: p)(eval('*'.join(['1'] + [f'Fr({b_.numerator},{b_.denominator})/Fr({a_.numerator},{a_.denominator})' for a_, b_ in zip(al, be)]))))
        check(pa == want, f'{kind} n={n}: T_(t*,a_1) = {pa} = 1/(1+prod beta/alpha), r={r}')
        vals.append(pa)
    return vals


def part_iii(kind, ns):
    print(f'Teil (iii), {kind}: LP-Minimum ueber alle Zertifikate der Trunkierung')
    out = []
    for n in ns:
        al, be = profile(kind, n)
        P = two_chains(al, be)
        tk, basis, wt, idx = L.certificate_space(P)
        kn = max(abs(t) / w for t, w in zip(tk, wt))
        try:
            val, (cmax, lam, resid) = L.chebyshev_lp(tk, basis, wt)
        except RuntimeError as exc:
            # bekannte numerische Sackgasse (Lauf 29): dichter Simplex bei schlechter Skalierung; kein Befund
            print(f'     n={n}: dim Nullraum={len(basis)}, Krylow ||T||_m={mp.nstr(kn, 8)}, LP: Simplex numerisch abgebrochen ({exc}) -- nicht gemessen', flush=True)
            continue
        print(f'     n={n}: dim Nullraum={len(basis)}, Krylow ||T||_m={mp.nstr(kn, 8)}, LP-Minimum={mp.nstr(val, 10)} (primal {mp.nstr(cmax, 8)})', flush=True)
        out.append(val)
    return out


def main():
    kind = 'gestoert' + (sys.argv[1] if len(sys.argv) > 1 else '8')
    q = part_i(kind)
    even = [q[k - 1] for k in range(2, 81, 2)]
    odd = [q[k - 1] for k in range(1, 81, 2)]
    check(abs(even[-1] - even[-2]) < mp.mpf(10) ** -20 and abs(odd[-1] - odd[-2]) < mp.mpf(10) ** -20,
          f'{kind}: gerade und ungerade Teilfolge konvergieren (Zuwaechse {mp.nstr(abs(even[-1]-even[-2]),3)}, {mp.nstr(abs(odd[-1]-odd[-2]),3)})')
    check(abs(even[-1] - odd[-1]) > mp.mpf(1) / 20,
          f'{kind}: die Limiten sind verschieden: gerade {mp.nstr(even[-1], 15)}, ungerade {mp.nstr(odd[-1], 15)} -- kein Limes, kein Zertifikat (Theorem 36)')
    q3 = part_i('drittel')
    check(abs(q3[-1] - 1) < mp.mpf(10) ** -20, f'drittel: q_k -> 1 (k=80: {mp.nstr(q3[-1], 12)})')
    qs = part_i('gleich')
    check(abs(qs[-1] - mp.mpf(1) / 2) < mp.mpf(10) ** -20, f'gleich: q_k -> 1/2 (Symmetrie; k=80: {mp.nstr(qs[-1], 12)})')
    v = part_ii(kind)
    check(all(v[i] == (Fr(1, 3) if (i + 2) % 2 else Fr(1, 2)) for i in range(len(v))), f'{kind}: Spitzenzeile der Trunkierungen alterniert 1/2, 1/3 -- konvergiert nicht')
    ns = [int(x) for x in sys.argv[2:]] or [3, 4, 5, 6, 7, 8]
    lp = part_iii(kind, ns)
    check(lp[-1] > lp[0] * 2, f'{kind}: LP-Minimum waechst ({mp.nstr(lp[0], 6)} -> {mp.nstr(lp[-1], 6)})')
    lp3 = part_iii('drittel', ns)
    lpg = part_iii('gleich', ns)
    print('FEHLER:', len(FAIL))
    for f in FAIL:
        print('  ', f)
    return 1 if FAIL else 0


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    sys.exit(main())
