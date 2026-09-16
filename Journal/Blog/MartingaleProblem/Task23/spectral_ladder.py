r"""Das Spektralzertifikat auf der unendlichen Leiter.

PROTOKOLL, neunundzwanzigster Lauf, "Das Kettenpolynom", Probe (B).

Leiter: T = {0} u {a_i} u {b_j} u {t*}, a_i<a_i' iff i<i', b_j<b_j' iff j<j',
a_i<b_j iff i<j, nie b<a.  Massen alpha_i, beta_j > 0, summierbar.  Mit

    Pb_{>i}(c) = prod_{j>i} (1 - c beta_j),   Pa_{<i}(c) = prod_{i'<i} (1 - c alpha_i'),
    Pb(c) = Pb_{>0}(c),  Pa(c) = prod_i (1 - c alpha_i)

ist das Kettenpolynom (Lemma 27.1; jede Kette hat ein groesstes a-Element
a_i oder besteht aus b's; im ersten Fall ist sie eine Teilmenge von
a_{<i} u {a_i} u b_{>i}, und jede solche Teilmenge ist eine Kette)

    P_T(c) = Pb(c) - c sum_i alpha_i Pa_{<i}(c) Pb_{>i}(c),

und die Resolvente y^c = (I + cW)^{-1} m ist

    y_{b_j} = beta_j Pb_{>j}(c),
    y_{a_i} = alpha_i (Pb_{>i}(c) - c U_i),   U_i = sum_{i'>i} alpha_i' Pa_{(i,i')}(c) Pb_{>i'}(c),

Pa_{(i,i')} = prod_{i<i''<i'} (1 - c alpha_i'').  (Rueckwaertsrekursion
U_{i-1} = (1 - c alpha_i) U_i + alpha_i Pb_{>i}, U_oo = 0.)

Proben:
  (B1) P_T und y^c stimmen auf der endlichen Leiter mit spectral.Poset ueberein
  (B2) Nullstellen von P_T: reell? einfach?  Vergleich mit den Nullstellen der
       Trunkierungen (exakte Koeffizienten, polyroots)
  (B3) die Residuenidentitaet (R): sum_k gamma_k c_k^-2 y^{c_k} = m
  (B4) sup |T_su| / (w_s w_u) auf wachsenden Fenstern, M = 1 normiert
  (B5) die Spektralreihe fuer den Eckeintrag T[a1,a1] -- sie DIVERGIERT
       (Lauf 29); nur gemessen

  python3 spectral_ladder.py trunc [n ...]  -- das Krylow-Zertifikat auf den
       Trunkierungen n = 8..24 (Theorem 28), ||T||_m und Eckeintraege; die
       Explosion bei (1/3,1/2) ab n = 18, bei (1/2,2/3) ab n = 30, und die
       Konvergenz bei (1/4,1/2) bis n = 32 (Lauf 29, Nachtrag)
"""
import sys
from fractions import Fraction as Fr

import mpmath as mp

mp.mp.dps = 50
TOL = mp.mpf(10) ** (-25)
FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


class Ladder:
    """alpha, beta: Listen der Massen alpha[1..N], beta[1..N] (Index 0 leer),
    N = Trunkierung der unendlichen Produkte."""

    def __init__(self, alpha, beta):
        assert len(alpha) == len(beta)
        self.N = len(alpha) - 1
        self.al = alpha
        self.be = beta
        self.M = sum(alpha[1:]) + sum(beta[1:])

    # Produkte
    def Pb_gt(self, i, c):
        p = mp.mpf(1)
        for j in range(i + 1, self.N + 1):
            p *= (1 - c * self.be[j])
        return p

    def Pa_lt(self, i, c):
        p = mp.mpf(1)
        for k in range(1, i):
            p *= (1 - c * self.al[k])
        return p

    def P(self, c):
        # P_T(c) = Pb(c) - c sum_i alpha_i Pa_{<i}(c) Pb_{>i}(c); Pb_{>i} und
        # Pa_{<i} laufend
        N = self.N
        Pb = [None] * (N + 2)
        Pb[N] = mp.mpf(1)
        for i in range(N - 1, -1, -1):
            Pb[i] = Pb[i + 1] * (1 - c * self.be[i + 1])
        s = mp.mpf(0)
        pa = mp.mpf(1)
        for i in range(1, N + 1):
            s += self.al[i] * pa * Pb[i]
            pa *= (1 - c * self.al[i])
        return Pb[0] - c * s

    def dP(self, c):
        return mp.diff(self.P, c)

    def y(self, c):
        """(ya[1..N], yb[1..N])."""
        N = self.N
        Pb = [None] * (N + 2)
        Pb[N] = mp.mpf(1)
        for i in range(N - 1, -1, -1):
            Pb[i] = Pb[i + 1] * (1 - c * self.be[i + 1])
        yb = [None] + [self.be[j] * Pb[j] for j in range(1, N + 1)]
        U = [None] * (N + 2)
        U[N] = mp.mpf(0)
        for i in range(N, 0, -1):
            U[i - 1] = (1 - c * self.al[i]) * U[i] + self.al[i] * Pb[i]
        ya = [None] + [self.al[i] * (Pb[i] - c * U[i]) for i in range(1, N + 1)]
        return ya, yb

    def x(self, c):
        """Vektor ueber (0; a_1..a_N; b_1..b_N; t*)."""
        ya, yb = self.y(c)
        return [mp.mpf(0)] + ya[1:] + yb[1:] + [-1 / c]

    def zeros(self, K, cmax_factor=None):
        """Die K kleinsten positiven reellen Nullstellen von P_T, per
        Vorzeichenwechsel auf einem logarithmischen Gitter plus Bisektion."""
        found = []
        # Gitter: von 0.5/M bis weit hinaus; Schrittweite fein im Log
        lo = mp.mpf('0.5') / self.M
        c = lo
        f = self.P(c)
        grid = mp.mpf(1) + mp.mpf(1) / 400
        while len(found) < K:
            c2 = c * grid
            f2 = self.P(c2)
            if f == 0:
                found.append(c)
            elif f * f2 < 0:
                found.append(self._bisect(c, c2, f, f2))
            c, f = c2, f2
            if c > mp.mpf(10) ** 40:
                break
        return found

    def _bisect(self, a, b, fa, fb):
        for _ in range(200):
            mid = (a + b) / 2
            fm = self.P(mid)
            if fm == 0:
                return mid
            if fa * fm < 0:
                b, fb = mid, fm
            else:
                a, fa = mid, fm
            if (b - a) < a * mp.mpf(10) ** (-46):
                break
        return (a + b) / 2

    def spectral_entries(self, zs):
        """gamma_k und x^{c_k} fuer die Nullstellen zs."""
        out = []
        for c in zs:
            g = -c / self.dP(c)
            out.append((c, g, self.x(c)))
        return out


def geometric(alpha, beta, N):
    al = [None] + [mp.mpf(alpha) ** i for i in range(1, N + 1)]
    be = [None] + [mp.mpf(beta) ** j for j in range(1, N + 1)]
    return al, be


def normalize(al, be):
    M = sum(al[1:]) + sum(be[1:])
    return [None] + [a / M for a in al[1:]], [None] + [b / M for b in be[1:]]


def probe_B():
    import spectral as S
    print('(B) Die unendliche Leiter')
    # (B1) endliche Kontrolle
    n = 6
    alF = [Fr(1, 2) ** i for i in range(1, n + 1)]
    beF = [Fr(1, 3) ** j for j in range(1, n + 1)]
    P = S.ladder(alF, beF)
    coeffs = P.chain_poly()
    L = Ladder([None] + [S.fr(a) for a in alF], [None] + [S.fr(b) for b in beF])
    dev = mp.mpf(0)
    devy = mp.mpf(0)
    for c in (mp.mpf('0.7'), mp.mpf('2.3'), mp.mpf('-1.1'), mp.mpf('5.5')):
        dev = max(dev, abs(L.P(c) - S.poly_eval(coeffs, c)))
        ya, yb = L.y(c)
        yP = P.y(c)
        devy = max(devy, max(abs(ya[i] - yP[i - 1]) for i in range(1, n + 1)),
                   max(abs(yb[j] - yP[n + j - 1]) for j in range(1, n + 1)))
    check(dev < TOL, f'(B1) P_T-Formel = Kettenpolynom auf der endlichen Leiter n={n}: {mp.nstr(dev, 2)}')
    check(devy < TOL, f'(B1) y^c-Formeln = Resolvente auf der endlichen Leiter n={n}: {mp.nstr(devy, 2)}')

    # Bei (2/3,1/2) hat schon die Trunkierung komplexe Nullstellen, der reelle
    # Scan ist dort unvollstaendig; bei (1/2,1/2) konvergiert (R) nur langsam.
    # Beides wird gemessen und ausgewiesen, nicht als Fehler gezaehlt.
    for (alpha, beta, claim) in (('1/2', '1/3', True), ('1/3', '1/2', True), ('1/2', '2/3', True),
                                 ('2/3', '1/2', False), ('1/2', '1/2', False)):
        print(f'\n  --- Leiter alpha={alpha}, beta={beta}, auf M=1 normiert'
              + ('' if claim else ' (nur gemessen, s. PROTOKOLL Lauf 29)') + ' ---')
        N = 300
        al, be = geometric(S.fr(Fr(alpha)), S.fr(Fr(beta)), N)
        al, be = normalize(al, be)
        L = Ladder(al, be)
        K = 24
        zs = L.zeros(K)
        print('   die ersten Nullstellen c_k:', ' '.join(mp.nstr(z, 8) for z in zs[:8]))
        print('   Quotienten c_{k+1}/c_k   :', ' '.join(mp.nstr(zs[k + 1] / zs[k], 6) for k in range(min(10, len(zs) - 1))))
        # (B2) Vergleich mit den Trunkierungen (exakt -> polyroots)
        for n in (8, 12):
            alF = [Fr(alpha) ** i for i in range(1, n + 1)]
            beF = [Fr(beta) ** j for j in range(1, n + 1)]
            MF = sum(alF) + sum(beF)
            # dieselbe Normierung wie oben: durch M der UNENDLICHEN Leiter
            Minf = Fr(alpha) / (1 - Fr(alpha)) + Fr(beta) / (1 - Fr(beta))
            Pn = S.ladder([a / Minf for a in alF], [b / Minf for b in beF])
            rts = S.roots_of(Pn.chain_poly())
            real = all(abs(mp.im(r)) < mp.mpf(10) ** -20 for r in rts)
            rr = sorted(mp.re(r) for r in rts)
            close = [abs(rr[k] - zs[k]) for k in range(min(4, len(rr), len(zs)))]
            print(f'   Trunkierung n={n}: {len(rts)} Nullstellen, {"reell" if real else "KOMPLEX"};'
                  f' Abstand zu den unendlichen: ' + ' '.join(mp.nstr(d, 2) for d in close))
            if claim:
                check(real, f'(B2) alpha={alpha},beta={beta}: Nullstellen der Trunkierung n={n} reell')
            elif not real:
                print(f'   -> komplexe Nullstellen der Trunkierung: ' + ', '.join(mp.nstr(r, 6) for r in rts if abs(mp.im(r)) > 1e-20))
        # Einfachheit: P' an den Nullstellen
        dPs = [L.dP(z) for z in zs]
        check(all(abs(d) > mp.mpf(10) ** -30 for d in dPs), f'(B2) alpha={alpha},beta={beta}: Nullstellen einfach (P_T\' != 0)')
        # (B3) Residuenidentitaet
        ent = L.spectral_entries(zs)
        Wn = 24   # Fenster
        for Kuse in (8, 16, K):
            res = mp.mpf(0)
            for idx in list(range(1, Wn + 1)) + list(range(N + 1, N + Wn + 1)):
                s = sum(g / c ** 2 * x[idx] for (c, g, x) in ent[:Kuse])
                mass = al[idx] if idx <= N else be[idx - N]
                res = max(res, abs(s - mass) / mass)
            print(f'   (R) mit K={Kuse:2d} Nullstellen: groesster relativer Fehler {mp.nstr(res, 3)}')
        if claim:
            check(res < mp.mpf(10) ** -20, f'(B3) alpha={alpha},beta={beta}: Residuenidentitaet (R) auf den ersten {Wn} Atomen je Kette')
        else:
            print(f'   (R) nicht als Aussage gefuehrt: {"Spektrum unvollstaendig (komplexe Nullstellen)" if alpha == "2/3" else "Konvergenz zu langsam fuer eine Aussage"}')
        # (B4) Schranke
        tstar = 2 * N + 1
        w = [mp.mpf(1)] + al[1:] + be[1:] + [mp.mpf(1)]

        def T_entry(s, u):
            v = -sum(g * x[s] * x[u] for (c, g, x) in ent)
            if s == tstar and u == tstar:
                v += 1
            return v
        for Wn2 in (6, 12, 24):
            idxs = [0] + list(range(1, Wn2 + 1)) + list(range(N + 1, N + Wn2 + 1)) + [tstar]
            best, arg = mp.mpf(0), None
            for s in idxs:
                for u in idxs:
                    if u < s:
                        continue
                    q = abs(T_entry(s, u)) / (w[s] * w[u])
                    if q > best:
                        best, arg = q, (s, u)

            def name(i):
                if i == 0:
                    return '0'
                if i == tstar:
                    return 't*'
                return f'a{i}' if i <= N else f'b{i - N}'
            print(f'   Fenster {Wn2:2d}: sup |T_su|/(w_s w_u) = {mp.nstr(best, 10)} an ({name(arg[0])},{name(arg[1])})')
        # (B5) die Spektralreihe fuer T_{a1 a1}: Terme -gamma_k x_k(a1)^2
        terms = [-g * x[1] ** 2 for (c, g, x) in ent]
        print('   (B5) Terme der Spektralreihe fuer T[a1,a1], k=0..' + str(K - 1) + ':')
        print('        ' + ' '.join(mp.nstr(t, 3) for t in terms))
        grow = abs(terms[-1]) > 10 * abs(terms[K // 2]) > 0
        print(f'        Divergenz (|Term_{K-1}| > 10 |Term_{K // 2}|): {grow}')
        # Zeile t* und Zeile 0
        print('   T[t*,.] auf (0,a1,a2,b1,b2):', ' '.join(mp.nstr(T_entry(tstar, u), 8) for u in (0, 1, 2, N + 1, N + 2)))
        print('   T[0,.]  auf (0,a1,a2,b1,b2):', ' '.join(mp.nstr(T_entry(0, u), 8) for u in (0, 1, 2, N + 1, N + 2)))


def probe_trunc(ns=(8, 12, 16, 20, 24), dps=220):
    """Das Krylow-Zertifikat (= Spektral-T = Formel des sechsten Laufs, Theorem 28)
    auf den Trunkierungen der Leiter; ||T||_m und die Eckeintraege.  Normiert
    mit M der UNENDLICHEN Leiter.  Nur Messung."""
    import spectral as S
    mp.mp.dps = dps
    print(f'(trunc) Krylow-Zertifikat auf Trunkierungen der Leiter, dps={dps}')
    for (alpha, beta) in (('1/2', '1/3'), ('1/3', '1/2'), ('1/2', '2/3'), ('1/4', '1/2')):
        Minf = Fr(alpha) / (1 - Fr(alpha)) + Fr(beta) / (1 - Fr(beta))
        print(f'  --- ({alpha},{beta})')
        for n in ns:
            if (alpha, beta) == ('1/2', '1/3') and n > 12:
                continue
            alF = [Fr(alpha) ** i / Minf for i in range(1, n + 1)]
            beF = [Fr(beta) ** j / Minf for j in range(1, n + 1)]
            P = S.ladder(alF, beF)
            T, rts, info = S.spectral_T(P)
            sym, imag, inter, hit = S.verify_certificate_numeric(P, T)
            w = [S.fr(P.masses[i]) + (1 if i in (0, P.t) else 0) for i in range(P.n + 2)]
            best = (mp.mpf(0), None)
            for i in range(P.n + 2):
                for j in range(i, P.n + 2):
                    q = abs(T[i][j]) / (w[i] * w[j])
                    if q > best[0]:
                        best = (q, (i, j))

            def name(i):
                if i == 0:
                    return '0'
                if i == P.t:
                    return 't*'
                return f'a{i}' if i <= n else f'b{i - n}'
            print(f'    n={n:2d}: ||T||_m={mp.nstr(best[0], 12)} an ({name(best[1][0])},{name(best[1][1])})'
                  f'  T[a1,a1]/w^2={mp.nstr(mp.re(T[1][1]) / w[1] ** 2, 8)}'
                  f'  T[b1,b1]/w^2={mp.nstr(mp.re(T[n + 1][n + 1]) / w[n + 1] ** 2, 8)}'
                  f'  T[t*,a1]={mp.nstr(mp.re(T[P.t][1]), 8)}  Zertifikat-Fehler<{mp.nstr(max(inter, hit), 1)}')
            check(max(inter, hit, sym, imag) < mp.mpf(10) ** (-dps // 2), f'({alpha},{beta}) n={n}: Krylow-T ist ein Zertifikat der Trunkierung')


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    if len(sys.argv) > 1 and sys.argv[1] == 'trunc':
        ns = tuple(int(a) for a in sys.argv[2:]) or (8, 12, 16, 20, 24)
        probe_trunc(ns=ns, dps=max(220, 8 * max(ns)))
    else:
        probe_B()
    print()
    print('FEHLER:' if FAIL else 'rc=0, keine Abweichung.', *FAIL, sep='\n  ')
    sys.exit(1 if FAIL else 0)
