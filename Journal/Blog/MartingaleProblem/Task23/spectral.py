r"""Das Spektralzertifikat auf einer beliebigen Halbordnung.

PROTOKOLL, neunundzwanzigster Lauf, "Das Kettenpolynom".

Rahmen wie im fuenfundzwanzigsten Lauf: T = {0} u A u {t*}, m_0 = m_t* = 0,
V_{s,a} = [a<s] m_a.  Auf den Atomen sei W_{c,s} = m_c [c<s] (der Atomblock
von V^T).  Fuer c in C setze

    y^c := (I + c W)^{-1} m = sum_k (-c)^k W^k m,      x^c := (0; y^c; -1/c),

dann ist V^T x^c = -(1/c) x^c auf allen Atomen (Resolventenrechnung), und

    x^c . 1  =  -P_T(c)/c,      P_T(c) := sum_k (-c)^k e_k,
    e_k := sum ueber k-Ketten c_0<...<c_{k-1} in A von m_{c_0}...m_{c_{k-1}}

ist das (massengewichtete) KETTENPOLYNOM der Halbordnung.  Sind c_1,c_2,...
die Nullstellen von P_T (einfach), so ist mit gamma_k := -c_k/P_T'(c_k)

    T := - sum_k gamma_k x^{c_k} (x^{c_k})^T + e_t* e_t*^T

symmetrisch mit T 1 = e_t* (jedes x^{c_k}.1 = 0) und T V = V^T T genau dann,
wenn die Residuenidentitaet

    sum_k gamma_k c_k^{-2} y^{c_k} = m       (R)

gilt, d.h. wenn die Summe aller Residuen von y^c/(c P_T(c)) verschwindet.
Auf ENDLICHEN Halbordnungen ist y^c/(c P_T(c)) rational vom Grad <= -2, (R)
gilt also automatisch, und T ist ein Zertifikat -- eine neue geschlossene
Form neben der des sechsten Laufs.  Auf der Kette ist P_T = prod(1 - c m_l),
c_k = 1/m_k, und T ist das Zertifikat des siebenundzwanzigsten Laufs.

Proben:

    python3 spectral.py A    -- endliche Halbordnungen (Kette, Antikette,
                                N, Leiter, Krone, zufaellig): P_T, seine
                                Nullstellen, x^c.1 = -P_T(c)/c, und T ist ein
                                Zertifikat; Vergleich mit Theorem 20 und mit
                                dem Zertifikat des sechsten Laufs
    python3 spectral.py B    -- die unendliche Leiter, geometrische Massen:
                                Nullstellen von P_T, (R) numerisch,
                                sup |T_su|/(w_s w_u)
    python3 spectral.py C    -- Theorem 28: Hankel-Normalform im Krylow-Raum
                                von e_t*, exakt; = Spektral-T = Formel des
                                sechsten Laufs
    python3 spectral.py D    -- Lemma 27.3: y^c_a = m_a P_{up(a)}(c)
    python3 spectral.py all
"""
import random
import sys
from fractions import Fraction as Fr

import mpmath as mp

from certificate_m import (certificate, check_certificate, mat_mul, mat_vec,
                           poset_V, transpose)

mp.mp.dps = 50
TOL = mp.mpf(10) ** (-30)
FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


# --------------------------------------------------------------- Halbordnung
#
# Punkte 0..n+1: Index 0 ist "0", 1..n die Atome, n+1 ist t*.  `less(a, s)`
# auf Indizes; 0 < alles < t*.


class Poset:
    def __init__(self, name, atom_masses, atom_less):
        self.name = name
        n = len(atom_masses)
        self.n = n
        self.masses = [Fr(0)] + [Fr(x) for x in atom_masses] + [Fr(0)]
        self.t = n + 1
        self.atoms = list(range(1, n + 1))

        def less(a, s):
            if a == s:
                return False
            if a == 0:
                return True
            if s == self.t:
                return a != self.t
            if s == 0 or a == self.t:
                return False
            return atom_less(a - 1, s - 1)
        self.less = less
        self.V = poset_V(self.masses, less)

    # W auf den Atomen, W_{c,s} = m_c [c<s]
    def W_apply(self, v):
        """(W v)_c = m_c sum_{s>c} v_s, v ueber Atomen (Liste der Laenge n)."""
        out = []
        for c in self.atoms:
            out.append(self.masses[c] * sum((v[s - 1] for s in self.atoms
                                             if self.less(c, s)), Fr(0)))
        return out

    def chain_moments(self):
        """e_k = 1^T W^{k-1} m, k = 1..height; exakt."""
        m = [self.masses[a] for a in self.atoms]
        v = m[:]
        e = [Fr(1)]
        while any(x != 0 for x in v):
            e.append(sum(v, Fr(0)))
            v = self.W_apply(v)
        return e                # e[0] = 1, e[k] = k-Ketten

    def chain_poly(self):
        """Koeffizienten von P_T(c) = sum_k (-c)^k e_k, als Fractions,
        aufsteigend in c."""
        return [(-1) ** k * ek for k, ek in enumerate(self.chain_moments())]

    def y(self, c):
        """y^c = sum_k (-c)^k W^k m, c in mpmath (reell oder komplex)."""
        m = [self.masses[a] for a in self.atoms]
        v = m[:]
        out = [mp.mpc(0)] * self.n
        k = 0
        while any(x != 0 for x in v):
            coef = (-c) ** k
            out = [o + coef * fr(x) for o, x in zip(out, v)]
            v = self.W_apply(v)
            k += 1
        return out

    def x(self, c):
        return [mp.mpc(0)] + self.y(c) + [-1 / c]


def fr(x):
    return mp.mpf(x.numerator) / x.denominator


def roots_of(coeffs):
    """Nullstellen eines Polynoms mit Fraction-Koeffizienten (aufsteigend)."""
    cs = [mp.mpf(x.numerator) / x.denominator for x in coeffs]
    while cs and cs[-1] == 0:
        cs.pop()
    return mp.polyroots(list(reversed(cs)), maxsteps=200, extraprec=200)


def poly_eval(coeffs, c, deriv=0):
    val = mp.mpc(0)
    for k, a in enumerate(coeffs):
        if k < deriv:
            continue
        f = 1
        for j in range(deriv):
            f *= (k - j)
        val += f * (mp.mpf(a.numerator) / a.denominator) * c ** (k - deriv)
    return val


def spectral_T(P):
    """Das Spektralzertifikat, numerisch (mpmath)."""
    coeffs = P.chain_poly()
    rts = roots_of(coeffs)
    N = P.n + 2
    T = [[mp.mpc(0)] * N for _ in range(N)]
    T[P.t][P.t] = mp.mpc(1)
    info = []
    for c in rts:
        x = P.x(c)
        dP = poly_eval(coeffs, c, 1)
        gamma = -c / dP
        info.append((c, gamma, sum(x)))
        for i in range(N):
            if x[i] == 0:
                continue
            for j in range(N):
                T[i][j] -= gamma * x[i] * x[j]
    return T, rts, info


def to_mp_matrix(A):
    return [[mp.mpf(a.numerator) / a.denominator if isinstance(a, Fr) else a
             for a in row] for row in A]


def mp_matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][l] * B[l][j] for l in range(k)) for j in range(m)]
            for i in range(n)]


def max_abs(A):
    return max(abs(a) for row in A for a in row)


def verify_certificate_numeric(P, T):
    N = P.n + 2
    V = to_mp_matrix(P.V)
    Vt = [[V[j][i] for j in range(N)] for i in range(N)]
    sym = max(abs(T[i][j] - T[j][i]) for i in range(N) for j in range(N))
    imag = max(abs(mp.im(T[i][j])) for i in range(N) for j in range(N))
    TV, VtT = mp_matmul(T, V), mp_matmul(Vt, T)
    inter = max(abs(TV[i][j] - VtT[i][j]) for i in range(N) for j in range(N))
    row = [sum(T[i]) for i in range(N)]
    hit = max(abs(row[i] - (1 if i == P.t else 0)) for i in range(N))
    return sym, imag, inter, hit


def weighted_norm(P, T, Z=None):
    Z = Z if Z is not None else {0, P.t}
    w = [mp.mpf(P.masses[i].numerator) / P.masses[i].denominator
         + (1 if i in Z else 0) for i in range(P.n + 2)]
    return max(abs(T[i][j]) / (w[i] * w[j]) for i in range(P.n + 2)
               for j in range(P.n + 2))


# ----------------------------------------------------------------- Familien


def chain(ms):
    return Poset('Kette', ms, lambda a, b: a < b)


def antichain(ms):
    return Poset('Antikette', ms, lambda a, b: False)


def N_poset(ms):
    """a<c, b<c ... nein: das N: a<c, b<c?  Das N ist a<c, b<c und a<d? --
    kanonisch: Punkte a,b,c,d mit a<c, b<c, b<d (a||b, a||d, c||d)."""
    rel = {(0, 2), (1, 2), (1, 3)}
    return Poset('N', ms, lambda x, y: (x, y) in rel)


def ladder(alpha, beta):
    """a_1<...<a_n, b_1<...<b_n, a_i<b_j iff i<j.  Atome: a_i = i-1,
    b_j = n+j-1."""
    n = len(alpha)

    def lt(x, y):
        xa, ya = x < n, y < n
        if xa and ya:
            return x < y
        if (not xa) and (not ya):
            return x < y
        if xa and not ya:
            return x < y - n
        return False
    return Poset('Leiter', list(alpha) + list(beta), lt)


def crown(alpha, beta):
    """a_i<b_j iff i != j."""
    n = len(alpha)

    def lt(x, y):
        return x < n and y >= n and x != y - n
    return Poset('Krone', list(alpha) + list(beta), lt)


def random_poset(n, rng, p=0.4):
    """Zufaellige Halbordnung: zufaellige Aufwaertskanten auf 0..n-1
    (i<j), transitiv abgeschlossen."""
    rel = set()
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                rel.add((i, j))
    changed = True
    while changed:
        changed = False
        for (a, b) in list(rel):
            for (c, d) in list(rel):
                if b == c and (a, d) not in rel:
                    rel.add((a, d))
                    changed = True
    ms = [Fr(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(n)]
    return Poset(f'zufaellig n={n}', ms, lambda x, y: (x, y) in rel)


# ============================================================ Probe (A)


def probe_A():
    print('(A) Endliche Halbordnungen: Kettenpolynom, Nullstellen, Zertifikat')
    rng = random.Random(23)
    cases = [
        chain([Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(1, 16)]),
        chain([Fr(3), Fr(1), Fr(2), Fr(5)]),
        antichain([Fr(1, 2), Fr(1, 3), Fr(1, 6)]),
        N_poset([Fr(1), Fr(2), Fr(3), Fr(4)]),
        ladder([Fr(1, 2) ** i for i in range(1, 4)], [Fr(1, 3) ** j for j in range(1, 4)]),
        ladder([Fr(1, 2) ** i for i in range(1, 6)], [Fr(1, 3) ** j for j in range(1, 6)]),
        ladder([Fr(1, 2) ** i for i in range(1, 5)], [Fr(1, 2) ** j for j in range(1, 5)]),
        crown([Fr(1, 2) ** i for i in range(1, 5)], [Fr(1, 3) ** j for j in range(1, 5)]),
    ] + [random_poset(rng.randint(4, 8), rng) for _ in range(12)]
    for P in cases:
        coeffs = P.chain_poly()
        deg = len(coeffs) - 1
        T, rts, info = spectral_T(P)
        # x^c . 1 = -P_T(c)/c an zufaelligen Stellen c (keine Nullstellen)
        res_dot = mp.mpf(0)
        for _ in range(5):
            c = mp.mpc(rng.uniform(-3, 3), rng.uniform(-3, 3))
            lhs = sum(P.x(c))
            rhs = -poly_eval(coeffs, c) / c
            res_dot = max(res_dot, abs(lhs - rhs))
        real = all(abs(mp.im(r)) < TOL for r in rts)
        simple = min((abs(rts[i] - rts[j]) for i in range(len(rts))
                      for j in range(i)), default=mp.mpf(1)) > mp.mpf(10) ** -10
        dots = max(abs(d) for _, _, d in info)
        sym, imag, inter, hit = verify_certificate_numeric(P, T)
        nrm = weighted_norm(P, T)
        print(f'  {P.name:16s} n={P.n:2d} deg P_T={deg:2d}  Nullstellen '
              f'{"reell" if real else "KOMPLEX"}{"" if simple else ", MEHRFACH"}'
              f'  |x.1+P/c|<{mp.nstr(res_dot, 2)}  |x_k.1|<{mp.nstr(dots, 2)}'
              f'  TV-VtT<{mp.nstr(inter, 2)}  T1-e<{mp.nstr(hit, 2)}'
              f'  Im<{mp.nstr(imag, 2)}  ||T||_m={mp.nstr(mp.re(nrm), 8)}')
        if not real:
            print('      Nullstellen:', [mp.nstr(r, 8) for r in rts])
        check(res_dot < TOL, f'{P.name}: x^c.1 = -P_T(c)/c')
        check(dots < TOL, f'{P.name}: x^(c_k).1 = 0 an den Nullstellen')
        if simple:
            check(inter < TOL and hit < TOL and sym < TOL and imag < TOL,
                  f'{P.name}: Spektral-T ist ein Zertifikat (sym, TV=VtT, T1=e_t*, reell)')
        else:
            print('      (mehrfache Nullstelle: Spektralform nicht definiert, uebersprungen)')
    # Vergleich mit Theorem 20 auf der Antikette: T = (e mu^T + mu e^T)/M - mu mu^T/M^2
    P = antichain([Fr(1, 2), Fr(1, 3), Fr(1, 6)])
    T, rts, _ = spectral_T(P)
    M = sum(P.masses)
    dev = mp.mpf(0)
    for i in range(P.n + 2):
        for j in range(P.n + 2):
            mi, mj = P.masses[i], P.masses[j]
            ref = Fr(0)
            if i == P.t and j != P.t:
                ref = mj / M
            elif j == P.t and i != P.t:
                ref = mi / M
            elif i != P.t and j != P.t:
                ref = -mi * mj / M ** 2
            dev = max(dev, abs(T[i][j] - mp.mpf(ref.numerator) / ref.denominator))
    check(dev < TOL, f'Antikette: Spektral-T = Theorem 20, Abweichung {mp.nstr(dev, 2)}')
    check(len(rts) == 1 and abs(rts[0] - 1 / mp.mpf(M.numerator) * M.denominator) < TOL,
          'Antikette: P_T = 1 - cM, einzige Nullstelle 1/M')
    # Vergleich mit dem Zertifikat des sechsten Laufs auf der Kette
    for ms in ([Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(1, 16)], [Fr(3), Fr(1), Fr(2), Fr(5)]):
        P = chain(ms)
        T, rts, _ = spectral_T(P)
        T6, _r = certificate(P.V, P.t)
        assert all(check_certificate(T6, P.V, P.t))
        # die eine Freiheit ist T_{0 a_1}; auf ihr Nullsetzen: T6' = T6 - c (e_0 - e_{a1})(e_0 - e_{a1})^T? nein --
        # wir vergleichen den Atomblock samt t*-Zeile, der frei von c ist.
        dev = mp.mpf(0)
        for i in range(1, P.n + 2):
            for j in range(1, P.n + 2):
                dev = max(dev, abs(T[i][j] - mp.mpf(T6[i][j].numerator) / T6[i][j].denominator))
        check(dev < TOL, f'Kette {ms}: Spektral-T = Zertifikat des sechsten Laufs auf A u {{t*}}, Abweichung {mp.nstr(dev, 2)}')
        check(all(abs(r - 1 / (mp.mpf(m.numerator) / m.denominator)) < TOL
                  for r, m in zip(sorted(rts, key=lambda z: mp.re(z)), sorted(ms, reverse=True))),
              f'Kette {ms}: Nullstellen sind 1/m_k')


def main(argv):
    which = argv[1] if len(argv) > 1 else 'all'
    if which in ('A', 'all'):
        probe_A()
    if which in ('C', 'all'):
        probe_C()
    if which in ('D', 'all'):
        probe_D()
    if which in ('B', 'all'):
        import spectral_ladder
        spectral_ladder.probe_B()
    print()
    print('FEHLER:' if FAIL else 'rc=0, keine Abweichung.', *FAIL, sep='\n  ')
    return 1 if FAIL else 0



# ============================================================ Probe (C)
#
# Theorem 28: die Hankel-Normalform.  psi_k = (V^T)^k e_t*, c_k = psi_k . 1,
# r = Nilpotenzindex von V.  Jedes Zertifikat der Gestalt sum B_kl psi_k psi_l^T
# hat B_kl = b_{k+l} mit b_j = 0 (j < r-1) und sum_l b_{k+l} c_l = [k=0];
# das Dreieckssystem hat genau eine Loesung.  Spektral-T und die Formel des
# sechsten Laufs liegen beide in dieser Klasse, also stimmen sie ueberein,
# und b_j = (-1)^j q_j mit 1/P_T(c) = sum_j q_j c^{-j} (Entwicklung bei oo).


def hankel_certificate(P):
    """T = sum_{k,l} b_{k+l} psi_k psi_l^T, exakt in Fractions."""
    N = P.n + 2
    Vt = transpose(P.V)
    psi = [[Fr(1) if i == P.t else Fr(0) for i in range(N)]]
    while any(psi[-1]):
        psi.append(mat_vec(Vt, psi[-1]))
    psi.pop()                       # psi_r = 0 weg
    r = len(psi)
    c = [sum(p) for p in psi]       # c_k = psi_k . 1
    assert c[r - 1] != 0
    b = {}
    # sum_{l} b_{k+l} c_l = [k=0], b_j = 0 fuer j < r-1; loesen nach b_{r-1+k}
    for k in range(r):
        s = sum((b[k + l] * c[l] for l in range(r) if (k + l) in b), Fr(0))
        # unbekannt: b_{k + (r-1)} mit Koeffizient c_{r-1}
        b[k + r - 1] = ((1 if k == 0 else 0) - s) / c[r - 1]
    T = [[Fr(0)] * N for _ in range(N)]
    for k in range(r):
        for l in range(r):
            if (k + l) in b and b[k + l] != 0:
                for i in range(N):
                    if psi[k][i]:
                        for j in range(N):
                            T[i][j] += b[k + l] * psi[k][i] * psi[l][j]
    return T, b, r, c


def probe_C():
    print('(C) Theorem 28: Hankel-Normalform = Spektral-T = Formel des sechsten Laufs')
    rng = random.Random(28)
    cases = [chain([Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(1, 16)]),
             antichain([Fr(1, 2), Fr(1, 3), Fr(1, 6)]),
             N_poset([Fr(1), Fr(2), Fr(3), Fr(4)]),
             ladder([Fr(1, 2) ** i for i in range(1, 6)], [Fr(1, 3) ** j for j in range(1, 6)]),
             crown([Fr(1, 2) ** i for i in range(1, 5)], [Fr(1, 3) ** j for j in range(1, 5)])] + \
            [random_poset(rng.randint(4, 8), rng) for _ in range(10)]
    for P in cases:
        TH, b, r, c = hankel_certificate(P)
        ok6 = all(check_certificate(TH, P.V, P.t))
        T6, r6 = certificate(P.V, P.t)
        N = P.n + 2
        same6 = all(TH[i][j] == T6[i][j] for i in range(N) for j in range(N))
        TS, rts, _ = spectral_T(P)
        devS = max(abs(TS[i][j] - fr(TH[i][j])) for i in range(N) for j in range(N))
        # b_j = (-1)^j q_j, 1/P_T = sum q_j c^{-j}: Laurent-Koeffizienten aus der Polynomdivision
        coeffs = P.chain_poly()
        d = len(coeffs) - 1
        # 1/P_T(c) = c^{-d} / (a_d + a_{d-1} c^{-1} + ...) ; Potenzreihe in u = 1/c
        a = list(reversed(coeffs))             # a[0] = a_d, ...
        q = {}
        inv = [Fr(1) / a[0]]
        for j in range(1, 2 * r):
            s = sum((a[i] * inv[j - i] for i in range(1, min(j, d) + 1)), Fr(0))
            inv.append(-s / a[0])
        for j in range(len(inv)):
            q[j + d] = inv[j]
        okq = all(b[j] == (-1) ** j * q.get(j, Fr(0)) for j in b)
        print(f'  {P.name:16s} n={P.n} r={r} deg P_T={d}  Hankel-T Zertifikat={ok6}  =T6:{same6}  |T_spek-T_H|<{mp.nstr(devS, 2)}  b_j=(-1)^j q_j:{okq}')
        check(ok6, f'{P.name}: Hankel-Normalform ist ein Zertifikat')
        check(same6, f'{P.name}: Hankel-Normalform = Formel des sechsten Laufs, exakt')
        check(devS < TOL, f'{P.name}: Hankel-Normalform = Spektral-T')
        check(okq, f'{P.name}: b_j = (-1)^j q_j (Laurent-Koeffizienten von 1/P_T bei oo)')
        check(r - 1 == d, f'{P.name}: r - 1 = deg P_T')


# ============================================================ Probe (D)
#
# Lemma 27.3: y^c_a = m_a * P_{up(a)}(c), das Kettenpolynom der Atome ECHT
# UEBER a.  Denn (W^k m)_a = m_a * sum_{a<c_1<...<c_k} m_{c_1}...m_{c_k}.
# Folge: x^{c_k}(a) = 0 genau dann, wenn c_k Nullstelle von P_{up(a)} ist;
# auf der Kette teilt P_{up(a_i)} das P_T (daher die endlichen Summen von
# Theorem 25), auf der Leiter nicht.


def up_poset(P, a):
    """Die Halbordnung der Atome echt ueber a (Indizes in P), als Poset."""
    ups = [s for s in P.atoms if P.less(a, s)]
    ms = [P.masses[s] for s in ups]
    return Poset(f'up({a})', ms, lambda x, y: P.less(ups[x], ups[y]))


def probe_D():
    print('(D) Lemma 27.3: y^c_a = m_a P_{up(a)}(c)')
    rng = random.Random(273)
    cases = [chain([Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(1, 16)]),
             ladder([Fr(1, 2) ** i for i in range(1, 5)], [Fr(1, 3) ** j for j in range(1, 5)]),
             crown([Fr(1, 2) ** i for i in range(1, 4)], [Fr(1, 3) ** j for j in range(1, 4)])] + \
            [random_poset(rng.randint(4, 8), rng) for _ in range(8)]
    for P in cases:
        dev = mp.mpf(0)
        for _ in range(3):
            c = mp.mpc(rng.uniform(-3, 3), rng.uniform(-3, 3))
            y = P.y(c)
            for a in P.atoms:
                Pa = up_poset(P, a).chain_poly()
                dev = max(dev, abs(y[a - 1] - fr(P.masses[a]) * poly_eval(Pa, c)))
        # Teilbarkeit auf der Kette: P_{up(a_i)} | P_T (Nullstellen von P_{up} sind Nullstellen von P_T)
        print(f'  {P.name:16s} n={P.n}  max |y^c_a - m_a P_up(a)(c)| = {mp.nstr(dev, 2)}')
        check(dev < TOL, f'{P.name}: Lemma 27.3')


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    sys.exit(main(sys.argv))
