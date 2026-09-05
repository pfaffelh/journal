r"""Die omega-Kette: das Zertifikat in geschlossener Form.

PROTOKOLL, siebenundzwanzigster Lauf, "Die omega-Kette".

Der sechsundzwanzigste Lauf hat die Existenzfrage auf der omega-Kette
T = {0} u {a_1 < a_2 < ...} u {t*} in Proposition 24.2 gebuendelt: gesucht ist
ein symmetrisches Phi auf N_0^2 mit

    Phi(i,0) = 0,
    (m_i - m_j) Phi(i,j) = m_i Phi(i,j-1) - m_j Phi(i-1,j)      (i,j >= 1),
    Phi(i,k) --> [i=1]/m_1                                      (k --> oo),
    |Phi(i,j) - Phi(i,j-1)| <= C m_j                            (Bedingung 1).

Dieser Lauf loest die ersten drei Forderungen geschlossen und unbedingt
(Theorem 25) und die vierte unter geometrischem Massenabfall (Korollar 25.3).
Mit c_k = 1/m_k, pi_k(i) = prod_{l>i} (1 - m_l/m_k) und

    beta_k  = 1 / (m_k prod_{l != k} (1 - m_l/m_k)),
    Phi(i,j) = sum_{k <= min(i,j)} beta_k pi_k(i) pi_k(j)     (endliche Summe),
    G(i,j)   = -T_{a_i a_j}/(m_i m_j) = sum_{k<=min(i,j)} (beta_k/m_k)
                                        pi_k(i) pi_k(j)

ist Bedingung 1 gleichbedeutend mit sup_{i,j} |G(i,j)| < oo.

Proben:

    python3 omega_chain.py A     -- Theorem 25: Symmetrie, Rand, Rekursion
    python3 omega_chain.py B     -- Theorem 25(3): die Randidentitaet
                                    sum_{k<=i} beta_k pi_k(i) = [i=1]/m_1
    python3 omega_chain.py C     -- Korollar 25.1: G(.,1) --> 1/m_1^2,
                                    G(.,2) --> -1/(m_1 m_2), G(.,j) --> 0
    python3 omega_chain.py D     -- Theorem 25.2: G als dividierte Differenz
    python3 omega_chain.py E     -- die Schranke von Theorem 25.2
    python3 omega_chain.py F     -- die Dreiecksschranke Lambda_j (Sackgasse)
    python3 omega_chain.py sup   -- sup|G| auf vier Profilen (langsam)
    python3 omega_chain.py all   -- A bis F

Gerechnet wird in `mpmath` mit 120 Stellen; die Schwanzprodukte werden per
Euler-Maclaurin (`mp.sumem`) ausgewertet.  Exakte Bruchrechnung ist hier nicht
moeglich -- die Bausteine pi_k(i) sind unendliche Produkte --, die Residuen der
geprueften Identitaeten liegen bei 10^-120 und damit 100 Stellen unter jeder
auftretenden Groesse.  rc = 0 heisst: keine Abweichung.
"""
import sys

import mpmath as mp

mp.mp.dps = 120

TOL = mp.mpf(10)**(-90)

FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


# ================================================================= Profile
#
# m: 1-indizierte Massenfunktion, auf reelle Argumente fortgesetzt, damit
# mp.sumem die Schwaenze per Euler-Maclaurin auswerten kann.

PROFILES = [
    ('m_i = 2^-i', lambda l: 1 / mp.mpf(2)**l),
    ('m_i = 2*3^-i', lambda l: 2 / mp.mpf(3)**l),
    ('m_i = 1/(i(i+1))', lambda l: 1 / (mp.mpf(l) * (l + 1))),
    ('m_i = i^-3/2', lambda l: 1 / mp.mpf(l)**mp.mpf('1.5')),
    ('m_i = 1/((i+1) log^2(i+1))',
     lambda l: 1 / (mp.mpf(l + 1) * mp.log(l + 1)**2)),
]


CUT = 400          # exakt aufsummiert wird bis i + CUT, dann Euler-Maclaurin


def tail(f, a):
    """sum_{l>a} f(l): exakt bis a+CUT, der Rest per Euler-Maclaurin.

    mp.sumem allein ist dicht am Anfang ungenau (bei sum 1/l^1.5 ab l=1 nur
    drei Stellen); ab l = a+CUT ist der Summand klein und glatt, und dort
    trifft Euler-Maclaurin voll.
    """
    s = mp.fsum(f(l) for l in range(a + 1, a + CUT + 1))
    return s + mp.sumem(f, [a + CUT + 1, mp.inf])


def sigma(m, i):
    """sigma_i = sum_{l>i} m_l."""
    return tail(m, i)


def grid(m, N):
    """pi[(k,i)] fuer 1 <= k <= i <= N, dazu beta_k und gamma_k = beta_k/m_k.

    pi_k(N) kommt aus dem Schwanz des Logarithmus, die kleineren i aus
    pi_k(i-1) = (1 - m_i/m_k) pi_k(i).  Die Proben (A) und (B) haengen von
    diesen Startwerten nicht ab: Rekursion und Symmetrie gelten fuer jede
    Wahl, und in der Randidentitaet kuerzen sich die Schwanzprodukte heraus.
    """
    pi = {}
    for k in range(1, N + 1):
        mk = m(k)
        pi[(k, N)] = mp.e**tail(lambda x: mp.log1p(-m(x) / mk), N)
        for i in range(N, k, -1):
            pi[(k, i - 1)] = pi[(k, i)] * (1 - m(i) / mk)
    bet = [None] * (N + 1)
    for k in range(1, N + 1):
        mk = m(k)
        d = pi[(k, k)]                       # prod_{l>k} (1 - m_l/m_k)
        for l in range(1, k):
            d *= (1 - m(l) / mk)
        bet[k] = 1 / (mk * d)
    gam = [None] + [bet[k] / m(k) for k in range(1, N + 1)]
    return pi, bet, gam


def phi_fun(m, pi, bet):
    def Phi(i, j):
        if i < 1 or j < 1:
            return mp.mpf(0)
        return sum(bet[k] * pi[(k, i)] * pi[(k, j)]
                   for k in range(1, min(i, j) + 1))
    return Phi


def g_fun(m, pi, gam):
    def G(i, j):
        return sum(gam[k] * pi[(k, i)] * pi[(k, j)]
                   for k in range(1, min(i, j) + 1))
    return G


def scale(m, N):
    """Groessenordnung der auftretenden Zahlen -- Massstab fuer die Residuen."""
    return max(abs(1 / m(1)), mp.mpf(1))


# ===================================================================== (A)


def run_A(N=14):
    print('(A) Theorem 25: Symmetrie, Phi(i,0) = 0, Zwei-Diagonalen-Rekursion.')
    for lab, m in PROFILES[:4]:
        pi, bet, gam = grid(m, N)
        Phi = phi_fun(m, pi, bet)
        sym = max(abs(Phi(i, j) - Phi(j, i))
                  for i in range(1, N + 1) for j in range(1, N + 1))
        rand = max(abs(Phi(i, 0)) for i in range(0, N + 1))
        rec = mp.mpf(0)
        for i in range(1, N + 1):
            for j in range(1, N + 1):
                lhs = m(i) * (Phi(i, j) - Phi(i, j - 1))
                rhs = m(j) * (Phi(i, j) - Phi(i - 1, j))
                rec = max(rec, abs(lhs - rhs))
        s = scale(m, N)
        print(f'    {lab:<30} sym {mp.nstr(sym, 3)}  '
              f'rand {mp.nstr(rand, 3)}  rek {mp.nstr(rec, 3)}')
        check(sym < TOL * s and rand < TOL * s and rec < TOL * s,
              f'{lab}: Symmetrie, Rand und Rekursion')
    print()


# ===================================================================== (B)


def run_B(N=14):
    print('(B) Theorem 25(3): sum_{k<=i} beta_k pi_k(i) = [i=1]/m_1.')
    for lab, m in PROFILES[:4]:
        pi, bet, gam = grid(m, N)
        err = max(abs(sum(bet[k] * pi[(k, i)] for k in range(1, i + 1))
                      - (1 / m(1) if i == 1 else 0))
                  for i in range(1, N + 1))
        print(f'    {lab:<30} max. Residuum {mp.nstr(err, 3)}')
        check(err < TOL * scale(m, N), f'{lab}: Randidentitaet')
    print()


# ===================================================================== (C)


def run_C(N=14):
    print('(C) Korollar 25.1: die Limiten von G(.,j).')
    print('    j=1: 1/m_1^2,  j=2: -1/(m_1 m_2),  j>=3: 0.')
    print('    Geprueft wird die Identitaet lim_i G(i,j)')
    print('      = sum_{k<=j} (m_k^2 prod_{l<=j, l!=k} (1-m_l/m_k))^-1,')
    print('    in der sich die Schwanzprodukte herauskuerzen: sie ist exakt')
    print('    und haengt von den Startwerten pi_k(N) nicht ab.')
    for lab, m in PROFILES[:4]:
        pi, bet, gam = grid(m, N)
        G = g_fun(m, pi, gam)
        err = mp.mpf(0)
        for j in range(1, N + 1):
            lim = sum(1 / (m(k)**2 * mp.fprod([1 - m(l) / m(k)
                                               for l in range(1, j + 1)
                                               if l != k]))
                      for k in range(1, j + 1))
            pred = (1 / m(1)**2 if j == 1
                    else -1 / (m(1) * m(2)) if j == 2 else mp.mpf(0))
            err = max(err, abs(lim - pred))
        print(f'    {lab:<30} max. Residuum {mp.nstr(err, 3)};'
              f'  G(N,j) = ' + ' '.join(mp.nstr(G(N, j), 6)
                                        for j in (1, 2, 3, 4)))
        check(err < TOL * scale(m, N)**2,
              f'{lab}: die Limiten von Korollar 25.1')
    print()


# ===================================================================== (D)


def run_D(N=14):
    print('(D) Theorem 25.2: G(i,j) = (-1)^(j+1)/(m_1...m_j) g_i[c_1,...,c_j].')
    for lab, m in PROFILES[:4]:
        pi, bet, gam = grid(m, N)
        G = g_fun(m, pi, gam)
        c = [None] + [1 / m(l) for l in range(1, N + 1)]
        worst = mp.mpf(0)
        for (i, j) in ((N, 2), (N, 3), (N - 1, 5), (N, 6)):
            def g(x, i=i):
                return x * mp.e**tail(lambda y: mp.log1p(-x * m(y)), i)
            dd = sum(g(c[k]) / mp.fprod([c[k] - c[l]
                                         for l in range(1, j + 1) if l != k])
                     for k in range(1, j + 1))
            pref = (-1)**(j + 1) / mp.fprod([m(l) for l in range(1, j + 1)])
            worst = max(worst, abs(G(i, j) - pref * dd))
        print(f'    {lab:<30} max. Abweichung {mp.nstr(worst, 3)}')
        check(worst < mp.mpf(10)**(-20) * scale(m, N),
              f'{lab}: dividierte Differenz')
    print()


# ===================================================================== (E)


def run_E(N=14):
    print('(E) Die Schranke von Theorem 25.2, |G(i,j)| <= 2 c_j^2'
          ' e^(2 sigma_i/m_j) prod_{l<=j} m_j/m_l.')
    for lab, m in PROFILES[:4]:
        pi, bet, gam = grid(m, N)
        G = g_fun(m, pi, gam)
        sig = [sigma(m, i) for i in range(0, N + 1)]
        ok = True
        row = []
        for j in range(1, N + 1):
            b_j = None
            for i in range(j, N + 1):
                b = (2 / m(j)**2 * mp.e**(2 * sig[i] / m(j))
                     * mp.fprod([m(j) / m(l) for l in range(1, j + 1)]))
                if i == j:
                    b_j = b
                ok &= abs(G(i, j)) <= b * (1 + TOL)
            if j <= 8:
                row.append(b_j)
        print(f'    {lab:<30} Schranke bei i=j, j=1..8: '
              + ' '.join(mp.nstr(v, 3) for v in row))
        check(ok, f'{lab}: die Schranke gilt an allen Paaren j <= i <= N')
    print('    Brauchbar ist sie nur bei geometrischem Abfall (Kor. 25.3);')
    print('    bei m_i = 1/(i(i+1)) waechst sie, waehrend |G| < 12 bleibt.')
    print()


# ===================================================================== (F)


def run_F(N=14):
    print('(F) Sackgasse: die Dreiecksschranke'
          ' Lambda_j = sum_{k<=j} |gamma_k pi_k(j)|.')
    for lab, m in PROFILES[:4]:
        pi, bet, gam = grid(m, N)
        G = g_fun(m, pi, gam)
        lam = [sum(abs(gam[k] * pi[(k, j)]) for k in range(1, j + 1))
               for j in range(1, N + 1)]
        supG = max(abs(G(i, j))
                   for i in range(1, N + 1) for j in range(1, i + 1))
        print(f'    {lab:<30} Lambda_1..8 = '
              + ' '.join(mp.nstr(v, 4) for v in lam[:8]))
        print(f'    {"":<30} Lambda_{N} = {mp.nstr(lam[-1], 5)}'
              f'   sup|G| = {mp.nstr(supG, 5)}')
        check(lam[-1] > supG,
              f'{lab}: Lambda ist echt groeber als sup|G|')
    print('    Die Koeffizienten der Zerlegung sind unbeschraenkt;')
    print('    nur ihre alternierende Summe ist es.')
    print()


# =================================================================== (sup)


def run_sup(N=40):
    print(f'(sup) sup|G| auf den Trunkierungen, N = {N}.')
    print('      Vermutung: sup|G| = max(1/m_1^2, 1/(m_1 m_2)).')
    for lab, m in PROFILES:
        pi, bet, gam = grid(m, N)
        G = g_fun(m, pi, gam)
        best, arg = mp.mpf(0), None
        colmax = []
        for j in range(1, N + 1):
            cm = mp.mpf(0)
            for i in range(j, N + 1):
                v = abs(G(i, j))
                cm = max(cm, v)
                if v > best:
                    best, arg = v, (i, j)
            colmax.append(cm)
        pred = max(1 / m(1)**2, 1 / (m(1) * m(2)))
        print(f'    {lab:<30} sup|G| = {mp.nstr(best, 8)} bei {arg},'
              f'  Vermutung {mp.nstr(pred, 8)}')
        print(f'    {"":<30} max_i|G(i,j)| fuer j=3..8: '
              + ' '.join(mp.nstr(v, 4) for v in colmax[2:8]))
        check(best <= pred * (1 + TOL),
              f'{lab}: sup|G| <= max(1/m_1^2, 1/(m_1 m_2))')
    print()


# ====================================================================== main


PROBES = {'A': run_A, 'B': run_B, 'C': run_C, 'D': run_D, 'E': run_E,
          'F': run_F, 'sup': run_sup}

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    args = sys.argv[1:] or ['all']
    if args[0] == 'all':
        args = ['A', 'B', 'C', 'D', 'E', 'F']
    for a in args:
        if a.isdigit():                      # optionales N fuer die Vorprobe
            continue
        n = next((int(x) for x in args[args.index(a) + 1:args.index(a) + 2]
                  if x.isdigit()), None)
        PROBES[a]() if n is None else PROBES[a](n)
    if FAIL:
        print('FEHLGESCHLAGEN:')
        for f in FAIL:
            print('  -', f)
        sys.exit(1)
    print('rc = 0: keine Abweichung.')
