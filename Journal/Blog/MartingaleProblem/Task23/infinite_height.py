r"""Unendliche Hoehe: die Fundiertheit ist die Grenze, nicht die Hoehe.

PROTOKOLL, sechsundzwanzigster Lauf, "Die unendliche Hoehe".

Der fuenfundzwanzigste Lauf hat das unendliche Zertifikat fuer Halbordnungen
**endlicher Hoehe** hingeschrieben (Theorem 23) und an Ketten ohne kleinstes
Atom scheitern sehen (Proposition 23.1).  Dieser Lauf verschiebt die Grenze:

  Proposition 24.1.  Hat T ein Maximum t* mit m_{t*} = 0 und ist die Atommenge
  A nichtleer, abwaerts gerichtet und **ohne minimales Element**, so gibt es
  kein unendliches Zertifikat an der Stelle t*, in keiner Gewichtsklasse.
  (Verallgemeinert Proposition 23.1: keine Kette noetig, groesstes Element
  erlaubt, T ausserhalb A u {t*} beliebig.)

  Proposition 24.2.  Auf der omega-Kette T = {0} u {a_1 < a_2 < ...} u {t*}
  ist (a) die Spitzenzeile erzwungen, T_{t*.} = e_{a_1}, und (b) der Atomblock
  ist genau eine symmetrische Funktion Phi auf N_0^2 mit Phi(i,0) = 0,

      (m_i - m_j) Phi(i,j) = m_i Phi(i,j-1) - m_j Phi(i-1,j)   (i,j >= 1),
      Phi(i,k) --> [i=1]/m_1   (k --> oo),

  vermoege T_{a_i a_j} = m_i (Phi(i,j-1) - Phi(i,j)); (c) Bedingung 1 ist die
  Lipschitzbedingung |Phi(i,j) - Phi(i,j-1)| <= C m_j.

Die Halbordnung unendlicher Hoehe mit nicht transitiver Unvergleichbarkeit --
die Leiter a_i < b_j <=> i < j ueber zwei omega-Ketten -- ist damit nicht
bewiesen, aber gemessen: das **Minimum** von ||T||_m ueber alle Zertifikate der
Trunkierung konvergiert, sobald die beiden Massenskalen getrennt sind, waehrend
die explizite Formel des sechsten Laufs dort davonlaeuft.

Proben:

    python3 infinite_height.py A   -- die erzwungene Spitzenzeile, exakt
                                      (Prop. 24.2(a) auf der Kette,
                                       Schritt (1) von Prop. 24.1 auf der
                                       Leiter)
    python3 infinite_height.py B   -- Phi: Symmetrie, Rand, Rekursion,
                                      Rueckgewinnung von T, exakt
    python3 infinite_height.py C   -- ||T||_m auf der omega-Kette konvergiert;
                                      geometrisch gegen rho^3/(rho-1)^2
    python3 infinite_height.py D   -- die Leiter: min ||T||_m ueber alle
                                      Zertifikate (LP, Gleitkomma) gegen die
                                      explizite Formel (exakt)
    python3 infinite_height.py E   -- der Bodenansatz ist unloesbar
    python3 infinite_height.py all

(A), (B), (C), (E) sind exakt in `fractions.Fraction`; (D) ist ein
Gleitkomma-LP und als solches ausgewiesen.  rc = 0 heisst: keine Abweichung.
"""
import sys
from fractions import Fraction as F

from certificate_m import (certificate, check_certificate, poset_V)

FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


# ================================================================= Familien
#
# Durchweg T = {0} u Atome u {t*}, m_0 = m_{t*} = 0, t = t*.


def chain(ms):
    """0 < a_1 < ... < a_n < t*.  Gibt (Massen, less, t, Etiketten)."""
    masses = [F(0)] + [F(m) for m in ms] + [F(0)]
    lab = ['0'] + [f'a{i}' for i in range(1, len(ms) + 1)] + ['t*']
    return masses, (lambda a, s: a < s), len(masses) - 1, lab


def ladder(n, al, be):
    """Die Leiter: a_i < a_i', b_j < b_j', a_i < b_j <=> i < j, nie b_j < a_i.

    Unvergleichbarkeit nicht transitiv (a_1 || b_1, b_1 || a_2, a_1 < a_2),
    Hoehe unendlich, A fundiert mit den minimalen Atomen a_1, b_1.
    """
    masses = ([F(0)] + [F(al) ** i for i in range(1, n + 1)]
              + [F(be) ** j for j in range(1, n + 1)] + [F(0)])
    N = len(masses)
    lab = ['0'] + [f'a{i}' for i in range(1, n + 1)] \
        + [f'b{j}' for j in range(1, n + 1)] + ['t*']

    def kind(i):
        if i == 0:
            return ('0', 0)
        if i == N - 1:
            return ('t', 0)
        if i <= n:
            return ('a', i)
        return ('b', i - n)

    def less(a, s):
        if a == s:
            return False
        ka, ia = kind(a)
        ks, js = kind(s)
        if ka == '0':
            return True
        if ks == 't':
            return True
        if ks == '0' or ka == 't':
            return False
        if ka == ks:
            return ia < js
        if ka == 'a':
            return ia < js
        return False
    return masses, less, N - 1, lab


CHAIN_PROFILES = [
    ('m_i = 2^-i', lambda n: [F(1, 2) ** i for i in range(1, n + 1)]),
    ('m_i = 3^-i', lambda n: [F(1, 3) ** i for i in range(1, n + 1)]),
    ('m_i doppelt (2^-k je zweimal)',
     lambda n: [F(1, 2) ** ((i + 1) // 2) / 2 for i in range(1, n + 1)]),
    ('m_i = 1/(i(i+1))', lambda n: [F(1, i * (i + 1)) for i in range(1, n + 1)]),
]

LADDER_PROFILES = [('1/2, 1/3', F(1, 2), F(1, 3)),
                   ('1/3, 1/2', F(1, 3), F(1, 2)),
                   ('1/2, 1/2', F(1, 2), F(1, 2))]


def build(masses, less, t):
    """Normiert auf M = 1, baut das explizite Zertifikat, prueft es."""
    M = sum(masses)
    ms = [F(m) / M for m in masses]
    V = poset_V(ms, less)
    T, r = certificate(V, t)
    assert all(check_certificate(T, V, t))
    return ms, T, r


def norm_m(T, ms):
    n = len(ms)
    w = [ms[i] if ms[i] else F(1) for i in range(n)]
    return max((abs(T[i][j]) / (w[i] * w[j])
                for i in range(n) for j in range(n) if T[i][j]), default=F(0))


# ===================================================================== (A)


def run_A():
    print('(A) Die erzwungene Spitzenzeile.')
    print('    Kette: T_{t*.} = e_{a_1} und T_{0.} = 0, exakt.')
    for lab, mk in CHAIN_PROFILES:
        ok_top = ok_bot = True
        for n in range(2, 11):
            masses, less, t, _ = chain(mk(n))
            ms, T, _ = build(masses, less, t)
            N = len(ms)
            ok_top &= all(T[t][j] == (1 if j == 1 else 0) for j in range(N))
            ok_bot &= all(T[0][j] == 0 for j in range(N))
        check(ok_top and ok_bot, f'Kette {lab}: T_{{t*.}} = e_a1, T_{{0.}} = 0')
    print('    Leiter: T_{t*.} traegt auf {0, a_1, b_1} und summiert zu 1.')
    for lab, al, be in LADDER_PROFILES:
        ok = True
        for n in range(2, 8):
            masses, less, t, _ = ladder(n, al, be)
            ms, T, _ = build(masses, less, t)
            N = len(ms)
            bottom = {0, 1, n + 1}                     # 0, a_1, b_1
            ok &= all(T[t][j] == 0 for j in range(N) if j not in bottom)
            ok &= sum(T[t][j] for j in bottom) == 1
        check(ok, f'Leiter {lab}: Spitzenzeile auf {{0,a1,b1}}, Summe 1')
    print()


# ===================================================================== (B)


def phi_from(T, ms, n, t):
    """Phi(i,k) = (sum_{j>k} T_{a_i a_j} + g_i) / m_i, Phi(0,.) = 0."""
    g = [F(0)] * (n + 1)
    g[1] = F(1)
    Phi = [[F(0)] * (n + 1) for _ in range(n + 1)]
    for i in range(1, n + 1):
        for k in range(n + 1):
            Phi[i][k] = (sum(T[i][j] for j in range(k + 1, n + 1))
                         + g[i]) / ms[i]
    return Phi, g


def run_B():
    print('(B) Proposition 24.2(b): Phi, Rand, Rekursion, Rueckgewinnung.')
    for lab, mk in CHAIN_PROFILES:
        sym = rand0 = randn = rec = back = True
        for n in range(2, 10):
            masses, less, t, _ = chain(mk(n))
            ms, T, _ = build(masses, less, t)
            Phi, g = phi_from(T, ms, n, t)
            sym &= all(Phi[i][k] == Phi[k][i]
                       for i in range(n + 1) for k in range(n + 1))
            rand0 &= all(Phi[i][0] == 0 for i in range(n + 1))
            randn &= all(Phi[i][n] == g[i] / ms[i] for i in range(1, n + 1))
            for i in range(1, n + 1):
                for j in range(1, n + 1):
                    if i == j:
                        continue
                    rec &= ((ms[i] - ms[j]) * Phi[i][j]
                            == ms[i] * Phi[i][j - 1] - ms[j] * Phi[i - 1][j])
            back &= all(T[i][j] == ms[i] * (Phi[i][j - 1] - Phi[i][j])
                        for i in range(1, n + 1) for j in range(1, n + 1))
        check(sym, f'{lab}: Phi symmetrisch')
        check(rand0, f'{lab}: Phi(i,0) = 0')
        check(randn, f'{lab}: Phi(i,n) = g_i/m_i (der Rand der Trunkierung)')
        check(rec, f'{lab}: Zwei-Diagonalen-Rekursion an allen i != j')
        check(back, f'{lab}: T_{{a_i a_j}} = m_i (Phi(i,j-1) - Phi(i,j))')
    print()


# ===================================================================== (C)


def run_C():
    print('(C) Die omega-Kette: ||T||_m auf den Trunkierungen, exakt.')
    ns = (2, 4, 8, 12, 14)
    for lab, mk in CHAIN_PROFILES:
        vals = []
        for n in ns:
            masses, less, t, _ = chain(mk(n))
            ms, T, _ = build(masses, less, t)
            vals.append(norm_m(T, ms))
        mono = all(vals[i] <= vals[i + 1] for i in range(len(vals) - 1))
        print(f'    {lab:<32} ' + ' '.join(f'n={n}:{float(v):.5g}'
                                           for n, v in zip(ns, vals)))
        check(mono, f'{lab}: ||T||_m waechst monoton in n')
    print('    Die geometrische Kette: Limes rho^3/(rho-1)^2.')
    for rho in (2, 3, 4, 5):
        masses, less, t, _ = chain([F(1, rho) ** i for i in range(1, 15)])
        ms, T, _ = build(masses, less, t)
        v = norm_m(T, ms)
        pred = F(rho) ** 3 / F(rho - 1) ** 2
        rel = abs(float(v) - float(pred)) / float(pred)
        print(f'    rho={rho}: n=14 gibt {float(v):.9f}, '
              f'Formel {float(pred):.9f}, rel. Abstand {rel:.2e}')
        check(v <= pred and rel < 1e-3, f'rho={rho}: ||T||_m -> rho^3/(rho-1)^2')
    print()


# ===================================================================== (D)


def min_norm_lp(masses, less, t):
    """Minimum von ||T||_m ueber alle Zertifikate der Trunkierung.

    In den skalierten Variablen S_ij = T_ij/(w_i w_j); Gleitkomma.
    Gibt (status, Wert) zurueck.
    """
    import numpy as np
    from scipy.optimize import linprog
    M = sum(masses)
    ms = [F(x) / M for x in masses]
    n = len(ms)
    w = [float(ms[i]) if ms[i] else 1.0 for i in range(n)]
    V = [[float(ms[a]) if less(a, s) else 0.0 for a in range(n)]
         for s in range(n)]
    idx = [(i, j) for i in range(n) for j in range(i, n)]
    pos = {p: k for k, p in enumerate(idx)}
    d = len(idx)

    def var(i, j):
        return pos[(min(i, j), max(i, j))]

    Aeq, beq = [], []
    for i in range(n):
        for j in range(i + 1, n):
            row = np.zeros(d + 1)
            for k in range(n):
                row[var(i, k)] += w[i] * w[k] * V[k][j]
                row[var(k, j)] -= V[k][i] * w[k] * w[j]
            sc = np.abs(row).max()
            if sc == 0:
                continue
            Aeq.append(row / sc)
            beq.append(0.0)
    for i in range(n):
        row = np.zeros(d + 1)
        for k in range(n):
            row[var(i, k)] += w[k]
        Aeq.append(row)
        beq.append((1.0 if i == t else 0.0) / w[i])
    Aub, bub = [], []
    for k in range(d):
        for sgn in (1.0, -1.0):
            row = np.zeros(d + 1)
            row[k] = sgn
            row[d] = -1.0
            Aub.append(row)
            bub.append(0.0)
    c = np.zeros(d + 1)
    c[d] = 1.0
    res = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub),
                  A_eq=np.array(Aeq), b_eq=np.array(beq),
                  bounds=[(None, None)] * d + [(0, None)], method='highs')
    return res.status, (res.x[-1] if res.status == 0 else float('nan'))


def run_D():
    print('(D) Die Leiter.  Links das Minimum ueber alle Zertifikate (LP,')
    print('    GLEITKOMMA, mit Status), rechts das explizite Zertifikat des')
    print('    sechsten Laufs (exakt).  Alle Profile: nicht transitive')
    print('    Unvergleichbarkeit, unendliche Hoehe, A fundiert.')
    try:
        import numpy  # noqa: F401
        import scipy  # noqa: F401
    except ImportError:
        print('    scipy/numpy fehlen -- (D) entfaellt, kein Ausfall.')
        print()
        return
    ns = (4, 6, 8, 10, 12)
    for lab, al, be in [('1/2, 1/3', F(1, 2), F(1, 3)),
                        ('1/3, 1/2', F(1, 3), F(1, 2)),
                        ('1/2, 2/3', F(1, 2), F(2, 3)),
                        ('2/3, 1/2', F(2, 3), F(1, 2)),
                        ('1/2, 1/2', F(1, 2), F(1, 2)),
                        ('2/3, 2/3', F(2, 3), F(2, 3))]:
        cells = []
        for n in ns:
            masses, less, t, _ = ladder(n, al, be)
            st, v = min_norm_lp(masses, less, t)
            ms, T, _ = build(masses, less, t)
            ex = float(norm_m(T, ms))
            cells.append(f'n={n}: {v:.4g}({st}) / {ex:.4g}')
        print(f'    (alpha,beta) = ({lab:<8})  ' + '  '.join(cells))
    print('    Lesart: bei getrennten Skalen bleibt das Minimum stehen,')
    print('    waehrend die explizite Formel davonlaeuft -- der Spielraum')
    print('    dim{T sym, TV = V^T T, T1 = 0} ist auf der Leiter n+2, auf der')
    print('    Kette 1.')
    print()


# ===================================================================== (E)


def solve_supported(masses, less, t, support):
    """Loest die drei Bedingungen unter T_su = 0 ausserhalb der Zeilen von
    `support`, exakt.  Gibt True/False fuer Loesbarkeit."""
    M = sum(masses)
    ms = [F(x) / M for x in masses]
    n = len(ms)
    V = poset_V(ms, less)
    idx = [(i, j) for i in range(n) for j in range(i, n)
           if i in support or j in support]
    pos = {p: k for k, p in enumerate(idx)}
    d = len(idx)

    def var(i, j):
        return pos.get((min(i, j), max(i, j)))

    A = []
    for i in range(n):
        for j in range(i + 1, n):
            row = [F(0)] * (d + 1)
            for k in range(n):
                if V[k][j]:
                    p = var(i, k)
                    if p is not None:
                        row[p] += V[k][j]
                if V[k][i]:
                    p = var(k, j)
                    if p is not None:
                        row[p] -= V[k][i]
            A.append(row)
    for i in range(n):
        row = [F(0)] * (d + 1)
        for k in range(n):
            p = var(i, k)
            if p is not None:
                row[p] += F(1)
        row[d] = F(1) if i == t else F(0)
        A.append(row)
    r = 0
    for c in range(d):
        p = next((i for i in range(r, len(A)) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = F(1) / A[r][c]
        A[r] = [x * inv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        r += 1
        if r == len(A):
            break
    return not any(A[i][d] for i in range(r, len(A)))


def run_E():
    print('(E) Der Bodenansatz: T traegt nur auf den Zeilen von {0,a1,b1,t*}')
    print('    bzw. {0,a1,t*}.  Erwartet: unloesbar.')
    for lab, al, be in LADDER_PROFILES:
        ok = True
        for n in range(2, 8):
            masses, less, t, _ = ladder(n, al, be)
            N = len(masses)
            ok &= not solve_supported(masses, less, t, {0, 1, n + 1, N - 1})
        check(ok, f'Leiter {lab}: Bodenansatz unloesbar auf n = 2..7')
    for lab, mk in CHAIN_PROFILES[:2]:
        ok = True
        for n in range(2, 8):
            masses, less, t, _ = chain(mk(n))
            N = len(masses)
            ok &= not solve_supported(masses, less, t, {0, 1, N - 1})
        check(ok, f'Kette {lab}: Bodenansatz unloesbar auf n = 2..7')
    print()


RUNS = {'A': run_A, 'B': run_B, 'C': run_C, 'D': run_D, 'E': run_E}


def main(argv):
    what = argv[1] if len(argv) > 1 else 'all'
    if what == 'all':
        for f in RUNS.values():
            f()
    elif what in RUNS:
        RUNS[what]()
    else:
        print(__doc__)
        return 1
    if FAIL:
        print(f'AUSFAELLE: {len(FAIL)}')
        for f in FAIL:
            print(f'  - {f}')
        return 1
    print('kein Ausfall.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
