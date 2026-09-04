r"""Das unendliche Zertifikat (Theorem 22) und die endliche Hoehe (Theorem 23).

PROTOKOLL, fuenfundzwanzigster Lauf, "Das unendliche Zertifikat".

Der vierundzwanzigste Lauf hat die Ausschoepfung als Methode erledigt und die
unendliche Halbordnung genau bis zur Transitivitaet der Unvergleichbarkeit
geschlossen (Theorem 21).  Dieser Lauf schliesst sie fuer **endliche Hoehe**,
und zwar ohne Ausschoepfung: das Zertifikat des sechsten Laufs laesst sich
direkt auf der unendlichen Halbordnung hinschreiben.

  Definition.  Z c T endlich, w_s = m_s + [s in Z].  Ein unendliches
  Zertifikat an der Stelle t ist ein T mit
     1. T = T^T  und  |T_st| <= C w_s w_t,
     2. m_t' sum_{a>t'} T_{s a} = m_s sum_{a>s} T_{a t'}   (also T V = V^T T),
     3. sum_a T_{sa} = [s = t].

  Theorem 22.  Unter (F) = sum_{a,b} m_a m_b |kappa(a,b)| < oo und
  rho_z < oo fuer z in Z folgt aus der Existenz eines unendlichen Zertifikats
  an der Stelle t, dass delta(t) = 0.

  Theorem 23.  Ist V^r = 0 fuer ein r (keine Kette aus r+1 Punkten, deren
  erste r positive Masse tragen), so gibt es zu jedem t ein unendliches
  Zertifikat -- naemlich die Formel des sechsten Laufs, deren Vektoren
  saemtlich in ell^1 liegen.  Korollar: auf jeder abzaehlbaren Halbordnung
  endlicher Hoehe gilt die Dualitaet unter (F), bei beliebiger, insbesondere
  nicht transitiver Unvergleichbarkeit.

  Proposition 23.1.  Auf T = {0} u A u {t*} mit A einer Kette ohne kleinstes
  und ohne groesstes Element (m_0 = m_t* = 0, m > 0 auf A) gibt es kein
  unendliches Zertifikat an der Stelle t*.  Die beiden Methoden -- Theorem 17
  (Ketten) und Theorem 23 (endliche Hoehe) -- haben also disjunkte blinde
  Flecken.

Proben:

    python3 finite_height.py A   -- die Konstruktion auf zufaelligen
                                   Halbordnungen endlicher Hoehe mit nicht
                                   transitiver Unvergleichbarkeit
    python3 finite_height.py B   -- C = max |T_st|/(w_s w_t) bleibt beschraenkt,
                                   wenn die Breite waechst (Leiter, Krone);
                                   Kontrolle: die Kette, wo r mitwaechst
    python3 finite_height.py C   -- das Zertifikat auf der *unendlichen*
                                   Leiter, exakt, mit geschlossenen Reihen
    python3 finite_height.py D   -- der Antikettenzeuge: tr((TV)K) ist
                                   reihenfolgeabhaengig, +1/M gegen -1/M
    python3 finite_height.py E   -- Proposition 23.1 an der dyadischen Uhr:
                                   die Zeile t* sitzt auf dem kleinsten Atom
    python3 finite_height.py all

Alles exakt in `fractions.Fraction`.  rc = 0 heisst: keine Abweichung.
"""
import random
import sys
from fractions import Fraction as F

from certificate_m import (certificate, check_certificate, mat_mul, mat_vec,
                           poset_V, transpose)

FAIL = []


def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)


# ===================================================================== (A)
#
# Zufaellige gestufte Halbordnungen: 0 < alles < t*, dazwischen L Ebenen der
# Breite `width` mit zufaelligen Aufwaertskanten, transitiv abgeschlossen.
# Die Unvergleichbarkeit ist dort i.a. **nicht** transitiv -- genau die
# Klasse, die Theorem 21 nicht sieht.


def random_graded(L, width, rng):
    levels = [[(l, k) for k in range(width)] for l in range(L)]
    pts = ['0'] + [p for lv in levels for p in lv] + ['t*']
    n = len(pts)
    idx = {p: i for i, p in enumerate(pts)}
    rel = [[False] * n for _ in range(n)]          # rel[s][a]  heisst  a < s
    for p in pts[1:]:
        rel[idx[p]][0] = True
    for p in pts[:-1]:
        rel[n - 1][idx[p]] = True
    for l in range(L - 1):
        for p in levels[l]:
            for q in levels[l + 1]:
                if rng.random() < 0.5:
                    rel[idx[q]][idx[p]] = True
    for k in range(n):
        for i in range(n):
            if rel[i][k]:
                for j in range(n):
                    if rel[k][j]:
                        rel[i][j] = True
    return n, rel


def incomparability_transitive(rel, n):
    def inc(i, j):
        return i != j and not rel[i][j] and not rel[j][i]
    return not any(inc(i, j) and inc(j, k) and i != k and not inc(i, k)
                   for i in range(n) for j in range(n) for k in range(n))


def weighted_norm(T, w):
    n = len(T)
    out = F(0)
    outside = []
    for i in range(n):
        for j in range(n):
            if not T[i][j]:
                continue
            if w[i] and w[j]:
                out = max(out, abs(T[i][j]) / (w[i] * w[j]))
            else:
                outside.append((i, j))
    return out, outside


def probe_A():
    print('(A) die Konstruktion auf Halbordnungen endlicher Hoehe')
    rng = random.Random(20260904)
    bad_sym = bad_int = bad_row = bad_out = 0
    weak = 0
    total = 0
    rs = set()
    for L in (2, 3):
        for width in (2, 3, 4, 5, 6):
            for _ in range(3):
                n, rel = random_graded(L, width, rng)
                m = [F(0)] + [F(1, 2) ** (k + 1) for k in range(n - 2)] + [F(0)]
                M = sum(m)
                m = [x / M for x in m]
                V = poset_V(m, lambda a, s: rel[s][a])
                T, r = certificate(V, n - 1)
                sym, inter, row = check_certificate(T, V, n - 1)
                bad_sym += not sym
                bad_int += not inter
                bad_row += not row
                rs.add(r)
                w = [m[i] + (1 if i in (0, n - 1) else 0) for i in range(n)]
                _, outside = weighted_norm(T, w)
                bad_out += bool(outside)
                weak += incomparability_transitive(rel, n)
                total += 1
    print(f'  {total} Halbordnungen, r in {sorted(rs)}, '
          f'{total - weak} davon mit nicht transitiver Unvergleichbarkeit')
    check(bad_sym == 0, 'T symmetrisch')
    check(bad_int == 0, 'T V = V^T T')
    check(bad_row == 0, 'T 1 = e_{t*}')
    check(bad_out == 0, 'T traegt nur auf Punkten positiven Gewichts')
    check(total - weak == total, 'keine der Halbordnungen ist eine schwache '
                                 'Ordnung (Theorem 21 greift nirgends)')


# ===================================================================== (B)
#
# Die Breite waechst, die Hoehe nicht.  Familien:
#   Leiter  a_i < b_j  <=>  i < j        (Hoehe 4, r = 3)
#   Krone   a_i < b_j  <=>  i != j       (Hoehe 4, r = 3)
#   Kette   (Kontrolle: die Hoehe waechst mit, r waechst mit)


def two_level(nn, al, be, cross):
    n = 2 * nn + 2
    masses = [F(0)] + [al ** i for i in range(1, nn + 1)] \
        + [be ** j for j in range(1, nn + 1)] + [F(0)]
    tstar = n - 1

    def less(c, s):
        if c == s or s == 0 or c == tstar:
            return False
        if c == 0 or s == tstar:
            return True
        if 1 <= c <= nn and nn + 1 <= s <= 2 * nn:
            return cross(c, s - nn)
        return False
    return masses, less, tstar


def chain_family(nn, al):
    n = nn + 2
    masses = [F(0)] + [al ** i for i in range(1, nn + 1)] + [F(0)]
    return masses, (lambda c, s: c < s), n - 1


def measure(masses, less, tstar):
    M = sum(masses)
    masses = [x / M for x in masses]
    n = len(masses)
    V = poset_V(masses, less)
    T, r = certificate(V, tstar)
    assert all(check_certificate(T, V, tstar))
    w = [masses[i] + (1 if i in (0, tstar) else 0) for i in range(n)]
    C, outside = weighted_norm(T, w)
    assert not outside
    return n, r, C


def probe_B():
    print('(B) waechst die Breite, so bleibt C = max |T_st|/(w_s w_t) '
          'beschraenkt')
    fams = [
        ('Leiter i<j, al=1/2, be=1/3',
         lambda k: two_level(k, F(1, 2), F(1, 3), lambda i, j: i < j)),
        ('Leiter i<j, al=1/3, be=1/2',
         lambda k: two_level(k, F(1, 3), F(1, 2), lambda i, j: i < j)),
        ('Krone i!=j, al=1/2, be=1/3',
         lambda k: two_level(k, F(1, 2), F(1, 3), lambda i, j: i != j)),
        ('Kette, al=1/2 (Kontrolle: die Hoehe waechst mit)',
         lambda k: chain_family(k, F(1, 2))),
    ]
    for name, fam in fams:
        print(f'  {name}')
        prev = None
        vals = []
        for k in (2, 3, 4, 5, 6, 7, 8, 10, 12):
            n, r, C = measure(*fam(k))
            vals.append((n, r, C))
            print(f'    n = {n:3d}   r = {r:2d}   C = {float(C):14.6f}')
            prev = C
        rs = [r for _, r, _ in vals]
        if 'Kette' in name:
            check(rs[-1] > rs[0], 'r waechst mit der Kettenlaenge')
        else:
            check(len(set(rs)) == 1, f'r konstant = {rs[0]}')
            tail = [C for _, _, C in vals[-5:]]
            inc = [abs(b - a) for a, b in zip(tail, tail[1:])]
            check(inc == sorted(inc, reverse=True) and inc[-1] < tail[-1] / 200,
                  f'die Zuwaechse von C fallen, der letzte betraegt '
                  f'{float(inc[-1] / tail[-1]) * 100:.3f}% von C')
    return {name: measure(*fam(12))[2] for name, fam in fams[:1]}


# ===================================================================== (C)
#
# Das Zertifikat auf der **unendlichen** Leiter, exakt.
#
#   T = {0} u {a_i}_{i>=1} u {b_j}_{j>=1} u {t*},  0 < alles < t*,
#   a_i < b_j <=> i < j,  m(a_i) = al^i,  m(b_j) = be^j,  m(0) = m(t*) = 0.
#
# Vektoren werden als geschlossene geometrische Reihen gefuehrt: Wert an 0,
# Koeffizientenliste (c, x) mit Wert an a_i = sum c x^i, dito an b_j, Wert an
# t*.  Diese Klasse ist unter V, V^T und unter Produkten abgeschlossen, und
# alle Reihen werden in geschlossener Form summiert -- kein Grenzuebergang,
# keine Trunkierung.

AL = F(1, 2)
BE = F(1, 3)


class Vec:
    def __init__(self, z=0, A=(), B=(), t=0):
        self.z, self.A, self.B, self.t = F(z), list(A), list(B), F(t)

    def at(self, p):
        kind, k = p
        if kind == '0':
            return self.z
        if kind == 't':
            return self.t
        terms = self.A if kind == 'a' else self.B
        return sum((c * base ** k for c, base in terms), F(0))

    def total(self):
        s = self.z + self.t
        for c, base in self.A + self.B:
            assert base < 1, 'divergente Reihe'
            s += c * base / (1 - base)
        return s

    def __add__(self, o):
        return Vec(self.z + o.z, self.A + o.A, self.B + o.B, self.t + o.t)

    def __rmul__(self, k):
        k = F(k)
        return Vec(k * self.z, [(k * c, b) for c, b in self.A],
                   [(k * c, b) for c, b in self.B], k * self.t)


ONE = Vec(1, [(F(1), F(1))], [(F(1), F(1))], 1)
ET = Vec(0, [], [], 1)


def Vt(x):
    """(V^T x)_c = m_c sum_{s>c} x_s."""
    A = [(c * base / (1 - base), AL * base) for c, base in x.B]
    A.append((x.t, AL))
    return Vec(0, A, [(x.t, BE)], 0)


def Vfwd(x):
    """(V x)_s = sum_{c<s} m_c x_c."""
    B, t = [], F(0)
    for c, base in x.A:
        g = AL * base
        assert g < 1
        B.append((c * g / (1 - g), F(1)))
        B.append((-c / (1 - g), g))
        t += c * g / (1 - g)
    for c, base in x.B:
        g = BE * base
        assert g < 1
        t += c * g / (1 - g)
    return Vec(0, [], B, t)


def infinite_certificate():
    powers = [ONE]
    probe = [('0', 0), ('t', 0)] + [('a', i) for i in range(1, 7)] \
        + [('b', j) for j in range(1, 7)]
    while True:
        nxt = Vfwd(powers[-1])
        if all(nxt.at(p) == 0 for p in probe):
            break
        powers.append(nxt)
        assert len(powers) < 8
    r = len(powers)
    u = powers[r - 1]
    assert u.t != 0 and all(u.at(p) == 0 for p in probe if p != ('t', 0))
    S = u.t
    p = [None] * r
    p[r - 1] = (F(1) / S) * ET
    for k in range(r - 2, -1, -1):
        p[k] = Vt(p[k + 1])
    a = [pk.total() for pk in p]
    assert a[0] == 1
    ws = [F(1)]
    for k in range(1, r):
        ws.append(-sum(a[j] * ws[k - j] for j in range(1, k + 1)))
    ph = []
    for k in range(r):
        v = Vec()
        for j in range(k + 1):
            v = v + ws[k - j] * p[j]
        ph.append(v)
    psi = [ET]
    for k in range(1, r):
        psi.append(Vt(psi[-1]))
    c = [pk.total() for pk in psi]
    terms = []
    for k in range(r):
        terms.append((F(1), ph[k], psi[k]))
        terms.append((F(1), psi[k], ph[k]))
    for k in range(r):
        for l in range(r):
            if k + l < r:
                terms.append((-c[k + l], ph[k], ph[l]))
    return r, S, c, terms


def Tval(terms, s, t):
    return sum((co * u.at(s) * v.at(t) for co, u, v in terms), F(0))


def probe_C():
    print('(C) das Zertifikat auf der unendlichen Leiter, exakt')
    r, S, c, terms = infinite_certificate()
    print(f'  r = {r},  S = (V^{r - 1} 1)_(t*) = {S},  c = {[str(x) for x in c]}')
    pts = [('0', 0), ('t', 0)] + [('a', i) for i in range(1, 9)] \
        + [('b', j) for j in range(1, 9)]
    check(all(Tval(terms, s, t) == Tval(terms, t, s) for s in pts for t in pts),
          'T symmetrisch')
    rows = {s: sum((co * u.at(s) * v.total() for co, u, v in terms), F(0))
            for s in pts}
    check(all(v == (1 if s == ('t', 0) else 0) for s, v in rows.items()),
          'T 1 = e_{t*}  (Zeilensummen in geschlossener Form)')
    tv = [(co, u, Vt(v)) for co, u, v in terms]
    vtt = [(co, Vt(u), v) for co, u, v in terms]
    check(all(Tval(tv, s, t) == Tval(vtt, s, t) for s in pts for t in pts),
          'T V = V^T T')
    check(all(Tval(tv, s, t) == Tval(tv, t, s) for s in pts for t in pts),
          'T V symmetrisch')

    def wgt(p):
        kind, k = p
        return {'0': F(1), 't': F(1), 'a': AL ** k, 'b': BE ** k}[kind]
    C = max(abs(Tval(terms, s, t)) / (wgt(s) * wgt(t)) for s in pts for t in pts)
    deep = max(abs(Tval(terms, s, t)) / (wgt(s) * wgt(t))
               for s in [('a', i) for i in range(1, 26)]
                        + [('b', j) for j in range(1, 26)]
               for t in [('a', i) for i in range(1, 26)]
                        + [('b', j) for j in range(1, 26)])
    check(deep <= C, f'die Schranke wird nicht tief drinnen ueberboten '
                     f'({float(deep):.6f} <= {float(C):.6f})')
    check(all(Tval(terms, ('0', 0), t) == 0 for t in pts), 'Zeile 0 ist null')
    M = AL / (1 - AL) + BE / (1 - BE)
    print(f'  sup |T_st|/(w_s w_t) = {float(C):.6f}  (unnormiert, M = {M})')
    print(f'  auf M = 1 normiert:    {float(C * M * M):.6f}')
    gaps = []
    for k in (8, 12, 16, 20):
        _, _, Cfin = measure(*two_level(k, AL, BE, lambda i, j: i < j))
        gaps.append(C * M * M - Cfin)
        print(f'  Probe (B) bei Breite {k:2d}:  {float(Cfin):.6f}'
              f'   Abstand {float(gaps[-1]):.3e}')
    check(all(0 < g for g in gaps) and gaps == sorted(gaps, reverse=True)
          and gaps[-1] < gaps[0] / 20,
          'die endlichen Zertifikate steigen monoton gegen den unendlichen '
          'Wert (zwei unabhaengige Implementierungen)')


# ===================================================================== (D)
#
# Der Antikettenzeuge des dreiundzwanzigsten Laufs:  T = {0} u A u {t*},
# A unendliche Antikette, kappa(a_i,a_j) = sgn(i-j) f(min(i,j)) mit
# f(i) = 1/(sigma_i sigma_{i+1}).  Dort ist r = 2, das Zertifikat existiert
# (Theorem 20) und ist beschraenkt, (F) faellt aus -- und der Ausfall sitzt
# genau in der einen Umbenennung tr(SK) = -tr(SK).


def probe_D():
    print('(D) der Antikettenzeuge: tr((TV)K) haengt an der Reihenfolge')
    fams = [('m_i = 2^-i', lambda i: F(1, 2) ** i,
             lambda i: F(1, 2) ** (i - 1)),
            ('m_i = 1/(i(i+1))', lambda i: F(1, i * (i + 1)),
             lambda i: F(1, i)),
            ('m_i = 3^-i', lambda i: F(1, 3) ** i,
             lambda i: F(1, 2) * F(1, 3) ** (i - 1))]
    for name, mass, sigma in fams:
        Mtot = sigma(1)
        check(all(sigma(i) - sigma(i + 1) == mass(i) for i in range(1, 40)),
              f'{name}: sigma ist der Schwanz von m')

        def f(i):
            return 1 / (sigma(i) * sigma(i + 1))

        def kap(i, j):
            return F(0) if i == j else (1 if i > j else -1) * f(min(i, j))

        def v(j):
            """v_j = sum_i m_i kappa(a_i,a_j), Partialsumme plus exakter
            Schwanz: fuer i > N >= j ist kappa(a_i,a_j) = +f(j)."""
            N = j + 20
            return sum(mass(i) * kap(i, j) for i in range(1, N + 1)) \
                + sigma(N + 1) * f(j)

        check(all(v(j) == Mtot ** -1 for j in range(1, 25)),
              f'{name}: v_j = 1/M fuer j = 1..24 (Theorem 19)')
        # tr((TV)K) = sum_{i,j} m_i (m_j/M) kappa(a_i,a_j).  Innen vollstaendig
        # summiert, aussen abgeschnitten -- und die beiden Reihenfolgen laufen
        # auseinander:
        for N in (10, 40, 80):
            outer_j = sum(mass(j) / Mtot * v(j) for j in range(1, N + 1))
            outer_i = sum(mass(i) / Mtot * (-v(i)) for i in range(1, N + 1))
            exact = (Mtot - sigma(N + 1)) / Mtot ** 2
            if N == 80:
                print(f'    {name}: N = {N}: {float(outer_j):+.8f} gegen '
                      f'{float(outer_i):+.8f},  1/M = '
                      f'{float(Mtot ** -1):.8f}')
            check(outer_j == exact and outer_i == -exact,
                  f'{name}: N = {N}: die Reihenfolgen geben '
                  f'+({1}-sigma_(N+1)/M)/M und ihr Negatives')
        check(True, f'{name}: Grenzwerte +1/M und -1/M, Differenz '
                    f'2 delta(t*) = {2 / Mtot}')


# ===================================================================== (E)
#
# Proposition 23.1 in der Messung.  Auf der dyadischen ordnungsdichten Uhr
# sitzt die Zeile T_{t* .} auf dem kleinsten Atom, und ihr Gewicht dort
# waechst wie 1/m_min -- genau der Mechanismus, an dem der Beweis von
# Proposition 23.1 den Widerspruch holt.


def probe_E():
    print('(E) Proposition 23.1 an der dyadischen Uhr')
    print(f'  {"Level":>5} {"n":>4} {"T_(t*,a_1)":>12} {"Rest der Zeile":>16}'
          f' {"C >= 1/m_(a_1)":>16}')
    ok_row = ok_grow = True
    prev = None
    for level in (1, 2, 3, 4, 5, 6):
        inner = sorted({F(k, 2 ** e) for e in range(1, level + 1)
                        for k in range(1, 2 ** e, 2)})

        def lvl(p):
            return p.denominator.bit_length() - 1

        m = [F(0)] + [F(1, 8) ** lvl(p) for p in inner] + [F(0)]
        M = sum(m)
        m = [x / M for x in m]
        n = len(m)
        order = [F(-1)] + inner + [F(2)]
        V = poset_V(m, lambda a, s: order[a] < order[s])
        T, _ = certificate(V, n - 1)
        assert all(check_certificate(T, V, n - 1))
        row = T[n - 1]
        # a_1 = das ordnungskleinste Atom
        a1 = 1 + min(range(len(inner)), key=lambda k: inner[k])
        rest = sum(abs(row[i]) for i in range(n) if i != a1)
        bound = 1 / m[a1]
        print(f'  {level:5d} {n:4d} {float(row[a1]):12.6g} '
              f'{float(rest):16.6g} {float(bound):16.6g}')
        ok_row = ok_row and row[a1] == 1 and rest == 0
        ok_grow = ok_grow and (prev is None or bound > prev)
        prev = bound
    check(ok_row, 'die Zeile t* ist genau e_(a_1): das ganze Gewicht sitzt '
                  'auf dem ordnungskleinsten Atom')
    check(ok_grow, 'die noetige Konstante 1/m_(a_1) waechst unbeschraenkt -- '
                   'im ordnungsdichten Limes gibt es a_1 nicht mehr')


# =====================================================================


PROBES = {'A': probe_A, 'B': probe_B, 'C': probe_C, 'D': probe_D, 'E': probe_E}


def main(argv):
    which = argv[1:] or ['all']
    keys = sorted(PROBES) if which == ['all'] else which
    for k in keys:
        PROBES[k]()
        print()
    if FAIL:
        print('AUSFAELLE:')
        for f in FAIL:
            print(' ', f)
        return 1
    print('alles ok')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
