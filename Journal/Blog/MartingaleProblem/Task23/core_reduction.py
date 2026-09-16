r"""Lauf 33: die endliche Kernreduktion (Theorem 39), am Orakel geprueft.

Rahmen wie in `ideal_exhaustion.py`: T abzaehlbare Halbordnung mit kleinstem
Element 0, m >= 0, kappa antisymmetrisch, Psi(s,t) = sum_{a<s} m_a kappa(a,t),
(diamondsuit) an allen Paaren, delta = diag Psi, t* die Spitze, W = T_{<t*}.

Die Beobachtung.  Sei K ein *endliches* Abwaertsideal von W mit 0 in K,
P = K \ {0}, und Z_K : R^P -> R^K, (Z f)(s) = sum_{a<s} f(a).  Fuer jedes d in W
ist die Funktion s |-> Psi(d,s) auf K gleich -Z_K(psi_d) mit psi_d(b) = m_b
kappa(b,d)  [(diamondsuit) an (d,s) und delta = 0].  Also liegt fuer jede
Funktion f im abgeschlossenen Spann der Idealindikatoren 1_{T_{<d}} die
Funktion F_f(s) := sum_a f(a) m_a kappa(a,s) (s in K) im Bild R := range(Z_K).
Ist insbesondere 1_{W \ K} in diesem Spann, so ist

    chi(s) := sum_{c in W \ K} m_c kappa(c,s)      (s in K)

in R, chi = Z psi'' fuer ein psi'' auf P, und die Korrektur
kappa'(a,t*) := kappa(a,t*) + psi''(a)/m_a  (a in P) macht K' := K + {t*} zu
einem endlichen (diamondsuit)-System mit delta'(t*) = delta(t*).  Dann
`prop:atomicposet`.  Das ist die Klasse "endlicher Kern plus haengende
omega-Ketten" fuer *alle* m >= 0, ohne die Vermutung C(K).

Geprueft wird hier die endliche Mechanik, exakt in `Fraction`:

  (A) Trunkierungen W_n ohne Spitze, Kern K = der endliche Kern:  fuer jeden
      kettenueberdeckten Kettenpunkt c und jedes h in ker Z_K^T ist das
      Funktional sum_{s in K} h(s) m_c kappa(c,s) erzwungen (= 0); fuer den
      obersten Kettenpunkt (nicht ueberdeckt) ist es das i.a. nicht
      (Kontrolle).  Ebenso fuer jedes d in W_n die Funktion Psi(d,.)|_K.

  (B) Das endliche Reduktionslemma: T endlich mit Spitze t*, K ein
      Abwaertsideal von W mit 1_K im Spann der Idealindikatoren (dann ist chi
      in R fuer jede Loesung).  Fuer eine Kernbasis des (diamondsuit)-Systems
      auf T: chi in R, psi'' konstruiert, kappa' auf K' erfuellt (diamondsuit)
      an allen Paaren von K', delta'(t*) = delta(t*).  Zufaellige endliche
      Halbordnungen mit Spitze plus alle Abwaertsideale K; und die vier
      Schleifen des 32. Laufs mit Ketten der Laenge n und K = ein Ideal.

  (C) Kontrolle des Orakels: bei gleichen Massen auf einer Kette ist Psi
      konstant auf Antidiagonalen (Phi-Bild) -- hier in kappa-Gestalt: auf
      der Kette mit gleichen Massen ist kappa(a,b) fuer alle Paare erzwungen
      symmetrisch in dem Sinn, dass Psi(s,t) = -Psi(t,s) (delta = 0) --
      und am Diamanten mit m = (0,1,-1,0) faellt die Dualitaet (antisym.py).
"""
import itertools
import random
import sys
from fractions import Fraction

from posetsearch import rank
from antisym import kappa_index, psi_row, system as diamond_system, check_diamond
from ideal_exhaustion import closure, is_forced, maximal, psi_row_single
from bowties import with_chains


# ------------------------------------------------------------ lineare Algebra

def nullspace(rows, ncol):
    """Basis des Kerns von rows (Liste von Zeilen), exakt."""
    M = [r[:] for r in rows if any(r)]
    pivots = []
    r = 0
    for c in range(ncol):
        piv = None
        for i in range(r, len(M)):
            if M[i][c]:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncol) if c not in pivots]
    basis = []
    for fc in free:
        v = [Fraction(0)] * ncol
        v[fc] = Fraction(1)
        for i, pc in enumerate(pivots):
            v[pc] = -M[i][fc]
        basis.append(v)
    return basis


def in_span(vectors, target, dim):
    """Liegt target im Spann der vectors?  (Vektoren als Listen der Laenge dim.)"""
    if not any(target):
        return True
    base = rank(vectors, dim) if vectors else 0
    return rank(vectors + [target], dim) == base


def solve_in_span(vectors, target, dim):
    """Koeffizienten c mit sum c_i vectors_i = target, oder None."""
    k = len(vectors)
    # Gleichungssystem: fuer jede Koordinate j: sum_i c_i vectors[i][j] = target[j]
    rows = []
    for j in range(dim):
        rows.append([vectors[i][j] for i in range(k)] + [target[j]])
    # Gauss
    M = [r[:] for r in rows]
    pivots = []
    r = 0
    for c in range(k):
        piv = None
        for i in range(r, len(M)):
            if M[i][c]:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
    for i in range(r, len(M)):
        if M[i][k] != 0:
            return None
    c = [Fraction(0)] * k
    for i, pc in enumerate(pivots):
        c[pc] = M[i][k]
    return c


# ------------------------------------------------------------ Halbordnungen

def Z_columns(K, down):
    """Spalten von Z_K : R^P -> R^K als Vektoren auf K (Indexliste K)."""
    P = [a for a in K if a != 0]
    pos = {s: i for i, s in enumerate(K)}
    cols = []
    for a in P:
        v = [Fraction(0)] * len(K)
        for s in K:
            if a in down[s]:
                v[pos[s]] = Fraction(1)
        cols.append(v)
    return cols, pos


def kerZT(K, down):
    """Basis von ker Z_K^T = {h auf K : sum_{s>a} h(s) = 0 fuer alle a in P}."""
    P = [a for a in K if a != 0]
    pos = {s: i for i, s in enumerate(K)}
    rows = []
    for a in P:
        r = [Fraction(0)] * len(K)
        for s in K:
            if a in down[s]:
                r[pos[s]] = Fraction(1)
        rows.append(r)
    return nullspace(rows, len(K)), pos


def down_sets(pts, down):
    """Alle Abwaertsideale, die 0 enthalten (als sortierte Tupel)."""
    rest = [p for p in pts if p != 0]
    out = []
    for bits in itertools.product((0, 1), repeat=len(rest)):
        S = {0} | {p for p, b in zip(rest, bits) if b}
        if all(set(down[s]) <= S for s in S):
            out.append(tuple(sorted(S)))
    return out


def ideal_indicator_span(W, down):
    r"""Spann der 1_{T_{<d}}, d in W, als Funktionen auf W \ {0}."""
    Wp = [w for w in W if w != 0]
    pos = {w: i for i, w in enumerate(Wp)}
    vecs = []
    for d in W:
        v = [Fraction(0)] * len(Wp)
        for a in down[d]:
            if a != 0:
                v[pos[a]] = Fraction(1)
        if any(v):
            vecs.append(v)
    return vecs, pos, Wp


def random_poset_with_top(n, rng, density):
    """Halbordnung auf 0..n-1 mit 0 unten und n-1 oben."""
    edges = set()
    for i in range(1, n - 1):
        for j in range(i + 1, n - 1):
            if rng.random() < density:
                edges.add((i, j))
    edges |= {(0, i) for i in range(1, n)} | {(i, n - 1) for i in range(1, n - 1)}
    return closure(n, list(edges))


# ------------------------------------------------------------ Probe A

CORES = {
    'Doppelschleife': (7, [(0, i) for i in range(1, 7)] + [(1, 5), (2, 5), (3, 5), (1, 6), (2, 6), (4, 6)], [5, 6]),
    'haengende Doppelschleife': (9, [(0, i) for i in range(1, 9)] + [(3, 4), (5, 6), (1, 7), (2, 7), (4, 7), (1, 8), (2, 8), (6, 8)], [7, 8]),
    'doppelt haengende Doppelschleife': (11, [(0, i) for i in range(1, 11)] + [(1, 2), (3, 4), (5, 6), (7, 8), (2, 9), (4, 9), (6, 9), (2, 10), (4, 10), (8, 10)], [9, 10]),
    'Dreifachschleife': (8, [(0, i) for i in range(1, 8)] + [(1, 5), (2, 5), (3, 5), (1, 6), (2, 6), (4, 6), (3, 7), (4, 7)], [5, 6, 7]),
    'Krone': (5, [(0, i) for i in range(1, 5)] + [(1, 3), (2, 3), (1, 4), (2, 4)], [3, 4]),
}


def probe_A(label, N0, edges0, hooks, n, m_core, rng, verbose=True):
    """Trunkierung ohne Spitze; K = Kern (0..N0-1)."""
    N, edges, chain_pts = with_chains(N0, edges0, hooks, n)
    lt, down = closure(N, edges)
    pts = list(range(N))
    m = list(m_core) + [Fraction(rng.randint(1, 9), rng.randint(1, 7)) for _ in chain_pts]
    rows, idx, ncol = diamond_system(pts, down, m)
    base = rank(rows, ncol)
    K = list(range(N0))
    H, pos = kerZT(K, down)
    mx = maximal(N, lt)
    covered = [c for c in chain_pts if c not in mx]     # c_i, i < n
    top = [c for c in chain_pts if c in mx]             # c_n

    def functional_h_c(h, c):
        r = [Fraction(0)] * ncol
        for s in K:
            if h[pos[s]]:
                rr = psi_row_single(c, s, m, idx, ncol)
                r = [u + h[pos[s]] * v for u, v in zip(r, rr)]
        return r

    ok = True
    n_cov = n_top_free = 0
    for c in covered:
        for h in H:
            r = functional_h_c(h, c)
            if not is_forced(rows, base, ncol, r):
                ok = False
                print('   AUSFALL (A): %s, kettenueberdeckt c=%d, h=%s nicht erzwungen' % (label, c, h))
            n_cov += 1
    for c in top:
        for h in H:
            r = functional_h_c(h, c)
            if not is_forced(rows, base, ncol, r):
                n_top_free += 1
    # Psi(d,.)|_K in R fuer jedes d in W_n
    n_psi = 0
    for d in pts:
        for h in H:
            r = [Fraction(0)] * ncol
            for s in K:
                if h[pos[s]]:
                    rr = psi_row(d, s, down, m, idx, ncol)
                    r = [u + h[pos[s]] * v for u, v in zip(r, rr)]
            if not is_forced(rows, base, ncol, r):
                ok = False
                print('   AUSFALL (A): %s, Psi(%d,.)|_K nicht in R' % (label, d))
            n_psi += 1
    if verbose:
        print('  (A) %-34s n=%d: dim ker Z_K^T = %d; %d Proben an ueberdeckten c: alle erzwungen: %s;'
              ' Psi(d,.)|_K: %d Proben ok; oberste Kettenpunkte frei in %d/%d Proben'
              % (label, n, len(H), n_cov, ok, n_psi, n_top_free, len(top) * len(H)))
    return ok


# ------------------------------------------------------------ Probe B

def reduction_check(N, down, m, K, verbose_label=None):
    """Endliches Reduktionslemma auf T = 0..N-1 mit Spitze N-1, Kern K.
    Liefert (alles_ok, chi_in_R_fuer_alle, anzahl_basis)."""
    tstar = N - 1
    pts = list(range(N))
    rows, idx, ncol = diamond_system(pts, down, m)
    basis = nullspace(rows, ncol)
    W = [p for p in pts if p != tstar]
    C = [c for c in W if c not in K]
    P = [a for a in K if a != 0]
    cols, pos = Z_columns(K, down)
    Kp = list(K) + [tstar]
    down_Kp = {s: [a for a in down[s] if a in K] for s in Kp}
    down_Kp[tstar] = list(K)
    ok_all = chi_all = True
    for v in basis:
        def kap(a, b):
            if a == b:
                return Fraction(0)
            return v[idx[(a, b)]] if a < b else -v[idx[(b, a)]]
        # chi auf K
        chi = [sum((m[c] * kap(c, s) for c in C), Fraction(0)) for s in K]
        coef = solve_in_span(cols, chi, len(K))
        if coef is None:
            chi_all = False
            continue
        psi2 = dict(zip(P, coef))
        # Anpassung: psi''(P) = theta - psi_inf(K) = sum_{c in C} m_c kappa(c,t*)
        theta = sum((m[a] * kap(a, tstar) for a in W), Fraction(0))
        psi_inf_K = sum((m[a] * kap(a, tstar) for a in K), Fraction(0))
        need = theta - psi_inf_K
        have = sum(psi2.values(), Fraction(0))
        kmax = [k for k in P if not any(k in down[s] for s in K)]
        if P:
            psi2[kmax[0]] += need - have
        elif need != have:
            ok_all = False
            print('   AUSFALL (B): P leer, aber psi''(P) != g_t*(C)')
            continue
        # kappa' auf K'
        def kap2(a, b):
            if a == b:
                return Fraction(0)
            if a == tstar:
                return -kap2(b, a)
            if b == tstar:
                return kap(a, tstar) + (psi2[a] / m[a] if a in psi2 and m[a] else Fraction(0))
            return kap(a, b)
        def Psi2(s, t):
            return sum((m[a] * kap2(a, t) for a in down_Kp[s]), Fraction(0))
        delta2 = {s: Psi2(s, s) for s in Kp}
        for s in Kp:
            for t in Kp:
                if Psi2(s, t) + Psi2(t, s) != delta2[s] + delta2[t]:
                    ok_all = False
                    print('   AUSFALL (B): (diamondsuit) auf K'' verletzt an (%d,%d)' % (s, t))
        if delta2[tstar] != theta:
            ok_all = False
            print('   AUSFALL (B): delta''(t*) = %s != theta = %s' % (delta2[tstar], theta))
        if any(delta2[s] != 0 for s in K):
            ok_all = False
            print('   AUSFALL (B): delta'' auf K nicht 0')
    if verbose_label:
        print('  (B) %s: Kerndim %d, chi in R fuer alle: %s, Reduktion ok: %s'
              % (verbose_label, len(basis), chi_all, ok_all))
    return ok_all, chi_all, len(basis)


def probe_B_random(rng, trials, nrange):
    tot = tot_span = tot_ok = tot_chi_not_span = 0
    fails = 0
    for _ in range(trials):
        n = rng.choice(nrange)
        lt, down = random_poset_with_top(n, rng, rng.choice((0.2, 0.35, 0.5)))
        m = [Fraction(0)] + [Fraction(rng.randint(1, 9), rng.randint(1, 5)) for _ in range(1, n - 1)] + [Fraction(0)]
        pts = list(range(n))
        W = pts[:-1]
        vecs, posW, Wp = ideal_indicator_span(W, down)
        for K in down_sets(W, {s: down[s] for s in W}):
            if len(K) == n - 1:
                continue                     # K = W: C leer, trivial
            indK = [Fraction(0)] * len(Wp)
            for a in K:
                if a != 0:
                    indK[posW[a]] = Fraction(1)
            in_sp = in_span(vecs, indK, len(Wp))
            ok, chi_all, dim = reduction_check(n, down, m, list(K))
            tot += 1
            if in_sp:
                tot_span += 1
                if not chi_all:
                    fails += 1
                    print('   AUSFALL (B): 1_K im Spann, aber chi nicht in R: n=%d down=%s K=%s' % (n, down, K))
                if not ok:
                    fails += 1
            else:
                if chi_all:
                    tot_chi_not_span += 1
                    if not ok:
                        fails += 1
            if chi_all and ok:
                tot_ok += 1
    print('  (B) zufaellig: %d Paare (T,K); 1_K im Spann: %d (chi in R und Reduktion ok in allen);'
          ' chi in R ohne Spannzugehoerigkeit: %d (Reduktion dort ebenfalls ok); Ausfaelle: %d'
          % (tot, tot_span, tot_chi_not_span, fails))
    return fails == 0


def probe_B_signed(rng, trials, nrange):
    """Wie probe_B_random, aber mit gemischten Vorzeichen: dort ist theta i.a.
    nicht 0 (Diamant), und delta'(t*) = theta wird nichttrivial geprueft.
    Das Reduktionslemma braucht m >= 0 nicht; nur prop:atomicposet tut es."""
    tot = tot_span = n_theta_nonzero = fails = 0
    for _ in range(trials):
        n = rng.choice(nrange)
        lt, down = random_poset_with_top(n, rng, rng.choice((0.2, 0.35, 0.5)))
        m = [Fraction(0)] + [Fraction(rng.choice((-3, -2, -1, 1, 2, 3, 5)), rng.randint(1, 3)) for _ in range(1, n - 1)] + [Fraction(0)]
        pts = list(range(n))
        W = pts[:-1]
        # theta frei?  (delta(t*) erzwungen?)
        rows, idx, ncol = diamond_system(pts, down, m)
        base = rank(rows, ncol)
        theta_free = not is_forced(rows, base, ncol, psi_row(n - 1, n - 1, down, m, idx, ncol))
        n_theta_nonzero += theta_free
        vecs, posW, Wp = ideal_indicator_span(W, down)
        for K in down_sets(W, {s: down[s] for s in W}):
            if len(K) == n - 1:
                continue
            indK = [Fraction(0)] * len(Wp)
            for a in K:
                if a != 0:
                    indK[posW[a]] = Fraction(1)
            if not in_span(vecs, indK, len(Wp)):
                continue
            # bei gemischten Vorzeichen kann m_a = 0 fuer a in P nicht vorkommen (gewaehlt != 0)
            ok, chi_all, dim = reduction_check(n, down, m, list(K))
            tot += 1
            if not chi_all:
                # 1_K im Spann, aber 1_W nur im Spann, wenn theta = 0: bei freiem theta erwartet
                if not theta_free:
                    fails += 1
                    print('   AUSFALL (B\'): theta erzwungen, 1_K im Spann, chi nicht in R')
                continue
            tot_span += 1
            if not ok:
                fails += 1
    print("  (B') vorzeichenbehaftet: %d Halbordnungen mit freiem theta von %d; %d Paare (T,K) mit 1_K im Spann,"
          " davon chi in R bei allen Loesungen: %d, Reduktion (inkl. delta'(t*) = theta) ok; Ausfaelle: %d"
          % (n_theta_nonzero, trials, tot, tot_span, fails))
    return fails == 0


def probe_B_diamond(rng):
    """Kontrolle: die Hypothese ist mit d in W zu lesen, nicht mit d = t*.
    Diamant 0 < a, b < d mit m_a = 1, m_b = -1, darueber eine Kette
    d < c_1 < ... < t* und seitlich zufaellige Punkte; K = T_{<d} = {0,a,b}.
    Im *endlichen* T enthaelt W \\ K maximale Elemente von W, die in keinem
    1_{T_{<d}} (d in W) liegen; 1_{W \\ K} liegt nur ueber d = t* im Spann, und
    F_{1_W}(s) = theta - Z psi_inf(s) liegt genau bei theta = 0 in R.
    Erwartet also: chi in R  <=>  theta = 0, Vektor fuer Vektor; wo chi in R,
    ist die Reduktion ok."""
    n_vec = n_chi_out = n_delta_d_nonzero = n_mismatch = fails = 0
    for trial in range(30):
        n = rng.randint(0, 2)
        k = rng.randint(0, 3)
        N = 5 + n + k
        tstar = N - 1
        edges = [(0, i) for i in range(1, N)] + [(1, 3), (2, 3)]
        prev = 3
        for i in range(n):
            edges.append((prev, 4 + i)); prev = 4 + i
        edges.append((prev, tstar))
        side = list(range(4 + n, 4 + n + k))
        for sp in side:
            edges.append((sp, tstar))
            for q in [1, 2, 3] + side:
                if q != sp and rng.random() < 0.3 and (q, sp) not in edges and (sp, q) not in edges:
                    edges.append((q, sp))
        try:
            lt, down = closure(N, edges)
        except AssertionError:
            continue
        m = [Fraction(0), Fraction(1), Fraction(-1)] + [Fraction(rng.choice((-2, -1, 1, 2, 3))) for _ in range(3, N - 1)] + [Fraction(0)]
        K = [0, 1, 2]
        pts = list(range(N))
        rows, idx, ncol = diamond_system(pts, down, m)
        basis = nullspace(rows, ncol)
        cols, pos = Z_columns(K, down)
        C = [c for c in range(N - 1) if c not in K]
        for v in basis:
            def kap(a, b):
                if a == b:
                    return Fraction(0)
                return v[idx[(a, b)]] if a < b else -v[idx[(b, a)]]
            theta = sum((m[a] * kap(a, tstar) for a in range(N - 1)), Fraction(0))
            chi = [sum((m[c] * kap(c, s) for c in C), Fraction(0)) for s in K]
            chi_in = solve_in_span(cols, chi, len(K)) is not None
            n_vec += 1
            n_delta_d_nonzero += (theta != 0)
            n_chi_out += (not chi_in)
            if (theta != 0) == chi_in:
                n_mismatch += 1
        ok, chi_all, dim = reduction_check(N, down, m, K)
        if not ok:
            fails += 1
    print("  (B'') Kontrolle Diamantfamilie: %d Basisvektoren, theta != 0 bei %d, chi nicht in R bei %d,"
          " Abweichungen zwischen beiden: %d (erwartet 0); wo chi in R: Reduktion ok, Ausfaelle %d"
          % (n_vec, n_delta_d_nonzero, n_chi_out, n_mismatch, fails))
    return fails == 0


def probe_B_cores(rng, n):
    ok = True
    for label, (N0, edges0, hooks) in CORES.items():
        N, edges, chain_pts = with_chains(N0, edges0, hooks, n)
        # Spitze anhaengen
        edges = edges + [(c, N) for c in range(1, N)] + [(0, N)]
        lt, down = closure(N + 1, edges)
        m = [Fraction(0)] + [Fraction(rng.randint(1, 9), rng.randint(1, 7)) for _ in range(1, N)] + [Fraction(0)]
        # K = Ideal T_{<c_1} ueber dem ersten Haken (kettenueberdeckt), und K = Kern
        c1 = chain_pts[0]
        K_ideal = sorted(down[c1])
        r1 = reduction_check(N + 1, down, m, K_ideal, '%s, n=%d, K = T_{<c_1}' % (label, n))
        K_core = list(range(N0))
        r2 = reduction_check(N + 1, down, m, K_core, '%s, n=%d, K = Kern' % (label, n))
        ok &= r1[0] and r2[0] and r1[1]
        # Erwartung: bei K = Kern ist chi in R genau dann, wenn 1_Kern im Idealspann
        W = list(range(N))
        vecs, posW, Wp = ideal_indicator_span(W, down)
        indK = [Fraction(0)] * len(Wp)
        for a in K_core:
            if a != 0:
                indK[posW[a]] = Fraction(1)
        print('      1_Kern im Idealspann (endliches T mit Spitze): %s' % in_span(vecs, indK, len(Wp)))
    return ok


# ------------------------------------------------------------ main

def main():
    rng = random.Random(33)
    rc = 0
    print('== (C) Kontrolle des Orakels (antisym.check_diamond)')
    if not check_diamond():
        rc = 1
    print('== (A) Trunkierungen ohne Spitze: kettenueberdeckte Werte liegen im Bild von Z_K')
    for label, (N0, edges0, hooks) in CORES.items():
        for n in (1, 2, 3):
            for trial in range(2):
                m_core = [Fraction(0)] + [Fraction(rng.randint(1, 9), rng.randint(1, 7)) for _ in range(1, N0)]
                if not probe_A(label, N0, edges0, hooks, n, m_core, rng, verbose=(trial == 0)):
                    rc = 1
    # zufaellige Kerne
    fails = 0
    for trial in range(40):
        N0 = rng.randint(4, 7)
        edges0 = [(0, i) for i in range(1, N0)]
        for i in range(1, N0):
            for j in range(i + 1, N0):
                if rng.random() < rng.choice((0.2, 0.4)):
                    edges0.append((i, j))
        lt0, down0 = closure(N0, edges0)
        hooks = sorted(maximal(N0, lt0))
        m_core = [Fraction(0)] + [Fraction(rng.randint(1, 9), rng.randint(1, 7)) for _ in range(1, N0)]
        if not probe_A('zufaelliger Kern %d' % trial, N0, edges0, hooks, 2, m_core, rng, verbose=False):
            fails += 1
    print('  (A) 40 zufaellige Kerne, n=2: Ausfaelle %d' % fails)
    rc |= bool(fails)
    print('== (B) endliches Reduktionslemma')
    if not probe_B_random(rng, 60, (5, 6, 7)):
        rc = 1
    if not probe_B_cores(rng, 2):
        rc = 1
    if not probe_B_signed(rng, 60, (4, 5, 6)):
        rc = 1
    if not probe_B_diamond(rng):
        rc = 1
    print('rc =', rc)
    return rc


if __name__ == '__main__':
    sys.exit(main())
