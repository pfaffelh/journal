r"""Ideal-Ausschoepfung (zweiunddreissigster Lauf, 2026-09-16).

Rahmen des fuenfundzwanzigsten Laufs: T abzaehlbare Halbordnung mit kleinstem
Element 0, kappa antisymmetrisch, Psi(s,t) = sum_{a<s} m_a kappa(a,t),
d(t) = Psi(t,t), (diamondsuit) an allen Paaren.  Setze

    g(c) := m_c kappa(c,0)        (c in T).

Dann ist d(t) = Psi(t,0) = sum_{c<t} g(c) fuer jedes t ((diamondsuit) an (t,0)).
Das Argument des Laufs:

  (i)  ist T_{<=a} endlich, so ist d(a) = 0 (prop:atomicposet auf dem Ideal),
       also  g(T_{<a}) = 0;
  (ii) liegt 1_{W}, W = T_{<t*}, im beschraenkten punktweisen Folgenabschluss
       des Spanns der Idealindikatoren 1_{T_{<a}} (a in W), so folgt
       d(t*) = g(W) = 0 aus (i) und dominierter Konvergenz (g ist absolut
       summierbar, weil Psi(t*,0) absolut konvergiert).

Dieses Skript prueft den endlichen Kern von (i)+(ii) exakt in Bruchrechnung,
und zwar OHNE die Spitze t*:  auf Trunkierungen W_n verschiedener Familien
wird fuer jedes c in W_n per Rangvergleich entschieden, ob das Funktional
g(c) auf dem Loesungsraum der Relationen (diamondsuit) innerhalb W_n
verschwindet.  Erwartung:

  * zwei disjunkte omega-Ketten, Leiter, Binaerbaum: g(c) erzwungen fuer jedes
    nicht-maximale c von W_n, frei fuer die maximalen (deren Ideale in W_n
    fehlen) -- das ist die Mechanik von (ii), Punkt fuer Punkt;
  * Antikette (Kanarienvogel): g(a_i) fuer kein i erzwungen;
  * "Doppelschleife" (p,q < a > r; p,q < a' > s; Ketten ueber a und a'):
    g(p), g(q), g(r), g(s) einzeln frei, aber g(T_{<a}) erzwungen -- und die
    Summe g(W_n minus maximale) ist NICHT erzwungen: die Idealmethode
    scheitert dort, wie im PROTOKOLL vorgerechnet.

Teil (E2): auf der Doppelschleife der Ausweg von Theorem 38 mit X = {x}: fuer
ein minimales Atom x hat phi_x(c) = m_c kappa(c,x) verschwindende Idealsummen,
und phi_x(W_n minus maximale minus x) ist erzwungen fuer x = r, s -- nicht aber
fuer x = p (p und q liegen in denselben Idealen; die Hypothese ist verletzt).

Teil (F): zufaellige Halbordnungen mit kleinstem Element -- fuer jede
Teilmenge S mit 1_S im Spann der Idealindikatoren ist g(S) erzwungen
(das ist die Algebra hinter (ii)); gezaehlt wird ausserdem, wie oft g(S)
erzwungen ist, ohne dass 1_S im Spann liegt (die (.,.)-Relationen geben mehr,
aber darauf ruht der Beweis nicht).

Aufruf:  python3 ideal_exhaustion.py [nmax]        (rc=0 heisst: alles wie erwartet)
"""
import itertools
import random
import sys
from fractions import Fraction

from posetsearch import rank
from antisym import kappa_index, psi_row, system as diamond_system


# ------------------------------------------------------------------ Halbordnungen

def closure(n, edges):
    """Transitiver Abschluss einer Relation auf range(n); down[s] = {a : a < s}."""
    lt = [[False] * n for _ in range(n)]
    for a, b in edges:
        lt[a][b] = True
    for k in range(n):
        for i in range(n):
            if lt[i][k]:
                for j in range(n):
                    if lt[k][j]:
                        lt[i][j] = True
    for i in range(n):
        assert not lt[i][i], "Zyklus"
    down = [[a for a in range(n) if lt[a][s]] for s in range(n)]
    return lt, down


def two_chains(n, alpha, beta):
    """0; a_1..a_n (1..n); b_1..b_n (n+1..2n).  a_i || b_j."""
    N = 2 * n + 1
    edges = [(0, i) for i in range(1, N)]
    edges += [(i, i + 1) for i in range(1, n)]
    edges += [(n + i, n + i + 1) for i in range(1, n)]
    m = [Fraction(0)] + [alpha(i) for i in range(1, n + 1)] + [beta(j) for j in range(1, n + 1)]
    names = ['0'] + ['a%d' % i for i in range(1, n + 1)] + ['b%d' % j for j in range(1, n + 1)]
    return N, edges, m, names


def ladder(n, alpha, beta):
    """Leiter: a_i < b_j  <=>  i < j."""
    N, edges, m, names = two_chains(n, alpha, beta)
    edges += [(i, n + j) for i in range(1, n + 1) for j in range(1, n + 1) if i < j]
    return N, edges, m, names


def antichain(n, mass):
    N = n + 1
    edges = [(0, i) for i in range(1, N)]
    m = [Fraction(0)] + [mass(i) for i in range(1, n + 1)]
    names = ['0'] + ['a%d' % i for i in range(1, n + 1)]
    return N, edges, m, names


def binary_tree(depth, mass):
    """Vollstaendiger Binaerbaum der Tiefe `depth` ueber 0 (Knoten 1..2^depth-1
    in Heap-Numerierung, Kinder von v sind 2v, 2v+1; 0 liegt unter allen)."""
    nodes = 2 ** depth - 1
    N = nodes + 1
    edges = [(0, v) for v in range(1, N)]
    for v in range(1, nodes + 1):
        for c in (2 * v, 2 * v + 1):
            if c <= nodes:
                edges.append((v, c))
    m = [Fraction(0)] + [mass(v) for v in range(1, nodes + 1)]
    names = ['0'] + ['v%d' % v for v in range(1, nodes + 1)]
    return N, edges, m, names


def double_bowtie(n, mass):
    """0; p,q,r,s minimal; a > p,q,r; a' > p,q,s; Ketten c_1<..<c_n ueber a,
    c'_1<..<c'_n ueber a'.  Ohne maximale Elemente im Limes, endliche Ideale,
    und die Idealsummen erzwingen g(W) NICHT (g(r)=g(s)=1, g(p)=-1)."""
    # Indizes: 0; p=1,q=2,r=3,s=4; a=5, a'=6; c_i = 6+i (1..n); c'_i = 6+n+i
    N = 7 + 2 * n
    edges = [(0, i) for i in range(1, N)]
    edges += [(1, 5), (2, 5), (3, 5), (1, 6), (2, 6), (4, 6)]
    edges += [(5, 7)] + [(6 + i, 7 + i) for i in range(1, n)]
    edges += [(6, 7 + n)] + [(6 + n + i, 7 + n + i) for i in range(1, n)]
    m = [Fraction(0)] + [mass(i) for i in range(1, N)]
    names = ['0', 'p', 'q', 'r', 's', 'a', "a'"] + ['c%d' % i for i in range(1, n + 1)] \
        + ["c'%d" % i for i in range(1, n + 1)]
    return N, edges, m, names


# ------------------------------------------------------------------ der Test

def g_row(c, m, idx, ncol):
    """Zeile des Funktionals kappa |-> g(c) = m_c kappa(c,0)."""
    r = [Fraction(0)] * ncol
    if c != 0 and m[c]:
        r[idx[(0, c)]] -= m[c]          # kappa(c,0) = -kappa(0,c)
    return r


def psi_row_single(c, x, m, idx, ncol):
    """Zeile des Funktionals kappa |-> m_c kappa(c,x)."""
    r = [Fraction(0)] * ncol
    if c == x or not m[c]:
        return r
    if c < x:
        r[idx[(c, x)]] += m[c]
    else:
        r[idx[(x, c)]] -= m[c]
    return r


def forced_set(N, edges, m):
    """Menge der c, fuer die g(c) auf dem Loesungsraum erzwungen ist, plus
    Hilfsdaten (rows, base, idx, ncol, down)."""
    lt, down = closure(N, edges)
    pts = list(range(N))
    rows, idx, ncol = diamond_system(pts, down, m)
    base = rank(rows, ncol)
    forced = set()
    for c in pts:
        r = g_row(c, m, idx, ncol)
        if not any(r) or rank(rows + [r], ncol) == base:
            forced.add(c)
    return forced, (rows, base, idx, ncol, down, lt)


def is_forced(rows, base, ncol, r):
    return (not any(r)) or rank(rows + [r], ncol) == base


def maximal(N, lt):
    return {c for c in range(N) if not any(lt[c][s] for s in range(N))}


def run_family(label, N, edges, m, names, expect_nonmax_forced, expect_max_free=True):
    forced, (rows, base, idx, ncol, down, lt) = forced_set(N, edges, m)
    mx = maximal(N, lt)
    nonmax = set(range(N)) - mx
    ok = True
    nm_forced = nonmax <= forced
    mx_free = not (mx & forced - {0})
    if expect_nonmax_forced and not nm_forced:
        ok = False
    if expect_max_free and not mx_free:
        ok = False
    print("  %-28s |W|=%2d  erzwungen: %s" % (
        label, N, ' '.join(names[c] for c in sorted(forced) if c != 0) or '-'))
    print("  %-28s        frei:      %s" % (
        '', ' '.join(names[c] for c in sorted(set(range(N)) - forced)) or '-'))
    return ok, forced, (rows, base, idx, ncol, down, lt)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    rc = 0
    half = lambda i: Fraction(1, 2 ** i)
    third = lambda j: Fraction(1, 3 ** j)
    # Theorem-37-Massen, B=16
    B = 16
    alphaB = lambda i: Fraction(1, B ** i)
    betaB = lambda j: Fraction(1, B ** j) * (Fraction(2) if j % 2 == 1 else Fraction(1, 2))

    print("(A) zwei disjunkte omega-Ketten, ohne Spitze: g(c) erzwungen genau fuer "
          "nicht-maximale c")
    for n in range(2, nmax + 1):
        for lab, al, be in (("2^-i, 3^-j", half, third), ("Theorem 37, B=16", alphaB, betaB)):
            N, edges, m, names = two_chains(n, al, be)
            ok, forced, _ = run_family("n=%d %s" % (n, lab), N, edges, m, names, True)
            rc |= (not ok)

    print("(B) Leiter a_i<b_j <=> i<j, ohne Spitze")
    for n in range(2, nmax + 1):
        for lab, al, be in (("(1/2,1/3)", half, third), ("(1/3,1/2)", third, half),
                            ("(1/2,1/2)", half, half)):
            N, edges, m, names = ladder(n, al, be)
            ok, forced, _ = run_family("n=%d %s" % (n, lab), N, edges, m, names, True)
            rc |= (not ok)

    print("(C) Binaerbaum ohne Spitze (Heap-Numerierung, Masse 2^-v)")
    for depth in range(2, 5):
        N, edges, m, names = binary_tree(depth, lambda v: Fraction(1, 2 ** v))
        ok, forced, _ = run_family("Tiefe %d" % depth, N, edges, m, names, True)
        rc |= (not ok)

    print("(D) Kanarienvogel: Antikette ohne Spitze -- nichts erzwungen")
    for n in range(2, nmax + 1):
        N, edges, m, names = antichain(n, half)
        forced, _ = forced_set(N, edges, m)
        ok = forced == {0}
        print("  n=%d  erzwungen: %s   %s" % (n, sorted(forced), 'ok' if ok else 'FEHLER'))
        rc |= (not ok)

    print("(E) Doppelschleife: Einzelwerte frei, g(T_<a) erzwungen, Gesamtsumme ueber "
          "die nicht-maximalen Punkte NICHT erzwungen")
    for n in range(1, 4):
        N, edges, m, names = double_bowtie(n, lambda i: Fraction(1, 2 ** i))
        ok, forced, (rows, base, idx, ncol, down, lt) = run_family(
            "Ketten der Laenge %d" % n, N, edges, m, names, False)
        # Einzelwerte p,q,r,s frei?
        singles_free = not ({1, 2, 3, 4} & forced)
        # g(T_<a) = g(p)+g(q)+g(r) erzwungen?
        ra = [Fraction(0)] * ncol
        for c in down[5]:
            ra = [x + y for x, y in zip(ra, g_row(c, m, idx, ncol))]
        ideal_forced = is_forced(rows, base, ncol, ra)
        # Summe ueber alle nicht-maximalen Punkte
        mx = maximal(N, lt)
        rs = [Fraction(0)] * ncol
        for c in range(N):
            if c not in mx:
                rs = [x + y for x, y in zip(rs, g_row(c, m, idx, ncol))]
        total_forced = is_forced(rows, base, ncol, rs)
        # g(r) - g(s) erzwungen (Differenz der beiden Ideale)?
        rd = [x - y for x, y in zip(g_row(3, m, idx, ncol), g_row(4, m, idx, ncol))]
        diff_forced = is_forced(rows, base, ncol, rd)
        ok = singles_free and ideal_forced and (not total_forced) and diff_forced
        print("  n=%d  p,q,r,s frei: %s | g(T_<a) erzwungen: %s | g(r)-g(s) erzwungen: %s"
              " | Summe ueber nicht-maximale erzwungen: %s   %s" % (
                  n, singles_free, ideal_forced, diff_forced, total_forced,
                  'ok' if ok else 'FEHLER'))
        rc |= (not ok)

    print("(E2) Doppelschleife, der Ausweg ueber ein minimales Atom x (Theorem 38, Fall X={x}):"
          " phi_x(c) = m_c kappa(c,x) hat verschwindende Idealsummen, und"
          " phi_x(W_n minus maximale minus x) ist erzwungen")
    for n in range(1, 4):
        N, edges, m, names = double_bowtie(n, lambda i: Fraction(1, 2 ** i))
        lt, down = closure(N, edges)
        pts = list(range(N))
        rows, idx, ncol = diamond_system(pts, down, m)
        base = rank(rows, ncol)
        mx = maximal(N, lt)
        # x=p ist Kontrolle: p und q liegen in denselben Idealen, 1_{W minus p} liegt
        # NICHT im Spann, die Hypothese von Theorem 38 ist verletzt -> nicht erzwungen.
        for x, xname, expect in ((3, 'r', True), (4, 's', True), (1, 'p', False)):
            # phi_x(T_<y) fuer alle y erzwungen?
            ideals_ok = True
            for y in pts:
                r = [Fraction(0)] * ncol
                for c in down[y]:
                    r = [u + v for u, v in zip(r, psi_row_single(c, x, m, idx, ncol))]
                ideals_ok &= is_forced(rows, base, ncol, r)
            # phi_x ueber die nicht-maximalen Punkte ohne x
            r = [Fraction(0)] * ncol
            for c in pts:
                if c not in mx and c != x:
                    r = [u + v for u, v in zip(r, psi_row_single(c, x, m, idx, ncol))]
            tot = is_forced(rows, base, ncol, r)
            # zum Vergleich: phi_x ueber die nicht-maximalen Punkte MIT x (= dasselbe, phi_x(x)=0)
            ok = ideals_ok and (tot == expect)
            print("  n=%d  x=%s  Idealsummen von phi_x erzwungen: %s | phi_x(W_n\\max\\{x}) erzwungen: %s"
                  " (erwartet %s)   %s" % (n, xname, ideals_ok, tot, expect, 'ok' if ok else 'FEHLER'))
            rc |= (not ok)
        # Kontrolle: mit x = a (nicht minimal) ist phi_a(W_n\max\{a}) NICHT erzwungen
        x = 5
        r = [Fraction(0)] * ncol
        for c in pts:
            if c not in mx and c != x:
                r = [u + v for u, v in zip(r, psi_row_single(c, x, m, idx, ncol))]
        tot = is_forced(rows, base, ncol, r)
        print("  n=%d  Kontrolle x=a (nicht minimal): phi_a(W_n\\max\\{a}) erzwungen: %s   %s"
              % (n, tot, 'ok' if not tot else 'UNERWARTET'))
        rc |= tot

    print("(F) zufaellige Halbordnungen mit kleinstem Element: 1_S im Spann der "
          "Idealindikatoren  =>  g(S) erzwungen")
    random.seed(23)
    checked = 0
    extra = 0
    total_sets = 0
    for trial in range(40):
        n = random.randint(3, 6)
        N = n + 1
        edges = [(0, i) for i in range(1, N)]
        for i in range(1, N):
            for j in range(i + 1, N):
                if random.random() < 0.4:
                    edges.append((i, j))
        m = [Fraction(0)] + [Fraction(random.randint(1, 5), random.randint(1, 3))
                             for _ in range(1, N)]
        lt, down = closure(N, edges)
        pts = list(range(N))
        rows, idx, ncol = diamond_system(pts, down, m)
        base = rank(rows, ncol)
        # Spann der Idealindikatoren (Vektoren in Q^N)
        ideal_vecs = []
        for a in pts:
            v = [Fraction(0)] * N
            for c in down[a]:
                v[c] = Fraction(1)
            ideal_vecs.append(v)
        span_rank = rank(ideal_vecs, N)
        for bits in range(1, 2 ** n):
            S = [c for c in range(1, N) if bits >> (c - 1) & 1]
            v = [Fraction(0)] * N
            for c in S:
                v[c] = Fraction(1)
            in_span = rank(ideal_vecs + [v], N) == span_rank
            rS = [Fraction(0)] * ncol
            for c in S:
                rS = [x + y for x, y in zip(rS, g_row(c, m, idx, ncol))]
            forcedS = is_forced(rows, base, ncol, rS)
            total_sets += 1
            if in_span:
                checked += 1
                if not forcedS:
                    print("  FEHLER: 1_S im Spann, g(S) frei; S=%s, edges=%s" % (S, edges))
                    rc |= 1
            elif forcedS:
                extra += 1
    print("  %d Teilmengen, davon %d mit 1_S im Spann (alle erzwungen), %d erzwungen ohne "
          "Spann-Zugehoerigkeit (die (.,.)-Relationen geben mehr)" % (total_sets, checked, extra))

    print("rc =", rc)
    return rc


if __name__ == '__main__':
    sys.exit(main())
