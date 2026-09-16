r"""Lauf 34: stumme Ketten.

Rahmen des 25. Laufs, m_0 = 0, delta == 0 auf W (endliche Ideale).  Eine
*haengende Kette* ist u_0 < u_1 < u_2 < ... vom Typ omega mit
T_{<u_{i+1}} = T_{<=u_i} fuer alle i.  Behauptung (Lemma 40, Protokoll):

    kappa(u_i, b) = 0   fuer jeden Punkt u_i einer haengenden Kette und
                        JEDEN Punkt b in W.

Beweis: Induktion ueber b (fundiert, weil die Ideale endlich sind).  Gilt
kappa(u, c) = 0 fuer alle c < b und alle Kettenpunkte u, so ist
Psi(b, u) = sum_{c<b} m_c kappa(c, u) = 0, also Psi(u, b) = 0 (Antisymmetrie
von Psi auf W), und m_{u_i} kappa(u_i, b) = Psi(u_{i+1}, b) - Psi(u_i, b) = 0.

Endliche Probe.  Auf der Trunkierung W_n ohne Spitze (Kettenpunkte
u_0 = Haken, u_1, ..., u_n) reicht die Induktion genau so weit, wie Kette
ueber dem Punkt steht: mit h(b) = Hoehe von b (h = 0 fuer minimale Atome,
h(b) = 1 + max_{c<b} h(c)) ist kappa(u_i, b) erzwungen 0, sobald

    i + h(b) <= n - 1 .                                             (*)

Geprueft wird (exakt in Fraction, ueber eine Kernbasis des Loesungsraums):

  (A)  (*) erzwingt kappa(u_i, b) = 0 -- fuer alle Paare, alle Familien;
  (A') an der Grenze i + h(b) = n ist kappa(u_i, b) in der Regel FREI: die
       Grenze ist scharf, das Lemma ist im Endlichen nicht trivial;
  (B)  Kontrolle: ein ueberdeckter Punkt, dessen Ueberdecker selbst nicht
       ueberdeckt ist (r_0 < r in der haengenden Doppelschleife), ist NICHT
       stumm: kappa(r_0, r') fuer den r'-Punkt eines anderen Kerns bleibt frei;
  (C)  Kontrolle: im Turm (Stufen {alpha_i, beta_i} statt Kette) ist der
       Haken a zwar ueberdeckt, aber nicht Teil einer haengenden Kette, und
       kappa(a, b) bleibt fuer geeignete b frei;
  (D)  Kontrolle des Orakels: antisym.check_diamond.

Familien fuer (A): disjunkte Doppelschleifen (k = 1, 2), haengende
Doppelschleife, Antikette plus haengende Kette ueber 0 (der Zeuge von
Theorem 19 mit einer Kette daneben), zwei disjunkte omega-Ketten, zufaellige
Kerne mit Ketten ueber jedem maximalen Kernpunkt.
"""
import random
import sys
from fractions import Fraction

from antisym import system as diamond_system, check_diamond
from ideal_exhaustion import closure, psi_row_single
from core_reduction import nullspace
from bowties import with_chains
from random_hanging import random_core


# ------------------------------------------------------------------ Halbordnungen

def rnd_mass(rng):
    return Fraction(rng.randint(1, 9), rng.randint(1, 7))


def disjoint_bowties(k, n, rng):
    """k Doppelschleifen (p,q,r < a; p,q,s < a'), je Ketten der Laenge n."""
    N0 = 1
    edges = []
    hooks = []
    for _ in range(k):
        p, q, r, s, a, a2 = range(N0, N0 + 6)
        edges += [(0, x) for x in (p, q, r, s, a, a2)]
        edges += [(p, a), (q, a), (r, a), (p, a2), (q, a2), (s, a2)]
        hooks += [a, a2]
        N0 += 6
    N, edges, chain_pts = with_chains(N0, edges, hooks, n)
    m = [Fraction(0)] + [rnd_mass(rng) for _ in range(1, N)]
    return N, edges, m, hooks, {}


def hanging_bowties(k, n, rng):
    """k haengende Doppelschleifen: p,q,r0,s0 minimal; r0<r, s0<s; p,q,r<a; p,q,s<a'."""
    N0 = 1
    edges = []
    hooks = []
    info = {'r0': [], 'r': []}
    for _ in range(k):
        p, q, r0, s0, r, s, a, a2 = range(N0, N0 + 8)
        edges += [(0, x) for x in range(N0, N0 + 8)]
        edges += [(r0, r), (s0, s), (p, a), (q, a), (r, a), (p, a2), (q, a2), (s, a2)]
        hooks += [a, a2]
        info['r0'].append(r0)
        info['r'].append(r)
        N0 += 8
    N, edges, chain_pts = with_chains(N0, edges, hooks, n)
    m = [Fraction(0)] + [rnd_mass(rng) for _ in range(1, N)]
    return N, edges, m, hooks, info


def antichain_plus_chain(k, n, rng):
    """k minimale Atome (Antikette) und eine haengende Kette ueber 0."""
    N0 = 1 + k
    edges = [(0, x) for x in range(1, N0)]
    # Haken ist ein weiterer minimaler Punkt, darueber die Kette
    hook = N0
    edges.append((0, hook))
    N0 += 1
    N, edges, chain_pts = with_chains(N0, edges, [hook], n)
    m = [Fraction(0)] + [rnd_mass(rng) for _ in range(1, N)]
    return N, edges, m, [hook], {}


def two_omega_chains(n, rng):
    edges = [(0, 1), (0, 2)]
    N, edges, chain_pts = with_chains(3, edges, [1, 2], n)
    m = [Fraction(0)] + [rnd_mass(rng) for _ in range(1, N)]
    return N, edges, m, [1, 2], {}


def random_cores_with_chains(kcores, n, rng):
    N0 = 1
    edges = []
    hooks = []
    for _ in range(kcores):
        k, e = random_core(rng, rng.randint(4, 6))
        # verschiebe die Punkte 1..k-1 nach N0..
        shift = {0: 0}
        for i in range(1, k):
            shift[i] = N0 + i - 1
        e = [(shift[a], shift[b]) for a, b in e]
        edges += e
        pts = list(range(N0, N0 + k - 1))
        lt, down = closure(N0 + k - 1, edges)
        mx = [x for x in pts if not any(lt[x][y] for y in range(N0 + k - 1))]
        hooks += mx
        N0 += k - 1
    N, edges, chain_pts = with_chains(N0, edges, hooks, n)
    m = [Fraction(0)] + [rnd_mass(rng) for _ in range(1, N)]
    return N, edges, m, hooks, {}


def tower_bowties(k, n, rng):
    """Doppelschleifen mit Tuermen: ueber jedem Haken Stufen {alpha_i, beta_i},
    alpha_i, beta_i < alpha_{i+1}, beta_{i+1}.  Keine Ueberdeckungen ausser
    Haken -> Stufe 1."""
    N0 = 1
    edges = []
    hooks = []
    for _ in range(k):
        p, q, r, s, a, a2 = range(N0, N0 + 6)
        edges += [(0, x) for x in (p, q, r, s, a, a2)]
        edges += [(p, a), (q, a), (r, a), (p, a2), (q, a2), (s, a2)]
        hooks += [a, a2]
        N0 += 6
    N = N0
    tower = {}
    for hk in hooks:
        prev = [hk]
        tower[hk] = []
        for i in range(n):
            new = [N, N + 1]
            for u in prev:
                for v in new:
                    edges.append((u, v))
            for v in new:
                edges.append((0, v))
            tower[hk].append(new)
            prev = new
            N += 2
    m = [Fraction(0)] + [rnd_mass(rng) for _ in range(1, N)]
    return N, edges, m, hooks, tower


# ------------------------------------------------------------------ Werkzeug

def heights(N, down):
    h = [0] * N
    order = sorted(range(N), key=lambda s: len(down[s]))
    for s in order:
        h[s] = 0 if not [c for c in down[s] if c != 0] else \
            1 + max(h[c] for c in down[s] if c != 0)
    return h


def chain_above(hook, N, down, lt):
    """Die haengende Kette u_0 = hook < u_1 < ... in W_n: u_{i+1} ist der Punkt
    mit T_{<u_{i+1}} = T_{<=u_i}."""
    chain = [hook]
    while True:
        cur = chain[-1]
        target = sorted(down[cur] + [cur])
        nxt = [w for w in range(N) if sorted(down[w]) == target]
        if not nxt:
            return chain
        chain.append(nxt[0])


class Space:
    def __init__(self, N, edges, m):
        self.lt, self.down = closure(N, edges)
        self.pts = list(range(N))
        self.m = m
        rows, self.idx, self.ncol = diamond_system(self.pts, self.down, m)
        self.basis = nullspace(rows, self.ncol)
        self.N = N

    def forced_zero(self, r):
        if not any(r):
            return True
        return all(sum(x * y for x, y in zip(r, v)) == 0 for v in self.basis)

    def kappa_forced_zero(self, u, b):
        return self.forced_zero(psi_row_single(u, b, self.m, self.idx, self.ncol))


# ------------------------------------------------------------------ Proben

def probe_A(label, N, edges, m, hooks):
    sp = Space(N, edges, m)
    h = heights(N, sp.down)
    ok = True
    n_in = n_border = free_border = 0
    for hk in hooks:
        chain = chain_above(hk, N, sp.down, sp.lt)
        n = len(chain) - 1                 # u_0..u_n
        for i, u in enumerate(chain):
            for b in range(1, N):
                if b == u:
                    continue
                if i + h[b] <= n - 1:
                    n_in += 1
                    if not sp.kappa_forced_zero(u, b):
                        ok = False
                        print('   AUSFALL (A): kappa(u_%d=%d, b=%d) frei, h(b)=%d, n=%d'
                              % (i, u, b, h[b], n))
                elif i + h[b] == n:
                    n_border += 1
                    if not sp.kappa_forced_zero(u, b):
                        free_border += 1
    print('  %-46s dim=%3d: (A) %4d Paare mit i+h(b)<=n-1 erzwungen 0: %s;'
          " (A') an der Grenze i+h(b)=n frei: %d/%d"
          % (label, len(sp.basis), n_in, 'ja' if ok else 'NEIN', free_border, n_border))
    return ok


def probe_B(n, rng):
    """Erste Fassung erwartete kappa(r_0, r') FREI.  Das Orakel sagt: erzwungen 0,
    und das ist richtig -- (diamondsuit) an (a_n, r_{0,k}) lautet
    Psi(a_n, r_{0,k}) = m_{r_n} kappa(r_n, r_{0,k}) = 0, weil die anderen Terme
    (p_n, q_n, r_{0,n} gegen das ueberdeckte minimale r_{0,k}) nach Lemma 40
    verschwinden.  r_0 ist also stumm, obwohl es auf keiner haengenden Kette
    liegt.  Kontrolle bleibt: kappa(r, r') und kappa(p, r') sind frei."""
    N, edges, m, hooks, info = hanging_bowties(2, n, rng)
    sp = Space(N, edges, m)
    r0a, r0b = info['r0']
    ra, rb = info['r']
    pa = r0a - 2
    f1 = sp.kappa_forced_zero(r0a, rb)
    f2 = sp.kappa_forced_zero(r0a, r0b)
    f3 = sp.kappa_forced_zero(ra, rb)
    f4 = sp.kappa_forced_zero(pa, rb)
    print("  haengende Doppelschleife x2, n=%d: kappa(r_0, r') erzwungen 0: %s; kappa(r_0, r_0') erzwungen 0: %s;"
          " kappa(r, r') erzwungen 0: %s (erwartet: nein); kappa(p, r') erzwungen 0: %s (erwartet: nein)"
          % (n, f1, f2, f3, f4))
    return f1 and f2 and not f3 and not f4


def probe_C(n, rng):
    """Stapel (Lemma 40, allgemeine Fassung): S_0 = {a}, S_i = {alpha_i, beta_i}.
    Erwartet auf W_n (n Stufen): kappa(a, b) erzwungen 0 fuer h(b) <= n-1;
    Stufensumme m_alpha kappa(alpha_i, b) + m_beta kappa(beta_i, b) erzwungen 0
    fuer i + h(b) <= n-1; die Einzelwerte kappa(alpha_i, b) i.a. FREI."""
    N, edges, m, hooks, tower = tower_bowties(2, n, rng)
    sp = Space(N, edges, m)
    h = heights(N, sp.down)
    ok = True
    n_hook = n_sum = n_single = free_single = 0
    for hk in hooks:
        stages = [[hk]] + tower[hk]
        for i, S in enumerate(stages):
            for b in range(1, N):
                if b in S or i + h[b] > n - 1:
                    continue
                r = [Fraction(0)] * sp.ncol
                for s in S:
                    r = [x + y for x, y in zip(r, psi_row_single(s, b, m, sp.idx, sp.ncol))]
                if not sp.forced_zero(r):
                    ok = False
                    print('   AUSFALL (C): Stufensumme S_%d gegen b=%d frei' % (i, b))
                if i == 0:
                    n_hook += 1
                else:
                    n_sum += 1
                    for s in S:
                        n_single += 1
                        if not sp.kappa_forced_zero(s, b):
                            free_single += 1
    print('  Doppelschleifen mit Tuermen x2, n=%d, dim=%d: Haken kappa(a,b) erzwungen 0 (%d Paare) und'
          ' Stufensummen erzwungen 0 (%d Paare): %s; Einzelwerte kappa(alpha_i,b) frei: %d/%d'
          % (n, len(sp.basis), n_hook, n_sum, 'ja' if ok else 'NEIN', free_single, n_single))
    return ok


def braided_bowtie(kind, n, rng):
    """Eine Doppelschleife; ueber jedem Haken ein Arm ohne haengenden Stapel:
    kind='shift': a_i<a_{i+1}, b_i<b_{i+1}, b_i<a_{i+1}, a_i<b_{i+2} (Ideale
    bilden eine Kette mit einelementigen Differenzen);
    kind='braid': drei Ketten a,b,c mit a_i<b_{i+1}, b_i<c_{i+1}, c_i<a_{i+1}
    (Ideale bilden keine Kette; 1_a in L_D durch Kombination)."""
    p, q, r, s, a, a2 = range(1, 7)
    edges = [(0, x) for x in range(1, 7)]
    edges += [(p, a), (q, a), (r, a), (p, a2), (q, a2), (s, a2)]
    N = 7
    arms = {}
    for hk in (a, a2):
        if kind == 'shift':
            A = list(range(N, N + n)); B = list(range(N + n, N + 2 * n)); N += 2 * n
            for x in A + B:
                edges.append((0, x))
            edges += [(hk, A[0]), (hk, B[0])]
            for i in range(n - 1):
                edges += [(A[i], A[i + 1]), (B[i], B[i + 1]), (B[i], A[i + 1])]
            for i in range(n - 2):
                edges += [(A[i], B[i + 2])]
            arms[hk] = A + B
        else:
            A = list(range(N, N + n)); B = list(range(N + n, N + 2 * n)); C = list(range(N + 2 * n, N + 3 * n)); N += 3 * n
            for x in A + B + C:
                edges.append((0, x))
            edges += [(hk, A[0]), (hk, B[0]), (hk, C[0])]
            for i in range(n - 1):
                edges += [(A[i], A[i + 1]), (B[i], B[i + 1]), (C[i], C[i + 1]),
                          (A[i], B[i + 1]), (B[i], C[i + 1]), (C[i], A[i + 1])]
            arms[hk] = A + B + C
    m = [Fraction(0)] + [rnd_mass(rng) for _ in range(1, N)]
    return N, edges, m, [a, a2], arms


def probe_E(kind, n, rng):
    """Lemma 40' jenseits der Stapel: Haken a und tiefe Armpunkte sind stumm
    gegen minimale Atome und Kernpunkte, sobald der Arm hoch genug ist."""
    N, edges, m, hooks, arms = braided_bowtie(kind, n, rng)
    sp = Space(N, edges, m)
    core = list(range(1, 7))
    a, a2 = hooks
    tests = [('kappa(a, x) fuer minimale x', [(a, x) for x in (1, 2, 3, 4)]),
             ("kappa(a, a')", [(a, a2)]),
             ("kappa(a, s)", [(a, 4)]),
             ('kappa(arm_1, x) fuer minimale x', [(arms[a][0], x) for x in (1, 2, 3, 4)]),
             ("kappa(arm_1, a')", [(arms[a][0], a2)]),
             ("kappa(a, arm'_1)", [(a, arms[a2][0])])]
    out = []
    for label, pairs in tests:
        f = sum(1 for u, b in pairs if sp.kappa_forced_zero(u, b))
        out.append('%s: %d/%d erzwungen 0' % (label, f, len(pairs)))
    print('  Doppelschleife mit %s-Armen, n=%d, dim=%d: %s' % (kind, n, len(sp.basis), '; '.join(out)))
    return True


def main():
    rng = random.Random(34)
    rc = 0
    print('== (D) Kontrolle des Orakels')
    if not check_diamond():
        rc = 1
    print('== (A)/(A\') stumme Ketten auf Trunkierungen ohne Spitze')
    fams = []
    for k in (1, 2):
        for n in (2, 3, 4):
            if k == 2 and n == 4:
                continue
            fams.append(('%d Doppelschleife(n), Ketten n=%d' % (k, n),) + disjoint_bowties(k, n, rng)[:4])
    for n in (2, 3):
        fams.append(('haengende Doppelschleife, n=%d' % n,) + hanging_bowties(1, n, rng)[:4])
    fams.append(('2 haengende Doppelschleifen, n=2',) + hanging_bowties(2, 2, rng)[:4])
    for k, n in ((3, 3), (4, 4), (3, 5)):
        fams.append(('Antikette(%d) + Kette n=%d' % (k, n),) + antichain_plus_chain(k, n, rng)[:4])
    for n in (3, 4, 5):
        fams.append(('zwei omega-Ketten, n=%d' % n,) + two_omega_chains(n, rng)[:4])
    for t in range(6):
        fams.append(('zufaellige Kerne x%d, n=%d (#%d)' % (2, 2 + t % 2, t),)
                    + random_cores_with_chains(2, 2 + t % 2, rng)[:4])
    for label, N, edges, m, hooks in fams:
        if not probe_A(label, N, edges, m, hooks):
            rc = 1
    print('== (B) haengende Doppelschleife: r_0 ist stumm, r und p nicht')
    for n in (2, 3):
        if not probe_B(n, rng):
            rc = 1
    print('== (C) Stapel: Tuerme statt Ketten, Stufensummen')
    for n in (2, 3, 4):
        if not probe_C(n, rng):
            rc = 1
    print("== (E) Lemma 40' jenseits der Stapel: verschraenkte Doppelkette und Dreierzopf")
    for kind in ('shift', 'braid'):
        for n in (2, 3, 4):
            probe_E(kind, n, rng)
    print('rc =', rc)
    return rc


if __name__ == '__main__':
    sys.exit(main())
