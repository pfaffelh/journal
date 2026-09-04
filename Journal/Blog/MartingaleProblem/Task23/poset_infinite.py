#!/usr/bin/env python3
"""Task 23 — die unendliche Halbordnung: ein Gegenbeispiel, exakt nachgerechnet.

Gegenstand
----------
`prop:atomicposet` (sechster Lauf) beweist die Dualitaet fuer eine rein atomare
Uhr auf einer **endlichen** Halbordnung, mit nichtnegativen Massen und ohne jede
Bedingung an die Lage der Atome.  Theorem 17 (zweiundzwanzigster Lauf) beweist
sie fuer eine **beliebige abzaehlbare Kette**, unter der Zusatzhypothese

    (F)   sum_{a,b} m_a m_b |h(a,b)| < oo .

Offen war die unendliche Halbordnung.  Dieses Skript zeigt: sie ist **falsch**,
und zwar schon auf der einfachsten unendlichen Halbordnung ueberhaupt, der
abzaehlbaren Antikette.  Die Endlichkeit in `prop:atomicposet` ist keine
Bequemlichkeit des Beweises, und (F) ist im Halbordnungsfall unentbehrlich.

Das Modell (Variante I)
-----------------------
T = {0} < {a_1, a_2, ...} < {t*}, die a_i paarweise **unvergleichbar**;
m_0 = 0, Massen m_i > 0 mit M = sum_i m_i < oo, sigma_i = sum_{j>=i} m_j.
Abwaertsmengen: T_{<0} = leer, T_{<a_i} = {0}, T_{<t*} = {0} u A.

Setze  f(i) := 1 / (sigma_i sigma_{i+1})  und

    kappa(a_i, a_j) := sgn(i-j) * f(min(i,j)) .

Kernrechnung (Teleskop):  fuer jedes i ist

    v_i := sum_j m_j kappa(a_j, a_i)
         = - sum_{j<i} m_j f(j) + f(i) sigma_{i+1}
         = - (1/sigma_i - 1/sigma_1) + 1/sigma_i
         = 1/M ,

**konstant und von Null verschieden**, weil m_j f(j) = 1/sigma_{j+1} - 1/sigma_j
teleskopiert.  Jede Zeile konvergiert absolut (r_i = 2/sigma_i - 1/M < oo), die
Doppelsumme nicht (sum_i m_i r_i = oo) — genau (F) faellt aus.  Mit
kappa(a_j,0) = kappa(a_j,t*) = 1/M^2 loest das alle Relationen und hat
Phi(t*,0) - Phi(0,t*) = 1/M.

Variante II schiebt zwischen die Antikette und t* einen Punkt c mit
A < c < t* und Masse m_c > 0.  Dann ist q(T_{<c}) = M > 0, und der Defekt
delta(c) = 1/M sitzt an einem Punkt mit **positiver** Abwaertsmasse.

Was das Gegenbeispiel braucht (und was nicht)
---------------------------------------------
Es braucht q(T_{<a_i}) = 0, also q({0}) = 0 — der Normalfall einer Uhr, die
am kleinsten Punkt keine Masse hat.  Das ist nicht Zierde, sondern noetig:
ist q({0}) > 0, so gibt (diamondsuit) am Paar (0,a_i) sofort
m_0 kappa(0,a_i) = Psi(a_i,0) - delta(a_i) = 0, also kappa(0,a_i) = 0, und
(diamondsuit) am Paar (0,t*) gibt delta(t*) = sum_j m_j kappa(a_j,0) = 0.
Probe (H) haelt fest, dass das Gegenbeispiel unter q({0}) > 0 genau an den
Paaren (0,a_i) zerbricht — dort und nur dort.  Das ist dieselbe Bedingung, die
`sharp.py` (dritter Lauf) im
**endlichen** Fall als notwendig fuer jeden Ausfall gefunden hat: es gibt ein s
mit T_{<s} =/= leer und q(T_{<s}) = 0.  Im Endlichen brauchte ein Ausfall
ausserdem gemischte Vorzeichen; hier kauft die Unendlichkeit, was dort die
negativen Massen kauften.

Proben
------
(A) Massenfolgen: sigma_i = m_i + sigma_{i+1}, exakt.
(B) v_i = 1/M, auf zwei Wegen (geschlossene Form gegen Partialsumme + exakter
    Schwanz, fuer mehrere Abschneidestellen N).
(C) Zeilen konvergieren absolut, die Doppelsumme divergiert — (F) faellt aus.
(D) Alle Relationen (diamondsuit) auf ganz T, Varianten I und II.
(E) Ende zu Ende: Phi, gamma erfuellen beide Darstellungen (eq:incrementrep) an
    **jedem** vergleichbaren Paar, und der Defekt ist von Null verschieden;
    Phi ist dabei beschraenkt, gamma nicht.
(H) q({0}) > 0 zerbricht das Gegenbeispiel, und zwar genau an den Paaren
    (0,a_i) und (0,t*).
(G) Unter (F) ist der Antikettenfall wahr: die Fubini-Identitaet
    sum_i m_i v_i = 0 erzwingt delta = 0.  Auf endlichen Antiketten exakt
    geprueft; und die Trunkierung zeigt, wo der Rest sitzt:
    v_i^{(N)} = 1/M - f(i) sigma_{N+1}, punktweise -> 1/M, aber an der Spitze
    i = N ist der Fehler 1/sigma_N -> oo.  Der Trunkierungsrest verschwindet
    punktweise und nicht gleichmaessig.

Alles in exakter Bruchrechnung; kein Gleitkomma in den Entscheidungen.
rc=0 heisst: alle Proben bestanden.
"""

from fractions import Fraction as F
import random
import sys

FAIL = []


def check(name, cond, extra=""):
    if cond:
        print(f"  ok   {name}" + (f"   {extra}" if extra else ""))
    else:
        print(f"  FAIL {name}" + (f"   {extra}" if extra else ""))
        FAIL.append(name)


# ---------------------------------------------------------------------------
# Massenfolgen mit exaktem Schwanz
# ---------------------------------------------------------------------------

class Masses:
    """m_i > 0 fuer i >= 1, summierbar, mit geschlossener Schwanzformel."""

    def __init__(self, name, m, sigma):
        self.name = name
        self._m = m
        self._sigma = sigma

    def m(self, i):
        return self._m(i)

    def sigma(self, i):          # sum_{j >= i} m_j
        return self._sigma(i)

    @property
    def M(self):
        return self.sigma(1)

    def f(self, i):
        return 1 / (self.sigma(i) * self.sigma(i + 1))


GEOM = Masses("m_i = 2^-i", lambda i: F(1, 2 ** i), lambda i: F(1, 2 ** (i - 1)))
HARM = Masses("m_i = 1/(i(i+1))", lambda i: F(1, i * (i + 1)), lambda i: F(1, i))
CUBE = Masses("m_i = 3^-i", lambda i: F(1, 3 ** i),
              lambda i: F(1, 2 * 3 ** (i - 1)))

FAMILIES = [GEOM, HARM, CUBE]


def probe_A():
    print("(A) Massenfolgen: sigma_i = m_i + sigma_{i+1}")
    for ms in FAMILIES:
        ok = all(ms.sigma(i) == ms.m(i) + ms.sigma(i + 1) for i in range(1, 30))
        ok2 = True
        for i in range(1, 12):
            s = sum(ms.m(j) for j in range(i, i + 25))
            ok2 &= (ms.sigma(i) - s == ms.sigma(i + 25))
        check(f"{ms.name}: Rekursion und Partialsummen", ok and ok2,
              f"M = {ms.M}")


# ---------------------------------------------------------------------------
# Der Kern: kappa auf der Antikette, und v_i
# ---------------------------------------------------------------------------

def kappa_A(ms, i, j):
    """kappa(a_i, a_j) = sgn(i-j) * f(min(i,j))."""
    if i == j:
        return F(0)
    n = min(i, j)
    return ms.f(n) if i > j else -ms.f(n)


def v_closed(ms, i):
    """sum_j m_j kappa(a_j, a_i), geschlossene Form."""
    return -(1 / ms.sigma(i) - 1 / ms.sigma(1)) + ms.f(i) * ms.sigma(i + 1)


def v_partial(ms, i, N):
    """Dasselbe als Partialsumme bis N plus exakter Schwanz (N >= i)."""
    assert N >= i
    s = sum(ms.m(j) * kappa_A(ms, j, i) for j in range(1, N + 1))
    return s + ms.sigma(N + 1) * ms.f(i)      # kappa(a_j,a_i) = f(i) fuer j > N


def row_abs(ms, i):
    """sum_j m_j |kappa(a_j, a_i)|, geschlossene Form."""
    return (1 / ms.sigma(i) - 1 / ms.sigma(1)) + ms.f(i) * ms.sigma(i + 1)


def probe_B():
    print("(B) v_i = 1/M, geschlossene Form gegen Partialsumme + Schwanz")
    for ms in FAMILIES:
        ok = True
        for i in range(1, 10):
            vc = v_closed(ms, i)
            ok &= (vc == 1 / ms.M)
            for N in (i, i + 1, i + 7, i + 20):
                ok &= (v_partial(ms, i, N) == vc)
        check(f"{ms.name}: v_i = 1/M fuer i = 1..9, N = i..i+20", ok,
              f"1/M = {1 / ms.M}")


def probe_C():
    print("(C) Zeilen konvergieren absolut, die Doppelsumme nicht")
    for ms in FAMILIES:
        rows_ok = all(row_abs(ms, i) == 2 / ms.sigma(i) - 1 / ms.M
                      for i in range(1, 12))
        indep = True
        for i in range(1, 8):
            for N in (i, i + 5, i + 15):
                s = sum(ms.m(j) * abs(kappa_A(ms, j, i)) for j in range(1, N + 1))
                s += ms.sigma(N + 1) * ms.f(i)
                indep &= (s == row_abs(ms, i))
        check(f"{ms.name}: r_i = 2/sigma_i - 1/M, endlich fuer jedes i",
              rows_ok and indep)
        # die Doppelsumme: sum_i m_i r_i, Partialsummen bis N
        Ns = (10, 100, 1000, 5000)
        part, acc, k = [], F(0), 1
        for N in Ns:
            while k <= N:
                acc += ms.m(k) * row_abs(ms, k)
                k += 1
            part.append(acc)
        check(f"{ms.name}: sum_i m_i r_i waechst ueber jede Schranke — (F) faellt aus",
              all(part[i] < part[i + 1] for i in range(len(part) - 1))
              and part[-1] > 15,
              "N=" + ",".join(map(str, Ns)) + ": "
              + ", ".join(f"{float(p):.2f}" for p in part))


# ---------------------------------------------------------------------------
# Das volle System auf T
# ---------------------------------------------------------------------------

class Poset:
    """Variante I:  T = {0} < A < {t*},            m_0 = 0.
    Variante II: T = {0} < A < {c} < {t*},        m_0 = 0, m_c > 0.

    Punkte: "0", ("a", i), "c", "t*".  Alle Summen ueber A stehen in
    geschlossener Form; probe_sums prueft jede gegen Partialsumme + Schwanz.
    """

    def __init__(self, ms, mc=None):
        self.ms = ms
        self.mc = None if mc is None else F(mc)
        M = ms.M
        self.M = M
        self.x = 1 / M ** 2                    # kappa(a_j, 0)
        if self.mc is None:
            self.defect_at = "t*"
            self.defect = 1 / M
            self.y = 1 / M ** 2                # kappa(a_j, t*)
            self.k0t = F(0)                    # kappa(0, t*), frei
        else:
            # Herleitung siehe Kopf: chi = kappa(c,a_i) = -1/M^2,
            # delta(c) = 1/M, delta(t*) = 1/M - m_c/M^2, kappa(c,t*) = 0.
            self.chi = -1 / M ** 2
            self.delta_c = 1 / M
            self.defect_at = "c"
            self.defect = self.delta_c
            self.delta_t = 1 / M - self.mc / M ** 2
            self.y = self.delta_t / M          # kappa(a_j, t*)
            self.kc0 = -1 / M ** 2             # kappa(c, 0)
            self.kct = F(0)                    # kappa(c, t*)
            self.k0t = F(0)                    # kappa(0, t*), frei

    # -- Punkte ------------------------------------------------------------
    def points(self, n_atoms):
        p = ["0"] + [("a", i) for i in range(1, n_atoms + 1)]
        if self.mc is not None:
            p.append("c")
        p.append("t*")
        return p

    def mass(self, p):
        if p == "0":
            return F(0)
        if p == "c":
            return self.mc
        if p == "t*":
            return F(0)                        # t* ist maximal, kommt nie vor
        return self.ms.m(p[1])

    def le(self, p, q):
        if p == q:
            return True
        if p == "0":
            return True
        if q == "0":
            return False
        if q == "t*":
            return True
        if p == "t*":
            return False
        if q == "c":
            return isinstance(p, tuple)        # a_i < c
        if p == "c":
            return False
        return False                           # a_i, a_j unvergleichbar

    # -- kappa -------------------------------------------------------------
    def kappa(self, p, q):
        if p == q:
            return F(0)
        v = self._kappa_ordered(p, q)
        if v is not None:
            return v
        v = self._kappa_ordered(q, p)
        assert v is not None, (p, q)
        return -v

    def _kappa_ordered(self, p, q):
        if isinstance(p, tuple) and isinstance(q, tuple):
            return kappa_A(self.ms, p[1], q[1])
        if isinstance(p, tuple) and q == "0":
            return self.x
        if isinstance(p, tuple) and q == "t*":
            return self.y
        if p == "0" and q == "t*":
            return self.k0t
        if self.mc is not None:
            if p == "c" and isinstance(q, tuple):
                return self.chi
            if p == "c" and q == "0":
                return self.kc0
            if p == "c" and q == "t*":
                return self.kct
        return None

    # -- Summen ueber A ----------------------------------------------------
    def kappa_tail(self, t, j):
        """kappa(a_j, t) fuer grosses j — der Wert, der den Schwanz traegt."""
        if isinstance(t, tuple):
            assert j > t[1]
            return self.ms.f(t[1])
        return self.kappa(("a", j), t)

    def sumA_kappa(self, t, N=None):
        """sum_j m_j kappa(a_j, t).  Geschlossen (N=None) oder Partialsumme."""
        if N is None:
            if t == "0":
                return self.M * self.x
            if t == "t*":
                return self.M * self.y
            if t == "c":
                return -self.M * self.chi
            return v_closed(self.ms, t[1])
        s = sum(self.ms.m(j) * self.kappa(("a", j), t) for j in range(1, N + 1))
        return s + self.ms.sigma(N + 1) * self.kappa_tail(t, N + 1)

    # -- Psi, delta --------------------------------------------------------
    def downset(self, s):
        """(Punkte von T_{<s} ausser A, ob A ganz in T_{<s} liegt)."""
        if s == "0":
            return [], False
        if isinstance(s, tuple):
            return ["0"], False
        if s == "c":
            return ["0"], True
        if self.mc is None:
            return ["0"], True                 # s == "t*", Variante I
        return ["0", "c"], True                # s == "t*", Variante II

    def Psi(self, s, t):
        head, with_A = self.downset(s)
        val = sum(self.mass(p) * self.kappa(p, t) for p in head)
        if with_A:
            val += self.sumA_kappa(t)
        return val

    def delta(self, s):
        return self.Psi(s, s)

    # -- gamma, Phi --------------------------------------------------------
    def gamma(self, p, q):
        return self.kappa(p, q) / 2            # symmetrischer Anteil = 0

    def Phi(self, s, t):
        # Phi(s,t) = B(0,t) + A(s,t) mit A(s,t) = Psi(s,t)/2, B(0,t) = -Psi(t,0)/2
        return -self.Psi(t, "0") / 2 + self.Psi(s, t) / 2

    def interval_sum(self, s, sp, t, first=True):
        """int_{[s,sp)} gamma(r,t) q(dr) bzw. int_{[s,sp)} gamma(t,r) q(dr)."""
        head_s, A_s = self.downset(s)
        head_sp, A_sp = self.downset(sp)
        val = F(0)
        for p in head_sp:
            if p in head_s:
                continue
            val += self.mass(p) * (self.gamma(p, t) if first
                                   else self.gamma(t, p))
        if A_sp and not A_s:
            val += (self.sumA_kappa(t) / 2 if first else -self.sumA_kappa(t) / 2)
        return val


def probe_sums(P, label, n_atoms=6):
    ok = True
    targets = ["0", "t*"] + [("a", i) for i in range(1, n_atoms + 1)]
    if P.mc is not None:
        targets.append("c")
    for t in targets:
        base = P.sumA_kappa(t)
        for N in (n_atoms, n_atoms + 3, n_atoms + 11):
            ok &= (P.sumA_kappa(t, N) == base)
    check(f"{label}: alle A-Summen, geschlossen = Partialsumme + Schwanz", ok)


def probe_diamond(P, label, n_atoms=6):
    pts = P.points(n_atoms)
    bad = []
    for s in pts:
        for t in pts:
            if P.Psi(s, t) + P.Psi(t, s) != P.delta(s) + P.delta(t):
                bad.append((s, t))
    check(f"{label}: (diamondsuit) an {len(pts)**2} Paaren", not bad,
          "" if not bad else f"Ausfaelle: {bad[:3]}")


def probe_endtoend(P, label, n_atoms=6):
    pts = P.points(n_atoms)
    bad = []
    for s in pts:
        for sp in pts:
            if not P.le(s, sp):
                continue
            for t in pts:
                if P.Phi(sp, t) - P.Phi(s, t) != P.interval_sum(s, sp, t, True):
                    bad.append(("I", s, sp, t))
                if P.Phi(t, sp) - P.Phi(t, s) != P.interval_sum(s, sp, t, False):
                    bad.append(("II", s, sp, t))
    check(f"{label}: (eq:incrementrep), beide Darstellungen, alle vergleichbaren "
          f"Paare", not bad, "" if not bad else f"Ausfaelle: {bad[:3]}")
    d = P.Phi(P.defect_at, "0") - P.Phi("0", P.defect_at)
    check(f"{label}: Phi({P.defect_at},0) - Phi(0,{P.defect_at}) =/= 0",
          d == P.defect and d != 0, f"Defekt = {d}, "
          f"q(T_<{P.defect_at}) = {sum(P.mass(p) for p in P.downset(P.defect_at)[0]) + (P.M if P.downset(P.defect_at)[1] else 0)}")
    vals = {P.Phi(s, t) for s in pts for t in pts}
    check(f"{label}: Phi nimmt endlich viele Werte an (beschraenkt)",
          len(vals) <= 10, f"{len(vals)} Werte")
    gam = [abs(P.gamma(("a", i + 1), ("a", i))) for i in range(1, n_atoms)]
    check(f"{label}: gamma ist unbeschraenkt",
          all(gam[k] < gam[k + 1] for k in range(len(gam) - 1)),
          f"|gamma(a_{{i+1}},a_i)| von {gam[0]} bis {gam[-1]}")


def probe_H(n_atoms=6):
    """q({0}) > 0 zerbricht das Gegenbeispiel, an genau (0,a_i) und (0,t*)."""
    print("(H) q({0}) > 0 zerbricht das Gegenbeispiel")
    for ms in FAMILIES:
        P = Poset(ms)                                  # Variante I
        m0 = F(1, 7)
        pts = P.points(n_atoms)

        def Psi0(s, t):                                # dasselbe mit m_0 = 1/7
            head, with_A = P.downset(s)
            val = sum((m0 if p == "0" else P.mass(p)) * P.kappa(p, t)
                      for p in head)
            if with_A:
                val += P.sumA_kappa(t)
            return val

        bad = {(s, t) for s in pts for t in pts
               if Psi0(s, t) + Psi0(t, s) != Psi0(s, s) + Psi0(t, t)}
        expect = {("0", ("a", i)) for i in range(1, n_atoms + 1)}
        expect |= {(("a", i), "0") for i in range(1, n_atoms + 1)}
        check(f"{ms.name}: Ausfaelle genau an den Paaren (0,a_i)", bad == expect,
              f"{len(bad)} Ausfaelle, delta(a_i) = {-m0 * P.x} statt 0")


def probe_G():
    print("(G) Fubini schliesst den Antikettenfall, und die Trunkierung leckt")
    random.seed(23)
    ok = True
    for n in range(2, 8):
        for _ in range(30):
            m = [F(random.randint(1, 9)) for _ in range(n)]
            K = [[F(0)] * n for _ in range(n)]
            for i in range(n):
                for j in range(i + 1, n):
                    K[i][j] = F(random.randint(-9, 9), random.randint(1, 5))
                    K[j][i] = -K[i][j]
            v = [sum(m[j] * K[j][i] for j in range(n)) for i in range(n)]
            ok &= (sum(m[i] * v[i] for i in range(n)) == 0)
    check("endliche Antikette: sum_i m_i v_i = 0 (Antisymmetrie + Fubini)", ok)

    for ms in FAMILIES:
        ok_point, ok_top = True, True
        for N in (5, 10, 20):
            for i in range(1, N + 1):
                vN = sum(ms.m(j) * kappa_A(ms, j, i) for j in range(1, N + 1))
                ok_point &= (vN == 1 / ms.M - ms.f(i) * ms.sigma(N + 1))
            ok_top &= (ms.f(N) * ms.sigma(N + 1) == 1 / ms.sigma(N))
        tops = [1 / ms.sigma(N) for N in (5, 10, 20)]
        check(f"{ms.name}: v_i^(N) = 1/M - f(i) sigma_(N+1), Spitze 1/sigma_N",
              ok_point and ok_top and tops[0] < tops[1] < tops[2],
              f"Spitzenfehler N=5,10,20: {tops[0]}, {tops[1]}, {tops[2]}")


# ---------------------------------------------------------------------------

def main():
    print("Task 23 — die unendliche Halbordnung: ein Gegenbeispiel\n")
    probe_A()
    print()
    probe_B()
    print()
    probe_C()
    print()
    print("(D)/(E) Variante I: reine Antikette, T = {0} < A < {t*}")
    for ms in FAMILIES:
        P = Poset(ms)
        probe_sums(P, f"I/{ms.name}")
        probe_diamond(P, f"I/{ms.name}")
        probe_endtoend(P, f"I/{ms.name}")
    print()
    print("(D)/(E) Variante II: T = {0} < A < {c} < {t*}, m_c > 0 — der Defekt "
          "sitzt an c, und q(T_<c) = M > 0")
    for ms in FAMILIES:
        P = Poset(ms, mc=ms.M / 2)
        probe_sums(P, f"II/{ms.name}")
        probe_diamond(P, f"II/{ms.name}")
        probe_endtoend(P, f"II/{ms.name}")
    print()
    probe_H()
    print()
    probe_G()
    print()
    if FAIL:
        print(f"{len(FAIL)} Probe(n) gescheitert: {FAIL}")
        return 1
    print("alle Proben bestanden")
    return 0


if __name__ == "__main__":
    sys.exit(main())
