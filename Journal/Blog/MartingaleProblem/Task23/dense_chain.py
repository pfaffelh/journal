#!/usr/bin/env python3
"""Mechanische Verifikation der Beweisalgebra des zweiundzwanzigsten Laufs.

Gegenstand ist Theorem 17 des `PROTOKOLL.md` ("Die Stieltjes-Transformation,
2026-09-04"): das System (C1)-(C3) auf einer *beliebigen* abzaehlbaren
Atomkette erzwingt h(a,a)=0, ohne Diskretheit, ohne Intervallendlichkeit und
ohne einen einzigen Punkt zwischen einem Atom und seinem Nachfolger.

Der Beweis besteht aus einer Kette exakter Identitaeten; jede von ihnen wird
hier in `fractions.Fraction` auf zufaelligen endlichen Ketten geprueft, und
zwar **je unter genau den Hypothesen, die der Beweis fuer sie beansprucht** --
sonst waere die Probe entwertet, weil die volle Hypothesenmenge auf einer
endlichen Kette die Diagonale ohnehin toetet.

Bezeichnungen wie im Protokoll.  Punkte der Kette: 0 (Boden, Index -1), die
Atome a_0 < ... < a_{n-1} (Indizes 0..n-1), t^* (Index n).

    H(s,t)      = sum_{a<s} m_a h(a,t)
    Delta(t)    = sum_{a<t} m_a h(a,a)
    what(s,t)   = H(s,t) + Delta(t) - Delta(s)
    kappa(a,t)  = h(a,t) - h(a,a)
    W^c(a_i)    = prod_{j>i} (1 + c m_j),      V_0(c) = prod_j (1 + c m_j)
    K(t;c)      = sum_i m_i kappa(a_i,t) W^c(a_i)
    G(t;c)      = sum_i m_i what(a_i,t) W^c(a_i)
    P(c)        = sum_i m_i what(t^*,a_i) W^c(a_i)
    Q(c)        = sum_i m_i Delta(a_i)   W^c(a_i)
    R(c)        = sum_i m_i h(a_i,a_i)   W^c(a_i)
    S(c)        = sum_i m_i h(a_i,t^*)   W^c(a_i)

Proben:

  (A) Abel/Stieltjes auf beliebiger Kette:  K(t;c) - c G(t;c)
      = what(t^*,t) - what(0,t) V_0(c).   Ohne jede Hypothese an h.
  (B) P(c) = V_0(c) Q(c).   Nur (C2) und Antisymmetrie von what auf A x A.
  (C) R(c) = Delta(t^*) + c Q(c).   Nur (C1).
  (D) S(c) - R(c) + c P(c) = -Delta(t^*) V_0(c), die Identitaet (5).   Nur
      (C1) und Antisymmetrie von what an A x {t^*} samt (t^*,t^*).
  (D') S(c) = R(c) (1 - V_0(c)), also (7).   Unter der vollen
      Minimalhypothese, wo beide Seiten wegen (E) verschwinden.
  (E) Die Minimalhypothese -- (C1), (C2) auf A x A, (C3) nur auf
      (A cup {t^*})^2, also **ohne Luecken-Punkte** -- erzwingt h(a,a)=0.
      Rangprobe fuer n = 1..7.
  (F) Fusspunktzerlegung von Theorem 9 auf einer beliebigen Kette.
  (G) |V_0(c)| >= prod (1 + m_a^2 |c|^2)^{1/2} auf Re c >= 0, und
      |W^c(a)| <= |V_0(c)| dort.

rc = 0 genau dann, wenn alle Proben bestehen.
"""

from fractions import Fraction as F
import itertools
import random

import sympy

FAIL = []


def report(name, ok, detail=""):
    print(("  ok   " if ok else "  FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- Grundgroessen


class Chain:
    """Endliche Atomkette mit Boden 0 und Deckel t^*.

    h ist ein Dict (i, t) -> Fraction mit i in 0..n-1 (Atom) und
    t in {-1} u {0..n-1} u {n} (Punkt).
    """

    def __init__(self, m, h):
        self.m = list(m)
        self.n = len(self.m)
        self.h = h

    # Punkte: -1 = Boden 0, 0..n-1 = Atome, n = t^*
    def points(self):
        return list(range(-1, self.n + 1))

    def below(self, s):
        """Indizes der Atome a < s."""
        if s == -1:
            return []
        return list(range(s))  # s = i heisst Atom a_i; a_j < a_i <=> j < i
        # fuer s = n (= t^*) gibt range(n) alle Atome

    def H(self, s, t):
        return sum((self.m[j] * self.h[(j, t)] for j in self.below(s)), F(0))

    def Delta(self, t):
        return sum((self.m[j] * self.h[(j, j)] for j in self.below(t)), F(0))

    def what(self, s, t):
        return self.H(s, t) + self.Delta(t) - self.Delta(s)

    def kappa(self, i, t):
        return self.h[(i, t)] - self.h[(i, i)]

    def W(self, i, c):
        out = F(1)
        for j in range(i + 1, self.n):
            out *= 1 + c * self.m[j]
        return out

    def V0(self, c):
        out = F(1)
        for j in range(self.n):
            out *= 1 + c * self.m[j]
        return out

    def K(self, t, c):
        return sum((self.m[i] * self.kappa(i, t) * self.W(i, c) for i in range(self.n)), F(0))

    def G(self, t, c):
        return sum((self.m[i] * self.what(i, t) * self.W(i, c) for i in range(self.n)), F(0))

    def P(self, c):
        return sum((self.m[i] * self.what(self.n, i) * self.W(i, c) for i in range(self.n)), F(0))

    def Q(self, c):
        return sum((self.m[i] * self.Delta(i) * self.W(i, c) for i in range(self.n)), F(0))

    def R(self, c):
        return sum((self.m[i] * self.h[(i, i)] * self.W(i, c) for i in range(self.n)), F(0))

    def S(self, c):
        return sum((self.m[i] * self.h[(i, self.n)] * self.W(i, c) for i in range(self.n)), F(0))


def random_masses(n, rng):
    return [F(rng.randint(1, 12), rng.randint(1, 9)) for _ in range(n)]


def random_h(n, rng):
    h = {}
    for i in range(n):
        for t in range(-1, n + 1):
            h[(i, t)] = F(rng.randint(-9, 9), rng.randint(1, 5))
    return h


CS = [F(0), F(1), F(-1), F(3, 2), F(-7, 4), F(5), F(-13, 3)]


# ------------------------------------------------- Loeser fuer Teilhypothesen


def var_index(n):
    """Nummerierung der Unbekannten h(a_i, t)."""
    idx, k = {}, 0
    for i in range(n):
        for t in range(-1, n + 1):
            idx[(i, t)] = k
            k += 1
    return idx, k


def constraints(n, m, which):
    """Zeilen des homogenen Systems.  `which` waehlt die Bedingungen aus."""
    idx, nv = var_index(n)
    rows = []

    def below(s):
        return [] if s == -1 else list(range(s))

    if "C1" in which:  # h(a,0) = 0
        for i in range(n):
            r = [F(0)] * nv
            r[idx[(i, -1)]] = F(1)
            rows.append(r)

    if "C2" in which:  # h(a,b)+h(b,a) = h(a,a)+h(b,b) auf A x A
        for i in range(n):
            for j in range(i + 1, n):
                r = [F(0)] * nv
                r[idx[(i, j)]] += 1
                r[idx[(j, i)]] += 1
                r[idx[(i, i)]] -= 1
                r[idx[(j, j)]] -= 1
                rows.append(r)

    if "C3A" in which:  # H(s,t)+H(t,s)=0 nur fuer s,t in A u {t^*}
        pts = list(range(0, n + 1))
        for s, t in itertools.combinations_with_replacement(pts, 2):
            r = [F(0)] * nv
            for j in below(s):
                r[idx[(j, t)]] += m[j]
            for j in below(t):
                r[idx[(j, s)]] += m[j]
            rows.append(r)

    if "WHATA" in which:  # Antisymmetrie von what nur auf A x A: H(a,b)+H(b,a)=0
        for i in range(n):
            for j in range(i, n):
                r = [F(0)] * nv
                for k in below(i):
                    r[idx[(k, j)]] += m[k]
                for k in below(j):
                    r[idx[(k, i)]] += m[k]
                rows.append(r)

    if "TOP" in which:  # Antisymmetrie von what nur auf A x {t^*} und in (t^*,t^*)
        for i in list(range(n)) + [n]:
            r = [F(0)] * nv
            for k in below(i):
                r[idx[(k, n)]] += m[k]
            for k in below(n):
                r[idx[(k, i)]] += m[k]
            rows.append(r)

    return rows, idx, nv


def nullspace_sample(n, m, which, rng, tries=40):
    """Ein zufaelliges Element des Loesungsraums, moeglichst mit
    nichtverschwindender Diagonale."""
    rows, idx, nv = constraints(n, m, which)
    M = sympy.Matrix([[sympy.Rational(x) for x in r] for r in rows]) if rows else sympy.zeros(1, nv)
    ns = M.nullspace()
    if not ns:
        return None, idx, 0
    best, bestdiag = None, -1
    for _ in range(tries):
        coeffs = [sympy.Rational(rng.randint(-5, 5)) for _ in ns]
        v = sympy.zeros(nv, 1)
        for co, b in zip(coeffs, ns):
            v += co * b
        h = {key: F(int(sympy.Rational(v[k]).p), int(sympy.Rational(v[k]).q)) for key, k in idx.items()}
        d = sum(abs(h[(i, i)]) for i in range(n))
        if d > bestdiag:
            best, bestdiag = h, d
    return best, idx, bestdiag


def diagonal_is_forced(n, m, which):
    """Ist h(a_i,a_i)=0 eine Folgerung des Systems `which`?"""
    rows, idx, nv = constraints(n, m, which)
    M = sympy.Matrix([[sympy.Rational(x) for x in r] for r in rows])
    ns = M.nullspace()
    for i in range(n):
        for b in ns:
            if b[idx[(i, i)]] != 0:
                return False
    return True


# ------------------------------------------------------------------- Proben


def probe_A(rng):
    ok = True
    for n in (1, 2, 3, 4, 5):
        m = random_masses(n, rng)
        ch = Chain(m, random_h(n, rng))
        for t in ch.points():
            for c in CS:
                lhs = ch.K(t, c) - c * ch.G(t, c)
                rhs = ch.what(ch.n, t) - ch.what(-1, t) * ch.V0(c)
                if lhs != rhs:
                    ok = False
    report("(A) Abel/Stieltjes K - cG = what(t*,.) - what(0,.) V_0, ohne Hypothese", ok)


def probe_B(rng):
    ok, seen = True, 0
    for n in (2, 3, 4, 5):
        m = random_masses(n, rng)
        h, idx, diag = nullspace_sample(n, m, {"C2", "WHATA"}, rng)
        if h is None:
            continue
        if diag > 0:
            seen += 1
        ch = Chain(m, h)
        for c in CS:
            if ch.P(c) != ch.V0(c) * ch.Q(c):
                ok = False
    report("(B) P = V_0 Q, nur aus (C2) und Antisymmetrie von what auf A x A", ok,
           "nichttriviale Diagonale in %d von 4 Faellen" % seen)


def probe_C(rng):
    ok, seen = True, 0
    for n in (1, 2, 3, 4, 5):
        m = random_masses(n, rng)
        h, idx, diag = nullspace_sample(n, m, {"C1"}, rng)
        if h is None:
            continue
        if diag > 0:
            seen += 1
        ch = Chain(m, h)
        for c in CS:
            if ch.R(c) != ch.Delta(ch.n) + c * ch.Q(c):
                ok = False
    report("(C) R = Delta(t*) + c Q, nur aus (C1)", ok,
           "nichttriviale Diagonale in %d von 5 Faellen" % seen)


def probe_D(rng):
    """Die Identitaet (5), aus der (7) hervorgeht:  S - R + cP = -Delta(t*) V_0.

    Der Beweis leitet sie aus (A) bei t = t^* her und braucht dafuer allein
    (C1) und die Antisymmetrie von what auf A x {t^*} samt (t^*,t^*).  Unter
    dieser Teilhypothese ist die Diagonale frei, die Probe also nicht
    degeneriert.  (7) selbst -- S = R (1 - V_0) -- ist eine Zeile aus (5),
    (B) und (C) und wird zusaetzlich unter der vollen Minimalhypothese
    geprueft, wo sie wegen Probe (E) beidseits verschwindet."""
    ok, seen = True, 0
    for n in (2, 3, 4, 5):
        m = random_masses(n, rng)
        h, idx, diag = nullspace_sample(n, m, {"C1", "TOP"}, rng)
        if h is None:
            continue
        if diag > 0:
            seen += 1
        ch = Chain(m, h)
        for c in CS:
            if ch.S(c) - ch.R(c) + c * ch.P(c) != -ch.Delta(ch.n) * ch.V0(c):
                ok = False
    report("(D) S - R + cP = -Delta(t*) V_0, nur aus (C1) und what-Antisym. am Deckel", ok,
           "nichttriviale Diagonale in %d von 4 Faellen" % seen)

    ok2 = True
    for n in (2, 3, 4, 5):
        m = random_masses(n, rng)
        h, idx, diag = nullspace_sample(n, m, {"C1", "C2", "C3A"}, rng)
        if h is None:
            continue
        ch = Chain(m, h)
        for c in CS:
            if ch.S(c) != ch.R(c) * (1 - ch.V0(c)):
                ok2 = False
    report("(D') S = R (1 - V_0) unter der vollen Minimalhypothese", ok2,
           "beidseits 0, vgl. Probe (E)")


def probe_E():
    ok, detail = True, []
    rng = random.Random(20260904)
    for n in range(1, 8):
        m = random_masses(n, rng)
        forced = diagonal_is_forced(n, m, {"C1", "C2", "C3A"})
        detail.append("n=%d:%s" % (n, "ja" if forced else "NEIN"))
        ok = ok and forced
    report("(E) Minimalhypothese ohne Lueckenpunkte erzwingt h(a,a)=0", ok, " ".join(detail))

    # Kontrolle: laesst man (C2) weg, ist die Diagonale frei -- die Probe
    # misst also wirklich etwas.
    rng = random.Random(7)
    free = []
    for n in (2, 3, 4):
        m = random_masses(n, rng)
        free.append(not diagonal_is_forced(n, m, {"C1", "C3A"}))
    report("(E') Kontrolle: ohne (C2) ist die Diagonale frei", all(free),
           "n=2,3,4")


def probe_F(rng):
    ok = True
    for n in (1, 2, 3, 4, 5):
        m = random_masses(n, rng)
        ch = Chain(m, random_h(n, rng))
        for s0 in range(0, n + 1):  # Fusspunkt: Atom a_{s0} bzw. t^*
            V = F(1)
            for j in range(s0, n):
                V *= 1 + F(3, 2) * m[j]
            c = F(3, 2)
            for i in range(n):
                if i < s0:
                    pref = F(1)
                    for j in range(i + 1, s0):
                        pref *= 1 + c * m[j]
                    if ch.W(i, c) != V * pref:
                        ok = False
                else:
                    den = F(1)
                    for j in range(s0, i + 1):
                        den *= 1 + c * m[j]
                    if ch.W(i, c) * den != V:
                        ok = False
    report("(F) Fusspunktzerlegung von W^c (Theorem 9) auf beliebiger Kette", ok)


def probe_G(rng):
    import cmath
    ok = True
    for _ in range(200):
        n = rng.randint(1, 6)
        m = [rng.random() * 2 for _ in range(n)]
        c = complex(rng.random() * 5, rng.uniform(-5, 5))  # Re c >= 0
        V0 = 1.0 + 0j
        for mm in m:
            V0 *= 1 + c * mm
        lower = 1.0
        for mm in m:
            lower *= (1 + mm * mm * abs(c) ** 2) ** 0.5
        if abs(V0) < lower - 1e-9:
            ok = False
        for i in range(n):
            W = 1.0 + 0j
            for j in range(i + 1, n):
                W *= 1 + c * m[j]
            if abs(W) > abs(V0) + 1e-9:
                ok = False
    report("(G) |V_0| >= prod(1+m^2|c|^2)^{1/2} und |W^c(a)| <= |V_0| auf Re c >= 0", ok)


def main():
    rng = random.Random(4711)
    print("Theorem 17, zweiundzwanzigster Lauf -- exakte Proben")
    probe_A(rng)
    probe_B(rng)
    probe_C(rng)
    probe_D(rng)
    probe_E()
    probe_F(rng)
    probe_G(rng)
    print()
    if FAIL:
        print("FEHLGESCHLAGEN: " + ", ".join(FAIL))
        return 1
    print("alle Proben bestanden")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
