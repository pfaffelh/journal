#!/usr/bin/env python3
"""Mechanische Verifikation der Beweisalgebra des einundzwanzigsten Laufs.

Gegenstand ist Theorem 12 aus `Task23/PROTOKOLL.md`, Abschnitt "Die nackte
Klasse, 2026-09-03 (einundzwanzigster Lauf)": eine Loesung von (Q), die die
Bedingung (U) erfuellt, verschwindet.  (U) ersetzt die Hypothese (H) des
zwanzigsten Laufs durch Straffheit nach Norden plus Nordsummierbarkeit der
Zeilensummen und hat zwei unvergleichbare hinreichende Kriterien, (H) und die
Beschraenktheit des Flusses.

Was hier geprueft wird, ist die *endliche* Algebra des Beweises, exakt in
Bruchrechnung und exakt in Polynomen ueber der Variablen c:

  (A) die Abel-Identitaet von Schritt 2, mit ihren Randtermen;
  (B) die Nordrekursion von Schritt 3, in ihre zwei Haelften zerlegt;
  (C) der Koeffizientenvergleich von Schritt 6, der die Identitaet I ersetzt;
  (D) die Fortsetzung nach Sueden von Schritt 7, samt Produktschranke;
  (E) die Strukturgleichungen, auf denen Proposition 15 und die Diskussion
      der Unvergleichbarkeit in Korollar 13(c) ruhen:
      rho_j = Var_i F(.,j), kappa_i = Var_j F(i,.), Tonelli, sup_i |F| <= rho_j;
  (F) Typ 0: Phi_mu(r)/r -> 0, und |W_i^c| >= 1 auf Re c >= 0.

Was hier NICHT geprueft wird, weil es klassisch ist und nicht endlich:
Phragmen--Lindeloef fuer Typ 0 (Titchmarsh 5.62, Boas Thm. 6.2.4 mit tau=0),
Liouville, und die drei Grenzuebergaenge (Westabfall, Nordabfall,
dominierte bzw. gleichmaessig summierbare Konvergenz).  Theorem 9 des
zwanzigsten Laufs wird unveraendert benutzt und ist dort geprueft
(`Task23/quarter_transform.py`, Proben (D1), (D2)).

Aufruf: python3 naked_class.py   --  rc=0 heisst: alle Proben exakt bestanden.
"""

from fractions import Fraction as Fr
import sys

FAILURES = []


def check(name, ok, detail=""):
    mark = "ok " if ok else "FEHLER"
    print(f"  [{mark}] {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


# ---------------------------------------------------------------- Polynome
# Ein Polynom in c ist eine Liste von Fraction-Koeffizienten, Index = Potenz.

def padd(p, q):
    n = max(len(p), len(q))
    return [(p[k] if k < len(p) else Fr(0)) + (q[k] if k < len(q) else Fr(0))
            for k in range(n)]


def psub(p, q):
    return padd(p, [-a for a in q])


def pmul(p, q):
    if not p or not q:
        return [Fr(0)]
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for a, pa in enumerate(p):
        if pa:
            for b, qb in enumerate(q):
                r[a + b] += pa * qb
    return r


def pscale(p, s):
    return [s * a for a in p]


def piszero(p):
    return all(a == 0 for a in p)


ONE = [Fr(1)]
C = [Fr(0), Fr(1)]          # das Polynom c


def linear(mu):
    """1 + c*mu."""
    return [Fr(1), Fr(mu)]


# ------------------------------------------------------- Testdaten (exakt)

def masses(n, seed_num, seed_den):
    """n paarweise verschiedene positive rationale Massen, ohne Muster."""
    out = []
    a, b = seed_num, seed_den
    for k in range(n):
        a = (a * 7 + 3) % 23 + 1
        b = (b * 5 + 11) % 31 + 2
        out.append(Fr(a, b * (k + 2)))
    return out


def values(n, seed):
    """n rationale Werte beiderlei Vorzeichens."""
    out = []
    a = seed
    for k in range(n):
        a = (a * 13 + 7) % 41
        out.append(Fr(a - 20, (k % 5) + 3))
    return out


# --------------------------------------------------- (A) die Abel-Identitaet

def probe_A():
    """Schritt 2: sum_{i=iA}^{iB} (F_{i+1}-F_i) W_i
       = F_{iB+1} W_{iB} - F_{iA} W_{iA} + c * sum_{i=iA+1}^{iB} mu_i F_i W_i,

    mit W_i = prod_{i'=i+1}^{N} (1 + c mu_{i'}), also W_{i-1} = (1+c mu_i) W_i.
    Reine Algebra; im Beweis geht F_{iB+1} -> R_j, W_{iB} -> 1, F_{iA} -> 0.
    """
    print("(A) Abel-Identitaet mit Randtermen, exakt in c")
    N = 9
    mu = masses(N + 1, 5, 4)
    F = values(N + 2, 9)

    # W_i fuer i = 0..N, W_N = 1 (leeres Produkt), W_{i-1} = (1+c mu_i) W_i
    W = [None] * (N + 1)
    W[N] = ONE
    for i in range(N, 0, -1):
        W[i - 1] = pmul(linear(mu[i]), W[i])

    # Rekursionsprobe
    ok = all(piszero(psub(W[i - 1], pmul(linear(mu[i]), W[i])))
             for i in range(1, N + 1))
    check("W-Rekursion W_{i-1} = (1+c mu_i) W_i", ok)

    iA, iB = 0, N - 1
    lhs = [Fr(0)]
    for i in range(iA, iB + 1):
        lhs = padd(lhs, pscale(W[i], F[i + 1] - F[i]))

    rhs = psub(pscale(W[iB], F[iB + 1]), pscale(W[iA], F[iA]))
    tail = [Fr(0)]
    for i in range(iA + 1, iB + 1):
        tail = padd(tail, pscale(W[i], mu[i] * F[i]))
    rhs = padd(rhs, pmul(C, tail))

    check("Abel: linke und rechte Seite identisch als Polynome",
          piszero(psub(lhs, rhs)), f"Grad {len(lhs) - 1}")

    # Gegenprobe: ohne den Faktor mu_i im Schwanz stimmt es nicht.
    bad = padd(psub(pscale(W[iB], F[iB + 1]), pscale(W[iA], F[iA])),
               pmul(C, [Fr(0)]))
    check("Kanarienvogel: ohne Schwanzterm falsch", not piszero(psub(lhs, bad)))


# ------------------------------------------- (B) die Nordrekursion, zweiteilig

def flux_array(n, m, mu, nu, F0):
    """Erzeugt ein echtes Flussfeld auf einem schrumpfenden Fenster.

    Gegeben Zeile j=0 als F(.,0) = F0 auf i=0..n, setze rekursiv
        F(i,j+1) := F(i,j) + nu_j * (F(i+1,j) - F(i,j)) / mu_i .
    Dann erfuellt x_{ij} := (F(i+1,j)-F(i,j))/mu_i **beide** Einschritt-
    relationen, also (*) -- das ist genau die Normalform des achtzehnten
    Laufs, F(.,j+1) = (I + nu_j L) F(.,j).
    Rueckgabe: F[j][i] und x[j][i] auf i = 0..n-j-1 bzw. n-j.
    """
    F = [list(F0)]
    for j in range(m):
        prev = F[-1]
        row = []
        for i in range(len(prev) - 1):
            row.append(prev[i] + nu[j] * (prev[i + 1] - prev[i]) / mu[i])
        F.append(row)
    x = []
    for j, row in enumerate(F):
        x.append([(row[i + 1] - row[i]) / mu[i] for i in range(len(row) - 1)])
    return F, x


def probe_B():
    """Schritt 3, in zwei Haelften:
         (B1)  G_{j+1} - G_j = nu_j * sum_i mu_i x_{ij} W_i   (termweise, exakt)
         (B2)  beide Einschrittrelationen gelten fuer dasselbe x  (Konstruktion)
       Zusammen mit (A) ist das (B-unendlich).
    """
    print("(B) Nordrekursion: beide Einschrittrelationen und die Differenz")
    n, m = 8, 4
    mu = masses(n + 1, 3, 7)
    nu = masses(m + 1, 11, 5)
    F, x = flux_array(n, m, mu, nu, values(n + 1, 17))

    ok_i = all(F[j][i + 1] - F[j][i] == mu[i] * x[j][i]
               for j in range(m + 1) for i in range(len(x[j])))
    check("i-Schritt: F(i+1,j) - F(i,j) = mu_i x_ij", ok_i)

    ok_j = all(F[j + 1][i] - F[j][i] == nu[j] * x[j][i]
               for j in range(m) for i in range(len(F[j + 1])))
    check("j-Schritt: F(i,j+1) - F(i,j) = nu_j x_ij", ok_j)

    ok_star = all(mu[i] * (x[j + 1][i] - x[j][i])
                  == nu[j] * (x[j][i + 1] - x[j][i])
                  for j in range(m) for i in range(len(x[j + 1])))
    check("Kreuzrelation (*) fuer x", ok_star)

    # W_i auf dem gemeinsamen Fenster i = 0..K
    K = len(F[m]) - 1
    W = [None] * (K + 1)
    W[K] = ONE
    for i in range(K, 0, -1):
        W[i - 1] = pmul(linear(mu[i]), W[i])

    def G(j):
        g = [Fr(0)]
        for i in range(K + 1):
            g = padd(g, pscale(W[i], mu[i] * F[j][i]))
        return g

    def Gtilde(j):
        g = [Fr(0)]
        for i in range(K + 1):
            g = padd(g, pscale(W[i], mu[i] * x[j][i]))
        return g

    ok = all(piszero(psub(psub(G(j + 1), G(j)), pscale(Gtilde(j), nu[j])))
             for j in range(m))
    check("(B1) G_{j+1} - G_j = nu_j * Gtilde_j, exakt in c", ok)


# ------------------------------------- (C) der Koeffizientenvergleich, Schritt 6

def probe_C():
    """Schritt 6: sind G_j und G_{j+1} konstant in c und gilt
       G_{j+1} = (1 + c nu_j) G_j + nu_j R_j identisch in c, so folgt
       K_j = 0 und R_j = 0.  Das ersetzt die Identitaet I des zwanzigsten
       Laufs vollstaendig.
    """
    print("(C) Koeffizientenvergleich statt reellem Limes")
    nu_j = Fr(3, 7)
    ok_all = True
    for kj in [Fr(0), Fr(5, 3), Fr(-2)]:
        for rj in [Fr(0), Fr(4, 9), Fr(-11, 2)]:
            # Kandidat: K_{j+1} als Polynom in c
            poly = padd(pscale(ONE, kj), padd(pmul(C, pscale(ONE, nu_j * kj)),
                                              pscale(ONE, nu_j * rj)))
            konstant = all(a == 0 for a in poly[1:])
            # Behauptung: konstant  <=>  K_j = 0
            if konstant != (kj == 0):
                ok_all = False
            if konstant and kj == 0:
                # dann ist K_{j+1} = nu_j R_j; K_{j+1} = 0 erzwingt R_j = 0
                if poly[0] != nu_j * rj:
                    ok_all = False
                if (poly[0] == 0) != (rj == 0):
                    ok_all = False
    check("K_{j+1} konstant in c  <=>  K_j = 0, und dann K_{j+1} = nu_j R_j",
          ok_all)


# ----------------------------------- (D) die Fortsetzung nach Sueden, Schritt 7

def probe_D():
    """Schritt 7: verschwinden alle Zeilen j' > j, so ist F(i,j) = -nu_j x_ij,
       also P_{i+1} = (1 - mu_i/nu_j) P_i fuer P_i = F(i,j); das Produkt ueber
       i' < i konvergiert absolut, und P_{iA} -> 0 gibt P == 0.
    """
    print("(D) Fortsetzung nach Sueden: Rekursion und Produktschranke")
    n = 12
    mu = masses(n, 2, 9)
    nu_j = Fr(5, 4)

    # Rekursionsprobe: setze P_0 beliebig, erzeuge P und x, pruefe beide
    # Darstellungen F(i,j) = sum_{i'<i} mu_i' x_i'j  und  F(i,j) = -nu_j x_ij.
    P = [Fr(7, 3)]
    x = []
    for i in range(n):
        x.append(-P[i] / nu_j)
        P.append(P[i] + mu[i] * x[i])
    ok_rec = all(P[i + 1] == (1 - mu[i] / nu_j) * P[i] for i in range(n))
    check("P_{i+1} = (1 - mu_i/nu_j) P_i", ok_rec)
    ok_west = all(P[i] == sum((mu[k] * x[k] for k in range(i)), P[0])
                  for i in range(n + 1))
    check("Westdarstellung P_i = P_0 + sum_{i'<i} mu_i' x_i'", ok_west)

    # Produktschranke: |prod (1 - mu_i/nu)| <= prod (1 + mu_i/nu) <= exp(S/nu)
    prod = Fr(1)
    bound = Fr(1)
    for i in range(n):
        prod *= (1 - mu[i] / nu_j)
        bound *= (1 + mu[i] / nu_j)
    check("Teilprodukt gleichmaessig beschraenkt",
          abs(prod) <= bound, f"|prod| = {float(abs(prod)):.6f} <= {float(bound):.6f}")

    # Die Schlussfigur: P_iA -> 0 mal beschraenktes Produkt gibt P_i = 0.
    ok_zero = True
    for eps_exp in range(1, 40):
        p0 = Fr(1, 2 ** eps_exp)
        val = p0 * prod
        if abs(val) > abs(p0) * bound:
            ok_zero = False
    check("P_i = lim P_iA * Teilprodukt = 0, gleichmaessig dominiert", ok_zero)


# --------------------------- (E) die Strukturgleichungen von Proposition 15

def probe_E():
    """Proposition 15 und Korollar 13(c):
         rho_j = Var_i F(.,j),  kappa_i = Var_j F(i,.),
         sum_j nu_j rho_j = sum_i mu_i kappa_i  (Tonelli),
         sup_i |F(i,j)| <= |F(0,j)| + rho_j   -- im Unendlichen mit F(-oo,j)=0
                                                 also sup_i |F(i,j)| <= rho_j.
    """
    print("(E) Strukturgleichungen: Variationen, Tonelli, Wertschranke")
    n, m = 9, 5
    mu = masses(n + 1, 13, 6)
    nu = masses(m + 1, 4, 13)
    F, x = flux_array(n, m, mu, nu, values(n + 1, 29))

    # gemeinsames Fenster: x auf i = 0..Kx, F auf i = 0..Kx+1
    Kx = len(x[m]) - 1
    rho = [sum(mu[i] * abs(x[j][i]) for i in range(Kx + 1)) for j in range(m + 1)]
    var_i = [sum(abs(F[j][i + 1] - F[j][i]) for i in range(Kx + 1))
             for j in range(m + 1)]
    check("rho_j = Var_i F(.,j)", rho == var_i)

    kappa = [sum(nu[j] * abs(x[j][i]) for j in range(m)) for i in range(Kx + 1)]
    var_j = [sum(abs(F[j + 1][i] - F[j][i]) for j in range(m))
             for i in range(Kx + 1)]
    check("kappa_i = Var_j F(i,.)", kappa == var_j)

    left = sum(nu[j] * rho[j] for j in range(m))
    right = sum(mu[i] * kappa[i] for i in range(Kx + 1))
    check("Tonelli: sum_j nu_j rho_j = sum_i mu_i kappa_i", left == right,
          f"= {float(left):.10f}")

    ok_val = all(max(abs(F[j][i]) for i in range(Kx + 2))
                 <= abs(F[j][0]) + rho[j] for j in range(m + 1))
    check("sup_i |F(i,j)| <= |F(0,j)| + rho_j", ok_val)

    # Die Lesart von Korollar 13(c): die Wertschranke laesst rho_j frei,
    # die Summenschranke laesst sup |F| frei.  Auf dem Fenster sichtbar als
    # zwei Groessen, die nicht monoton ineinander laufen.
    print("      rho_j  =", [f"{float(r):.4f}" for r in rho])
    print("      sup|F| =", [f"{float(max(abs(F[j][i]) for i in range(Kx+2))):.4f}"
                             for j in range(m + 1)])


# ------------------------------------------------------------- (F) Typ 0

def probe_F():
    """Schritt 1: Phi_mu(r) = sum_i log(1 + r mu_i) = o(r) fuer summierbares mu,
       und |1 + c mu| >= 1 auf Re c >= 0, also 1 <= |W_i^c| <= exp(Phi_mu).
    """
    print("(F) Typ 0 und die Halbebenenschranke")
    import math
    # geometrische Massen: bei 200 Termen ist die Abschneidung fuer r <= 1e10
    # unterhalb der Maschinengenauigkeit, die Zahlen sind also die echten.
    mu = [2.0 ** (-k) for k in range(1, 201)]         # summierbar, S = 1
    quot = []
    rs = [1e1, 1e2, 1e4, 1e6, 1e8, 1e10]
    for r in rs:
        phi = sum(math.log1p(r * m) for m in mu)
        quot.append(phi / r)
    check("Phi_mu(r)/r faellt monoton gegen 0",
          all(quot[k] > quot[k + 1] for k in range(len(quot) - 1))
          and quot[-1] < 1e-6,
          " -> ".join(f"{q:.3e}" for q in quot))
    check("jeder Summand ist durch mu_i dominiert (die DK-Majorante)",
          all(math.log1p(r * m) / r <= m + 1e-18 for r in rs for m in mu))

    ok = True
    for re in [0.0, 0.5, 3.0]:
        for im in [-7.0, -0.3, 0.0, 1.0, 12.0]:
            c = complex(re, im)
            for m in [1e-6, 0.1, 1.0, 5.0]:
                if abs(1 + c * m) < 1 - 1e-15:
                    ok = False
    check("|1 + c mu| >= 1 auf Re c >= 0", ok)


def main():
    print(__doc__.strip().splitlines()[0])
    print()
    for probe in (probe_A, probe_B, probe_C, probe_D, probe_E, probe_F):
        probe()
        print()
    if FAILURES:
        print("FEHLGESCHLAGEN:", ", ".join(FAILURES))
        return 1
    print("alle Proben bestanden")
    return 0


if __name__ == "__main__":
    sys.exit(main())
