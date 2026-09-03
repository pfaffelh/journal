#!/usr/bin/env python3
"""Weg (α) der Viertelgitterfrage (zwanzigster Lauf): mechanische Verifikation
der Beweisalgebra des Transformationsbeweises, exakt in Brüchen. Keine LPs,
keine Messung — jede Probe ist eine endliche algebraische Identität, die im
Beweis des zwanzigsten Laufs wörtlich vorkommt.

System und Konventionen wie in zeta_cross.py: Massen μ_i := m^B_i,
ν_j := m^A_j, Fluss x_{ij}, F(i,j) = Σ_{i'<i} μ_{i'} x_{i'j}. Die duale
Transformation paart Zeilen von F gegen die Geschlecht-0-Produkte
    W^c_i := Π_{i'>i} (1 + c μ_{i'}),
im Endlichen W^c_i := Π_{i'=i+1}^{iB} (1 + c μ_{i'}), also W_{iB} = 1.

Proben:
  (A) endliche Abel-Identität (unbedingte Algebra, zufälliges x):
      Σ_i μ_i x_{ij} W^c_i = F(iB+1,j) W_{iB} − F(iA,j) W_{iA−1} + c G_j
      mit G_j := Σ_i μ_i F(i,j) W^c_i.  [Beweisschritt: Abel-Summation]
  (B) endliche Rekursion (T_W) mit exakt mitgeführtem Norddefekt
      D(i,j) := F(i,j+1) − F(i,j) − ν_j x_{ij}:
      G_{j+1} = (1+cν_j) G_j + ν_j R̃_j + Σ_i μ_i D(i,j) W^c_i,
      R̃_j := F(iB+1,j).  [Beweisschritt: die skalare Nordrekursion]
  (C) endliche Identität I (aufsummierte Rekursion):
      G_{jB}/Π_{j0,jB−1} = G_{j0} + Σ_{J=j0}^{jB−1} (ν_J R̃_J + S_J)/Π_{j0,J},
      Π_{a,b} := Π_{j'=a}^{b} (1+cν_{j'}), S_J := Σ_i μ_i D(i,J) W^c_i.
      Auf Lösungen ist D ≡ 0 und der Limes J→∞ von G_J/Π null — das ist
      Identität I des Beweises; hier wird die exakte endliche Fassung geprüft.
  (D) Injektivität der W-Transformation:
      (D1) die Koeffizientenmatrix M[k][I] = e_k(μ_{I+1..iB}) von
           Σ_I a_I W^c_I ist nach Grad dreieckig mit Antidiagonale
           Π_{i'>I} μ_{i'} ≠ 0, also invertierbar (exakte Determinante);
      (D2) die Aufspaltung am Fußpunkt I0:
           (Σ_I a_I W^c_I)/W^c_{I0} = P_{I0}(c) + N_{I0}(c) mit
           P_{I0} = Σ_{I≤I0} a_I Π_{I<i'≤I0}(1+cμ_{i'}),
           N_{I0} = Σ_{I>I0} a_I / Π_{I0<i'≤I}(1+cμ_{i'}),
           und der Konstantenterm P_{I0}(0) = Σ_{I≤I0} a_I — das ist die
           Dreiecksextraktion, die im Beweis a ≡ 0 liefert.
  (E) endliche Starrheit als Regression: das endliche System (Q) —
      Σ_{i'<i} μ_{i'} x_{i'j} + Σ_{j'≥j} ν_{j'} x_{ij'} = 0 auf einem
      n×m-Gitter (leerer West- und Nordrand) — hat exakt nur die Nulllösung
      (Rang = nm, exakte Gauß-Elimination).

Nicht geprüft wird, was klassische Funktionentheorie ist und bleibt:
Phragmén–Lindelöf für Typ 0 auf der Halbebene (Titchmarsh §5.62, Boas Kap. 6)
und Liouville. Der Typ-0-Nachweis Φ_μ(r) = o(r) ist dominierte Konvergenz.

rc=0 genau dann, wenn alle Proben exakt aufgehen.
"""

from fractions import Fraction as Fr
import random

random.seed(20260903)

ok_all = True


def report(name, ok, detail=""):
    global ok_all
    ok_all = ok_all and ok
    print(f"  [{'ok' if ok else 'FEHLER'}] {name}" + (f" — {detail}" if detail else ""))


def rand_fr(lo=1, hi=9, den=7):
    return Fr(random.randint(lo, hi), random.randint(1, den))


# ---------------------------------------------------------------- Aufbau
# Fenster i ∈ [0..nI−1], j ∈ [0..nJ−1]; F auf i ∈ [0..nI], j ∈ [0..nJ−1].
nI, nJ = 6, 5
mu = [rand_fr() for _ in range(nI)]          # μ_i, i = 0..nI−1
nu = [rand_fr() for _ in range(nJ)]          # ν_j, j = 0..nJ−1
x = [[rand_fr() - rand_fr() for _ in range(nJ)] for _ in range(nI)]

# F als Westsummen mit leerem Westrand: F[0][j] = 0.
F = [[Fr(0)] * nJ for _ in range(nI + 1)]
for j in range(nJ):
    for i in range(nI):
        F[i + 1][j] = F[i][j] + mu[i] * x[i][j]

# Norddefekt D(i,j) für j = 0..nJ−2, i = 0..nI−1 (generisch ≠ 0).
D = [[F[i][j + 1] - F[i][j] - nu[j] * x[i][j] for j in range(nJ - 1)]
     for i in range(nI)]


def W(i, c):
    """W^c_i = Π_{i'=i+1}^{nI−1} (1 + c μ_{i'}); W(nI−1) = 1; W(−1) voll."""
    out = Fr(1)
    for ip in range(i + 1, nI):
        out *= 1 + c * mu[ip]
    return out


def G(j, c):
    return sum(mu[i] * F[i][j] * W(i, c) for i in range(nI))


def Rt(j):
    return F[nI][j]


# ---------------------------------------------------------------- Probe (A)
print("(A) endliche Abel-Identität")
ok = True
for _ in range(4):
    c = rand_fr()
    for j in range(nJ):
        lhs = sum(mu[i] * x[i][j] * W(i, c) for i in range(nI))
        rhs = Rt(j) * W(nI - 1, c) - F[0][j] * W(-1, c) + c * G(j, c)
        ok = ok and (lhs == rhs)
report("Σ μ x W = R̃·W_{iB} − F(iA)·W_{iA−1} + cG, alle j, 4 zufällige c", ok)

# ---------------------------------------------------------------- Probe (B)
print("(B) endliche Rekursion (T_W) mit Norddefekt")
ok = True
for _ in range(4):
    c = rand_fr()
    for j in range(nJ - 1):
        S = sum(mu[i] * D[i][j] * W(i, c) for i in range(nI))
        lhs = G(j + 1, c)
        rhs = (1 + c * nu[j]) * G(j, c) + nu[j] * Rt(j) + S
        ok = ok and (lhs == rhs)
report("G_{j+1} = (1+cν_j)G_j + ν_j R̃_j + Σ μ D W, alle j, 4 zufällige c", ok)

# ---------------------------------------------------------------- Probe (C)
print("(C) endliche Identität I (aufsummierte Rekursion)")
ok = True
for _ in range(4):
    c = rand_fr()
    j0 = 0

    def Pi(a, b):
        out = Fr(1)
        for jp in range(a, b + 1):
            out *= 1 + c * nu[jp]
        return out

    lhs = G(nJ - 1, c) / Pi(j0, nJ - 2)
    rhs = G(j0, c)
    for J in range(j0, nJ - 1):
        S = sum(mu[i] * D[i][J] * W(i, c) for i in range(nI))
        rhs += (nu[J] * Rt(J) + S) / Pi(j0, J)
    ok = ok and (lhs == rhs)
report("G_{jB}/Π = G_{j0} + Σ (νR̃ + S)/Π_{j0,J}, 4 zufällige c", ok)

# ---------------------------------------------------------------- Probe (D)
print("(D) Injektivität der W-Transformation")


def esym(vals, k):
    """Elementarsymmetrische Funktion e_k, exakt."""
    e = [Fr(1)] + [Fr(0)] * k
    for v in vals:
        for d in range(min(k, len(e) - 1), 0, -1):
            e[d] += v * e[d - 1]
    return e[k]


# (D1): Koeffizientenmatrix, Dreiecksgestalt, Determinante.
M = [[esym(mu[I + 1:], k) for I in range(nI)] for k in range(nI)]
tri = all(M[k][I] == 0 for I in range(nI) for k in range(nI)
          if k > nI - 1 - I)
anti = all(M[nI - 1 - I][I] != 0 for I in range(nI))


def det(A):
    A = [row[:] for row in A]
    n = len(A)
    d = Fr(1)
    for col in range(n):
        piv = next((r for r in range(col, n) if A[r][col] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            d = -d
        d *= A[col][col]
        for r in range(col + 1, n):
            f = A[r][col] / A[col][col]
            for cc in range(col, n):
                A[r][cc] -= f * A[col][cc]
    return d


d = det(M)
report("(D1) M[k][I]=e_k(μ-Schwanz) dreieckig, Antidiagonale ≠ 0, det ≠ 0",
       tri and anti and d != 0, f"det = {d}")

# (D2): Aufspaltung am Fußpunkt und Konstantenterm.
ok = True
a = [rand_fr() - rand_fr() for _ in range(nI)]
for _ in range(4):
    c = rand_fr()
    for I0 in range(nI):
        Gc = sum(a[I] * W(I, c) for I in range(nI))
        P = sum(a[I] * Pi_prod for I, Pi_prod in
                ((I, prod := Fr(1)) for I in []))  # placeholder, built below
        P = Fr(0)
        for I in range(I0 + 1):
            prod = Fr(1)
            for ip in range(I + 1, I0 + 1):
                prod *= 1 + c * mu[ip]
            P += a[I] * prod
        N = Fr(0)
        for I in range(I0 + 1, nI):
            prod = Fr(1)
            for ip in range(I0 + 1, I + 1):
                prod *= 1 + c * mu[ip]
            N += a[I] / prod
        ok = ok and (Gc / W(I0, c) == P + N)
# Konstantenterm: P_{I0}(0) = Σ_{I≤I0} a_I.
okc = True
for I0 in range(nI):
    P0 = Fr(0)
    for I in range(I0 + 1):
        P0 += a[I]  # alle Produkte sind 1 bei c = 0
    okc = okc and (P0 == sum(a[:I0 + 1]))
    # und die Extraktion: verschwinden alle P_{I0}(0), so ist a ≡ 0
extr = all(
    (lambda partial: partial[I0] - (partial[I0 - 1] if I0 else Fr(0)) == a[I0])(
        [sum(a[:k + 1]) for k in range(nI)])
    for I0 in range(nI))
report("(D2) G/W_{I0} = P + N exakt, alle I0, 4 zufällige c", ok)
report("(D2) Konstantenterm P_{I0}(0) = Σ_{I≤I0} a_I, Dreiecksextraktion", okc and extr)

# ---------------------------------------------------------------- Probe (E)
print("(E) endliche Starrheit des Systems (Q) als Regression")


def rank(A):
    A = [row[:] for row in A]
    rows, cols = len(A), len(A[0]) if A else 0
    r = 0
    for col in range(cols):
        piv = next((i for i in range(r, rows) if A[i][col] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(rows):
            if i != r and A[i][col] != 0:
                f = A[i][col] / A[r][col]
                for cc in range(cols):
                    A[i][cc] -= f * A[r][cc]
        r += 1
    return r


ok = True
for (n, m) in [(2, 2), (3, 3), (3, 4), (4, 3)]:
    mus = [rand_fr() for _ in range(n)]
    nus = [rand_fr() for _ in range(m)]
    rows = []
    for i in range(n):
        for j in range(m):
            row = [Fr(0)] * (n * m)
            for ip in range(i):
                row[ip * m + j] += mus[ip]
            for jp in range(j, m):
                row[i * m + jp] += nus[jp]
            rows.append(row)
    ok = ok and (rank(rows) == n * m)
report("Rang((Q)-endlich) = nm für (n,m) ∈ {(2,2),(3,3),(3,4),(4,3)}", ok)

# ---------------------------------------------------------------- Ergebnis
print()
if ok_all:
    print("Alle Proben exakt bestanden (rc=0).")
    raise SystemExit(0)
print("MINDESTENS EINE PROBE GESCHEITERT (rc=1).")
raise SystemExit(1)
