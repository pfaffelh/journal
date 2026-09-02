#!/usr/bin/env python3
"""Die Viertelgitterfrage der zwei ζ-Ketten (achtzehnter Lauf): mechanische
Verifikation der Beweisalgebra, exakt in Brüchen. Keine LPs, keine Messung —
jede Probe ist eine endliche algebraische Identität, die in einem Beweis des
achtzehnten Laufs wörtlich vorkommt.

System: F auf einem Fenster von Z×Z mit der Kreuzrelation
    (∗)   m^A_j (F(i+1,j) − F(i,j)) = m^B_i (F(i,j+1) − F(i,j)),
Fluss x_{ij} := (F(i+1,j) − F(i,j))/m^B_i.

Proben:
  (a) Flussgleichheit und Vererbung: x_{ij} = (F(i,j+1) − F(i,j))/m^A_j,
      und x erfüllt selbst (∗).  [Lemma 1, Schritt 1]
  (b) endliche Hakenidentität: für
      H(i,j) = Σ_{i0≤i'<i} m^B_{i'} x_{i'j} + Σ_{j≤j'≤j1} m^A_{j'} x_{ij'}
      gilt exakt H(i+1,j) − H(i,j) = m^B_i x_{i,j1+1}.  [Lemma 1, Schritt 2:
      der endliche Kern der Konstanz von D und der Limiten L_i = ℓ_j = 0]
  (c) der Buckel bei konstanten Massen: F(i,j) = g(i+j) erfüllt (∗) für
      m^A ≡ m^B ≡ 1 und ist nicht 0.  [Proposition 2: ohne Summierbarkeit
      ist die Viertelgitteraussage falsch]
  (d) separable Lösungen und Momentenfortpflanzung: β^c_i λ^c_j erfüllt (∗);
      c·λ^c_j = (λ^c_{j+1} − λ^c_j)/m^A_j; und ein Vektor w mit
      Σ_r w_r λ^{c_r}_j = 0 auf einem j-Fenster erfüllt automatisch
      Σ_r w_r c_r^k λ^{c_r}_j = 0 auf dem um k verkürzten Fenster.
      [Theorem 4, Momentenschritt]
  (e) der Defekt des charakteristischen Ansatzes F⁰ = G(B_i + A_j):
      für affines G ist der (∗)-Defekt exakt 0, für G(u) = u² exakt
      m^A_j m^B_i (m^B_i − m^A_j).  [Mechanismus (ii), Defektformel]
  (f) die Energieidentität in Bilanzform: für endlich getragenes x gilt exakt
      Σ m^B_i m^A_j x_{ij}((Px)_{ij} + (Nx)_{ij})
        = ½ Σ_j m^A_j R_j² + ½ Σ_i m^B_i C_i²
          + ½ Σ_{ij} m^B_i m^A_j (m^A_j − m^B_i) x_{ij}².
      Der letzte Summand trägt denselben antisymmetrischen Faktor wie der
      Defekt in (e); auf Lösungen von (Q) ist die linke Seite 0.
      [Sackgasse: die Paarung ist indefinit, siehe PROTOKOLL, achtzehnter Lauf]

rc=0 genau dann, wenn alle Proben exakt aufgehen.
"""

from fractions import Fraction as Fr
import random

random.seed(20260902)

ok_all = True


def report(name, ok, detail=""):
    global ok_all
    ok_all = ok_all and ok
    print(f"  [{'ok' if ok else 'FEHLER'}] {name}" + (f" — {detail}" if detail else ""))


def rand_fr(lo=1, hi=9, den=7):
    return Fr(random.randint(lo, hi), random.randint(1, den))


# ---------------------------------------------------------------- Proben (a), (b)
print("(a) Flussgleichheit und Vererbung von (∗)")

I0, I1 = 0, 14          # i-Fenster der Basiszeile
J0, JH = 0, 10          # Basiszeile j=J0, Höhe JH
mB = {i: rand_fr() for i in range(I0, I1)}
mA = {j: rand_fr() for j in range(J0, J0 + JH)}

F = {}
for i in range(I0, I1 + 1):
    F[(i, J0)] = rand_fr(-9, 9) if random.random() < 0.8 else Fr(0)
# aufwärts propagieren; die Zeile verliert rechts je Schritt einen Punkt
for j in range(J0, J0 + JH):
    for i in range(I0, I1 - (j - J0)):
        F[(i, j + 1)] = F[(i, j)] + (mA[j] / mB[i]) * (F[(i + 1, j)] - F[(i, j)])

x = {}
ok_flux = True
for (i, j) in list(F):
    if (i + 1, j) in F and (i, j + 1) in F:
        xi = (F[(i + 1, j)] - F[(i, j)]) / mB[i]
        xj = (F[(i, j + 1)] - F[(i, j)]) / mA[j]
        ok_flux = ok_flux and (xi == xj)
        x[(i, j)] = xi
report("x aus i-Schritt = x aus j-Schritt, auf allen inneren Punkten", ok_flux,
       f"{len(x)} Punkte")

ok_star_x = True
n_star = 0
for (i, j) in x:
    if (i + 1, j) in x and (i, j + 1) in x:
        ok_star_x = ok_star_x and (
            mA[j] * (x[(i + 1, j)] - x[(i, j)]) == mB[i] * (x[(i, j + 1)] - x[(i, j)]))
        n_star += 1
report("x erfüllt (∗)", ok_star_x, f"{n_star} Relationen")

print("(b) endliche Hakenidentität")
ok_hook = True
n_hook = 0
for j in range(J0, J0 + 3):
    j1 = j + 3
    for i in range(I0, I0 + 4):
        def hook(ii):
            s = sum(mB[i2] * x[(i2, j)] for i2 in range(I0, ii))
            s += sum(mA[j2] * x[(ii, j2)] for j2 in range(j, j1 + 1))
            return s
        need = {(i2, j) for i2 in range(I0, i + 1)}
        need |= {(i, j2) for j2 in range(j, j1 + 2)}
        need |= {(i + 1, j2) for j2 in range(j, j1 + 1)}
        if not need <= set(x):
            continue
        lhs = hook(i + 1) - hook(i)
        rhs = mB[i] * x[(i, j1 + 1)]
        ok_hook = ok_hook and (lhs == rhs)
        n_hook += 1
report("H(i+1,j) − H(i,j) = m^B_i · x(i, j1+1)", ok_hook, f"{n_hook} Instanzen")

# ---------------------------------------------------------------- Probe (c)
print("(c) Buckel bei konstanten Massen (Nicht-Summierbarkeit)")
g = {s: Fr(0) for s in range(-30, 31)}
g[0], g[1], g[2] = Fr(1), Fr(-2), Fr(1)   # kompakter Buckel, beliebig
ok_bump = True
nonzero = False
for i in range(-12, 12):
    for j in range(-12, 12):
        # (∗) mit m^A = m^B = 1: F(i+1,j) − F(i,j) = F(i,j+1) − F(i,j)
        ok_bump = ok_bump and (g[i + 1 + j] == g[i + j + 1])
        nonzero = nonzero or (g[i + j] != 0)
report("F = g(i+j) erfüllt (∗) bei Massen ≡ 1 und ist ≠ 0", ok_bump and nonzero)

# ---------------------------------------------------------------- Probe (d)
print("(d) separable Lösungen und Momentenfortpflanzung")

JW = 12
mA2 = {j: rand_fr() for j in range(JW)}
mB2 = {i: rand_fr() for i in range(10)}


def lam(c, j):
    p = Fr(1)
    for j2 in range(j):
        p *= (1 + c * mA2[j2])
    return p


def bet(c, i):
    p = Fr(1)
    for i2 in range(i):
        p *= (1 + c * mB2[i2])
    return p


cs = [Fr(1, 2), Fr(2, 3), Fr(3), Fr(-1, 5), Fr(5, 4), Fr(-2, 7)]
r = len(cs)

ok_sep = True
for c in cs[:3]:
    for i in range(6):
        for j in range(6):
            lhs = mA2[j] * (bet(c, i + 1) - bet(c, i)) * lam(c, j)
            rhs = mB2[i] * bet(c, i) * (lam(c, j + 1) - lam(c, j))
            ok_sep = ok_sep and (lhs == rhs)
report("β^c λ^c erfüllt (∗)", ok_sep)

ok_rec = all((lam(c, j + 1) - lam(c, j)) / mA2[j] == c * lam(c, j)
             for c in cs for j in range(JW - 1))
report("c·λ^c_j = (λ^c_{j+1} − λ^c_j)/m^A_j", ok_rec)

# w ≠ 0 mit Σ w_r λ^{c_r}_j = 0 für j = 0..r−2 (r−1 Bedingungen, r Unbekannte):
# exakter Kern per Gauß-Elimination in Brüchen.
rows = [[lam(c, j) for c in cs] for j in range(r - 1)]
M = [row[:] for row in rows]
piv_cols, prow = [], 0
for col in range(r):
    pr = next((k for k in range(prow, len(M)) if M[k][col] != 0), None)
    if pr is None:
        continue
    M[prow], M[pr] = M[pr], M[prow]
    M[prow] = [v / M[prow][col] for v in M[prow]]
    for k in range(len(M)):
        if k != prow and M[k][col] != 0:
            M[k] = [a - M[k][col] * b for a, b in zip(M[k], M[prow])]
    piv_cols.append(col)
    prow += 1
free = [col for col in range(r) if col not in piv_cols]
w = [Fr(0)] * r
w[free[0]] = Fr(1)
for k, col in enumerate(piv_cols):
    w[col] = -M[k][free[0]]
ok_ker = all(sum(w[a] * rows[j][a] for a in range(r)) == 0 for j in range(r - 1))
report("Kernvektor w gefunden (w ⊥ λ_j, j = 0..r−2), w ≠ 0", ok_ker and any(w))

ok_mom = True
for k in range(1, r - 1):
    for j in range(0, r - 1 - k):
        s = sum(w[a] * cs[a] ** k * lam(cs[a], j) for a in range(r))
        ok_mom = ok_mom and (s == 0)
report("Momentenfortpflanzung: w ⊥ c^k λ_j auf dem verkürzten Fenster", ok_mom,
       f"k bis {r - 2}")

# ---------------------------------------------------------------- Probe (e)
print("(e) Defekt des charakteristischen Ansatzes F⁰ = G(B_i + A_j)")
B = {0: Fr(0)}
for i in range(8):
    B[i + 1] = B[i] + mB2[i]
A = {0: Fr(0)}
for j in range(8):
    A[j + 1] = A[j] + mA2[j]


def defect(G):
    bad = []
    for i in range(7):
        for j in range(7):
            u = B[i] + A[j]
            e = mA2[j] * (G(B[i + 1] + A[j]) - G(u)) - mB2[i] * (G(B[i] + A[j + 1]) - G(u))
            bad.append((i, j, e))
    return bad


ok_aff = all(e == 0 for _, _, e in defect(lambda u: Fr(3, 2) * u - Fr(5)))
report("affines G: Defekt exakt 0", ok_aff)

ok_quad = all(e == mA2[j] * mB2[i] * (mB2[i] - mA2[j])
              for i, j, e in defect(lambda u: u * u))
report("G(u) = u²: Defekt exakt m^A_j m^B_i (m^B_i − m^A_j)", ok_quad)

print("(f) Energieidentität (Bilanzform von Mechanismus (ii))")
# Reine endliche Algebra, kein (Q): mit
#   (Px)_{ij} = Σ_{i'<i} m^B_{i'} x_{i'j},  (Nx)_{ij} = Σ_{j'≥j} m^A_{j'} x_{ij'},
#   R_j = Σ_i m^B_i x_{ij},  C_i = Σ_j m^A_j x_{ij}
# ist die Identität der Probenbeschreibung exakt; auf Lösungen von (Q) ist die
# linke Seite 0, und der letzte Summand ist indefinit.
NI, NJ = 7, 6
mB3 = {i: rand_fr() for i in range(NI)}
mA3 = {j: rand_fr() for j in range(NJ)}
X = {(i, j): rand_fr(-9, 9) for i in range(NI) for j in range(NJ)}
lhs = Fr(0)
for i in range(NI):
    for j in range(NJ):
        Px = sum(mB3[i2] * X[(i2, j)] for i2 in range(i))
        Nx = sum(mA3[j2] * X[(i, j2)] for j2 in range(j, NJ))
        lhs += mB3[i] * mA3[j] * X[(i, j)] * (Px + Nx)
R = {j: sum(mB3[i] * X[(i, j)] for i in range(NI)) for j in range(NJ)}
C = {i: sum(mA3[j] * X[(i, j)] for j in range(NJ)) for i in range(NI)}
rhs = (sum(mA3[j] * R[j] ** 2 for j in range(NJ))
       + sum(mB3[i] * C[i] ** 2 for i in range(NI))
       + sum(mB3[i] * mA3[j] * (mA3[j] - mB3[i]) * X[(i, j)] ** 2
             for i in range(NI) for j in range(NJ))) / 2
report("Σ m^B m^A x (Px+Nx) = ½Σ m^A R² + ½Σ m^B C² + ½Σ m^B m^A (m^A−m^B) x²",
       lhs == rhs)

print()
print("alle Proben exakt bestanden" if ok_all else "MINDESTENS EINE PROBE GESCHEITERT")
raise SystemExit(0 if ok_all else 1)
