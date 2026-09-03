#!/usr/bin/env python3
"""Der Weg (β) ist zu (neunzehnter Lauf): mechanische Verifikation von
Theorem 6 und Korollar 7/8 des PROTOKOLLs.

Behauptung (Theorem 6): für jedes reelle signierte Maß σ mit
∫ e^{Φ_μ(|c|)+Φ_ν(|c|)} d|σ| < ∞ sind äquivalent: (i) alle Momente von σ
verschwinden; (ii) σ annihiliert jede ganze Funktion, deren Koeffizienten-
Majorante Σ|E_k|r^k durch C·e^{Φ_μ(r)+Φ_ν(r)} beschränkt ist; (iii) σ
annihiliert alle λ^c_j; (iv) σ annihiliert alle β^c_i. Der Beweismechanismus
ist die Nichtnegativität der Taylorkoeffizienten der Geschlecht-0-Produkte:
die Majorante der Moden IST die Zulässigkeitsschranke, also konvergiert die
Taylorreihe absolut gegen jedes zulässige σ (Fubini), und die Momente
entscheiden alles. Korollar: die Spektralkandidaten x_ij = ∫β_iλ_j dσ des
Weges (β) sind identisch 0 — für jede summierbare Massenfolge.

Instanz: geometrische Massen μ_i = (1/2)·8^{−|i|}, ν_j = (1/3)·8^{−|j|}
(i,j ∈ Z), Stieltjes-Maß dσ = e^{−t²/(2s²)} sin(2πt/s²) dt unter c = e^t,
s² = 7/20. Zulässig: Φ_μ(r)+Φ_ν(r) ≈ 0.96·(ln r)², 1/(2s²) = 10/7 ≈ 1.43.
Alle Momente ∫c^k dσ verschwinden exakt (Verschiebung um ks² = k Perioden
des Sinus; das klassische Stieltjes-Argument).

Proben (Quadratur: Gauß–Legendre 16 je Halbperiode, dps = 50; alle
„= 0"-Aussagen relativ zur d|σ|-Größe derselben Funktion):
  (a) Momente k = 0..10 verschwinden; d|σ|-Größen sind O(1) bis O(e^{k²s²/2}).
  (b) Zulässigkeit: ∫e^{Φ_μ+Φ_ν} d|σ| ist endlich (Wert wird berichtet),
      und der Integrand ist an den Fensterrändern < 1e−40 (Abschneidung ok).
  (c) (iii): ∫λ_j dσ = 0 für j ∈ {−6..6}, obwohl ∫λ_j d|σ| = O(1) — das
      ganze System ist annihiliert, ohne dass σ = 0 wäre.
  (d) (iv): ∫β_i dσ = 0 für i ∈ {−6..6}.
  (e) Korollar 7: x_ij = ∫β_iλ_j dσ = 0 auf dem ganzen Gitter — der
      Spektralkandidat kollabiert.
  (f) die zwei übrigen (β)-Bedingungen des achtzehnten Laufs gelten
      automatisch: ∫β_iΛ dσ = 0 und ∫(λ_j − β_iΛ)/c dσ = 0.
  (g) Trennschärfe: die Kontrollfunktion e^{−ac} (Majorante e^{ar}, außerhalb
      der Klasse) wird NICHT annihiliert — ihre Paarung ist ≥ 1e−20, viele
      Größenordnungen über den Klasse-𝓔-Paarungen. Es ist also die
      Koeffizienten-Majorante, nicht die Kleinheit von σ, die tötet.
  (h) Quadratur-Konsistenz: der Momentenschritt
      I_{k+1}(j) = (I_k(j+1) − I_k(j))/ν_j gilt auf den berechneten Werten.

rc=0 genau dann, wenn alle Proben bestehen.
"""

from mpmath import mp, mpf, exp, sin, log, polyroots, taylor, legendre, fabs

mp.dps = 50

# ---------------------------------------------------------------- Parameter
S2 = mpf(7) / 20                      # s²; Sinusperiode in t
IMAX = 80                             # Produktabschneidung |i'| ≤ IMAX
T0, T1 = mpf(-15), mpf(19)            # t-Fenster (Momente bis k=10 zentrieren bei ks² ≤ 3.5)
KMAX = 10
ILIST = list(range(-6, 7))
JLIST = list(range(-6, 7))
AS = [mpf(1) / 3, mpf(1), mpf(3)]     # Kontrollfunktionen e^{−ac}

EIGHT = mpf(8)


def mass_mu(i):
    return EIGHT ** (-abs(i)) / 2


def mass_nu(j):
    return EIGHT ** (-abs(j)) / 3


# ---------------------------------------------------------------- GL-Knoten
n_gl = 16
coeffs = taylor(lambda x: legendre(n_gl, x), 0, n_gl)
roots = polyroots(list(reversed(coeffs)))
dcoeffs = [c * k for k, c in enumerate(coeffs)][1:]


def dP(x):
    return sum(c * x ** k for k, c in enumerate(dcoeffs))


gl_nodes = [(r.real, 2 / ((1 - r.real ** 2) * dP(r.real) ** 2)) for r in roots]

# ---------------------------------------------------------------- Integration
half = S2 / 2
n_iv = int((T1 - T0) / half) + 1

acc = {}       # Name -> [∫f dσ, ∫f d|σ|]


def add(name, val, wsig, wabs):
    a = acc.setdefault(name, [mpf(0), mpf(0)])
    a[0] += val * wsig
    a[1] += fabs(val) * wabs


edge_env = mpf(0)

for iv in range(n_iv):
    a0 = T0 + iv * half
    a1 = min(a0 + half, T1)
    mid, rad = (a0 + a1) / 2, (a1 - a0) / 2
    for xi, wgt in gl_nodes:
        t = mid + rad * xi
        w = wgt * rad
        c = exp(t)
        gauss = exp(-t * t / (2 * S2))
        osc = sin(2 * mp.pi * t / S2)
        wsig = w * gauss * osc
        wabs = w * gauss * fabs(osc)

        # Präfixprodukte: β_i = Π_{i'<i}(1+cμ), λ_j = Π_{j'<j}(1+cν)
        bet, lam = {}, {}
        p = mpf(1)
        for i2 in range(-IMAX, IMAX + 1):
            if -6 <= i2 <= 6:
                bet[i2] = p
            p *= 1 + c * mass_mu(i2)
        full_mu = p
        p = mpf(1)
        for j2 in range(-IMAX, IMAX + 1):
            if -6 <= j2 <= 7:
                lam[j2] = p
            p *= 1 + c * mass_nu(j2)
        Lam = p

        env = full_mu * Lam            # = e^{Φ_μ(c)+Φ_ν(c)} für c > 0
        if iv == 0 or iv == n_iv - 1:
            edge_env = max(edge_env, env * gauss)

        add("env", env, wsig, wabs)
        ck = mpf(1)
        for k in range(KMAX + 1):
            add(f"c^{k}", ck, wsig, wabs)
            ck *= c
        for j in JLIST + [7]:
            add(f"lam_{j}", lam[j], wsig, wabs)
        for k in range(1, 4):          # für Probe (h): I_k(j) = ∫c^k λ_j dσ
            for j in JLIST + [7]:
                add(f"c^{k}lam_{j}", c ** k * lam[j], wsig, wabs)
        for i in ILIST:
            add(f"bet_{i}", bet[i], wsig, wabs)
        for i in ILIST:
            for j in JLIST:
                add(f"x_{i}_{j}", bet[i] * lam[j], wsig, wabs)
        for i in ILIST:
            add(f"betLam_{i}", bet[i] * Lam, wsig, wabs)
        for i in (-4, 0, 3):
            for j in (-4, 0, 3):
                add(f"comb_{i}_{j}", (lam[j] - bet[i] * Lam) / c, wsig, wabs)
        for a in AS:
            add(f"exp_{a}", exp(-a * c), wsig, wabs)
        add("one_tv", mpf(1), wsig, wabs)

# ---------------------------------------------------------------- Auswertung
ok_all = True
REL = mpf(10) ** (-35)


def report(name, ok, detail=""):
    global ok_all
    ok_all = ok_all and ok
    print(f"  [{'ok' if ok else 'FEHLER'}] {name}" + (f" — {detail}" if detail else ""))


def rel(name):
    v, va = acc[name]
    return fabs(v) / va if va > 0 else mpf(0)


print("(a) Momente verschwinden (relativ zu ∫|c^k| d|σ|)")
worst = max(rel(f"c^{k}") for k in range(KMAX + 1))
report(f"max_k |∫c^k dσ| / ∫c^k d|σ| = {mp.nstr(worst, 3)}", worst < REL)

print("(b) Zulässigkeit")
report(f"∫e^(Φμ+Φν) d|σ| = {mp.nstr(acc['env'][1], 6)} (endlich)", acc["env"][1] > 0)
report(f"Randintegrand {mp.nstr(edge_env, 3)} < 1e−40 (Fensterabschneidung)",
       edge_env < mpf(10) ** (-40))

print("(c) das ganze λ-System ist annihiliert, σ aber nicht 0")
worst = max(rel(f"lam_{j}") for j in JLIST)
sizes = min(acc[f"lam_{j}"][1] for j in JLIST)
report(f"max_j |∫λ_j dσ| / ∫λ_j d|σ| = {mp.nstr(worst, 3)}", worst < REL)
report(f"min_j ∫λ_j d|σ| = {mp.nstr(sizes, 4)} > 0.1 und ‖σ‖_TV = "
       f"{mp.nstr(acc['one_tv'][1], 4)} > 0.1",
       sizes > mpf(1) / 10 and acc["one_tv"][1] > mpf(1) / 10)

print("(d) das ganze β-System ist annihiliert")
worst = max(rel(f"bet_{i}") for i in ILIST)
report(f"max_i |∫β_i dσ| / ∫β_i d|σ| = {mp.nstr(worst, 3)}", worst < REL)

print("(e) der Spektralkandidat kollabiert: x_ij = ∫β_iλ_j dσ = 0")
worst = max(rel(f"x_{i}_{j}") for i in ILIST for j in JLIST)
report(f"max_ij |x_ij| / ∫β_iλ_j d|σ| = {mp.nstr(worst, 3)} "
       f"({len(ILIST) * len(JLIST)} Gitterpunkte)", worst < REL)

print("(f) die übrigen (β)-Bedingungen gelten automatisch")
worst = max(rel(f"betLam_{i}") for i in ILIST)
report(f"max_i |∫β_iΛ dσ| relativ = {mp.nstr(worst, 3)}", worst < REL)
worst = max(rel(f"comb_{i}_{j}") for i in (-4, 0, 3) for j in (-4, 0, 3))
report(f"max |∫(λ_j−β_iΛ)/c dσ| relativ = {mp.nstr(worst, 3)}", worst < REL)

print("(g) Trennschärfe: außerhalb der Klasse wird nicht annihiliert")
vals = {a: fabs(acc[f"exp_{a}"][0]) for a in AS}
best = max(vals.values())
detail = ", ".join(f"a={mp.nstr(a, 2)}: {mp.nstr(v, 3)}" for a, v in vals.items())
report(f"max_a |∫e^(−ac) dσ| = {mp.nstr(best, 3)} ≥ 1e−20 ({detail})",
       best > mpf(10) ** (-20))

print("(h) Momentenschritt auf den berechneten Integralen")
ok_ms = True
worst_ms = mpf(0)
for k in range(0, 3):
    for j in JLIST:
        ik = acc[f"c^{k}lam_{j}"][0] if k > 0 else acc[f"lam_{j}"][0]
        ik1 = acc[f"c^{k}lam_{j + 1}"][0] if k > 0 else acc[f"lam_{j + 1}"][0]
        ik_next = acc[f"c^{k + 1}lam_{j}"][0]
        d = fabs((ik1 - ik) / mass_nu(j) - ik_next)
        scale = acc[f"c^{k + 1}lam_{j}"][1]
        worst_ms = max(worst_ms, d / scale)
ok_ms = worst_ms < REL
report(f"max |I_(k+1)(j) − (I_k(j+1)−I_k(j))/ν_j| relativ = {mp.nstr(worst_ms, 3)}",
       ok_ms)

print()
print("alle Proben bestanden" if ok_all else "MINDESTENS EINE PROBE GESCHEITERT")
raise SystemExit(0 if ok_all else 1)
