"""Task 23, dreizehnter Lauf: die Energieschranke ist falsch.

Widerlegt wird die Vermutung des zwoelften Laufs: fuer endliche Kettensysteme
mit (1) h(a,0)=0, (2) h(a,b)+h(b,a)=h(a,a)+h(b,b), (3) bis auf eta, |h| <= B
gelte Delta(t)^2 <= C*B*M*eta mit C <= 1.

Teil 1 (analytisch, hier exakt nachgerechnet): die Zwei-Atom-Familie
Massen (mu, 1), eta = 2 mu^2/3, B = 1 erreicht Delta = mu - mu^2/3, also
Delta^2/(B*M*eta) = (1-mu/3)^2 * (3/2) / (1+mu)  ->  3/2  fuer mu -> 0.

Teil 2 (zertifiziert): fuer aufsteigend-geometrische Massen liefert das LP
(energy_lp.py) Loesungen mit Delta^2/(B*M*eta) in den Tausenden. Die
LP-Loesung wird auf rationale Zahlen gerundet, (1) und (2) werden per
Konstruktion exakt erzwungen (runde d_a und den antisymmetrischen Teil g_ab,
setze h(a,b) = (d_a+d_b)/2 + g_ab), dann wird in exakter Bruchrechnung
eta_used := max Residuum von (3) und B_used := max|h| bestimmt und das exakte
Verhaeltnis Delta^2/(B_used*M*eta_used) ausgegeben. Jede so zertifizierte
Instanz ist ein echtes Gegenbeispiel gegen die jeweilige Konstante.

Folgerung: es gibt keine universelle Konstante C. Der Mechanismus ist der des
elften Laufs, nur eine Ebene hoeher: leichte Atome unter schweren saettigen
|h| = B und tragen d_schwer ~ (Masse darunter)/m_schwer, bei einem Residuum
eta ~ (leichte Masse)^2. Die Beschraenktheit von h deckelt das nicht.
"""

from fractions import Fraction as F
import numpy as np


# ---------------------------------------------------------------- Verifizierer

def verify_chain(mass, d, g, u, Bclaim=None):
    """Exakte Pruefung eines Kettensystems.

    mass: Liste von Fractions, Massen der Atome 1..n (aufsteigende Ordnung).
    d:    d[a] = h(a,a), Fractions.
    g:    g[(a,b)] = antisymmetrischer Teil, a<b (g[(b,a)] := -g[(a,b)]).
    u:    u[(a,p)] = h(a, s_p) fuer Schnitte p in 0..n (s_0 unter allen
          Atomen; h(a,0) := 0 ist der Punkt t=0, getrennt von s_0 -- beide
          tragen dieselben Constraints, da H(s_0,.) = 0 = H(0,.)).

    Erzwingt (1),(2) per Konstruktion, berechnet eta_used = max Residuum von
    (3) ueber alle Gitterpaare, B_used = max|h|, Delta = Sum m_a d_a und gibt
    (Delta, M, eta_used, B_used, ratio) zurueck.
    """
    n = len(mass)

    def h_atom(a, b):  # h(a_a, a_b)
        if a == b:
            return d[a]
        base = (d[a] + d[b]) / 2
        return base + (g[(a, b)] if a < b else -g[(b, a)])

    def h_cut(a, p):  # h(a_a, s_p)
        return u[(a, p)]

    # Gitter: Punkte 0 (=t0), Atome 1..n, Schnitte s_0..s_n. Fuer (3) zaehlt
    # nur (i) wie viele Atome strikt unterhalb liegen und (ii) der Wert h(.,t).
    # Zeitpunkte kodiert als ('zero',), ('atom',a), ('cut',p).
    points = [('zero', 0)] + [('atom', a) for a in range(1, n + 1)] \
             + [('cut', p) for p in range(0, n + 1)]

    def below(pt):
        kind, idx = pt
        if kind == 'zero':
            return 0
        if kind == 'atom':
            return idx - 1
        return idx

    def hval(a, pt):
        kind, idx = pt
        if kind == 'zero':
            return F(0)
        if kind == 'atom':
            return h_atom(a, idx)
        return h_cut(a, idx)

    def Hfield(s_pt, t_pt):
        return sum((mass[a - 1] * hval(a, t_pt) for a in range(1, below(s_pt) + 1)),
                   F(0))

    eta_used = F(0)
    for i, s in enumerate(points):
        for t in points[i:]:
            res = abs(Hfield(s, t) + Hfield(t, s))
            if res > eta_used:
                eta_used = res

    B_used = F(0)
    for a in range(1, n + 1):
        for pt in points:
            B_used = max(B_used, abs(hval(a, pt)))

    Delta = sum((mass[a - 1] * d[a] for a in range(1, n + 1)), F(0))
    M = sum(mass, F(0))
    ratio = Delta * Delta / (B_used * M * eta_used) if eta_used and B_used else None
    if Bclaim is not None:
        assert B_used <= Bclaim, (B_used, Bclaim)
    return Delta, M, eta_used, B_used, ratio


# ------------------------------------------- Teil 1: die Zwei-Atom-Familie

def two_atom_witness(mu):
    """Massen (mu,1), eta = 2mu^2/3, B = 1: Delta = mu - mu^2/3."""
    mass = [mu, F(1)]
    eta = 2 * mu * mu / 3
    d = {1: -2 * mu / 3, 2: mu + mu * mu / 3}
    # x_12 = eta/(2 mu) = mu/3, also g_12 = x_12 - (d1+d2)/2.
    x12 = mu / 3
    g = {(1, 2): x12 - (d[1] + d[2]) / 2}
    u = {(1, 0): F(0), (1, 1): F(0), (1, 2): F(-1),
         (2, 0): F(0), (2, 1): mu, (2, 2): mu}
    return mass, eta, d, g, u


# --------------------------- Teil 2: LP-Loesung runden und exakt zertifizieren

def certify_from_lp(mass_float, eta_float, denom=10 ** 9):
    from energy_lp import solve_chain
    n = len(mass_float)
    v, res = solve_chain(mass_float, eta_float, want_dual=True)
    x = res.x
    m_grid = 2 * n + 1

    def var(a, gp):
        return a * m_grid + gp

    mass = [F(m).limit_denominator(denom) for m in mass_float]
    d = {a: F(x[var(a - 1, 2 * (a - 1) + 1)]).limit_denominator(denom)
         for a in range(1, n + 1)}
    g = {}
    for a in range(1, n + 1):
        for b in range(a + 1, n + 1):
            xab = x[var(a - 1, 2 * (b - 1) + 1)]
            xba = x[var(b - 1, 2 * (a - 1) + 1)]
            g[(a, b)] = F((xab - xba) / 2).limit_denominator(denom)
    u = {}
    for a in range(1, n + 1):
        u[(a, 0)] = F(0)
        for p in range(1, n + 1):
            u[(a, p)] = F(x[var(a - 1, 2 * p)]).limit_denominator(denom)
    Delta, M, eta_used, B_used, ratio = verify_chain(mass, d, g, u)
    return v, Delta, M, eta_used, B_used, ratio


if __name__ == "__main__":
    print("== Teil 1: Zwei-Atom-Familie (mu, 1), exakt ==")
    for mu in (F(1, 10), F(1, 100), F(1, 1000)):
        mass, eta, d, g, u = two_atom_witness(mu)
        Delta, M, eta_used, B_used, ratio = verify_chain(mass, d, g, u, Bclaim=F(1))
        assert eta_used <= eta, (eta_used, eta)
        print(f"  mu={mu}: Delta={Delta} M={M} eta_used={eta_used} "
              f"B={B_used} ratio={float(ratio):.6f} (exakt {ratio})")

    print("== Teil 2: aufsteigend geometrisch, LP-Loesung exakt zertifiziert ==")
    for rho, n, eta in ((2.0, 6, 1.6e-7), (2.0, 8, 1.6e-7), (2.0, 10, 1.0e-7),
                        (3.0, 8, 1.0e-7)):
        mass_f = np.array([rho ** k for k in range(n)])
        mass_f /= mass_f.sum()
        v, Delta, M, eta_used, B_used, ratio = certify_from_lp(list(mass_f), eta)
        print(f"  rho={rho} n={n}: LP v={v:.5f}  zertifiziert: Delta={float(Delta):.5f} "
              f"eta_used={float(eta_used):.3e} B_used={float(B_used):.6f} "
              f"ratio={float(ratio):.1f}")
