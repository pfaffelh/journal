r"""Orakel fuer Task 23, rein atomare Uhr.

Modell.  T = {0,1,...,N}, Atome a_k = k fuer k=1..N mit Massen m_k, Konvention
iota = p, also [s,s') = T_{<s'} \ T_{<s}.  Dann ist [s,s+1) = {s}, und {s} ist
genau fuer s >= 1 ein Atom.  (eq:incrementrep) mit gamma_1 = gamma_2 = gamma:

    Phi(s+1,t) - Phi(s,t) = m_s gamma(s,t)      (s >= 1),   = 0  (s = 0)
    Phi(s,t+1) - Phi(s,t) = m_t gamma(s,t)      (t >= 1),   = 0  (t = 0)

Also Phi(1,t) = Phi(0,t) und Phi(s,1) = Phi(s,0); die Behauptung
Phi(N,0) = Phi(0,N) ist damit gleichwertig zu Phi(N,1) = Phi(1,N), einer
Aussage ueber das Innere.  Im Inneren (s,t >= 1) gilt

    Phi(s+1,t) = Phi(s,t) + (m_s/m_t) (Phi(s,t+1) - Phi(s,t)),

die Zeile s+1 ist also aus Zeile s bestimmt.  Freie Daten: Phi(1,1..N).
"""
import sympy as sp

def phi_grid(N, masses=None, row=None):
    m = masses or list(sp.symbols('m1:%d' % (N + 1), positive=True))
    r = row if row is not None else list(sp.symbols('c1:%d' % (N + 1)))
    M = {k: m[k - 1] for k in range(1, N + 1)}
    P = {(1, t): r[t - 1] for t in range(1, N + 1)}       # freie Zeile s=1
    for s in range(1, N):
        for t in range(1, N - s + 1):
            P[(s + 1, t)] = sp.expand(P[(s, t)] + M[s] / M[t] * (P[(s, t + 1)] - P[(s, t)]))
    return P, M

def defect(N, masses=None, row=None):
    """Phi(N,1) - Phi(1,N); null genau dann, wenn die Dualitaet gilt."""
    P, _ = phi_grid(N, masses, row)
    return sp.simplify(sp.expand(P[(N, 1)] - P[(1, N)]))

if __name__ == '__main__':
    for N in range(2, 7):
        d = defect(N)
        print("N=%d:  Phi(N,1)-Phi(1,N) = %s" % (N, d))
