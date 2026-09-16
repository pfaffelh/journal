r"""Doppelt haengende Doppelschleife: die Resonanzidentitaet (Lauf 32, Nachtrag).
0; p0<p, q0<q, r0<r, s0<s (p0,q0,r0,s0 minimal); a>p,q,r; a'>p,q,s; Ketten ueber a, a'.
Behauptung (Handrechnung):  m_{r0} m_r phi_{r0}(W) = m_p m_{p0} phi_{p0}(W) + m_q m_{q0} phi_{q0}(W)
als erzwungene Identitaet auf W_n\max, also  delta(t*) [m_{r0}m_r - m_p m_{p0} - m_q m_{q0}] = 0.
Geprueft: (a) die Identitaet ist auf Trunkierungen ohne Spitze erzwungen (generische und resonante Massen);
(b) phi_{r0}(W_n\max) ist bei generischen Massen erzwungen, bei resonanten NICHT."""
import sys
from fractions import Fraction
from posetsearch import rank
from antisym import system as diamond_system
from ideal_exhaustion import closure, is_forced, maximal, psi_row_single
from bowties import with_chains

e = [(0, i) for i in range(1, 11)] + [(1, 2), (3, 4), (5, 6), (7, 8), (2, 9), (4, 9), (6, 9), (2, 10), (4, 10), (8, 10)]
P0, P, Q0, Q, R0, R, S0, S, A, A2 = range(1, 11)

def masses(kind, N):
    m = [Fraction(0)] * N
    if kind == 'generisch':
        for i in range(1, N):
            m[i] = Fraction(1, 2 ** i)
    elif kind == 'resonant':
        for i in range(1, N):
            m[i] = Fraction(1, 2 ** i)
        m[P0] = m[P] = m[Q0] = m[Q] = Fraction(1)
        m[R0] = Fraction(1); m[R] = Fraction(2)        # m_r0 m_r = 2 = m_p m_p0 + m_q m_q0
        m[S0] = Fraction(1); m[S] = Fraction(2)
    elif kind == 'halbresonant':                      # nur r-Seite resonant
        for i in range(1, N):
            m[i] = Fraction(1, 2 ** i)
        m[P0] = m[P] = m[Q0] = m[Q] = Fraction(1)
        m[R0] = Fraction(1); m[R] = Fraction(2)
        m[S0] = Fraction(1); m[S] = Fraction(3)
    return m

for n in (2, 3):
    N, edges, cp = with_chains(11, e, [A, A2], n)
    lt, down = closure(N, edges)
    pts = list(range(N))
    mx = maximal(N, lt)
    nonmax = [c for c in pts if c not in mx]
    for kind in ('generisch', 'resonant', 'halbresonant'):
        m = masses(kind, N)
        rows, idx, ncol = diamond_system(pts, down, m)
        base = rank(rows, ncol)
        def phiW(x):
            r = [Fraction(0)] * ncol
            for c in nonmax:
                if c != x:
                    r = [u + v for u, v in zip(r, psi_row_single(c, x, m, idx, ncol))]
            return r
        fr0, fp0, fq0, fs0 = phiW(R0), phiW(P0), phiW(Q0), phiW(S0)
        ident = [m[R0] * m[R] * a - m[P] * m[P0] * b - m[Q] * m[Q0] * c for a, b, c in zip(fr0, fp0, fq0)]
        ident_s = [m[S0] * m[S] * a - m[P] * m[P0] * b - m[Q] * m[Q0] * c for a, b, c in zip(fs0, fp0, fq0)]
        eq_pq = [a - b for a, b in zip(fp0, fq0)]
        print("n=%d %-12s Kerndim %2d | Identitaet r erzwungen: %s | Identitaet s erzwungen: %s | phi_p0=phi_q0 erzwungen: %s | phi_r0(W) erzwungen: %s | phi_p0(W) erzwungen: %s"
              % (n, kind, ncol - base, is_forced(rows, base, ncol, ident), is_forced(rows, base, ncol, ident_s),
                 is_forced(rows, base, ncol, eq_pq), is_forced(rows, base, ncol, fr0), is_forced(rows, base, ncol, fp0)))
