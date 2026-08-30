r"""Verifikation zu Task 23, Stufe 1 (endlich viele Atome).

Anders als `oracle.py` setzt dieses Skript **nichts** ueber die Gestalt der
Loesung voraus.  Es baut das volle homogene lineare Gleichungssystem, das
(eq:incrementrep) mit gamma_1 = gamma_2 = gamma den Unbekannten

    Phi(s,t),  gamma(s,t)      (s,t) in {0,...,N}^2

auferlegt, bestimmt dessen Loesungsraum als Kern und prueft die Behauptungen an
einer Basis des Kerns.  Geprueft werden drei Aussagen:

    (D)  Phi(N,0) = Phi(0,N)                     -- die Dualitaetsidentitaet,
    (S)  Phi(s,t) = Phi(t,s) fuer alle s,t       -- die staerkere Symmetrie,
    (G)  gamma(s,t) = gamma(t,s) im Inneren      -- die Symmetrie der Dichte.

und zwar fuer **beide** Konventionen von Definition~\ref{def:clock}.  Das
Modell ist T = {0,1,...,N} mit Atomen bei k = 1..N und Massen m_k.

    iota = p:   [s,s') = T_{<s'} \ T_{<s},  also [s,s+1) = {s},   Masse m_s
                Phi(s+1,t) - Phi(s,t) = m_s     gamma(s,t)
                Phi(s,t+1) - Phi(s,t) = m_t     gamma(s,t)
    iota = o:   (s,s'] = T_{<=s'} \ T_{<=s}, also (s,s+1] = {s+1}, Masse m_{s+1}
                Phi(s+1,t) - Phi(s,t) = m_{s+1} gamma(s+1,t)
                Phi(s,t+1) - Phi(s,t) = m_{t+1} gamma(s,t+1)

In beiden Faellen ist m_0 = 0: das kleinste Element 0 von T traegt kein Atom.
Alle uebrigen Faelle von (eq:incrementrep) folgen aus diesen Einschrittrelationen
durch Teleskopieren, denn [s,u) = [s,t) + [t,u) nach (eq:clockadd).

Die Massen sind exakte rationale Zahlen aus einer festen Liste; die Arithmetik
ist damit exakt und der Lauf schnell.  Der Beweis in PROTOKOLL.md ist von diesem
Skript unabhaengig -- das Skript ist die Gegenprobe, nicht die Begruendung.
"""
import sympy as sp

# gleiche Massen; paarweise verschiedene ganze; paarweise verschiedene Stammbrueche
MASSVECTORS = [
    [sp.Integer(1)] * 12,
    [sp.Integer(k) for k in [3, 1, 7, 2, 11, 5, 4, 13, 6, 1, 9, 8]],
    [sp.Rational(1, k) for k in [2, 5, 3, 7, 1, 11, 4, 9, 13, 6, 8, 10]],
]


def system(N, mass, iota):
    """Kernmatrix und Variablenindex des Systems zu (eq:incrementrep)."""
    m = [sp.Integer(0)] + [mass[k] for k in range(N)]        # m[0] = 0, m[1..N]
    idx = {(kind, s, t): None for kind in ('P', 'g')
           for s in range(N + 1) for t in range(N + 1)}
    for n, key in enumerate(sorted(idx, key=lambda k: (k[0], k[1], k[2]))):
        idx[key] = n
    rows = []
    shift = 1 if iota == 'o' else 0        # welches Atom das Einschrittintervall traegt
    for s in range(N):
        for t in range(N + 1):
            r = [sp.Integer(0)] * len(idx)
            r[idx[('P', s + 1, t)]] += 1
            r[idx[('P', s, t)]] -= 1
            r[idx[('g', s + shift, t)]] -= m[s + shift]
            rows.append(r)
    for s in range(N + 1):
        for t in range(N):
            r = [sp.Integer(0)] * len(idx)
            r[idx[('P', s, t + 1)]] += 1
            r[idx[('P', s, t)]] -= 1
            r[idx[('g', s, t + shift)]] -= m[t + shift]
            rows.append(r)
    return sp.Matrix(rows), idx


def report(Nmax=8):
    ok = True
    for iota in ('p', 'o'):
        lo, hi = (1, Nmax) if iota == 'p' else (1, Nmax + 1)   # Bereich fuer (G)
        for N in range(2, Nmax + 1):
            for v_i, mass in enumerate(MASSVECTORS):
                A, idx = system(N, mass, iota)
                basis = A.nullspace()
                val = lambda v, kind, s, t: v[idx[(kind, s, t)]]
                dual = all(val(v, 'P', N, 0) == val(v, 'P', 0, N) for v in basis)
                asymP = sorted({(s, t) for v in basis
                                for s in range(N + 1) for t in range(N + 1)
                                if val(v, 'P', s, t) != val(v, 'P', t, s)})
                asymg = sorted({(s, t) for v in basis
                                for s in range(lo, min(hi, N) + 1)
                                for t in range(lo, min(hi, N) + 1)
                                if val(v, 'g', s, t) != val(v, 'g', t, s)})
                ok &= dual and not asymP and not asymg
                print('iota=%s N=%d Massen#%d: dim=%2d  (D) %s  (S) %s  (G) %s'
                      % (iota, N, v_i, len(basis),
                         'ja' if dual else 'NEIN',
                         'ja' if not asymP else 'NEIN bei %s' % asymP,
                         'ja' if not asymg else 'NEIN bei %s' % asymg))
    return ok


def report_symbolic(Nmax=5):
    """Dasselbe mit **vollstaendig symbolischen** Massen m_1,...,m_N.

    Langsam (Nullraum ueber Q(m_1,...,m_N)), deshalb nur bis N = 5.  Der Zweck
    ist die Gegenprobe zu `report`: stimmen die Dimensionen der Loesungsraeume
    ueberein, so war keine der rationalen Spezialisierungen entartet.
    """
    ok = True
    for iota in ('p', 'o'):
        for N in range(2, Nmax + 1):
            mass = list(sp.symbols('m1:%d' % (N + 1), positive=True))
            A, idx = system(N, mass, iota)
            basis = A.nullspace()
            val = lambda v, kind, s, t: sp.simplify(v[idx[(kind, s, t)]])
            dual = all(val(v, 'P', N, 0) - val(v, 'P', 0, N) == 0 for v in basis)
            asymP = sorted({(s, t) for v in basis
                            for s in range(N + 1) for t in range(N + 1)
                            if val(v, 'P', s, t) - val(v, 'P', t, s) != 0})
            ok &= dual and not asymP
            print('iota=%s N=%d symbolisch: dim=%2d  (D) %s  (S) %s'
                  % (iota, N, len(basis), 'ja' if dual else 'NEIN',
                     'ja' if not asymP else 'NEIN bei %s' % asymP))
    return ok


if __name__ == '__main__':
    import sys
    fn = report_symbolic if '--symbolic' in sys.argv else report
    sys.exit(0 if fn() else 1)
