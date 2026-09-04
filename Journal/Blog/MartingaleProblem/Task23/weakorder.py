r"""Die Stufenmittelung: eine Halbordnung mit transitiver Unvergleichbarkeit
faellt auf ihre Stufenkette zurueck.

Eine Halbordnung ist genau dann ein Ordinalsummenstapel von Antiketten, wenn
die Unvergleichbarkeit transitiv ist -- also genau dann, wenn sie eine
**schwache Ordnung** (totale Praeordnung) ist.  Fuer eine solche Halbordnung
haengt die Abwaertsmenge T_{<s} nur von der Stufe von s ab, und das erlaubt es,
das ganze System auf die Kette der Stufen zu mitteln:

    lambda_j := sum_{a in L_j} m_a,      pi_j := m|_{L_j} / lambda_j,
    tilde kappa(j,l) := sum_{a in L_j, b in L_l} pi_j(a) pi_l(b) kappa(a,b).

Behauptet und hier exakt nachgerechnet wird:

  (1)  Psi(s,t) haengt von s nur ueber die Stufe ab;
  (2)  tilde Psi(j,l) = sum_{p<j} lambda_p tilde kappa(p,l)
       = E_{pi_l} [ Psi(j, .) ],  also ist das gemittelte System das System
       der gemittelten Daten;
  (3)  aus der Relation (diamond) fuer kappa folgt (diamond) fuer tilde kappa;
  (4)  tilde delta(j) = E_{pi_j} [ delta ], insbesondere
       tilde delta(oberste Stufe) = delta(t*), wenn t* allein dort steht;
  (5)  (F) faellt mit: sum_{j,l} lambda_j lambda_l |tilde kappa(j,l)|
       <= sum_{a,b} m_a m_b |kappa(a,b)|.

Zusammen mit Theorem 17 des zweiundzwanzigsten Laufs -- Dualitaet auf jeder
Atomkette unter (F) -- ergibt das die Dualitaet auf jeder schwachen Ordnung
unter (F).  Das enthaelt Theorem 17 (lauter einelementige Stufen) und
Proposition 19.1 (eine einzige Stufe) und ist ihre gemeinsame Verschaerfung.

Keine der Identitaeten (1)--(5) benutzt m >= 0, und (1), (2), (4), (5) auch
(diamond) nicht.  Die Proben laufen deshalb mit gemischten Vorzeichen und an
beliebigem antisymmetrischem kappa, wo delta nicht verschwindet und die
Behauptungen Inhalt haben; nur (3) braucht (diamond) und laeuft auf einer
Basis des Loesungsraums.  Mit m >= 0 waere delta nach prop:atomicposet
ohnehin null und die Probe leer.

Zusaetzlich:

  (6)  die Hebung eines Kettenzertifikats,  T = sum_{j,l} tilde T_{jl}
       pi_j pi_l^T, ist ein Zertifikat der Halbordnung mit derselben
       massegewichteten Norm (der Weg ueber Proposition 19.3, unabhaengig von
       Theorem 17);
  (7)  auf der Antikette ist das Zertifikat explizit,
       T = (e_{t*} mu^T + mu e_{t*}^T)/M - mu mu^T / M^2  mit
       mu = m|_A, und ||T||_m = max(1/M, 1/M^2), auf M = 1 normiert also
       ||T||_m = 1 -- gleichmaessig in |F|, und minimal;
  (8)  auf einer Halbordnung mit nicht transitiver Unvergleichbarkeit
       (dem "N") faellt (1) aus, und mit ihr die ganze Mittelung.

Aufruf:  python3 weakorder.py        (rc = 0, wenn alle Proben halten)
"""
import random
import sys
from fractions import Fraction


# --------------------------------------------------------------- Grundlagen


def psi(masses, less, kappa, s, t):
    """Psi(s,t) = sum_{a<s} m_a kappa(a,t)."""
    return sum((masses[a] * kappa[a][t] for a in range(len(masses))
                if less(a, s)), Fraction(0))


def diamond_defect(masses, less, kappa, s, t):
    return (psi(masses, less, kappa, s, t) + psi(masses, less, kappa, t, s)
            - psi(masses, less, kappa, s, s) - psi(masses, less, kappa, t, t))


def kappa_space(masses, less, n):
    r"""Basis des Raums der antisymmetrischen kappa mit (diamond).

    (diamond) wird nur an VERGLEICHBAREN Paaren gefordert -- das ist die
    Hypothese von \eqref{eq:incrementrep} und die des Gegenbeispiels des
    23. Laufs, und die Mittelung braucht nicht mehr."""
    idx = [(i, j) for i in range(n) for j in range(i + 1, n)]
    pos = {p: k for k, p in enumerate(idx)}
    d = len(idx)

    def build(x):
        K = [[Fraction(0)] * n for _ in range(n)]
        for (i, j), k in pos.items():
            K[i][j] = x[k]
            K[j][i] = -x[k]
        return K

    rows = []
    basis = [[Fraction(1) if k == c else Fraction(0) for k in range(d)]
             for c in range(d)]
    cols = [build(b) for b in basis]
    for s in range(n):
        for t in range(s + 1, n):
            if not (less(s, t) or less(t, s)):
                continue            # (diamond) nur an VERGLEICHBAREN Paaren
            rows.append([diamond_defect(masses, less, K, s, t) for K in cols])
    return _kernel(rows, d), build


def _kernel(rows, d):
    A = [list(r) for r in rows]
    piv, r = [], 0
    for c in range(d):
        p = next((i for i in range(r, len(A)) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = Fraction(1) / A[r][c]
        A[r] = [x * inv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    free = [c for c in range(d) if c not in piv]
    ker = []
    for f in free:
        v = [Fraction(0)] * d
        v[f] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -A[i][f]
        ker.append(v)
    return ker


# ------------------------------------------------- schwache Ordnungen bauen


def weak_order(layer_sizes):
    """Die schwache Ordnung mit den gegebenen Stufengroessen.

    Gibt (n, layer, less) zurueck; Stufe 0 ist {0}, die letzte ist {t*}.
    """
    layers = [1] + list(layer_sizes) + [1]
    layer = []
    for j, w in enumerate(layers):
        layer.extend([j] * w)
    n = len(layer)
    return n, layer, (lambda a, s: layer[a] < layer[s])


def averaged(masses, layer, kappa, n):
    """lambda, pi, tilde kappa -- auf den Stufen positiver Masse."""
    J = max(layer) + 1
    lam = [sum((masses[a] for a in range(n) if layer[a] == j), Fraction(0))
           for j in range(J)]
    pi = []
    for j in range(J):
        members = [a for a in range(n) if layer[a] == j]
        if lam[j]:
            pi.append({a: masses[a] / lam[j] for a in members})
        else:                       # massefreie Stufe: muss einelementig sein
            assert len(members) == 1, 'massefreie Stufe mit mehreren Punkten'
            pi.append({members[0]: Fraction(1)})
    tk = [[sum((pi[j][a] * pi[l][b] * kappa[a][b]
                for a in pi[j] for b in pi[l]), Fraction(0))
           for l in range(J)] for j in range(J)]
    return lam, pi, tk


# ------------------------------------------------------------------- Proben


def probe_A(trials=200, seed=20260904):
    """(1)--(5) auf zufaelligen schwachen Ordnungen, gemischte Vorzeichen."""
    rng = random.Random(seed)
    shapes = [(2,), (3,), (1, 2), (2, 1), (2, 2), (1, 3), (3, 1), (2, 1, 1),
              (1, 2, 1)]
    seen = nontrivial = solved = 0
    for _ in range(trials):
        shape = rng.choice(shapes)
        n, layer, less = weak_order(shape)
        while True:
            masses = [Fraction(0)] + [Fraction(rng.choice([-3, -2, -1, 1, 2, 3]))
                                      for _ in range(n - 2)] + [Fraction(0)]
            J = max(layer) + 1
            lam = [sum((masses[a] for a in range(n) if layer[a] == j),
                       Fraction(0)) for j in range(J)]
            if all(lam[j] or sum(1 for a in range(n) if layer[a] == j) == 1
                   for j in range(J)):
                break
        # Die Identitaeten (1), (2), (4), (5) sind reine Algebra und gelten
        # fuer JEDES antisymmetrische kappa; sie werden deshalb an einem
        # beliebigen kappa geprueft, wo delta nicht verschwindet.  Nur (3)
        # braucht (diamond) und laeuft auf dem Loesungsraum.
        K = [[Fraction(0)] * n for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                K[i][j] = Fraction(rng.randint(-4, 4))
                K[j][i] = -K[i][j]
        # (1) Psi(s,t) haengt von s nur ueber die Stufe ab
        for s in range(n):
            for s2 in range(n):
                if layer[s] == layer[s2]:
                    for t in range(n):
                        assert (psi(masses, less, K, s, t)
                                == psi(masses, less, K, s2, t)), 'Probe (1)'
        lam, pi, tk = averaged(masses, layer, K, n)
        J = len(lam)
        # tilde Psi aus den gemittelten Daten
        def tpsi(j, l):
            return sum((lam[p] * tk[p][l] for p in range(J) if p < j),
                       Fraction(0))
        # (2) tilde Psi(j,l) = E_{pi_l} Psi(j, .)
        for j in range(J):
            for l in range(J):
                rep = next(a for a in range(n) if layer[a] == j)
                got = sum((pi[l][b] * psi(masses, less, K, rep, b)
                           for b in pi[l]), Fraction(0))
                assert tpsi(j, l) == got, 'Probe (2)'
        # (4) tilde delta = E_pi delta
        delta = [psi(masses, less, K, s, s) for s in range(n)]
        for j in range(J):
            got = sum((pi[j][a] * delta[a] for a in pi[j]), Fraction(0))
            assert tpsi(j, j) == got, 'Probe (4)'
        assert tpsi(J - 1, J - 1) == delta[n - 1], 'Probe (4), Spitze'
        if any(d for d in delta):
            nontrivial += 1
        # (5) (F) faellt mit
        lhs = sum((abs(lam[j] * lam[l] * tk[j][l])
                   for j in range(J) for l in range(J)), Fraction(0))
        rhs = sum((abs(masses[a] * masses[b] * K[a][b])
                   for a in range(n) for b in range(n)), Fraction(0))
        assert lhs <= rhs, 'Probe (5)'
        # (3) (diamond) faellt auf die Stufenkette -- jetzt auf dem
        #     Loesungsraum von (diamond), wo die Aussage Gegenstand hat
        ker, build = kappa_space(masses, less, n)
        for v in ker:
            K2 = build(v)
            _, pi2, tk2 = averaged(masses, layer, K2, n)

            def tpsi2(j, l):
                return sum((lam[p] * tk2[p][l] for p in range(J) if p < j),
                           Fraction(0))
            for j in range(J):
                for l in range(J):
                    assert (tpsi2(j, l) + tpsi2(l, j) - tpsi2(j, j)
                            - tpsi2(l, l) == 0), 'Probe (3)'
            solved += 1
        seen += 1
    print(f'(A) {seen} schwache Ordnungen, Identitaeten (1),(2),(4),(5) an'
          f' beliebigem kappa -- davon {nontrivial} mit delta =/= 0;'
          f' (3) an {solved} Basisloesungen von (diamond).')


def probe_B(seed=20260904):
    """(6) die Hebung eines Kettenzertifikats."""
    import certificate_m as C
    rng = random.Random(seed)
    shapes = [(2,), (1, 2), (2, 2), (3, 1), (2, 1, 2), (1, 3, 2)]
    for shape in shapes:
        n, layer, less = weak_order(shape)
        J = max(layer) + 1
        lamvals = [Fraction(0)] + [Fraction(1, 2) ** j for j in range(1, J - 1)] \
            + [Fraction(0)]
        masses = []
        for j in range(J):
            members = [a for a in range(n) if layer[a] == j]
            if lamvals[j] == 0:
                masses.extend([Fraction(0)] * len(members))
            else:
                parts = [Fraction(rng.randint(1, 5)) for _ in members]
                tot = sum(parts)
                masses.extend([lamvals[j] * p / tot for p in parts])
        # Kettenzertifikat auf den Stufen
        chainV = C.poset_V(lamvals, lambda a, s: a < s)
        Tt, _ = C.certificate(chainV, J - 1)
        pi = []
        for j in range(J):
            members = [a for a in range(n) if layer[a] == j]
            s = sum(masses[a] for a in members)
            pi.append({a: (masses[a] / s if s else Fraction(1))
                       for a in members})
        T = [[sum((Tt[layer[i]][layer[k]] * pi[layer[i]][i] * pi[layer[k]][k]
                   for _ in (0,)), Fraction(0))
              for k in range(n)] for i in range(n)]
        V = C.poset_V(masses, less)
        ok = C.check_certificate(T, V, n - 1)
        assert all(ok), (shape, ok)
        w = [masses[a] if masses[a] else Fraction(1) for a in range(n)]
        wt = [lamvals[j] if lamvals[j] else Fraction(1) for j in range(J)]
        nm = max(abs(T[i][k]) / (w[i] * w[k])
                 for i in range(n) for k in range(n))
        nmt = max(abs(Tt[j][l]) / (wt[j] * wt[l])
                  for j in range(J) for l in range(J))
        assert nm == nmt, (shape, nm, nmt)
    print(f'(B) {len(shapes)} Hebungen: Zertifikat und Norm bleiben erhalten.')


def probe_C():
    """(7) die geschlossene Formel auf der Antikette."""
    import certificate_m as C
    for ms in ([Fraction(1, 2) ** (k + 1) for k in range(6)],
               [Fraction(1, (k + 1) * (k + 2)) for k in range(7)],
               [Fraction(k + 1) for k in range(5)]):
        masses = [Fraction(0)] + list(ms) + [Fraction(0)]
        n = len(masses)
        M = sum(masses)

        def less(a, s):
            return a != s and (a == 0 or s == n - 1)
        mu = list(masses)
        e = [Fraction(1) if i == n - 1 else Fraction(0) for i in range(n)]
        T = [[(e[i] * mu[j] + mu[i] * e[j]) / M - mu[i] * mu[j] / M ** 2
              for j in range(n)] for i in range(n)]
        V = C.poset_V(masses, less)
        assert all(C.check_certificate(T, V, n - 1)), ms
        w = [masses[a] if masses[a] else Fraction(1) for a in range(n)]
        nm = max(abs(T[i][j]) / (w[i] * w[j])
                 for i in range(n) for j in range(n))
        assert nm == max(1 / M, 1 / M ** 2), (ms, nm, M)
        # Die Zeile t* liest sich ab: T_{t*,a} = m_a / M.  Auf M = 1 normiert
        # ist ||T||_m = 1, und das ist das Minimum: aus sum_a T_{t*,a} = 1 und
        # |T_{t*,a}| <= C m_a folgt C >= 1/M.
        assert all(T[n - 1][j] == masses[j] / M for j in range(1, n - 1)), ms
        mn = [x / M for x in masses]
        Tn = [[(e[i] * mn[j] + mn[i] * e[j]) - mn[i] * mn[j]
               for j in range(n)] for i in range(n)]
        wn = [mn[a] if mn[a] else Fraction(1) for a in range(n)]
        assert max(abs(Tn[i][j]) / (wn[i] * wn[j])
                   for i in range(n) for j in range(n)) == 1, ms
    print('(C) Antikette: T explizit, ||T||_m = max(1/M,1/M^2), auf M=1'
          ' normiert also 1 -- unabhaengig von |F|.')


def probe_D():
    """(8) ohne transitive Unvergleichbarkeit faellt (1) aus.

    Das "N": 0 < a,b ; a < c ; b unvergleichbar zu c ; a,b unvergleichbar.
    Dort ist Psi(c,.) =/= Psi(b,.), obwohl b und c unvergleichbar sind -- die
    Stufen sind nicht definiert, und die Mittelung hat keinen Gegenstand.
    """
    pts = ['0', 'a', 'b', 'c', 't']
    rel = {('0', 'a'), ('0', 'b'), ('0', 'c'), ('0', 't'), ('a', 'c'),
           ('a', 't'), ('b', 't'), ('c', 't')}
    idx = {p: i for i, p in enumerate(pts)}
    n = len(pts)

    def less(a, s):
        return (pts[a], pts[s]) in rel
    # Unvergleichbarkeit ist nicht transitiv:  a ~ b,  b ~ c,  aber a < c
    inc = lambda x, y: x != y and (x, y) not in rel and (y, x) not in rel
    assert inc('a', 'b') and inc('b', 'c') and not inc('a', 'c')
    masses = [Fraction(0), Fraction(1), Fraction(2), Fraction(3), Fraction(0)]
    K = [[Fraction(0)] * n for _ in range(n)]
    K[idx['a']][idx['t']] = Fraction(1)
    K[idx['t']][idx['a']] = Fraction(-1)
    assert (psi(masses, less, K, idx['b'], idx['t'])
            != psi(masses, less, K, idx['c'], idx['t']))
    print('(D) das "N": Unvergleichbarkeit nicht transitiv, Psi nicht'
          ' stufenkonstant -- die Mittelung greift nicht.')


def probe_E():
    """Das Gegenbeispiel des 23. Laufs im Licht der Mittelung.

    Dort ist die ganze Atommenge EINE Stufe, die Stufenkette also 0 < L < t*.
    Die Mittelung verlangt die absolute Konvergenz von
    sum_{a,b} pi(a) pi(b) |kappa(a,b)|, und genau die faellt aus: mit
    kappa(a_i,a_j) = sgn(i-j)/(sigma_n sigma_{n+1}), n = min(i,j), ist
    sum_{i,j} m_i m_j |kappa| = oo.  Gezeigt wird das an den Partialsummen.
    """
    prev = None
    for N in (4, 8, 16, 32, 64):
        m = [Fraction(1, 2) ** (i + 1) for i in range(N)]
        sig = [sum(m[i:], Fraction(0)) for i in range(N + 1)]
        tot = Fraction(0)
        for i in range(N):
            for j in range(N):
                if i == j:
                    continue
                k = min(i, j)
                tot += m[i] * m[j] / (sig[k] * sig[k + 1])
        assert prev is None or tot > prev
        prev = tot
    print(f'(E) das Gegenbeispiel: sum m_i m_j |kappa| waechst unbeschraenkt'
          f' (N=64: {float(prev):.3f}) -- (F) faellt aus, wie es muss.')


def main():
    probe_A()
    probe_B()
    probe_C()
    probe_D()
    probe_E()
    print('alle Proben halten.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
