r"""min ||T||_m ueber ALLE Zertifikate der Leiter-Trunkierung, hochstellig.

PROTOKOLL, neunundzwanzigster Lauf, dritter Nachtrag.  Der sechsundzwanzigste
Lauf hat dieses LP in Gleitkomma (scipy) bis n = 12 gerechnet; scipy fehlt in
der Umgebung dieses Laufs, und die Krylow-Zertifikate zeigen, dass n = 12 nicht
reicht.  Hier: Zertifikatsraum = Krylow-T + Nullraum (mpmath-Gauss), dann das
Tschebyscheff-Problem  min C  s.t.  |T_K + sum_k lam_k D_k|_{su} <= C w_s w_u
als LP in n+3 Variablen, geloest ueber den dualen Simplex (Bland, mpmath).
Normierung: M der unendlichen Leiter (wie in spectral_ladder.py trunc).

    python3 ladder_lp.py 1/2 1/3 6 8 10 12 14
    python3 ladder_lp.py 1/3 1/2 12 18 --show   -- zusaetzlich das optimale T:
        aktive Eintraege und die Eckeintraege, gegen das Krylow-T

Numerik (Lauf 29, dritter Nachtrag): das Dual wird in der GEWICHTETEN Norm
skaliert (nu_j = w_j mu_j), sonst liegt das Tableau bei 10^34 und der Simplex
meldet faelschlich "unbeschraenkt"; kuenstliche Variablen werden ueber den
groessten Zeileneintrag ausgeraeumt, redundante Zeilen bleiben stehen.
"""
import sys
from fractions import Fraction as Fr

import mpmath as mp
import spectral as S

mp.mp.dps = int(__import__("os").environ.get("LP_DPS", "80"))
EPS = mp.mpf(10) ** (-45)


def nullspace(A, ncols):
    """Nullraum einer mpmath-Matrix (Liste von Zeilen), Gauss mit Pivotsuche."""
    rows = [r[:] for r in A]
    pivcols = []
    r = 0
    m = len(rows)
    for c in range(ncols):
        # Pivot
        best, bi = mp.mpf(0), None
        for i in range(r, m):
            if abs(rows[i][c]) > best:
                best, bi = abs(rows[i][c]), i
        if bi is None or best < EPS:
            continue
        rows[r], rows[bi] = rows[bi], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        pivcols.append(c)
        r += 1
        if r == m:
            break
    free = [c for c in range(ncols) if c not in pivcols]
    basis = []
    for fcol in free:
        v = [mp.mpf(0)] * ncols
        v[fcol] = mp.mpf(1)
        for i, pc in enumerate(pivcols):
            v[pc] = -rows[i][fcol]
        basis.append(v)
    return basis


def certificate_space(P):
    """Krylow-Zertifikat (exakt) und Basis des Nullraums {D sym, DV=V^T D, D1=0}."""
    N = P.n + 2
    idx = {}
    for i in range(N):
        for j in range(i, N):
            idx[(i, j)] = len(idx)
    E = len(idx)

    def var(i, j):
        return idx[(min(i, j), max(i, j))]
    m = [S.fr(x) for x in P.masses]
    rows = []
    # Bedingung 2 an (s,u), s<u:  m_u sum_{a>u} T_{sa} - m_s sum_{a>s} T_{au} = 0
    for s in range(N):
        for u in range(s + 1, N):
            row = [mp.mpf(0)] * E
            for a in range(N):
                if P.less(u, a):
                    row[var(s, a)] += m[u]
                if P.less(s, a):
                    row[var(a, u)] -= m[s]
            if any(x != 0 for x in row):
                rows.append(row)
    # Bedingung 3 homogen: sum_a T_{sa} = 0
    for s in range(N):
        row = [mp.mpf(0)] * E
        for a in range(N):
            row[var(s, a)] += 1
        rows.append(row)
    basis = nullspace(rows, E)
    basis = [[x / max(abs(y) for y in v) for x in v] for v in basis]
    TK, b, r, c = S.hankel_certificate(P)
    tk = [mp.mpf(0)] * E
    for (i, j), k in idx.items():
        tk[k] = S.fr(TK[i][j])
    w = [m[i] + (1 if i in (0, P.t) else 0) for i in range(N)]
    wt = [w[i] * w[j] for (i, j) in idx]
    return tk, basis, wt, idx


def chebyshev_lp(tk, basis, wt):
    """Skalierung: nu_j = wt_j mu_j; dann Normierungszeile sum nu = 1, Kosten
    tk_j/wt_j, Zeilen D_k[j]/wt_j -- alles in der gewichteten Norm, O(1)."""
    tk = [t / w for t, w in zip(tk, wt)]
    basis = [[d / w for d, w in zip(D, wt)] for D in basis]
    basis = [[x / max(abs(y) for y in D) for x in D] for D in basis]
    wt = [mp.mpf(1)] * len(wt)
    val, y = _chebyshev_lp(tk, basis, wt)
    # y[0] ~ C, y[1..K] ~ lambda (Vorzeichen per Probe festlegen)
    K = len(basis)
    best = None
    for sgn in (1, -1):
        lam = [sgn * y[k + 1] for k in range(K)]
        resid = [t + sum(lam[k] * basis[k][j] for k in range(K)) for j, t in enumerate(tk)]
        cmax = max(abs(r) for r in resid)
        if best is None or cmax < best[0]:
            best = (cmax, lam, resid)
    return val, best


def _chebyshev_lp(tk, basis, wt):
    """min C s.t. |tk_j + sum_k lam_k D_k[j]| <= C wt_j.  Primaler Simplex auf
    dem Dual:  max -sum_j (mu+_j - mu-_j) tk_j  s.t.
       sum_j wt_j (mu+_j + mu-_j) = 1,  sum_j (mu+_j - mu-_j) D_k[j] = 0 (k),  mu >= 0.
    Dualwert = Optimum C.  Dichte Tableau-Form, Bland-Regel, Phase I ueber
    kuenstliche Variablen."""
    E = len(tk)
    K = len(basis)
    nrows = K + 1
    ncols = 2 * E
    # Spalten: j -> mu+_j (Spalte j), mu-_j (Spalte E+j)
    A = [[mp.mpf(0)] * ncols for _ in range(nrows)]
    bvec = [mp.mpf(0)] * nrows
    for j in range(E):
        A[0][j] = wt[j]
        A[0][E + j] = wt[j]
    bvec[0] = mp.mpf(1)
    for k in range(K):
        for j in range(E):
            A[k + 1][j] = basis[k][j]
            A[k + 1][E + j] = -basis[k][j]
    cost = [-tk[j] for j in range(E)] + [tk[j] for j in range(E)]   # maximieren
    # Vorzeichen der Zeilen so, dass b >= 0
    for i in range(nrows):
        if bvec[i] < 0:
            A[i] = [-x for x in A[i]]
            bvec[i] = -bvec[i]
    # Phase I: kuenstliche Variablen
    art = list(range(ncols, ncols + nrows))
    tab = [A[i] + [mp.mpf(1) if t == i else mp.mpf(0) for t in range(nrows)] + [bvec[i]] for i in range(nrows)]
    basis_idx = art[:]
    total = ncols + nrows

    def pivot(pr, pc):
        pv = tab[pr][pc]
        tab[pr] = [x / pv for x in tab[pr]]
        for i in range(nrows):
            if i != pr and tab[i][pc] != 0:
                f = tab[i][pc]
                tab[i] = [x - f * y for x, y in zip(tab[i], tab[pr])]
        basis_idx[pr] = pc

    def simplex(obj, allowed):
        # obj: Kostenvektor (maximieren); reduzierte Kosten = obj_c - sum_i obj_{B_i} tab[i][c]
        steps = 0
        while True:
            steps += 1
            if steps > 20000:
                raise RuntimeError('zu viele Pivots')
            cb = [obj[b] for b in basis_idx]
            enter = None
            for c in range(total):
                if c not in allowed or c in basis_idx:
                    continue
                rc = obj[c] - sum(cb[i] * tab[i][c] for i in range(nrows))
                if rc > EPS * (1 + abs(obj[c])):
                    enter = c           # Bland: kleinster Index
                    break
            if enter is None:
                return
            # Quotiententest, Bland: kleinster Basisindex bei Gleichstand
            best, pr = None, None
            colmax = max(abs(tab[i][enter]) for i in range(nrows))
            for i in range(nrows):
                if tab[i][enter] > EPS * colmax:
                    q = tab[i][-1] / tab[i][enter]
                    if best is None or q < best - EPS * (1 + abs(best)) or (abs(q - best) <= EPS * (1 + abs(best)) and basis_idx[i] < basis_idx[pr]):
                        best, pr = q, i
            if pr is None:
                # numerisch: Spalte ohne positiven Eintrag bei minimal positivem
                # reduzierten Kosten -> Spalte sperren statt abbrechen
                rc_val = obj[enter] - sum(cb[i] * tab[i][enter] for i in range(nrows))
                if rc_val < mp.mpf(10) ** (-20) * (1 + abs(obj[enter])):
                    allowed.discard(enter)
                    continue
                raise RuntimeError(f'unbeschraenkt (rc={mp.nstr(rc_val, 3)})')
            pivot(pr, enter)

    obj1 = [mp.mpf(0)] * ncols + [mp.mpf(-1)] * nrows
    simplex(obj1, set(range(total)))
    infeas = sum(tab[i][-1] for i in range(nrows) if basis_idx[i] >= ncols)
    if infeas > mp.mpf(10) ** (-30):
        raise RuntimeError(f'Phase I: unzulaessig ({mp.nstr(infeas, 3)})')
    # kuenstliche Variablen aus der Basis draengen: groesster Eintrag der Zeile
    # als Pivot; ist die Zeile (auf den echten Spalten) null, ist die
    # Gleichung redundant, und die Zeile bleibt mit der kuenstlichen Variablen
    # auf Niveau 0 stehen (sie darf dann nie wieder verlassen werden).
    for i in range(nrows):
        if basis_idx[i] >= ncols:
            c, val = max(((c, abs(tab[i][c])) for c in range(ncols)), key=lambda t: t[1])
            if val > mp.mpf(10) ** (-30):
                pivot(i, c)
    obj2 = cost + [mp.mpf(0)] * nrows
    simplex(obj2, set(range(ncols)))
    val = sum(obj2[basis_idx[i]] * tab[i][-1] for i in range(nrows))
    # primale Loesung aus den Schattenpreisen: y_i = c_B^T B^{-1} e_i steht in
    # der Spalte der i-ten kuenstlichen Variablen
    y = [sum(obj2[basis_idx[i]] * tab[i][ncols + r] for i in range(nrows)) for r in range(nrows)]
    return val, y


def main(argv):
    alpha, beta = Fr(argv[1]), Fr(argv[2])
    ns = [int(x) for x in argv[3:] if not x.startswith('--')] or [6, 8]
    Minf = alpha / (1 - alpha) + beta / (1 - beta)
    print(f'LP min ||T||_m auf der Leiter ({alpha},{beta}), Normierung M_oo = {Minf}')
    for n in ns:
        alF = [alpha ** i / Minf for i in range(1, n + 1)]
        beF = [beta ** j / Minf for j in range(1, n + 1)]
        P = S.ladder(alF, beF)
        tk, basis, wt, idx = certificate_space(P)
        # Kontrolle: Krylow-Norm
        kn = max(abs(t) / w for t, w in zip(tk, wt))
        val, (cmax, lam, resid) = chebyshev_lp(tk, basis, wt)
        print(f'  n={n:2d}: dim Nullraum = {len(basis)} (erwartet n+2 = {n + 2}),  Krylow ||T||_m = {mp.nstr(kn, 10)},  LP-Minimum = {mp.nstr(val, 10)}'
              f'  [primal rekonstruiert: max|T_opt|/w = {mp.nstr(cmax, 10)}]', flush=True)
        if '--show' in argv:
            N = P.n + 2
            names = {0: '0', P.t: 't*'}
            for i in range(1, N - 1):
                names[i] = f'a{i}' if i <= n else f'b{i - n}'
            pos = {k: ij for ij, k in idx.items()}
            act = [(abs(r), j) for j, r in enumerate(resid)]
            act.sort(reverse=True)
            print('      aktive Eintraege (|T_opt|/w = C):', ', '.join(f'({names[pos[j][0]]},{names[pos[j][1]]})' for a, j in act if a > cmax * (1 - mp.mpf(10) ** -8)))
            for (i, j) in ((1, 1), (n + 1, n + 1), (1, n + 1), (2, 2), (1, 2), (P.t, 1), (P.t, n + 1)):
                jj = idx[(min(i, j), max(i, j))]
                print(f'      T_opt/w an ({names[i]},{names[j]}) = {mp.nstr(resid[jj], 10)}   (Krylow: {mp.nstr(tk[jj] / wt[jj], 10)})')


if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    main(sys.argv)
