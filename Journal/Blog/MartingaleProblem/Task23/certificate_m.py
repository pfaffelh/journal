r"""Die massegewichtete Zertifikatsnorm  ||T||_m  (Proposition 19.3).

Der dreiundzwanzigste Lauf (PROTOKOLL, "Die unendliche Halbordnung", Nachtrag)
hat die Ausschoepfung unter der Hypothese

    (F)   sum_{a,b} m_a m_b |kappa(a,b)| < oo

neu aufgestellt.  Die Rechnung ist dieselbe wie im elften Lauf, nur die Paarung
ist eine andere: statt Cauchy-Schwarz gegen die Frobeniusnorm steht dort
Hoelder, ell^oo(m (x) m) gegen ell^1(m (x) m), und die Groesse, an der alles
haengt, ist

    ||T||_m := sup_{s,t} |T_{st}| / (w_s w_t),      w_a = m_a  fuer Atome a,
                                                    w_s = 1    fuer s in {0,t*}

(die weitere Klasse der zweiten Randbemerkung des Nachtrags: 0 und t* tragen
keine Masse, also duerfen sie eine eigene Gewichtseinheit haben).

  Proposition 19.3.  Gilt (F) und gibt es eine Ausschoepfung F_n ^ T und
  Zertifikate T_n auf F_n -- symmetrisch, T_n V^{F_n} symmetrisch,
  T_n 1 = e_{t*} -- mit sup_n ||T_n||_m < oo, so ist delta(t*) = 0.

Dieses Skript misst ||T||_m.  Zwei Groessen, und der Unterschied ist wesentlich:

  * das **explizite** Zertifikat des sechsten Laufs (PROTOKOLL, "Die
    Konstruktion von T, explizit") -- eine obere Schranke fuer das Minimum,
    exakt in Bruechen gerechnet;
  * das **Minimum** von ||T||_m ueber alle Zertifikate, als lineares Programm
    (die freie Wahl innerhalb von L, die noch nie ausgenutzt wurde).

Beide sind massenabhaengig und **nicht** skaleninvariant -- anders als ||T||_F,
das der elfte Lauf gemessen hat.  Die Schranke von Proposition 19.3 lautet
4 M ||T||_m eps_F, also wird hier durchweg auf M = sum_a m_a = 1 normiert.

Aufrufe:

    python3 certificate_m.py verify     -- die Konstruktion, exakt nachgeprueft
    python3 certificate_m.py chains     -- Ketten: gleich, fallend, steigend
    python3 certificate_m.py dyadic     -- die ordnungsdichte dyadische Uhr
    python3 certificate_m.py antichain  -- die Antikette des 23. Laufs
    python3 certificate_m.py posets     -- Halbordnungen mit fallendem Profil
    python3 certificate_m.py graded     -- gestufte Stapel, Breiteninvarianz
    python3 certificate_m.py graded2    -- Kontrollen dazu, tiefe Stufenketten
    python3 certificate_m.py scrambled  -- ordnungsdichte Uhr, verwuerfelt
    python3 certificate_m.py free       -- der Spielraum innerhalb von L
    python3 certificate_m.py lp         -- das Minimum von ||T||_m als LP
    python3 certificate_m.py all
"""
import sys
from fractions import Fraction

# ------------------------------------------------------------- Matrizen (Q)


def zeros(n, k):
    return [[Fraction(0)] * k for _ in range(n)]


def mat_mul(A, B):
    n, p, k = len(A), len(B), len(B[0])
    C = zeros(n, k)
    for i in range(n):
        Ai = A[i]
        Ci = C[i]
        for l in range(p):
            a = Ai[l]
            if a:
                Bl = B[l]
                for j in range(k):
                    if Bl[j]:
                        Ci[j] += a * Bl[j]
    return C


def mat_vec(A, x):
    return [sum((a * b for a, b in zip(row, x) if a and b), Fraction(0))
            for row in A]


def vec_mat(x, A):
    """x^T A."""
    n, k = len(A), len(A[0])
    out = [Fraction(0)] * k
    for i in range(n):
        if x[i]:
            for j in range(k):
                if A[i][j]:
                    out[j] += x[i] * A[i][j]
    return out


def transpose(A):
    return [list(col) for col in zip(*A)]


def poset_V(masses, less):
    """V_{s,a} = [a < s] m_a."""
    n = len(masses)
    return [[masses[a] if less(a, s) else Fraction(0) for a in range(n)]
            for s in range(n)]


# ------------------------------------- das explizite Zertifikat, sechster Lauf


def certificate(V, t):
    """T symmetrisch mit T V = V^T T und T 1 = e_t, nach der Formel des
    sechsten Laufs.  Setzt V nilpotent und m >= 0 voraus (dann ist
    V^{r-1} 1 =/= 0, das Lemma jenes Laufs)."""
    n = len(V)
    one = [Fraction(1)] * n

    # Potenzen von V, bis V^r = 0.
    powers = [[[Fraction(1) if i == j else Fraction(0) for j in range(n)]
               for i in range(n)]]
    while any(any(row) for row in powers[-1]):
        powers.append(mat_mul(powers[-1], V))
        if len(powers) > n + 2:
            raise ValueError('V ist nicht nilpotent')
    r = len(powers) - 1                       # V^r = 0 =/= V^{r-1}

    u = mat_vec(powers[r - 1], one)
    istar = next((i for i in range(n) if u[i]), None)
    if istar is None:
        raise ValueError('V^{r-1} 1 = 0 -- 1 hat nicht maximale Ordnung')
    lam = [Fraction(0)] * n
    lam[istar] = Fraction(1) / u[istar]

    P = [vec_mat(lam, powers[r - 1 - k]) for k in range(r)]     # p_k^T
    a = [sum(p) for p in P]                                     # p_k^T 1
    assert a[0] == 1

    w = [Fraction(1)]                                           # 1/a(x) mod x^r
    for k in range(1, r):
        w.append(-sum(a[j] * w[k - j] for j in range(1, k + 1)))
    Ph = [[sum(w[k - j] * P[j][i] for j in range(k + 1)) for i in range(n)]
          for k in range(r)]                                    # hat p_k^T

    Psi = [vec_mat([Fraction(1) if i == t else Fraction(0) for i in range(n)],
                   powers[k]) for k in range(r)]                # psi_k^T
    c = [mat_vec(powers[k], one)[t] for k in range(r)]

    T = zeros(n, n)
    for k in range(r):
        pk, sk = Ph[k], Psi[k]
        for i in range(n):
            if pk[i] or sk[i]:
                for j in range(n):
                    T[i][j] += pk[i] * sk[j] + sk[i] * pk[j]
    # dritter Term: hat P^T C hat P mit C_{kl} = c_{k+l}
    CP = [[sum((c[k + l] * Ph[l][i] for l in range(r) if k + l < r),
               Fraction(0)) for i in range(n)] for k in range(r)]
    for k in range(r):
        pk, ck = Ph[k], CP[k]
        for i in range(n):
            if pk[i]:
                for j in range(n):
                    if ck[j]:
                        T[i][j] -= pk[i] * ck[j]
    return T, r


def check_certificate(T, V, t):
    n = len(V)
    one = [Fraction(1)] * n
    sym = all(T[i][j] == T[j][i] for i in range(n) for j in range(n))
    TV, VtT = mat_mul(T, V), mat_mul(transpose(V), T)
    inter = all(TV[i][j] == VtT[i][j] for i in range(n) for j in range(n))
    row = mat_vec(T, one)
    hit = all(row[i] == (1 if i == t else 0) for i in range(n))
    return sym, inter, hit


# ------------------------------------------------------------------- Normen


def norms(T, weights, atoms):
    """(||T||_m auf den Atomen, ||T||_m auf allem, ||T||_F^2)."""
    n = len(T)
    bulk = Fraction(0)
    full = Fraction(0)
    frob = Fraction(0)
    for i in range(n):
        for j in range(n):
            frob += T[i][j] * T[i][j]
            v = abs(T[i][j])
            if not v:
                continue
            q = v / (weights[i] * weights[j])
            if q > full:
                full = q
            if i in atoms and j in atoms and q > bulk:
                bulk = q
    return bulk, full, frob


def measure(masses, less, t, atoms=None, label=''):
    """Normiert auf M = 1, baut das Zertifikat, misst."""
    M = sum(masses)
    masses = [Fraction(m) / M for m in masses]
    n = len(masses)
    if atoms is None:
        atoms = {i for i in range(n) if masses[i]}
    weights = [masses[i] if masses[i] else Fraction(1) for i in range(n)]
    V = poset_V(masses, less)
    T, r = certificate(V, t)
    ok = check_certificate(T, V, t)
    if not all(ok):
        raise AssertionError(f'Zertifikat falsch bei {label}: {ok}')
    bulk, full, frob = norms(T, weights, atoms)
    return dict(n=n, r=r, bulk=bulk, full=full, frob=frob)


def show(rows, head):
    print(head)
    print(f'{"N":>4} {"r":>4} {"||T||_m (Atome)":>18} {"||T||_m (alles)":>18}'
          f' {"||T||_F":>14}')
    for lab, d in rows:
        b = float(d['bulk'])
        f = float(d['full']) if d['full'] is not None else float('inf')
        print(f'{d["n"]:4d} {d["r"]:4d} {b:18.6e} {f:18.6e}'
              f' {float(d["frob"]) ** 0.5:14.6e}   {lab}')
    print()


# ---------------------------------------------------------------- Familien
#
# Durchweg T = {0} u A u {t*}:  Index 0 ist die Null (keine Masse), der
# letzte Index ist t* (keine Masse), dazwischen die Atome.  Das ist die Lage
# von prop:atomicposet, und sie ist die des Manuskripts.


def chain_family(ms):
    """0 < a_1 < ... < a_n < t*, Massen ms an den Atomen."""
    masses = [Fraction(0)] + [Fraction(m) for m in ms] + [Fraction(0)]
    n = len(masses)
    return masses, (lambda a, s: a < s), n - 1


def antichain_family(ms):
    """0 < a_i < t*, die a_i paarweise unvergleichbar."""
    masses = [Fraction(0)] + [Fraction(m) for m in ms] + [Fraction(0)]
    n = len(masses)

    def less(a, s):
        if a == s:
            return False
        if a == 0:
            return True
        if s == n - 1:
            return True
        return False
    return masses, less, n - 1


def layer_family(rows):
    """0 < (Schicht 1) < (Schicht 2) < ... < t*, innerhalb einer Schicht
    unvergleichbar.  rows ist eine Liste von Massenlisten."""
    masses = [Fraction(0)]
    layer = [0]
    for k, row in enumerate(rows, start=1):
        for m in row:
            masses.append(Fraction(m))
            layer.append(k)
    masses.append(Fraction(0))
    layer.append(len(rows) + 1)
    n = len(masses)

    def less(a, s):
        return layer[a] < layer[s]
    return masses, less, n - 1


def dyadic_atoms(level):
    """Atome k/2^j (k ungerade, j <= level), Masse 4^-j, nach Ort sortiert."""
    pts = []
    for j in range(1, level + 1):
        for k in range(1, 2 ** j, 2):
            pts.append((Fraction(k, 2 ** j), Fraction(1, 4 ** j)))
    pts.sort()
    return [m for _, m in pts]


# ------------------------------------------------------------------ Laeufe


def run_verify():
    """Die Konstruktion an kleinen Halbordnungen, exakt."""
    import itertools
    print('Probe: T symmetrisch, T V = V^T T, T 1 = e_t -- alle Halbordnungen')
    print('auf bis zu vier Punkten, Massen aus {0,1,2}, t jeder Punkt.')
    pts = 4
    pairs = [(i, j) for i in range(pts) for j in range(pts) if i != j]
    seen = 0
    for bits in itertools.product([0, 1], repeat=len(pairs)):
        rel = {p for p, b in zip(pairs, bits) if b}
        # Transitivitaet und Antisymmetrie
        if any((i, j) in rel and (j, i) in rel for i, j in pairs):
            continue
        if any((i, j) in rel and (j, k) in rel and (i, k) not in rel
               for i in range(pts) for j in range(pts) for k in range(pts)
               if i != j and j != k and i != k):
            continue
        for ms in itertools.product([0, 1, 2], repeat=pts):
            masses = [Fraction(m) for m in ms]
            V = poset_V(masses, lambda a, s: (a, s) in rel)
            for t in range(pts):
                try:
                    T, _ = certificate(V, t)
                except ValueError:
                    continue
                ok = check_certificate(T, V, t)
                assert all(ok), (rel, ms, t, ok)
                seen += 1
    print(f'   {seen} Konstruktionen, kein Ausfall.\n')


def run_chains():
    rows = []
    for n in (2, 3, 4, 6, 8, 10, 12):
        masses, less, t = chain_family([Fraction(1, n)] * n)
        rows.append((f'gleiche Massen 1/n, n={n}',
                     measure(masses, less, t, label=f'unif{n}')))
    show(rows, 'Kette, gleiche Massen (M = 1)')

    for rho in (2, 3):
        rows = []
        for n in (2, 3, 4, 6, 8, 10):
            ms = [Fraction(1, rho) ** k for k in range(n)]
            masses, less, t = chain_family(ms)
            rows.append((f'rho={rho}, n={n}', measure(masses, less, t)))
        show(rows, f'Kette, FALLENDE Massen m_k = rho^-k, rho={rho} (M = 1)')

        rows = []
        for n in (2, 3, 4, 6, 8, 10):
            ms = [Fraction(rho) ** k for k in range(n)]
            masses, less, t = chain_family(ms)
            rows.append((f'rho={rho}, n={n}', measure(masses, less, t)))
        show(rows, f'Kette, STEIGENDE Massen m_k = rho^k, rho={rho} (M = 1)')


def run_dyadic(levels=(1, 2, 3, 4, 5)):
    rows = []
    for lv in levels:
        ms = dyadic_atoms(lv)
        masses, less, t = chain_family(ms)
        eps = Fraction(1, 2 ** (lv + 1)) / Fraction(1, 2)   # normiert auf M=1
        d = measure(masses, less, t)
        d['eps'] = eps
        rows.append((f'Level<={lv}, eps={float(eps):.3e}', d))
    show(rows, 'Die dyadische ordnungsdichte Uhr, Ausschoepfung nach Level')
    print('Das Produkt der Schranke von Proposition 19.3, bis auf kappa:')
    print(f'{"Level":>6} {"eps_F":>12} {"||T||_m":>14} {"4 eps ||T||_m":>16}')
    for lab, d in rows:
        e = float(d['eps'])
        f = float(d['full'])
        print(f'{lab.split(",")[0][8:]:>6} {e:12.4e} {f:14.6e} {4 * e * f:16.6e}')
    print()


def run_antichain(ns=(2, 3, 4, 5, 6, 8, 10, 12)):
    rows = []
    for n in ns:
        ms = [Fraction(1, 2) ** (k + 1) for k in range(n)]
        masses, less, t = antichain_family(ms)
        rows.append((f'n={n}', measure(masses, less, t)))
    show(rows, 'Die Antikette, Massen 2^-k (die Familie des 23. Laufs)')

    rows = []
    for n in ns:
        ms = [Fraction(1, (k + 1) * (k + 2)) for k in range(n)]
        masses, less, t = antichain_family(ms)
        rows.append((f'n={n}', measure(masses, less, t)))
    show(rows, 'Die Antikette, Massen 1/(k(k+1)) -- langsamer Schwanz')


def run_posets():
    rows = []
    for k in (1, 2, 3, 4, 5):
        layers = [[Fraction(1, 2) ** j] * 2 for j in range(1, k + 1)]
        masses, less, t = layer_family(layers)
        rows.append((f'{k} Schichten a 2', measure(masses, less, t)))
    show(rows, 'Schichten aus je zwei unvergleichbaren Atomen, Massen 2^-j')

    rows = []
    for k in (1, 2, 3, 4):
        layers = [[Fraction(1, 2) ** j] * 3 for j in range(1, k + 1)]
        masses, less, t = layer_family(layers)
        rows.append((f'{k} Schichten a 3', measure(masses, less, t)))
    show(rows, 'Schichten aus je drei unvergleichbaren Atomen, Massen 2^-j')

    rows = []
    for k in (1, 2, 3, 4, 5):
        layers = [[Fraction(1, 2) ** j] * 2 for j in range(k, 0, -1)]
        masses, less, t = layer_family(layers)
        rows.append((f'{k} Schichten a 2', measure(masses, less, t)))
    show(rows, 'dieselben Schichten, Massen STEIGEND (2^-k ... 2^-1)')


def run_graded():
    """Gestufte Halbordnungen: ein Stapel endlicher Antiketten.

    Das ist die erste Familie, die weder Kette (Theorem 17) noch Antikette
    (Proposition 19.1) ist.  Die Uhr ist fest, die Ausschoepfung nimmt die
    ersten k Stufen; normiert wird auf die Masse der Trunkierung (der
    Unterschied zur Gesamtmasse ist ein beschraenkter Faktor gegen 1).
    """
    profiles = [
        ('lambda_j = 2^-j', lambda j: Fraction(1, 2) ** j),
        ('lambda_j = 3^-j', lambda j: Fraction(1, 3) ** j),
        ('lambda_j = 1/(j(j+1))', lambda j: Fraction(1, j * (j + 1))),
        ('lambda_j = 1/j^2', lambda j: Fraction(1, j * j)),
    ]
    for lab, lam in profiles:
        for width in (1, 2, 3):
            rows = []
            for k in range(1, 9 if width < 3 else 7):
                layers = [[lam(j) / width] * width for j in range(1, k + 1)]
                masses, less, t = layer_family(layers)
                rows.append((f'k={k}', measure(masses, less, t)))
            show(rows, f'gestuft, Breite {width}, {lab}'
                       f'  (Stufenmasse lambda_j, gleich verteilt)')


def run_graded2():
    """Zwei Kontrollen zur Breiteninvarianz von run_graded.

    (a) Ungleiche Massen INNERHALB einer Stufe.  In run_graded traegt jedes
        Atom einer Stufe dieselbe Masse; dann ist T blockkonstant, und die
        Uebereinstimmung mit der Stufenkette koennte daran liegen.
    (b) Tiefe Stufenketten (Breite 1) fuer die langsamen Profile: bleibt
        ||T||_m beschraenkt oder waechst es wie log k?
    """
    print('(a) ungleiche Massen innerhalb der Stufe, Stufenmasse 2^-j')
    for split in ((Fraction(1, 2), Fraction(1, 2)), (Fraction(9, 10),
                                                     Fraction(1, 10)),
                  (Fraction(99, 100), Fraction(1, 100))):
        rows = []
        for k in range(1, 7):
            layers = [[Fraction(1, 2) ** j * p for p in split]
                      for j in range(1, k + 1)]
            masses, less, t = layer_family(layers)
            rows.append((f'k={k}', measure(masses, less, t)))
        show(rows, f'   Aufteilung {tuple(str(p) for p in split)}')
    rows = []
    for k in range(1, 7):
        masses, less, t = chain_family([Fraction(1, 2) ** j
                                        for j in range(1, k + 1)])
        rows.append((f'k={k}', measure(masses, less, t)))
    show(rows, '   die Stufenkette selbst (Breite 1) zum Vergleich')

    print('(b) tiefe Stufenketten, Breite 1')
    for lab, lam in (('2^-j', lambda j: Fraction(1, 2) ** j),
                     ('1/(j(j+1))', lambda j: Fraction(1, j * (j + 1))),
                     ('1/j^2', lambda j: Fraction(1, j * j)),
                     ('1/(j (log(j+1))^2) ~ Bertrand',
                      lambda j: Fraction(1, j * (j.bit_length() + 1) ** 2))):
        vals = []
        for k in (4, 8, 12, 16, 20, 24, 28, 32):
            masses, less, t = chain_family([lam(j) for j in range(1, k + 1)])
            vals.append((k, float(measure(masses, less, t)['full'])))
        print(f'   {lab:<24} ' + ' '.join(f'k={k}:{v:.4f}' for k, v in vals))
    print()


def run_scrambled():
    """Eine ordnungsdichte Uhr, deren Massen NICHT nach dem Ort fallen.

    Atome an den dyadischen Bruechen in einer festen Aufzaehlung q_1,q_2,...,
    Masse 2^-k an q_k; die Ausschoepfung nimmt die ersten n.  Summierbar,
    ordnungsdicht, und das Massenprofil in der Ordnung ist verwuerfelt --
    genau die Lage, die eine ordnungsdichte summierbare Uhr erzwingt.
    """
    order = []
    for j in range(1, 8):
        for k in range(1, 2 ** j, 2):
            order.append(Fraction(k, 2 ** j))
    rows = []
    for n in (2, 3, 4, 6, 8, 10, 12, 14):
        pts = sorted((order[k], Fraction(1, 2) ** (k + 1)) for k in range(n))
        ms = [m for _, m in pts]
        masses, less, t = chain_family(ms)
        d = measure(masses, less, t)
        d['eps'] = Fraction(1, 2) ** n
        rows.append((f'n={n}, eps={float(d["eps"]):.2e}', d))
    show(rows, 'ordnungsdichte Uhr, Massen 2^-k in fester Aufzaehlung')
    print(f'{"n":>4} {"eps_F":>12} {"||T||_m":>14} {"eps ||T||_m":>14}'
          f' {"1/m_min^2":>14}')
    for lab, d in rows:
        e = float(d['eps'])
        f = float(d['full'])
        n = int(lab.split(',')[0][2:])
        mmin = float(Fraction(1, 2) ** n / (1 - Fraction(1, 2) ** n))
        print(f'{n:4d} {e:12.4e} {f:14.6e} {e * f:14.6e} {1 / mmin ** 2:14.6e}')
    print()


def run_lp():
    """Das Minimum von ||T||_m ueber alle Zertifikate, als LP."""
    try:
        import numpy as np
        from scipy.optimize import linprog
    except ImportError:
        print('scipy fehlt -- der LP-Teil entfaellt.')
        return

    def min_norm(masses, less, t):
        M = sum(masses)
        masses = [Fraction(m) / M for m in masses]
        n = len(masses)
        w = [float(masses[i]) if masses[i] else 1.0 for i in range(n)]
        V = np.array([[float(masses[a]) if less(a, s) else 0.0
                       for a in range(n)] for s in range(n)])
        idx = [(i, j) for i in range(n) for j in range(i, n)]
        pos = {p: k for k, p in enumerate(idx)}
        d = len(idx)                                # + 1 Variable C
        Aeq, beq = [], []
        for i in range(n):
            for j in range(i + 1, n):
                row = np.zeros(d + 1)
                for k in range(n):
                    row[pos[(min(i, k), max(i, k))]] += V[k, j]
                    row[pos[(min(k, j), max(k, j))]] -= V[k, i]
                Aeq.append(row)
                beq.append(0.0)
        for i in range(n):
            row = np.zeros(d + 1)
            for k in range(n):
                row[pos[(min(i, k), max(i, k))]] += 1.0
            Aeq.append(row)
            beq.append(1.0 if i == t else 0.0)
        Aub, bub = [], []
        for (i, j), k in pos.items():
            for sgn in (1.0, -1.0):
                row = np.zeros(d + 1)
                row[k] = sgn
                row[d] = -w[i] * w[j]
                Aub.append(row)
                bub.append(0.0)
        c = np.zeros(d + 1)
        c[d] = 1.0
        res = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub),
                      A_eq=np.array(Aeq), b_eq=np.array(beq),
                      bounds=[(None, None)] * d + [(0, None)],
                      method='highs')
        return res

    print('Minimum von ||T||_m ueber alle Zertifikate (LP, Gleitkomma).')
    print('Zum Vergleich das explizite Zertifikat des sechsten Laufs.\n')
    families = []
    for n in (2, 3, 4, 6, 8, 10, 12, 16):
        families.append((f'Kette gleich n={n}',
                         chain_family([Fraction(1, n)] * n)))
    for n in (2, 3, 4, 6, 8, 10, 12):
        families.append((f'Kette fallend 2^-k n={n}',
                         chain_family([Fraction(1, 2) ** k
                                       for k in range(n)])))
    for n in (2, 3, 4, 6, 8, 10):
        families.append((f'Kette steigend 2^k n={n}',
                         chain_family([Fraction(2) ** k for k in range(n)])))
    for lv in (1, 2, 3, 4):
        families.append((f'dyadisch Level<={lv}',
                         chain_family(dyadic_atoms(lv))))
    for n in (2, 3, 4, 6, 8, 10, 12):
        families.append((f'Antikette 2^-k n={n}',
                         antichain_family([Fraction(1, 2) ** (k + 1)
                                           for k in range(n)])))
    for k in (1, 2, 3, 4, 5):
        families.append((f'Schichten a 2, k={k}',
                         layer_family([[Fraction(1, 2) ** j] * 2
                                       for j in range(1, k + 1)])))
    print(f'{"Familie":<26} {"N":>4} {"min ||T||_m":>14}'
          f' {"explizit":>14} {"Verh.":>9}')
    for lab, (masses, less, t) in families:
        res = min_norm(masses, less, t)
        d = measure(list(masses), less, t)
        ex = float(d['full'])
        if res.status != 0:
            print(f'{lab:<26} {len(masses):4d} {"LP: " + res.message[:9]:>14}'
                  f' {ex:14.6e}')
            continue
        mn = res.x[-1]
        print(f'{lab:<26} {len(masses):4d} {mn:14.6e} {ex:14.6e}'
              f' {ex / mn if mn else float("inf"):9.2f}')
    print()


def _rank(rows, d):
    """Rang einer rationalen Matrix, Gauss."""
    A = [list(r) for r in rows]
    r = 0
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
        r += 1
        if r == len(A):
            break
    return r


def free_dim(masses, less, with_one=True):
    """dim {T = T^T, T V = V^T T (, T 1 = 0)}, exakt."""
    n = len(masses)
    V = poset_V(masses, less)
    idx = [(i, j) for i in range(n) for j in range(i, n)]
    pos = {p: k for k, p in enumerate(idx)}
    d = len(idx)
    rows = []
    for i in range(n):
        for j in range(i + 1, n):
            row = [Fraction(0)] * d
            for k in range(n):
                row[pos[(min(i, k), max(i, k))]] += V[k][j]
                row[pos[(min(k, j), max(k, j))]] -= V[k][i]
            rows.append(row)
    if with_one:
        for i in range(n):
            row = [Fraction(0)] * d
            for k in range(n):
                row[pos[(min(i, k), max(i, k))]] += Fraction(1)
            rows.append(row)
    return d - _rank(rows, d)


def run_free():
    """Wie gross ist die freie Wahl innerhalb von L ueberhaupt?

    Der Nachtrag des 23. Laufs haelt fest, das Zertifikat sei nicht eindeutig
    und die freie Wahl noch nie ausgenutzt.  Gemessen wird hier beides:
    dim {T sym, T V = V^T T} -- der ganze Loesungsraum -- und
    dim {T sym, T V = V^T T, T 1 = 0} -- der Spielraum bei festem T 1 = e_t.
    """
    print('Der Spielraum: dim{T sym, TV = V^T T} und dim{... , T 1 = 0}')
    print(f'{"Familie":<28} {"N":>4} {"dim ganz":>9} {"dim frei":>9}')
    fams = []
    for n in (2, 4, 6, 8, 10):
        fams.append((f'Kette gleich n={n}', chain_family([Fraction(1, n)] * n)))
    for n in (2, 4, 6, 8):
        fams.append((f'Kette fallend 2^-k n={n}',
                     chain_family([Fraction(1, 2) ** k for k in range(n)])))
    for lv in (1, 2, 3, 4):
        fams.append((f'dyadisch Level<={lv}', chain_family(dyadic_atoms(lv))))
    for n in (2, 3, 4, 6, 8):
        fams.append((f'Antikette 2^-k n={n}',
                     antichain_family([Fraction(1, 2) ** (k + 1)
                                       for k in range(n)])))
    for k in (1, 2, 3, 4):
        fams.append((f'Schichten a 2, k={k}',
                     layer_family([[Fraction(1, 2) ** j] * 2
                                   for j in range(1, k + 1)])))
    for k in (1, 2, 3):
        fams.append((f'Schichten a 3, k={k}',
                     layer_family([[Fraction(1, 2) ** j] * 3
                                   for j in range(1, k + 1)])))
    for lab, (masses, less, t) in fams:
        M = sum(masses)
        ms = [Fraction(m) / M for m in masses]
        print(f'{lab:<28} {len(ms):4d} {free_dim(ms, less, False):9d}'
              f' {free_dim(ms, less, True):9d}')
    print()


RUNS = {'verify': run_verify, 'chains': run_chains, 'dyadic': run_dyadic,
        'antichain': run_antichain, 'posets': run_posets, 'free': run_free, 'graded': run_graded, 'graded2': run_graded2, 'scrambled': run_scrambled,
        'lp': run_lp}


def main(argv):
    what = argv[1] if len(argv) > 1 else 'all'
    if what == 'all':
        for f in RUNS.values():
            f()
    elif what in RUNS:
        RUNS[what]()
    else:
        print(__doc__)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
