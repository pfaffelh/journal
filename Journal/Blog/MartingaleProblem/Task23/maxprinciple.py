r"""Die omega-Kette: Bedingung 1 durch ein Maximumprinzip.

PROTOKOLL, achtundzwanzigster Lauf, "Das Maximumprinzip".

Aus Phi(i,j)-Phi(i,j-1) = m_j G(i,j) und Phi(i,j)-Phi(i-1,j) = m_i G(i,j)
(G symmetrisch) folgt durch zweimaliges Abschreiten von (i,j) nach (i-1,j-1)

    m_j G(i,j) + m_i G(i,j-1) = m_i G(i,j) + m_j G(i-1,j),

also, nach G(i-1,j) aufgeloest,

    G(i-1,j) = (1 - m_i/m_j) G(i,j) + (m_i/m_j) G(i,j-1).          (K)

Bei fallenden Massen und i > j ist 0 < m_i/m_j < 1, (K) ist eine
KONVEXKOMBINATION, und daraus folgt fuer S_j := sup_{i>=j} |G(i,j)| und
L_j := lim_i G(i,j) (Korollar 25.1: 1/m_1^2, -1/(m_1 m_2), 0):

    S_j <= max(S_{j-1}, |L_j|),    S_1 = 1/m_1^2,

also sup_{i,j} |G(i,j)| = 1/(m_1 m_2)  fuer JEDES streng fallende summierbare
Massenprofil.  Das ist die Vermutung des siebenundzwanzigsten Laufs, bewiesen.

Proben:

    (K)   die Konvexrekursion, Residuum (haengt nicht von den Startwerten ab)
    (S)   S_j <= max(S_{j-1}, |L_{j-1}|, |L_j|) auf den Trunkierungen,
          spaltenweise (der Satz sagt S_j <= max(S_{j-1}, |L_j|) mit dem
          WAHREN S_{j-1} >= |L_{j-1}|; auf der Trunkierung fehlt der Limes)
    (sup) sup|G| <= 1/(m_1 m_2), und die Spalte 2 laeuft von unten dagegen
    (N)   Gegenprobe: ein NICHT monotones Profil (Paare vertauscht).  Dort ist
          (K) keine Konvexkombination; gemessen wird, ob sup|G| trotzdem
          beschraenkt bleibt und ob 1/(m_1 m_2) noch die Schranke ist.
"""
import sys
import mpmath as mp
import omega_chain as oc

mp.mp.dps = 40
oc.mp.mp.dps = 40
TOL = mp.mpf(10)**(-25)
FAIL = []

def check(ok, what):
    print(f'  {"ok  " if ok else "FEHL"}  {what}')
    if not ok:
        FAIL.append(what)

def grid_list(ml, N):
    """Wie oc.grid, aber fuer eine explizite Massenliste ml[1..L] mit L >> N;
    der Schwanz jenseits von L wird weggelassen (geometrische Profile)."""
    L = len(ml) - 1
    pi = {}
    for k in range(1, N + 1):
        p = mp.mpf(1)
        for l in range(N + 1, L + 1):
            p *= (1 - ml[l] / ml[k])
        pi[(k, N)] = p
        for i in range(N, k, -1):
            pi[(k, i - 1)] = pi[(k, i)] * (1 - ml[i] / ml[k])
    bet = [None] * (N + 1)
    for k in range(1, N + 1):
        d = pi[(k, k)]
        for l in range(1, k):
            d *= (1 - ml[l] / ml[k])
        bet[k] = 1 / (ml[k] * d)
    gam = [None] + [bet[k] / ml[k] for k in range(1, N + 1)]
    return pi, bet, gam

def analyse(lab, m, G, N, monotone=True):
    # (K)
    res = mp.mpf(0)
    for j in range(2, N):
        for i in range(j + 1, N + 1):
            lhs = G(i - 1, j)
            rhs = (1 - m(i) / m(j)) * G(i, j) + (m(i) / m(j)) * G(i, j - 1)
            res = max(res, abs(lhs - rhs))
    print(f'    {lab}: (K) groesstes Residuum {mp.nstr(res, 3)}')
    check(res < TOL * max(1, 1 / (m(1) * m(2))), f'{lab}: (K) Konvexrekursion')
    # (S)
    S = {}
    L = {1: 1 / m(1)**2, 2: 1 / (m(1) * m(2))}
    ok = True
    worst = None
    for j in range(1, N + 1):
        S[j] = max(abs(G(i, j)) for i in range(j, N + 1))
        Lj = L.get(j, mp.mpf(0))
        if j >= 2:
            # auf der Trunkierung ist S_{j-1} zu klein, wenn das Supremum der
            # Spalte j-1 erst im Limes erreicht wird; der Satz gibt daher nur
            # S_j^(N) <= max(S_{j-1}^(N), |L_{j-1}|, |L_j|).
            bound = max(S[j - 1], L.get(j - 1, mp.mpf(0)), Lj)
            if S[j] > bound * (1 + TOL) + TOL:   # absolute Untergrenze: Rauschen bei 1e-39
                ok = False
                worst = (j, S[j], bound)
    print(f'    {lab}: S_j fuer j=1..6: ' + ' '.join(mp.nstr(S[j], 6) for j in range(1, 7)))
    if monotone and N < 110:
        print(f'    {lab}: (S) {"gilt" if ok else "verletzt bei " + str(worst)}'
              '  (nur gemessen: bei N < 110 ist die Trunkierung fuer die langsamen Profile zu kurz, s. PROTOKOLL Lauf 28)')
    elif monotone:
        check(ok, f'{lab}: (S) S_j <= max(S_(j-1), |L_(j-1)|, |L_j|) fuer alle j<=N' + (f'  Verletzung {worst}' if worst else ''))
    else:
        print(f'    {lab}: (S) {"gilt" if ok else "VERLETZT bei " + str(worst)}  (kein Satz, nur gemessen)')
    sup = max(S.values())
    pred = 1 / (m(1) * m(2))
    print(f'    {lab}: sup|G| = {mp.nstr(sup, 10)},  1/(m_1 m_2) = {mp.nstr(pred, 10)},  G(N,2) = {mp.nstr(G(N, 2), 10)}')
    if monotone:
        check(sup <= pred * (1 + TOL), f'{lab}: (sup) sup|G| <= 1/(m_1 m_2)')
    return sup

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 40   # (S) braucht N >= 110 fuer das Log-Profil, s. PROTOKOLL Lauf 28
    print(f'Monotone Profile, N = {N}')
    for lab, m in oc.PROFILES:
        pi, bet, gam = oc.grid(m, N)
        analyse(lab, m, oc.g_fun(m, pi, gam), N)
    print()
    print('Gegenprobe: nicht monotone Profile (Paare vertauscht), N und 2N')
    def swapped(l):        # m_1=1/4, m_2=1/2, m_3=1/16, m_4=1/8, ...
        k = (l + 1) // 2
        return mp.mpf(2)**(-(2 * k)) if l % 2 == 1 else mp.mpf(2)**(-(2 * k - 1))
    def swapped3(l):       # m_1=1/9, m_2=1/3, m_3=1/81, m_4=1/27, ...
        k = (l + 1) // 2
        return mp.mpf(3)**(-(2 * k)) if l % 2 == 1 else mp.mpf(3)**(-(2 * k - 1))
    def sawslow(l):        # 1/(l(l+1)) mit vertauschten Paaren
        k = (l + 1) // 2
        ll = 2 * k if l % 2 == 1 else 2 * k - 1
        return 1 / (mp.mpf(ll) * (ll + 1))
    for lab, m in [('2^-i, Paare vertauscht', swapped), ('3^-i, Paare vertauscht', swapped3),
                   ('1/(i(i+1)), Paare vertauscht', sawslow)]:
        for NN in (N // 2, N):
            Ltail = NN + 3000
            ml = [None] + [m(l) for l in range(1, Ltail + 1)]
            pi, bet, gam = grid_list(ml, NN)
            analyse(f'{lab} [N={NN}]', m, oc.g_fun(m, pi, gam), NN, monotone=False)
    print()
    print('FEHLER:' if FAIL else 'rc=0, keine Abweichung.', *FAIL, sep='\n  ')
    sys.exit(1 if FAIL else 0)
