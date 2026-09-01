r"""Orakel fuer Task 23, Stufe 3: die gemischte Uhr.

Modell.  T = [0,t*], q = mu + sum_i m_i delta_{a_i} mit mu atomlos, endlich viele
Atome, iota = p.  Gerechnet wird in *Uhrzeit*: Q(s) = q(T_{<s}) bildet T auf
[0,L] ab bis auf die offenen Luecken G_i = (Q(a_i), Q(a_i)+m_i), die den Atomen
entsprechen.  Was bleibt, ist eine Kette von Strecken

    S_0 = [alpha_0,beta_0], ..., S_N = [alpha_N,beta_N],
    alpha_0 = 0,  beta_i = alpha_i + c_i,  alpha_i = beta_{i-1} + m_i,

mit c_i der mu-Masse zwischen dem i-ten und dem (i+1)-ten Atom.  Auf S_i x S_j
ist die Uhr in beiden Koordinaten Lebesgue, und (eq:incrementrep) mit
gamma_1 = gamma_2 sagt dort (partial_x - partial_y) Psi = 0, also

    Psi(x,y) = f_ij(x+y)          auf S_i x S_j.                        (A)

Das ist die *analytische* Eingabe des Modells (Distributionsargument; siehe
PROTOKOLL, Abschnitt zur gemischten Uhr); alles Weitere ist exakt.  Uebrig
bleiben die Relationen beim Ueberqueren einer Luecke:

    f_ij(u + m_i) = f_{i-1,j}(u) + m_i f'_{i-1,j}(u),  u in beta_{i-1} + S_j, (B)
    f_ij(u + m_j) = f_{i,j-1}(u) + m_j f'_{i,j-1}(u),  u in S_i + beta_{j-1}, (C)

denn der Sprung von Psi ueber die Luecke ist m_i gamma(a_i, .), und
gamma(a_i, .) ist zugleich die Dichte von y -> Psi(beta_{i-1}, y).  Dazu die
Eckrelationen an zwei Atomen, an denen gamma(a_i,a_j) keine Dichte ist:

    (f_{i-1,j}(beta_{i-1}+alpha_j) - f_{i-1,j-1}(beta_{i-1}+beta_{j-1})) / m_j
  = (f_{i,j-1}(alpha_i+beta_{j-1}) - f_{i-1,j-1}(beta_{i-1}+beta_{j-1})) / m_i. (D)

Entartet eine Strecke, c_j = 0, so ist (B) ueber diese Spalte leer -- der Sprung
m_i gamma(a_i, .) trifft dort keine Dichte, sondern einen einzelnen Punkt.  Der
Wert ist trotzdem nicht frei: alle Zeiten in tau^{-1}(alpha_j) = (a_j, a_{j+1}]
haben denselben Q-Wert, gamma(a_i, .) ist auf ihnen konstant, und a_{j+1} liegt
darunter.  Also ist der Sprung ueber eine entartete Spalte *dieselbe* Groesse
gamma(a_i, a_{j+1}), die auch in der Eckrelation steht:

    (f_ij(alpha_i+alpha_j) - f_{i-1,j}(beta_{i-1}+alpha_j)) / m_i
  = (f_{i-1,j+1}(beta_{i-1}+alpha_{j+1}) - f_{i-1,j}(beta_{i-1}+alpha_j))
    / m_{j+1},                                          (E)   falls c_j = 0,

und transponiert fuer c_i = 0.  (E) ist die Relation, die dem Modell bis zum
2026-09-01 gefehlt hat; sie ist wahr, sie ist der Angelpunkt des Beweises fuer
entartete Strecken, und sie *verkleinert* den Loesungsraum -- die frueheren
Befunde ohne sie bleiben also gueltig.

Der Defekt ist Psi(L,0) - Psi(0,L) = f_N0(beta_N) - f_0N(beta_N).

Das Skript stellt (B), (C), (D), (E) und die Stetigkeit der f_ij als lineares
System auf, nimmt dessen Kern und prueft, ob der Defekt darauf verschwindet.

Ansatz.  Alle c_i, m_i sind ganzzahlig; die f_ij werden stueckweise auf den
Einheitsintervallen ihres Definitionsbereichs angesetzt, jedes Stueck in
*lokaler* Koordinate tau in [0,1] mit der Basis

    1, tau, tau^2, tau^3, exp(-tau/m)   (m ueber die verschiedenen Massen).

Diese Basis ist unter Ableitung abgeschlossen, und weil alle Verschiebungen
ganzzahlig sind, ist (B)/(C) in lokalen Koordinaten ein *koeffizientenweiser*
Vergleich ohne Verschiebungskonstanten.  exp(-tau/m) ist mit Absicht dabei: der
Kern des Kreuzungsoperators 1 + m d/du ist genau exp(-u/m), und das ist die
einzige Richtung, in der ein Gegenbeispiel Platz haette.  Ueber die Stuecke
hinweg wird nur Stetigkeit verlangt (die f_ij sind absolut stetig, mehr nicht).
"""
import itertools

import numpy as np


def basis(masses):
    """Basisfunktionen und ihre Ableitungsmatrix auf einem Stueck."""
    ms = sorted(set(masses))
    B = 4 + len(ms)

    def ev(tau):
        return np.array([1.0, tau, tau ** 2, tau ** 3]
                        + [np.exp(-tau / m) for m in ms])

    D = np.zeros((B, B))
    D[0, 1], D[1, 2], D[2, 3] = 1.0, 2.0, 3.0
    for k, m in enumerate(ms):
        D[4 + k, 4 + k] = -1.0 / m
    return B, ev, D


class Model:
    def __init__(self, cs, ms):
        assert len(cs) == len(ms) + 1
        self.cs, self.ms, self.N = cs, ms, len(ms)
        self.alpha, self.beta = [0], [cs[0]]
        for i, m in enumerate(ms, start=1):
            self.alpha.append(self.beta[i - 1] + m)
            self.beta.append(self.alpha[i] + cs[i])
        self.B, self.ev, self.D = basis(ms)
        # Unbekannte: (i,j,k) -> Spaltenblock, k linker Rand eines Stuecks
        self.idx, n = {}, 0
        for i in range(self.N + 1):
            for j in range(self.N + 1):
                for k in self.pieces(i, j):
                    self.idx[(i, j, k)] = n
                    n += self.B
        self.n = n

    def pieces(self, i, j):
        """Einheitsstuecke von D_ij; ein entartetes Gebiet traegt einen Punkt."""
        lo, hi = self.lo(i, j), self.hi(i, j)
        return [lo] if hi == lo else list(range(lo, hi))

    def lo(self, i, j):
        return self.alpha[i] + self.alpha[j]

    def hi(self, i, j):
        return self.beta[i] + self.beta[j]

    def col(self, i, j, k):
        return self.idx[(i, j, k)]

    def value_row(self, i, j, u):
        """Zeilenvektor des Funktionals f_ij(u)."""
        r = np.zeros(self.n)
        k = int(np.floor(u))
        tau = u - k
        if (i, j, k) not in self.idx:          # rechter Randpunkt
            k, tau = k - 1, tau + 1.0
        r[self.col(i, j, k):self.col(i, j, k) + self.B] = self.ev(tau)
        return r

    def constraints(self, corners=True, ycross=True, degjump=True):
        rows = []
        I = np.eye(self.B)
        # Stetigkeit innerhalb eines Gebiets
        for i in range(self.N + 1):
            for j in range(self.N + 1):
                for k in range(self.lo(i, j), self.hi(i, j) - 1):
                    r = np.zeros(self.n)
                    a, b = self.col(i, j, k), self.col(i, j, k + 1)
                    r[a:a + self.B] += self.ev(1.0)
                    r[b:b + self.B] -= self.ev(0.0)
                    rows.append(r)
        # (B) und (C): Ueberqueren einer Luecke
        for i in range(self.N + 1):
            for j in range(self.N + 1):
                if i >= 1:                                  # Luecke i in x
                    T = I + self.ms[i - 1] * self.D
                    for k in range(self.beta[i - 1] + self.alpha[j],
                                   self.beta[i - 1] + self.beta[j]):
                        src, tgt = self.col(i - 1, j, k), self.col(i, j, k + self.ms[i - 1])
                        for b in range(self.B):
                            r = np.zeros(self.n)
                            r[tgt + b] = 1.0
                            r[src:src + self.B] -= T[:, b]
                            rows.append(r)
                if j >= 1 and ycross:                       # Luecke j in y
                    T = I + self.ms[j - 1] * self.D
                    for k in range(self.alpha[i] + self.beta[j - 1],
                                   self.beta[i] + self.beta[j - 1]):
                        src, tgt = self.col(i, j - 1, k), self.col(i, j, k + self.ms[j - 1])
                        for b in range(self.B):
                            r = np.zeros(self.n)
                            r[tgt + b] = 1.0
                            r[src:src + self.B] -= T[:, b]
                            rows.append(r)
        # (D): die Ecken, an denen gamma an zwei Atomen steht
        if corners:
            for i in range(1, self.N + 1):
                for j in range(1, self.N + 1):
                    mi, mj = self.ms[i - 1], self.ms[j - 1]
                    base = self.value_row(i - 1, j - 1,
                                          self.beta[i - 1] + self.beta[j - 1])
                    left = (self.value_row(i - 1, j, self.beta[i - 1] + self.alpha[j]) - base) / mj
                    right = (self.value_row(i, j - 1, self.alpha[i] + self.beta[j - 1]) - base) / mi
                    rows.append(left - right)
        # (E): der Sprung ueber eine entartete Spalte ist ein Eckwert
        if degjump:
            for i in range(1, self.N + 1):
                for j in range(self.N):                 # j+1 <= N
                    if self.cs[j] != 0:
                        continue
                    mi, mj1 = self.ms[i - 1], self.ms[j]
                    base = self.value_row(i - 1, j, self.beta[i - 1] + self.alpha[j])
                    left = (self.value_row(i, j, self.alpha[i] + self.alpha[j]) - base) / mi
                    right = (self.value_row(i - 1, j + 1,
                                            self.beta[i - 1] + self.alpha[j + 1]) - base) / mj1
                    rows.append(left - right)
            for j in range(1, self.N + 1):              # transponiert
                for i in range(self.N):                 # i+1 <= N
                    if self.cs[i] != 0:
                        continue
                    mj, mi1 = self.ms[j - 1], self.ms[i]
                    base = self.value_row(i, j - 1, self.alpha[i] + self.beta[j - 1])
                    left = (self.value_row(i, j, self.alpha[i] + self.alpha[j]) - base) / mj
                    right = (self.value_row(i + 1, j - 1,
                                            self.alpha[i + 1] + self.beta[j - 1]) - base) / mi1
                    rows.append(left - right)
        return np.array(rows)

    def defect_row(self):
        L = self.beta[self.N]
        return self.value_row(self.N, 0, L) - self.value_row(0, self.N, L)

    def symmetry_rows(self):
        """f_ij - f_ji, an den Stuecknahtstellen ausgewertet."""
        out = []
        for i in range(self.N + 1):
            for j in range(i + 1, self.N + 1):
                for k in range(self.lo(i, j), self.hi(i, j) + 1):
                    out.append(self.value_row(i, j, float(k))
                               - self.value_row(j, i, float(k)))
        return np.array(out) if out else np.zeros((0, self.n))


def nullspace(A, tol=1e-9):
    if A.shape[0] == 0:
        return np.eye(A.shape[1]), np.array([])
    U, s, Vt = np.linalg.svd(A)
    sm = np.concatenate([s, np.zeros(max(0, A.shape[1] - len(s)))])
    return Vt[sm <= tol * max(1.0, s[0])].T, s


def report(cs, ms, corners=True, ycross=True, degjump=True):
    M = Model(cs, ms)
    A = M.constraints(corners=corners, ycross=ycross, degjump=degjump)
    ker, s = nullspace(A)
    d = M.defect_row() @ ker
    sym = M.symmetry_rows() @ ker if ker.shape[1] else np.zeros((0, 0))
    tag = "" if (corners and ycross and degjump) else \
        "  [ohne %s]" % (", ".join(([] if corners else ["Ecken"])
                                   + ([] if ycross else ["y-Kreuzungen"])
                                   + ([] if degjump else ["(E)"])))
    print("  c=%s m=%s: %d Unbekannte, %d Gleichungen, dim ker = %d%s"
          % (cs, ms, M.n, A.shape[0], ker.shape[1], tag))
    print("      max |Defekt| auf einer Kernbasis: %.3e" % (np.max(np.abs(d)) if d.size else 0.0))
    if sym.size:
        print("      max |f_ij - f_ji| auf einer Kernbasis: %.3e" % np.max(np.abs(sym)))
    return np.max(np.abs(d)) if d.size else 0.0


CONFIGS = [
    ([1, 1], [1]),
    ([1, 3], [2]),
    ([2, 1], [3]),
    ([1, 1, 1], [1, 1]),
    ([1, 2, 1], [1, 3]),
    ([2, 1, 3], [3, 1]),
    ([1, 1, 1, 1], [1, 2, 3]),
    ([2, 1, 1, 2], [1, 3, 2]),
    ([1, 1, 1, 0], [1, 2, 3]),     # letzte Strecke darf entarten
]

# Entartete Strecken: zwei Atome ohne stetige Masse dazwischen, bzw. ein Atom
# ganz am Anfang.  Die Kreuzungsrelation ueber diese Spalte ist leer; an ihre
# Stelle tritt (E), und den Wert, den (E) einfuehrt, bindet (D).  Seit dem
# 2026-09-01 deckt der Beweis diesen Fall mit ab, die Hypothese c_j > 0 ist
# gefallen.
DEGENERATE = [
    ([0, 1], [1]),
    ([0, 1, 1], [1, 2]),
    ([1, 0, 1], [1, 2]),
    ([1, 0, 1], [2, 1]),
    ([2, 0, 1], [1, 3]),
    ([1, 0, 0, 1], [1, 2, 3]),
    ([0, 0, 1], [1, 2]),
    ([0, 1, 0, 1], [1, 2, 3]),
    ([2, 0, 1, 0], [1, 3, 2]),
    ([1, 0, 2, 0, 1], [1, 2, 3, 1]),
]

# Alle Strecken entartet: das ist die rein atomare Kette, und das Modell muss
# prop:atomicdual reproduzieren.  Ein Treffer hier prueft nicht die gemischte
# Uhr, sondern das Modell.
ATOMIC = [
    ([0, 0], [1]),
    ([0, 0, 0], [1, 2]),
    ([0, 0, 0, 0], [1, 2, 3]),
    ([0, 0, 0, 0, 0], [1, 2, 3, 4]),
]

if __name__ == '__main__':
    print("Gemischte Uhr: Defekt auf dem vollen Loesungsraum")
    for cs, ms in CONFIGS:
        report(cs, ms)
    print("\nKontrolle: ohne die Eckrelationen (D) --- der Beweis braucht sie nicht")
    for cs, ms in CONFIGS[:6]:
        report(cs, ms, corners=False)
    print("\nKanarienvogel: ohne die y-Kreuzungen (C) muss der Defekt stehen bleiben")
    for cs, ms in CONFIGS[:4]:
        report(cs, ms, ycross=False)
    print("\nEntartete Strecken --- seit dem 2026-09-01 vom Beweis gedeckt")
    for cs, ms in DEGENERATE:
        report(cs, ms)
    print("\nEntartete Spalten: (D) und (E) sind zwei Wege ueber dieselbe Spalte,")
    print("jeder fuer sich genuegt --- ohne (D):")
    for cs, ms in DEGENERATE[:6]:
        report(cs, ms, corners=False)
    print("\n... ohne (E):")
    for cs, ms in DEGENERATE[:6]:
        report(cs, ms, degjump=False)
    print("\nKanarienvogel: ohne beide steht der Symmetriedefekt")
    for cs, ms in DEGENERATE[:6]:
        report(cs, ms, degjump=False, corners=False)
    print("\nProbe aufs Modell: alle Strecken entartet ist prop:atomicdual")
    for cs, ms in ATOMIC:
        report(cs, ms)
