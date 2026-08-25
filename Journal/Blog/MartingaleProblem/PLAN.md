## Plan für Chacacteraization and Convergence of Markov Processes

Assume that all material in Chapters 2, 3 are available and can be cited.

Write a manuscript which covers the following results of EK86:
* Theorem 4.3.6: Cadlag version
* Theorem 4.4.2: Uniqueness of One-dimensional distributions suffice for uniqueness
* Theorem 4.4.11: Uniqueness via duality
* Lemma 5.5.1, Remark 5.5.2 Existence by convergence

> Note: the last item is EK86 **Lemma 4.5.1 / Remark 4.5.2** (Chapter 4, Section 5,
> printed in the book as "5.1 Lemma" / "5.2 Remark"). Chapter 5 has only five
> sections and contains no such item.

The manuscript is `MartingaleProblem.tex`; the record of how it came about, and
the decisions taken along the way, is in `FORTSCHRITT.md`.

**Layout** *(decided 2026-08-24, Q5).* Manuscript, plan and progress log live in
`Journal/Blog/MartingaleProblem/`; `Journal/Notes/MartingaleProblem/` is reserved
for the Lean files.

---

# Roadmap

Status of each task: `todo` / `wip` / `done`.
Every completed task gets an entry in `FORTSCHRITT.md`.

## Task 1 — Abstract the time index — `done` *(2026-08-24, v6)*

At present the manuscript hard-codes the time index as $[0,\infty) \subset \mathbb{R}$.
Replace it by an abstract index $\mathbb{T}$ and determine, for every definition and
every result, the *minimal* structure on $\mathbb{T}$ that the statement and its proof
actually use. This is the single change with the largest effect on the Lean
formalization, which is why it comes first: Mathlib indexes `Filtration`,
`Martingale` and `IsStoppingTime` by an arbitrary `[Preorder ι]`, so committing
to `ℝ≥0` early would mean fighting the library rather than using it.

### 1a. Fix the hierarchy of assumptions on the index

Introduce a new subsection §2.0 "The time index" with the following bundles, and
tag every later item with the weakest bundle it needs. Note that the bundles below
are assumptions on the *ordered set* $\mathbb{T}$ only; the compensator is **not**
one of them (see 1b).

| Bundle | Assumption on $\mathbb{T}$ | Needed for | Mathlib counterpart |
|---|---|---|---|
| **(T0)** | preordered set | filtration, adapted, martingale, Def. 3.2, Def. 3.3, Def. 3.4 | `[Preorder ι]` |
| **(T1)** | (T0) + directed, and a lattice: $s \wedge t$, $s \vee t$ exist | stopping times, $\mathcal{F}_\tau$, localization, optional sampling | `[Lattice ι]`, `[IsDirected ι (·≤·)]` |
| **(T1')** | (T1) made concrete as in EK86 §2.8: a *metric lattice* whose intervals are separable from above | EK86 Theorem 2.8.7 (optional sampling for directed index sets) | — |
| **(T2a)** | (T0) + linearly ordered | uniqueness half of Thm. 5.6, all of §6 | `[LinearOrder ι]` |
| **(T2b)** | (T2a) + order topology, countable dense $D$, no isolated points from the right | one-sided limits, càdlàg paths, §4 | `[OrderTopology ι] [SecondCountableTopology ι]` |
| **(T3)** | $\mathbb{T} = [0,\infty)$ or $[0,T]$ | Skorokhod topology, §7 | — |
| **(T4)** | (T0) + ordered commutative monoid, cancellative (shift $t \mapsto r+t$, difference $t-s$ for $s \le t$) | Markov property (Thm. 5.1), duality (§6) | `[OrderedAddCommMonoid ι]` + cancellation |

Two comments.

*Korrektur (D16), gegen EK86 §2.8 geprüft.* Der ursprüngliche Text hier lautete:
„Stoppzeiten brauchen $\tau_1\wedge\tau_2$, $\mathcal{F}_\tau$ braucht Infima."
**Beides ist falsch.** EK86 Prop. 2.8.1(a): das **Maximum** von Stoppzeiten ist
eine Stoppzeit; EK86 Rem. 2.8.3 warnt ausdrücklich, dass $\tau\wedge a$ i.A.
**keine** ist, weshalb EK die Trunkierung $\tau^a$ (8.10) als Ersatz einführen.
Grund: in einem Verband ist $x\wedge y\le u$ echt schwächer als „$x\le u$ oder
$y\le u$". Und $\mathcal{F}_\tau$ ist in EK86 (8.6) das übliche
$\{A: A\cap\{\tau\le u\}\in\mathcal{F}_u\}$, ohne Infima. Der Verband wird für
$\vee$ gebraucht, nicht für $\wedge$.

Ferner: (T1′) kommt im Manuskript **gar nicht** vor — jede Aussage mit Stoppzeiten
setzt schon (T2b) voraus. EK86 §2.8 wird für Kapitel 6 gebaut, aber dort trägt der
Mehrparameterindex die *Filtration* und die *Stoppzeiten*, nicht den Prozess;
$Z(t)=Y(\tau(t))$ lebt wieder in $\prod_k D_{E_k}[0,\infty)$.

*(T4) is independent of (T2)/(T3).* The monoid structure is what the shift
$X(r + \cdot)$ needs; it does not require a linear order. Keeping it separate makes
visible that §5 and §6 depend on an algebraic property of $\mathbb{T}$, whereas §4
and §7 depend on a topological one.

### 1b. The compensator is data of the problem, not structure on $\mathbb{T}$

The test processes of Definition 3.5 have the form
$$ Y_t \;=\; f(X_t) \;-\; C^{f,g}_t , \qquad (f,g) \in A , $$
and the question is what $C^{f,g}$ may be. It cannot be an arbitrary adapted
process: what distinguishes the compensator of a *generator* from an arbitrary one
is that it is **additive in time and generated pointwise from $g$**. That property
is exactly what carries Prop. 3.6 — the statement that "$X$ solves the martingale
problem for $A$" is a property of the finite-dimensional distributions of $X$.
Its proof needs Fubini in the form
$$ E\Big[ \int_{(s,t]} g(X_u)\, q(\mathrm{d}u) \cdot Z \Big]
   \;=\; \int_{(s,t]} E\big[ g(X_u) Z \big]\, q(\mathrm{d}u) . $$
Without such a decomposition there is no finite-dimensional characterization, and
without that, "martingale problem for the operator $A$" has no content: every
process solves the martingale problem for *some* family of test processes, namely
the family of its own martingales. The same structure is needed for the filtration
${}^{*}\mathcal{F}^X_t$ of (2), which is defined through
$\sigma\big(\int_0^s h(X_u)\,\mathrm{d}u\big)$.

**Minimal formulation — corrected, see D9.** The additive interval function
$q_{s,u}=q_{s,t}+q_{t,u}$ proposed here is the *wrong* notion: chain additivity
does not carry Prop. 3.6, whose proof needs Fubini and hence a measure. What is
required, and what suffices, is a **clock**: a σ-field $\mathcal{T}$ on
$\mathbb{T}$ for which every down-set $\mathbb{T}_{\le t}$ is measurable, plus a
measure $q$ with $q(\mathbb{T}_{\le t})<\infty$, plus joint measurability of
$(u,\omega)\mapsto X_u(\omega)$. Setting
$(s,t] := \mathbb{T}_{\le t}\setminus\mathbb{T}_{\le s}$, additivity is *free*
from transitivity, so a preorder still suffices — and $q$ is a Mathlib
`Measure`. This is Def. 2.2 of the manuscript.

With $q$ in hand, and allowing $g$ to depend on time, Definition 3.5 becomes
$$ Y_t \;=\; f(X_t) \;-\; \int_{[0,t]} g(s, X_s)\, q(\mathrm{d}s) . $$
This is the prototype test process of CPS23 §3.1, and their §5.3 develops the case
where $q$ has atoms. It covers in one stroke

* $q = $ Lebesgue measure on $[0,\infty)$ — the classical case;
* $q = $ counting measure on $\mathbb{N}_0$ — discrete time, where
  $Y_n = f(X_n) - \sum_{k<n} g(k, X_k)$ is the Doob decomposition and $A$ is the
  one-step generator $P - I$;
* $q$ with atoms — processes with *fixed times of discontinuity*, the subject of
  CPS23 §5;
* $q = $ Lebesgue measure on $[0,\infty)^d$ — multiparameter martingale problems,
  the setting for which EK86 §2.8 was written.

**Q6 decided (D9):** a measure, and the poset case is *not* lost by it — the
alternative was a false dichotomy.

### 1c. Audit every proof for hidden uses of $[0,\infty)$ — `done`

This was expected to be the actual work. It turned out not to be: the abstract
versions of §4, §5 and §6 written for D11–D13 make their hypotheses explicit, so
the audit is *read off* the theorems rather than performed on the proofs. The
result is §2.8 of the manuscript ("Which result needs which bundle"). Findings
below, all now confirmed or refuted.

* **Prop. 3.6** (EK86 (3.4), the finite-dimensional characterization): should go
  through under (T0) + $q$ unchanged, i.e. on a partially ordered index. The only
  ingredient is the Fubini decomposition of 1b.
* **Thm. 4.1** (càdlàg modification): **audited, see Q2 below.** Atomlessness of
  $q$ is *not* needed — the step only requires that
  $t \mapsto \int_{(0,t]} g(X_s)\,q(\mathrm{d}s)$ have one-sided limits, which holds
  for every locally finite $q$. What *is* needed is the half-open convention
  $(0,t]$ (Q8). Needs (T2) for the path regularity. §4 and §7 can therefore share
  one setting, atoms included.
* **Thm. 5.1** (uniqueness/Markov): **confirmed and split.** Needs (T4) and a
  shift-invariant $q$ — and shift-invariance is now literally the hypothesis
  (Def. 5.4, shift stability). But the two halves separate: the **Markov** half
  needs only (T0)+(T4), no linear order and no topology, whereas the
  **uniqueness** half needs **(T2a)**, because its induction requires the times
  to form a *chain*. On $\mathbb{T}=[0,\infty)^2$ the fdd's along chains do not
  determine the law, so "one-dimensional distributions suffice" is *false* for a
  multiparameter index. See Rem. 5.6 of the manuscript. The idea of re-basing
  $X|_{\{t\ge r\}}$ to drop (T4) does not work: without $+$ there is no
  $\theta_r$, and $\theta_r$ is what the restart lemma transports along.
* **Thm. 6.2 / Lemma 6.1** (duality): **confirmed and sharpened.** Needs (T4)
  plus translation invariance — *and* (T2a). Translation invariance alone does
  not suffice: the reflection $u\mapsto t-u$ carries a down-set to an up-set, and
  the two coincide only under a linear order. Lebesgue on $[0,\infty)^2$ is
  translation invariant and admits no duality (Rem. 6.4, with counterexample).
  The discrete case is written out and is *exact*, no summation by parts needed
  (Cor. 6.10). Everything is now a corollary of the chain identity Lem. 6.1, which
  itself needs only (T0)+(T4)+clock.
* **Lemma 7.1 / Thm. 7.3** (convergence): **audited, see Q7 below.** The escape
  hatch is real. CPS23 Thm. 3.14 / Cor. 3.17 — of which the manuscript's Thm. 7.3
  is one instance — uses the path space $F$ only through: $F$ Polish, $X^n \to X$
  weakly on $F$, a determining set exists, and $Y^\circ_t$, $Y^\circ_t Z^\circ_s$
  are $P$-continuous at $X$. No Skorokhod topology, no càdlàg paths, no Markov
  structure. The index enters only through the final extension step from $D$ to
  arbitrary $s<t$; with $D = \mathbb{T}$ that step is empty, so the abstract theorem
  holds under **(T0)**, and under **(T2)** for a countable dense $D$. Lemma 7.1
  (the EK86 version) does need (T3), but it is a corollary, not a prerequisite.

### 1d. Deliverable — `done` *(v6, 34 pp.)*

* §2.2 "The time index and the clock": Def. 2.1 (bundles T0, T1, T1′, T2a, T2b,
  T3, T4), Def. 2.2 (clock), Ex. 2.3 (the four clocks), Rem. 2.4 (the
  convention $(0,t]$). §1.3 gained a paragraph "Abstract time index".
* **§2.4 (Prerequisites aus EK Kap. 2) auf $\mathbb{T}$ umgestellt** — nachgezogen
  in D17: Def. 2.11 (messbarer Prozess, Filtration, adaptiert, progressiv,
  Modifikation, Stoppzeit, $\mathcal{F}_\tau$) und Def. 2.13 (Martingal) sind jetzt
  (T0); Facts 2.14/2.15 (Regularisierung) sind (T2b) über abzählbar dichtem
  $F\subset\mathbb{T}$. Das war die eigentliche Lücke: §4 war schon (T2b), zitierte
  aber Facts über $[0,\infty)$.
* **§2.5 (Skorokhod-Block)** trägt jetzt eine Kopfzeile „alles hier ist (T3)" —
  das ist der eine Prerequisites-Block, der sich nicht abstrahieren lässt.
* §3 rewritten over $\mathbb{T}$ and $q$: Def. 3.x, eq. (2), Prop. 3.6 all under
  (T0)+clock.
* Every statement in §3–§7 carries its bundle in the theorem head.
* §2.8 "Which result needs which bundle" — the result × bundle table, jetzt
  einschließlich der §2-Prerequisites.
* §8: each of (F1)–(F5b) names its target bundle, with the note that (F1),
  (F5a) and half of (F2) live under Mathlib's `[Preorder ι]`.
* Rem. 5.6 (why uniqueness needs a linear order) and Rem. 6.4 (why duality does)
  are new and are the two places where the poset case genuinely dies.

## Task 2 — Close the remaining proof gaps — `done` *(2026-08-24, v15)*

The manuscript currently states some proofs in condensed form. Before
formalization each of these must be written out in full, because a condensed step
is exactly where a formalization stalls.

1. ~~**Prop. 3.7**: the monotone class argument~~ — **done 2026-08-24 (D23).**
   Written out in four steps. Two findings: the statement had to be
   *strengthened* from chains to arbitrary finite subsets of $\mathbb{T}_{\le s}$
   (Rem. 3.8), and the terms $\int_{(0,s]}h(X_u)q(\mathrm{d}u)$ are handled by
   Fubini, not by simple-function approximation. Integrability of $Y^{f,g}$ is now
   an explicit hypothesis. **(F1) is unblocked.**
2. ~~**Lemma 3.11** (EK86 4.3.2): stated without proof.~~ — **done (D26).** The
   proof turns on one identity, $Z_t = e^{-\lambda t}Y_t + \lambda\int_0^t e^{-\lambda u}Y_u du$,
   whose inverse is the same formula with $+\lambda$; both directions are then one
   computation. Rem. 3.12 records that the lemma is (T3) for a reason of calculus.
2b. ~~the abstract local theory is stated but not carried out~~ — **done
   2026-08-24 (D19)**, now §5.2 of the manuscript, with full proofs.
2c. ~~**Shifted families (J&S III.2.39)**~~ — **done 2026-08-24 (D21).** Def. 5.5
   is now a *shift system* $(\mathbb{X}^\circ_r)$; Ex. 5.7 gives it for
   $\mathbb{X}_A$ with the pulled-back clock $q_r$. Shift invariance of the clock
   has left the hypotheses and become the criterion for *homogeneity*.
   Original wording: **Shifted families (J&S III.2.39)** — Def. 5.5 requires the shifted test
   process to stay in the *same* family, which forces the clock to be shift
   invariant and the Markov process to be homogeneous. J&S instead carry a family
   $\mathbb{X}^\circ_t$ of shifted problems. Cheap to adopt (Lem. 5.6 and 5.17
   use only that the shifted process is a $P$-martingale) and it buys the
   time-inhomogeneous case. See D20.4 and Rem. 5.19(i). **This is the natural
   next revision of §5.1.**
2d. ~~**Local uniqueness (J&S III.2.37, III.2.40)**~~ — **done (D26)**, now §5.3
   of the manuscript: Def. 5.23/5.24, Lem. 5.25 (pasting), Thm. 5.26. Needs one
   genuinely new hypothesis on $F$, concatenation (P2), which does not follow from
   the shift. Original wording: **Local uniqueness (J&S III.2.37, III.2.40)** — strictly stronger than the
   uniqueness hypothesis of Thm. 5.20, and what absolute-continuity and
   limit-theorem arguments actually need: for every strict stopping time $T$, two
   solutions of the stopped problem agree on $\mathcal{F}_T$. J&S Thm. III.2.40
   derives it from ordinary uniqueness once the problem is Markovian in the sense
   of 2c. Nothing in the manuscript corresponds. See D20.5 and Rem. 5.21(ii).
   **Now accessible**, since J&S III.2.40 presupposes exactly the shift-system
   structure that Task 2c installed.
3. ~~**Fact 2.43** (EK86 Chapter 3, Problem 7)~~ — **done (D26)**, proved as
   Rem. 2.44. The countability the argument needs comes from the *state space*
   being standard Borel, not from a countable subfamily of $M$ — there need be
   none. (F4) unblocked.
4. ~~**Thm. 5.1(b),(c)**: the optional sampling step and the construction of
   $P_1, P_2$ from $P_{X(\tau)}$ are condensed.~~ — **closed by D12.** Both are
   the restart lemma; (c) additionally needs Lemma 5.3.
5. ~~**Thm. 6.6**: the increment identity and the $O(h^2)$ bound~~ — **done
   (D26)**, four steps. Note the deviation from EK86 (44): the second term comes
   out as $\int_s^{s+h}\int_r^{s+h}$, with $g$ at the *later* time. Both are
   $O(h^2)$; the version written is the one the decomposition yields.
6. **Cor. 6.14**: the passage from $\delta_x$ to a general initial distribution
   $\mu$ — **closed by D12/D18**: it is Lem. 5.2 (mixtures) together with
   Lem. 5.3 (disintegration), both now stated and proved. What remains is to
   route Cor. 6.14 through Lem. 5.3 rather than through the Markov property.
7. ~~**Thm. 7.3**: the extension from $s,t \in D$ to arbitrary $s<t$~~ — **done
   by D24**: it is Step 3 of Thm. 7.4.
8. ~~**Rem. 7.5** (the abstract convergence theorem) is stated but not proved~~ —
   **done 2026-08-24 (D24)**, now Thm. 7.4 in a new §7.2, with a four-step proof;
   Thm. 7.7 (CPS) is an instance and its proof is a hypothesis check. Confirms
   D8 at the level of the proof: Steps 0–2 need only (T0), Step 3 alone needs
   (T2b), and with $D = \mathbb{T}$ it is empty. **(F5a) is unblocked.**

## Task 3 — Lean architecture — `on hold` *(2026-08-25, user)*

**Deferred deliberately.** The user's judgement: the theory has to stand first,
examples included, and since this is new ground much of it is still unclear.
Starting the formalization now would freeze definitions that are still moving —
Def. 5.7 (propagation), Def. 5.9 (shift system) and Def. 2.6 (clock) have each
changed shape within the last few revisions. Resume when the theory has settled.

Original content:

Decide, and record in `FORTSCHRITT.md`:

* file layout under `Journal/MartingaleProblem/`;
* whether an operator is `Set ((E → ℝ) × (E → ℝ))` or a bundled structure
  carrying its measurability proofs;
* whether the abstract martingale problem (Def. 3.2) is a `Prop` on a measure or
  a structure;
* how to model ${}^{*}\mathcal{F}^X_t$ of (2);
* how to express localization: Mathlib's `IsStoppingTime` takes
  `τ : Ω → WithTop ι`, so "$\tau_n \uparrow \infty$" is a statement in `WithTop ι`
  rather than in `ι`. This interacts with (T1) and should be settled together with
  Def. 3.2's local variant;
* naming conventions, aligned with Mathlib's `Probability/Process/`.

## Task 4 — Lean skeleton — `blocked by Task 3`

All definitions and all theorem statements, with `sorry` for every proof, in the
order §8 (F1)–(F5). The point is to make the statements type-check before any
proof is attempted; a statement that will not type-check is a statement that was
not fully understood.

## Task 5 — (F1) + (F2): definitions and uniqueness — `blocked by Task 3`

**(F1)** Def. 3.2, Def. 3.5, the filtration (2), Def. 3.10, Def. 3.15,
Prop. 3.7. **(F2)** Lem. 5.2 (mixtures), Lem. 5.3 (disintegration, needs (E1)),
Def. 5.5 (shift system), Lem. 5.8 (restart), Thm. 5.9; then §5.2 (local theory:
Def. 5.13, Lem. 5.14/5.16/5.18, Thm. 5.20) and §5.3 (Def. 5.23/5.24, Lem. 5.25,
Thm. 5.26); finally Thm. 5.28 and Cor. 5.29 as corollaries. Needs no path
regularity and no Skorokhod space — except Thm. 5.11 (strong Markov) and all of
§5.2/§5.3, which need stopping times and should wait for Task 7. This is the
natural first real proof effort; almost all the content sits in Lem. 5.8, which
is four lines.

## Task 6 — (F3): duality — `blocked by Task 3`

Lem. 6.1 (chain identity, (T0)+(T4)+clock), Prop. 6.2, Cor. 6.10 (Markov chains),
then Lem. 6.5, Thm. 6.6, Cor. 6.8, Cor. 6.14 (all (T3)). Self-contained measure
theory. Together with Task 5 this yields a complete uniqueness theory in Lean.
Lem. 6.1 and Cor. 6.10 need no analysis at all and can go first.

## Task 7 — (F4): càdlàg modification — `blocked by Task 3`

Facts 2.17, 2.18 — **but these exist already**, in `RemyDegenne/brownian-motion`,
and for quasimartingales at that (D27, Rem. 8.1 of the manuscript). What remains
is **Thm. 4.3** (the abstract regularization theorem, D11) and Thm. 4.5
(= EK86 4.3.6) as its one-line corollary, plus Fact 2.43 (now proved, Rem. 2.44).
Requires càdlàg paths but *not* the Skorokhod topology.
Formalize the abstract version: Def. 4.2 is three hypotheses (R1)–(R3) on a pair
of processes, while $\dom(A)$ would drag in the operator, its domain and the
filtration ${}^{*}\mathcal{F}^X$, none of which the proof uses.

## Task 8 — (F5): convergence — `blocked by Task 3`

Split in two by the answer to Q7; the split is the point, because 8a is small and
8b is the largest item in the whole plan.

### Task 8a — the abstract convergence theorem — `blocked by Task 3`

**Thm. 7.4** of the manuscript (= CPS23 Thm. 3.14 / Cor. 3.17), proved in full in
D24: Def. 7.3 ($P$-continuity at $X$), determining set, uniform integrability,
four steps. Needs an abstract Polish path space $F$ and **no** path regularity,
**no** Skorokhod topology, **no** Markov structure — and, with $D = \mathbb{T}$,
only bundle (T0). **This can be done directly after Task 5**, before Tasks 6 and
7, and it is the cheapest genuine theorem in the plan.

### Task 8b — Skorokhod space, and the concrete instances — `blocked by Task 3`

By far the largest item, and **the only part of the plan for which no prior art
exists** (D27): $D_E[0,\infty)$ with the $J_1$ metric, its Polishness,
Fact 2.33 ($\mathcal{B}(D_E) = \sigma(\pi_t)$), Facts 2.35/2.36, then Lem. 7.1,
Rem. 7.2 and Thm. 7.7 as instances of 8a. Candidate for upstreaming to Mathlib
independently of this project.

---

## Task 9 — Grade the state space — `done` *(2026-08-24, v14)*

Same operation as Task 1, for $E$ instead of $\mathbb{T}$. Bundles (E0)
measurable, (E1) standard Borel, (E2) separable metrizable, (E3) Polish
(Def. 2.6 of the manuscript); every statement tagged; the result × bundle table
of §2.9 gained a third column. See D25.

Findings: §3, §6 and almost all of §5 need only (E0); regular conditional
distributions, i.e. (E1), are needed at exactly three places (Lem. 5.3,
Fact 2.43, and the identification of a law by its fdd's); the topology of $E$ is
used only in §4 and §7. Consequence: distribution-valued martingale problems
($E = \mathcal{S}'$, standard Borel but not metrizable) are covered by §3, §5, §6
with no new proof. §4 and §7 are not, and the repair there is Mitoma's theorem —
flagged in Rem. 2.8, deliberately not attempted.

Side effect: Setting 3.1 now *requires* $\mathcal{S} = \sigma(\pi_t)$ of a path
space, so §5 no longer invokes Fact 2.33 at all.

---

## Task 10 — Existence theory — `done` *(2026-08-24, v17)*

Proposed by the user: the uniqueness theory had grown rich while existence had a
single conditional route. §7 is now "Existence" with four: (a) from a transition
semigroup, (b) **jump processes, constructed explicitly and proved**, (c) from
SDEs (stated, not proved — Picard–Lindelöf → Yamada–Watanabe → Stroock–Varadhan),
(d) by convergence. See D29.

(b) is the payoff: it is the only explicit solution in the manuscript, it needs
only (E0), its explosion case is the missing example for Def. 5.13, and its
discrete case is a clock with atoms. It is also step (F0) of §8 — the cheapest
theorem with real content, doable before (F1).

Deliberately **not** attempted: a self-contained proof of (c). Rem. 7.14 costs it
out; `brownian-motion` (D27) may supply the dependency.

## Task 11 — Convergence on different clocks — `done` *(2026-08-24, v18)*

Raised by the user. §7.7 of the manuscript: Thm. 7.25 lets each approximant carry
its own clock $q^n$ and convention $\iota_n$, linked to the limit only by the
discrepancy condition (K4) — CPS's (5.10). Ex. 7.27 works the invariance
principle: with $q^n = \frac1n\sum_k\delta_{k/n}$ a rescaled Markov chain
converging to a diffusion *is* a statement about clocks. See D31.

Three earlier decisions turn out to be what makes this expressible: atoms (D7),
clocks as measures on one $\mathbb{T}$ (D9), and carrying both conventions (D28,
where the difference is $O(1/n)$ and washes out). None was made with this in view.

Not supplied: tightness. (C1) is assumed.

## Task 12 — Weaken the bp-limit — `done` *(2026-08-24, v19)*

Raised by the user, and the diagnosis was right: bp entered at exactly one place
(Rem. 3.9(b),(c) = EK86 Prop. 4.3.1), and Fact 2.29 was cited in no proof at all.
What the argument uses is dominated convergence in (3), nothing more.

Now Lem. 3.10 (closure along a solution, $L^1$-convergence) with Cor. 3.11 (bp
implies it, for every solution at once) and Rem. 3.12, which states the role bp
actually plays: it is the strongest hypothesis *independent of $X$*, which is what
makes the closure statement one about operators. Also fixes an inconsistency —
Def. 3.5 admits unbounded $A$ and Prop. 3.7 assumes integrability, while the
bp-closure lives in $B \times B$. See D32.

## Task 13 — Push the non-Markovian theory as far as it goes — `done` *(2026-08-25, v20)*

Set by the user: go through the theorems one by one, stay non-Markovian in the
abstract setting as long as possible, let the Markov results fall out as
corollaries, and use CPS's non-Markovian examples as test objects.

Result: the dividing line is the **shift system** (Def. 5.7), and it falls later
than the manuscript had it. Uniqueness needs only condition (U) of Def. 5.5 and
is now Prop. 5.6, stated for an arbitrary family of measures — hence free for
$\mathcal{M}_{\mathrm{loc}}$ too — and it loses bundle (T4). §5 is re-sorted so
that §5.1 is Markov-free and §5.2 introduces the shift.

Test objects in §5.5: Volterra SDEs (CPS Ex. 3.13) and semimartingales with
path-dependent characteristics (J&S III). Rem. 5.34 tabulates the split. See
D33, D34.

Sharpest formulation found at the time: *localization is not Markovian,
restarting is.* — **superseded by Task 16**, which showed that pasting is not
Markovian either; the line falls later still.

## Task 14 — Weak-strong convergence; the restart corrected — `done` *(2026-08-25, v21)*

Both raised by the user. §7.8 states weak-strong convergence, $(P^n,P)$-continuity
and Jacod–Mémin, with the atomic counterexample that makes (C3a) fail on a set of
full measure — the second price atoms exact, after the convention clash of
Rem. 6.3. And Lem. 5.5 corrects the account of the restart: it needs no shift at
all; what needs the shift is the *re-indexing* to time $0$ that an unconditional
hypothesis demands. See D35, D36.

---

# Remaining theory tasks

Task 3 is on hold, and Tasks 4–8 depend on it, so what remains is theory.

## Task 15 — Hawkes processes and their Volterra limit — `done` *(2026-08-25, v22)*

Extended by the user from "a worked non-Markovian example" to the convergence of
Hawkes processes to a Volterra equation. §7.9 of the manuscript, in two parts.

**Part 1, proved.** Setting 7.35 and Thm. 7.37: jump processes with a
*predictable* rate $\Lambda(t,\omega)$ and kernel $\mu(t,\omega,\cdot)$. The
holding time is no longer exponential, but the cancellation of Thm. 7.5 survives
with the jump density $\Lambda_u e^{-A(u)}$ against the survival function
$e^{-A(s)}$. Ex. 7.39 is the Hawkes process; explosion for
$\|\phi\|_1 \ge 1$ puts it in §5.3, which is where the interesting scaling regime
lives anyway.

**Part 2, conditional.** Rem. 7.40 observes that a Hawkes process *is* a Volterra
SDE with pure-jump noise, so approximants and limit lie in one solution set.
Thm. 7.41 is then Thm. 7.4 for the identification plus Prop. 5.8 for uniqueness
of the limit. Tightness is assumed and Jaisson–Rosenbaum cited.

The example uses §5.1, §5.3, §7.2 and §7.5 at once, and **no result of §5.2** —
the first place where the non-Markovian layer is not merely applicable but
necessary. See D37.

## Task 16 — Local uniqueness with memory — `done` *(2026-08-25, v23)*

§5.4 no longer uses a state-indexed kernel, concatenation or a full shift system.
Def. 5.31 replaces all three by a **restart kernel** $\alpha \mapsto Q_\alpha$
indexed by the stopped path, whose defining property (R2) is exactly the
conclusion of Lem. 5.5. Lem. 5.32 and Thm. 5.33 follow, and the Markovian
construction is now Cor. 5.34.

The proof got *shorter*: a strict stopping time satisfies $T \circ a_T = T$, so
$T$ is $Q_\alpha$-a.s. deterministic, and optional sampling, the $(t-T)^+$ case
analysis and the cancellation of $\kappa$ all disappear.

What remains genuinely assumed is the existence of a restart kernel — pasting
must *supply* solutions after $T$, unlike the restart of Lem. 5.5 which merely
reweights one. That is the only place in §5 where something comes from outside.

Consequence: the slogan of D34, *localization is not Markovian, restarting is*,
is now wrong and has been removed — pasting is not Markovian either. See D38.

## Task 17 — Consistency sweep — `done` *(2026-08-25)*

The manuscript has been through twenty-three revisions, several of which changed
definitions that earlier remarks refer to. A full read for stale claims and
cross-references, with **every argument checked**, is due before anything is
frozen.

**Done so far** (§2, §3, §4, §5, §6). Findings and corrections are recorded in
D39 of `FORTSCHRITT.md`. The serious ones:

1. **§6 rewritten** — the claim "duality needs a translation invariant clock"
   was a fallacy. New Lem. `rectify`, Thm. `anyclock` (every clock admits
   duality), Rem. `atomicdual`; `lem:chain` generalized to staircases and freed
   of (T4); Rem. `conventionclash` deleted.
2. **`lem:L1auto`** used $\inf\{t:|Y_t|>n\}$, which is not a *strict* stopping
   time; replaced by the running supremum.
3. **`lem:localrestart`** needs $Z$ bounded, and is now two-level.
4. **`thm:absstrongmarkov`** — mixture over a random $\tau$ was ill-formed;
   restricted to countably-valued $\tau$.
5. New `lem:shiftembed`; §5.4 measurability and integrability made explicit.

6. **§7 durchgegangen** (→ D40). Der schwerste Fund: `ex:invariance` war in
   stetiger Zeit kein Martingal (Konvention $\mathrm p$ statt $\mathrm o$);
   `prop:jumpwellposed` leitete die Erstsprung-Gleichung zirkulär her;
   `thm:pathjumpMP` brauchte $E[N_t]<\infty$; `ex:atomicdiscontinuity` rechnete
   den Kompensator falsch aus.

7. **§7.8 vereinfacht** (→ D42, auf Nachfrage): weak-strong convergence wird
   für nichts im Manuskript gebraucht. Neu Lem. `contuse`, Thm. `absconvaug`,
   Prop. `atomaug`, Rem. `C1aug`, Rem. `augvsws`.
8. **§8, §9 und die Bündeltabellen** (→ D43). Die Mathlib-Bestandsaufnahme war
   falsch (Kolmogorov-Erweiterung ist **nicht** in v4.33.1, nur das Gerüst und
   Ionescu–Tulcea für sequentiellen Index); die (F)-Liste war fehlnummeriert und
   ist jetzt in Arbeitsreihenfolge; Design-Entscheidung (d) empfahl die von §5.3
   verworfene Operator-Route; eine widersprüchliche `lem:chain`-Zeile in den
   Tabellen entfernt.

**Task 17 ist damit abgeschlossen.**

## Task 18 — Existence by duality (\cite{DGP24}) — `done` *(2026-08-25)*

Ausgeführt als §7.2 „From a dual process", mit Beweisen — siehe D41. Setting
`dualdata` ((D1)–(D3)), Lem. `dualsemigroup`, Prop. `dualCK`, Thm. `exduality`,
Cor. `exdualitywellposed`, Prop. `rieszmarkov`, Fact `kolmogorov` neu in §2.6.
Drei Verallgemeinerungen gegenüber der Quelle: beliebige verschiebungsinvariante
Uhr, nicht-linearer Index, (E1) statt Kompaktheit.

## Task 20 — Fibrierter Zustandsraum — `angelegt` *(2026-08-25)*

Entschieden (→ D45): der Zustandsraum wird als `E : T → Type*` angelegt, nicht
fix. §2.3 hat jetzt Def. `Efibred`, den Audit (Rem. `fibredaudit`) und die
Begründung (Rem. `fibredrecommend`); §9 die Design-Entscheidung (i).

Offen bleibt nur die Ausführung dort, wo sie Inhalt hat:
* Thm. `absstrongmarkov` auf den Totalraum $\Sigma E$ umstellen (bisher nur
  vermerkt, nicht durchgeführt);
* die zwei-Parameter-Version von §7.2 (Rem. `exdualityscope`), die mit der
  Fibrierung zusammenfällt: $\mu_{s,t}$ von $E_{1,s}$ nach $E_{1,t}$;
* Raum-Zeit-Martingalproblem als Beispiel ausschreiben.

## Task 19 — Historischer Prozess als Dualer — `am Beispiel durchgeführt` *(2026-08-25)*

Durchdacht (D47) und am Hawkes-Prozess **ausgeführt** (D48). §7.2 hat jetzt
Setting `historical`, Lem. `histrestart`, Rem. `histbuys`/`histobstruction`,
und die vollständige Verifikation: Setting `hawkesdual`, Lem. `hawkesflow`,
Prop. `hawkesduality`, Prop. `hawkesDcheck`, Cor. `hawkesrestart`,
Rem. `hawkesscope`.

**Ergebnis.** (D1), (D2) und (D3) sind für den Hawkes-Prozess alle verifiziert;
der Duale ist die deterministische, rückwärts laufende Volterra-Gleichung, die
Flusseigenschaft ist bewiesen, (D3) ohne Zirkel über die
Generationen-Abschneidung gezeigt. Der Gewinn ist **Cor. `hawkesrestart`**: ein
nicht-Markovscher Restart-Kern, den §5.4 bisher nicht hatte — damit lokale
Eindeutigkeit für das Hawkes-Problem ohne Shift-System. Auf der Existenzseite
reproduziert die Dualität Hawkes–Oakes und spart nichts.

**Offen bleibt das allgemeine Programm**, Obstruktion benannt: für
Genealogieräume sind weder (D2) noch (D3) über Transformationen verfügbar
(Rem. `histobstruction`); für Punktkonfigurationen sind sie es, und das ist der
Grund, warum gerade dieses Beispiel durchgeht.

**Nächster möglicher Schritt:** dieselbe Rechnung für einen zweiten Typ — etwa
nichtlineare Hawkes-Prozesse oder Setting `pathjump` allgemein —, um zu sehen,
wieviel von Prop. `hawkesDcheck` strukturell ist und wieviel am Cluster hängt.

## Task 21 — Pfadabhängige (zufällige) Uhr — `geplant` *(2026-08-25)*

Ersetze die Uhr $q$ durch einen **Kern** $\mathsf q$ von $(F,\mathcal S)$ nach
$(\T,\mathcal T)$, so dass der Kompensator
$$C^g_t(\omega)=\int_{\langle0,t\rangle_\iota} g(u,\omega_u)\,\mathsf q(\omega,\dif u)$$
lautet. Das ist der Schritt zu den Semimartingal-Charakteristiken aus J&S Kap. II,
die das Manuskript durchgehend zitiert, aber nicht enthält.

### Was wirklich neu ist

Nur eine **singuläre** zufällige Uhr. Ist $\mathsf q(\omega,\dif u)=a_u(\omega)q(\dif u)$
absolutstetig gegen ein festes $q$, so ist das der pfadabhängige Integrand aus
Setting `pathjump` — bereits behandelt. Neu sind: Lokalzeit-Uhren, zufällige
Atome, zufällige Zeitwechsel.

**Ehrlicherweise:** *kein* Beispiel im jetzigen Manuskript braucht es.
Ex. `volterra`, `pathdepsemi` und `hawkes` sind alle absolutstetig. Task 21
rechtfertigt sich durch die Beispiele, die er **hinzufügt**, nicht durch
vorhandene.

### Designentscheidung, zuerst zu treffen

**Als Bündel, nicht als Ersatz.** Genau wie (T0)–(T4) und (E0)–(E3):

* **(Q0)** deterministische Uhr — Def. `clock`, der jetzige Zustand;
* **(Q1)** adaptierte zufällige Uhr: $\omega\mapsto\mathsf q(\omega,B)$ ist
  $\Filt^\circ_t$-messbar für $B\subseteq\langle0,t\rangle_\iota$;
* **(Q2)** prädiktable zufällige Uhr — was J&S Kap. II wirklich verlangt.

Grund für „Bündel statt Ersatz": §6 überlebt nicht und §5.2 braucht eine
Zusatzhypothese (s.u.), also darf (Q0) nicht verschwinden.

### Abschnittsweiser Audit

| Abschnitt | Verdikt |
|---|---|
| §2.2 Uhr | neue Def. + Adaptiertheitslemma. Die **Additivität** \eqref{eq:clockadd} überlebt wörtlich — sie ist die einzige Eigenschaft, die der Rest benutzt |
| §2.6 `compadapted` | überlebt; Fubini braucht nur die Kerneigenschaft. **Aber:** die Schranke $\lVert g\rVert q(\T_{\le u})$ wird zufällig, also ist die Menge $N^g_u$ auch für beschränktes $g$ nicht mehr ganz $\Omega$ |
| §3 `fddchar` | überlebt; ${}^*\Filt^X$ wird genauso gebildet |
| §4 càdlàg | **überlebt**, auch mit zufälligen Atomen: (R2) ist automatisch (monoton), (R3) folgt aus $\mathsf q((t,s])\downarrow0$ punktweise plus $E[\mathsf q(\T_{\le T})]<\infty$ |
| §5.1 | **unberührt** — erwähnt die Uhr nirgends (nachgeprüft) |
| §5.2 Markov-Schicht | braucht **Shift-Kovarianz** von $\mathsf q$; sonst ist die verschobene Uhr keine Funktion des verschobenen Pfades. Exaktes Analogon zu Q3/D21 („Shift-Invarianz von $q$ ⟺ Homogenität") |
| §5.3, §5.4 | unberührt |
| §6 Dualität | **fällt aus.** Man kann zwar auf $\bar q=E[\mathsf q]$ mitteln und die Dichte in $\gamma$ absorbieren — dann ist \eqref{eq:incrementrep} wieder deterministisch —, aber die **Balance-Bedingung** $\gamma_1=\gamma_2$ überlebt das Mitteln nicht. Ob es eine brauchbare Variante gibt: offen |
| §7 `absconv`, `clockchange` | überleben |
| §7.8 | `prop:atomaug` **fällt aus** (die Atome sind nicht mehr deterministisch), also wird **weak-strong convergence notwendig** — genau wie Rem. `augvsws` vorhersagt |
| §7.2 Dualer | fällt aus mit §6 bzw. mit der Shift-Invarianz in Lem. `dualsemigroup` |

### Die strukturelle Pointe

Mit (Q0) ist $|Y^{f,g}_t|\le\lVert f\rVert+\lVert g\rVert q(\T_{\le t})$
deterministisch beschränkt, und Thm. `uniqueness` kann sagen „alle
Integrierbarkeitsvorbehalte sind automatisch". Mit (Q1) ist das falsch. Damit
wird die **lokale** Theorie aus §5.3 nicht mehr optional, sondern primär — genau
das Phänomen, das Rem. `pathjumpprimary` schon für pfadabhängige Raten beschreibt
($E[N_t]<\infty$ war dort die Zusatzhypothese). Task 21 macht das strukturell
statt beispielhaft.

### Zwei Testobjekte

1. **Sticky Brownian motion.** Kompensator gegen $\dif t+\theta^{-1}\dif\ell^0_t$
   mit der Lokalzeit $\ell^0$ — die kanonische singuläre zufällige Uhr. Scharf
   als Test, weil das zugehörige SDE *keine* starke Lösung hat, das
   Martingalproblem aber wohlgestellt ist (Engelbert–Peskir, *Stochastics* **86**
   (2014), 993–1021). Prüft §4, §5.1 und §5.3 auf einmal.
2. **Uhr mit zufälligen Atomen.** Ein Sprungprozess, der nur an den Punkten eines
   unabhängigen Poissonprozesses springt: $\mathsf q(\omega,\cdot)$ = dessen
   Zählmaß. Elementar, und es ist das minimale Beispiel, an dem
   Thm. `absconvaug` scheitert und weak-strong gebraucht wird — das
   Zufalls-Gegenstück zu Ex. `invariance`.

### Reihenfolge und Umfang

1. §2.2 Def. + Lemma; §2.6 nachziehen  *(≈1,5 S.)*
2. §3 und §4 durchgehen, Integrierbarkeit explizit  *(≈1 S.)*
3. §5.2 Shift-Kovarianz; §5.1/§5.3/§5.4 nur Bemerkungen  *(≈1 S.)*
4. §6 und §7.2: Ausschluss mit Begründung (der $\bar q$-Reduktionsarbeit)  *(≈0,5 S.)*
5. §7.8: `prop:atomaug` scheitert, weak-strong wird notwendig  *(≈0,5 S.)*
6. Bündeltabelle, §1.3/§1.4, §8/§9  *(≈0,5 S.)*
7. Die zwei Testobjekte  *(≈2 S.)*

Etwa 7 Seiten, vergleichbar mit Task 18.

### Zuerst zu entscheiden

* (Q1) oder gleich (Q2)? Prädiktabilität ist das, was J&S braucht, aber auf einem
  Präorder ist „prädiktabel" nicht ohne Weiteres definiert. Vorschlag: (Q1)
  durchführen, (Q2) unter (T2b) als Verschärfung.
* Sticky BM ausführen oder zitieren? Vorschlag: Konstruktion zitieren, das
  Martingalproblem und die Verifikation von (R2)/(R3) ausführen.

## Task 22 — Submartingalprobleme (reflektierende Ränder) — `todo`

Rem. `inequalitystable` (→ D51) zeigt: Lem. `mixture`, `disint`, `restart`
gelten wörtlich, mit $\ge$ statt $=$ und nichtnegativer bestimmender Menge.
Offen ist allein das Eindeutigkeitskriterium — Def. `propagation` vergleicht
über Gleichheit und propagiert keine Ungleichung. Auszuführen wäre die
Stroock–Varadhan-Formulierung reflektierter Diffusionen als Testobjekt.


## Task 23 — §6: der gemischte Fall — `todo`

Nach D54 ist der Stand von §6:

| Uhr | Status |
|---|---|
| Haar (Lebesgue, Zählmaß) | bewiesen, `prop:haar` |
| atomlos, (T3) | bewiesen, `cor:atomless` — aber nur ein **Zeitwechsel** (D55) |
| rein atomar | symbolisch verifiziert, **nicht bewiesen**, `rem:atomicdual` |
| gemischt | **offen** |

Die beiden vorhandenen Argumente kombinieren sich nicht: der Zeitwechsel
scheitert an Atomen (`rem:atomsnotchange`, mit Gegenbeispiel), die
Linearalgebra der Atomrelationen hat keinen diffusen Gegenpart.

*Zur Einordnung (D55):* die Zeile „atomlos" ist billiger, als sie aussieht — unter
(T3) ist eine atomlose Uhr das Bild von Lebesgue unter $\tau$. Echten Inhalt hat
nur die Zeile „rein atomar", und nur sie führt über Lebesgue hinaus.

**Zwei Ansätze.** (a) Den atomaren Fall wirklich beweisen — die Relationen
$m_l\,\Delta_1F(k,l-1)=m_k\,\Delta_2F(k-1,l-1)$ sind ein lineares System, dessen
Lösungsraum die Konklusion enthalten sollte; Induktion über die Atome scheitert
bisher an ordnungsdichten Atommengen. (b) Approximation: eine gemischte Uhr
durch atomlose approximieren und die Stabilität von \eqref{eq:incrementrep}
unter dieser Approximation klären.

Nichts im Manuskript hängt daran — §7 benutzt Lebesgue-Uhren, §7.2 nur
\eqref{eq:clockadd}.


---

# Open questions

* **(Q1)** ~~(T1) or (T1') as the base assumption?~~ — **answered 2026-08-24:
  neither.** The base assumption is **(T0)**, a preorder. (T1′) is used at
  exactly one place in the whole manuscript, Thm. 5.7 (strong Markov), plus the
  localized statements — it is a local hypothesis, not a base. See D15.
  **Q1 and Q6 are one decision**, not two: both amount to asking how far the
  multiparameter case ($\mathbb{T} = [0,\infty)^d$, EK86 Chapter 6) is to be carried
  along. Answering "as far as possible" selects (T1') and the abstract additive $q$;
  answering "not at all" selects a linear order and a measure, and then (T1)/(T1')
  and Q6 both collapse. Settle this first — everything else in Task 1 follows.
* **(Q2)** ~~Does Thm. 4.1 require the clock $q$ to be atomless?~~ — **answered
  2026-08-24: no.** See decision D7 in `FORTSCHRITT.md`. The proof of Thm. 4.1
  goes through verbatim for an arbitrary locally finite $q$, provided the
  compensator is $\int_{(0,t]}$; the manuscript's "Lipschitz continuous" in Step 1
  is only the special case $q = \lambda$ and can be weakened to "has one-sided
  limits". Raises Q8.
* **(Q3)** ~~Does Thm. 5.1 need shift-invariance of $q$?~~ — **closed
  2026-08-24 (D21): no.** D12 answered "yes" for the narrow notion of shift
  stability; with shift *systems* (Task 2c) the shifted problem always exists and
  shift invariance of $q$ is merely the criterion for the Markov process to be
  *homogeneous*. Superseded reading of D12. Shift
  stability of $\mathbb{X}$ (Def. 5.4 of the manuscript) holds for $\mathbb{X}_A$
  *if and only if* $q$ is shift invariant. What remains open is only the
  cosmetic half: whether to *assume* shift invariance or to state the
  time-inhomogeneous version alongside. The (T4) half of Q3 also stands: the
  monoid structure is used through $\theta_r$ and cannot be avoided.
* **(Q4)** Should the semigroup route (EK86 4.4.1 / 4.4.4) come back in later?
  **Feller processes belong to this question**, not beside it: they are defined
  through a strongly continuous semigroup on $\hat{C}(E)$ and need local
  compactness, which D2 rejects. Asked and deferred 2026-08-24, see D30; if
  reopened, take Feller and 4.4.1/4.4.4 together as one package. Original
  wording: It
  was deliberately excluded; see Rem. 2.5 of the manuscript and decision D5 in
  `FORTSCHRITT.md`.
* **(Q5)** ~~Where do the Lean files live?~~ — **answered 2026-08-24.**
  `Journal/Blog/MartingaleProblem/` holds the manuscript (tex, pdf) together with
  `PLAN.md` and `FORTSCHRITT.md`; `Journal/Notes/MartingaleProblem/` is now empty
  and reserved for the Lean files. Task 3 is unblocked.
* **(Q6)** ~~Abstract additive interval function, or measure?~~ — **answered
  2026-08-24 (D9): a measure, on $\mathbb{T}$ itself.** The dichotomy was false —
  a measure keeps the poset case. Original wording:
  Compensator as an abstract additive interval function, or as a measure
  on $\mathbb{T}$? — see Task 1b. The first keeps the partially ordered case (and
  hence multiparameter indices) in reach, the second is closer to EK86, CPS23 and
  Mathlib.
* **(Q7)** ~~Does §7.2 really need the Skorokhod space?~~ — **answered
  2026-08-24: no.** See decision D8 in `FORTSCHRITT.md`. The abstract form detaches
  completely from Task 8; the Skorokhod space is needed only to *instantiate* it
  (for $\mathcal{B}(D_E) = \sigma(\pi_t)$ in the determining set, and for the continuity of
  the evaluation maps that produces the "countable complement $\Gamma$"
  hypothesis). Task order changed accordingly, see Tasks 8a/8b.
* **(Q8)** ~~$(0,t]$ or $[0,t)$?~~ — **answered 2026-08-24: both.** Def. 2.2 now
  defines the optional interval $(s,t] = \mathbb{T}_{\le t}\setminus\mathbb{T}_{\le s}$
  and the predictable interval $[s,t) = \mathbb{T}_{<t}\setminus\mathbb{T}_{<s}$,
  both additive, and Def. 3.5 carries a parameter
  $\iota \in \{\mathrm{o},\mathrm{p}\}$. The two part company at exactly two
  theorems: Thm. 4.3 needs $\iota=\mathrm{o}$, Prop. 6.2 needs
  $\iota=\mathrm{p}$. Everything else — including Lem. 6.1, the analytic core of
  §6 — uses only the additivity and is convention-agnostic. See D28.