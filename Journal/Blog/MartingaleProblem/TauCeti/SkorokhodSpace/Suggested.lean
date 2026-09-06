/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Suggested signatures for the Skorokhod space roadmap

Prototypes only. Names and argument orders are suggestions; the statements are
the commitments. `sorry` marks a statement whose proof is the work, never an
empty proposition.

**Status: type-checked** with `lake env lean` against Mathlib `v4.33.1`, last on
2026-09-07.  Every declaration elaborates; the `sorry`s are the statements' own
proofs, which is what this file is for.

Since 2026-09-07 the whole of `TimeChange.lipConst` and `TimeChange.norm` is
proved: the attainment `lipschitzWith_lipConst`, `lipConst_one`,
`lipConst_of_subsingleton`, `lipConst_mul_le`, `one_le_max_lipConst`,
`norm_one`, `norm_inv`, `norm_nonneg`, `norm_mul_le`, and `normOn_one`.  Two statements had to
go first, and both were false.  `normOn_mul_le` --- the windowed norm is not
subadditive, see `not_normOn_mul_le` for the witness --- so Milestone 4 builds
its metric on the global `norm`, as Billingsley does.  And
`dist_le_of_normOn_le`, which is now `dist_le_of_norm_le` and asks the time
change to fix the base point; without that a translation refutes it.

Seven `sorry`s went on 2026-09-06: `isCompact_exhaustion`,
`monotoneOn_dist_basepoint` and
`IsCadlag.eq_of_eqOn_dense` carry proofs --- the last had to be corrected first,
its hypothesis was bare density, under which it is false ---, the `Group
(TimeChange ι)` instance is constructed, `TimeChange.lipConstOn` and
`TimeChange.normOn` are defined instead of being `sorry`, and
`TimeChange.normOn_inv` follows from `inv_inv` and `max_comm`.  A definition
whose body is `sorry` makes every theorem about it a statement about `sorryAx`,
which is the same trap as a statement that is `True`; the statements about
`normOn` became propositions about something only then.  Three errors that the
signature check
of the previous run could not see came out of the first run: `IsCadlag.measurable`
had no `MeasurableSpace ι`, `TimeChange.dist_le_of_normOn_le` used `Real.exp`
without importing it, and Milestone 6 spoke of measurable maps out of `D(ι, E)`
with no measurable structure on it.  The last is now declared, as the Borel
structure of the metric.

`Function.RightContinuous` and `IsCadlag` are **not** in Mathlib — a search of
`upstream/master` for `IsCadlag` returns nothing — so the earlier version of this
file, which used them without defining them, could not be elaborated at all.
They are restated here, verbatim from Milestone 2 of the roadmap, so that the
file stands against Mathlib alone; the intended source is
`RemyDegenne/brownian-motion`, `BrownianMotion/StochasticIntegral/Cadlag.lean`
(Apache 2.0), and that file is what should be reused.
-/

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal

/-! ## Milestone 1: the index -/

/-- A metric additive along a linear order. Together with `OrderTopology` and
`ProperSpace` this pins the index down to a closed subset of `ℝ`. -/
class AdditiveDist (α : Type*) [LinearOrder α] [PseudoMetricSpace α] : Prop where
  dist_add : ∀ {s t u : α}, s ≤ t → t ≤ u → dist s u = dist s t + dist t u

variable {ι : Type*} [LinearOrder ι] [MetricSpace ι] [OrderTopology ι]
  [AdditiveDist ι] [ProperSpace ι]

/-- The exhaustion by closed balls around a base point. -/
def exhaustion (t₀ : ι) (m : ℕ) : Set ι := Metric.closedBall t₀ m

omit [LinearOrder ι] [OrderTopology ι] [AdditiveDist ι] in
theorem isCompact_exhaustion (t₀ : ι) (m : ℕ) : IsCompact (exhaustion t₀ m) :=
  isCompact_closedBall t₀ m

omit [OrderTopology ι] [ProperSpace ι] in
/-- The metric is the difference of the length function to a base point.  It is
`AdditiveDist` alone that does this, neither the order topology nor properness. -/
theorem dist_eq_sub_of_le {t₀ s t : ι} (h₀s : t₀ ≤ s) (hst : s ≤ t) :
    dist s t = dist t₀ t - dist t₀ s := by
  have := AdditiveDist.dist_add (α := ι) h₀s hst
  linarith

omit [OrderTopology ι] [ProperSpace ι] in
/-- Again `AdditiveDist` alone, through `dist_eq_sub_of_le`. -/
theorem monotoneOn_dist_basepoint {t₀ : ι} :
    MonotoneOn (fun t => dist t₀ t) (Set.Ici t₀) := by
  intro s hs t _ hst
  have h : dist s t = dist t₀ t - dist t₀ s := dist_eq_sub_of_le (Set.mem_Ici.1 hs) hst
  have h' : (0 : ℝ) ≤ dist s t := dist_nonneg
  simp only
  linarith

/-- Definitional, but it does not fire through a `SetLike` hull: the lattice
`AddSubgroup.zmultiples h` needs its `Set` coercion, or this instance restated
for `SetLike` carriers. -/
instance instAdditiveDistSubtype {α : Type*} [LinearOrder α] [PseudoMetricSpace α]
    [AdditiveDist α] (s : Set α) : AdditiveDist s where
  dist_add {_ _ _} hab hbc := AdditiveDist.dist_add (α := α) hab hbc

/-- An index satisfying the four hypotheses is order isomorphic and isometric to
a closed subset of `ℝ`. -/
theorem exists_orderIso_isometry_real :
    ∃ (s : Set ℝ) (e : ι ≃o s), IsClosed s ∧ Isometry e := sorry

/-! ## Milestone 2: càdlàg functions

Neither predicate is in Mathlib. `Function.leftLim` and `Function.rightLim` are
(`Mathlib/Topology/Order/LeftRightLim.lean:50` and `:59`), and the two lemmas
that connect the structure to them, `tendsto_leftLim_of_tendsto` and
`ContinuousWithinAt.rightLim_eq`, live in the same file. -/

/-- Right continuity at every point. -/
def Function.RightContinuous {α β : Type*} [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] (f : α → β) : Prop :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

/-- Right continuous with left limits. -/
structure IsCadlag {α β : Type*} [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] (f : α → β) : Prop where
  right_continuous : Function.RightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

variable {E : Type*} [MetricSpace E]

/-- The set of points where the left limit differs from the value. -/
def leftJumpSet (f : ι → E) : Set ι := {x | Function.leftLim f x ≠ f x}

theorem countable_leftJumpSet {f : ι → E} (hf : IsCadlag f) :
    (leftJumpSet f).Countable := sorry

theorem IsCadlag.measurable [MeasurableSpace ι] [BorelSpace ι]
    [MeasurableSpace E] [BorelSpace E] {f : ι → E}
    (hf : IsCadlag f) : Measurable f := sorry

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- A càdlàg function is determined by its values on a set that is dense **from
the right**: every point of the index either lies in `D` or is approached by
points of `D` from above.

Density alone is not enough, and the statement under it is false as soon as the
index has a point that is right isolated without being isolated -- which
Milestone 1 allows, since it pins the index down to a *closed subset of* `ℝ` and
not to an interval.  Take `ι = [0,1] ∪ {2}`, `D = ([0,1) ∩ ℚ) ∪ {2}`, which is
dense, `f = 0` and `g = ` the indicator of `{1}`.  Both are càdlàg: at `1` the
filter `𝓝[>] 1` is `⊥`, so right continuity there says nothing, and at `2` so is
`𝓝[<] 2`.  They agree on `D` and differ at `1`.

The hypothesis below is what the proof uses, and it implies `Dense D`.  Neither
the order topology nor `AdditiveDist` nor properness enters, so they are
omitted. -/
theorem IsCadlag.eq_of_eqOn_dense {f g : ι → E} (hf : IsCadlag f) (hg : IsCadlag g)
    {D : Set ι} (hD : ∀ t : ι, t ∈ D ∨ (𝓝[D ∩ Set.Ioi t] t).NeBot) (h : EqOn f g D) :
    f = g := by
  funext t
  rcases hD t with ht | ht
  · exact h ht
  · have := ht
    have hf' : ContinuousWithinAt f (D ∩ Set.Ioi t) t :=
      (hf.right_continuous t).mono Set.inter_subset_right
    have hg' : ContinuousWithinAt g (D ∩ Set.Ioi t) t :=
      (hg.right_continuous t).mono Set.inter_subset_right
    have hfg : g =ᶠ[𝓝[D ∩ Set.Ioi t] t] f := by
      filter_upwards [self_mem_nhdsWithin] with x hx using (h hx.1).symm
    exact tendsto_nhds_unique hf' (Filter.Tendsto.congr' hfg hg')

/-! ## Milestones 3 and 4: time changes and the metric -/

/-- Bi-Lipschitz order isomorphisms of the index. -/
structure TimeChange (ι : Type*) [LinearOrder ι] [MetricSpace ι] where
  toOrderIso : ι ≃o ι
  lipschitz : ∃ C, LipschitzWith C toOrderIso
  lipschitz_symm : ∃ C, LipschitzWith C toOrderIso.symm

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- Two time changes with the same order isomorphism are equal: the other two
fields are propositions. -/
@[ext]
theorem TimeChange.ext {l l' : TimeChange ι} (h : l.toOrderIso = l'.toOrderIso) :
    l = l' := by
  cases l; cases l'; subst h; rfl

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.exists_lipschitzWith_trans {e e' : ι ≃o ι}
    (h : ∃ C, LipschitzWith C e) (h' : ∃ C, LipschitzWith C e') :
    ∃ C, LipschitzWith C (e.trans e') := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  exact ⟨C' * C, by simpa only [OrderIso.coe_trans] using hC'.comp hC⟩

/-- Composition and inversion make the time changes a group; this is what turns
`normOn` into a length function and gives the triangle inequality of the metric
below.  Multiplication is composition of functions, `l * l' = l ∘ l'`, which is
`OrderIso.trans` in the other order. -/
instance : Group (TimeChange ι) where
  mul l l' :=
    { toOrderIso := l'.toOrderIso.trans l.toOrderIso
      lipschitz := TimeChange.exists_lipschitzWith_trans l'.lipschitz l.lipschitz
      lipschitz_symm := by
        rw [OrderIso.symm_trans]
        exact TimeChange.exists_lipschitzWith_trans l.lipschitz_symm l'.lipschitz_symm }
  one :=
    { toOrderIso := OrderIso.refl ι
      lipschitz := ⟨1, LipschitzWith.id⟩
      lipschitz_symm := ⟨1, LipschitzWith.id⟩ }
  inv l :=
    { toOrderIso := l.toOrderIso.symm
      lipschitz := l.lipschitz_symm
      lipschitz_symm := by rw [OrderIso.symm_symm]; exact l.lipschitz }
  mul_assoc l l' l'' := TimeChange.ext rfl
  one_mul l := TimeChange.ext rfl
  mul_one l := TimeChange.ext rfl
  inv_mul_cancel l := TimeChange.ext (OrderIso.self_trans_symm l.toOrderIso)

/-- The least Lipschitz constant. Mathlib carries no least Lipschitz constant:
`LipschitzWith (K : ℝ≥0) (f : α → β)`
(`Mathlib/Topology/EMetricSpace/Lipschitz.lean`) is a `Prop`, and
`LipschitzWith.const` there is the theorem that a constant map is `0`-Lipschitz,
not a constant attached to a map. -/
noncomputable def TimeChange.lipConst (l : TimeChange ι) : ℝ≥0 :=
  sInf {K : ℝ≥0 | LipschitzWith K l.toOrderIso}

/-- The same constant computed on `exhaustion t₀ m` only. -/
noncomputable def TimeChange.lipConstOn (t₀ : ι) (m : ℕ) (l : TimeChange ι) : ℝ≥0 :=
  sInf {K : ℝ≥0 | LipschitzOnWith K l.toOrderIso (exhaustion t₀ m)}

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The infimum is attained. This is where `ι` being a metric space and not
merely an extended metric space is used: `edist s t ≠ ∞`, so the inequality
`edist (l s) (l t) ≤ K * edist s t` may be divided by `edist s t` and passes to
the infimum over the admissible `K`. -/
theorem TimeChange.lipschitzWith_lipConst (l : TimeChange ι) :
    LipschitzWith l.lipConst ⇑l.toOrderIso := by
  obtain ⟨K₀, hK₀⟩ := l.lipschitz
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have h0 : edist x y ≠ 0 := by simpa [edist_eq_zero] using hxy
  have hfin : edist x y ≠ ⊤ := edist_ne_top x y
  rw [← ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)]
  have hr : ((edist (l.toOrderIso x) (l.toOrderIso y) / edist x y).toNNReal : ℝ≥0∞)
      = edist (l.toOrderIso x) (l.toOrderIso y) / edist x y :=
    ENNReal.coe_toNNReal (ENNReal.div_ne_top (edist_ne_top _ _) h0)
  rw [← hr, ENNReal.coe_le_coe, TimeChange.lipConst]
  refine le_csInf ⟨K₀, hK₀⟩ fun K hK => ?_
  rw [← ENNReal.coe_le_coe, hr]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)).2 (hK x y)

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- On a subsingleton index every constant is admissible, so the least one is
`0`; this is the degenerate case that `Real.log 0 = 0` carries below. -/
theorem TimeChange.lipConst_of_subsingleton [Subsingleton ι] (l : TimeChange ι) :
    l.lipConst = 0 := by
  refine le_antisymm (csInf_le' ?_) zero_le
  show LipschitzWith (0 : ℝ≥0) ⇑l.toOrderIso
  intro a b
  simp [Subsingleton.elim a b]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- With two distinct points the set of admissible constants of the identity is
`Set.Ici 1`, so its infimum is `1`. -/
theorem TimeChange.lipConst_one [Nontrivial ι] : (1 : TimeChange ι).lipConst = 1 := by
  have hone : ∀ t : ι, (1 : TimeChange ι).toOrderIso t = t := fun _ => rfl
  have hmem : LipschitzWith 1 ⇑(1 : TimeChange ι).toOrderIso := by
    intro a b; simp [hone]
  rw [TimeChange.lipConst]
  refine le_antisymm (csInf_le' hmem) (le_csInf ⟨1, hmem⟩ fun K hK => ?_)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ι
  have h := hK x y
  simp only [hone] at h
  have h0 : edist x y ≠ 0 := by simpa [edist_eq_zero] using hxy
  have hfin : edist x y ≠ ⊤ := edist_ne_top x y
  refine ENNReal.one_le_coe_iff.1 ?_
  have := (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)).2 h
  rwa [ENNReal.div_self h0 hfin] at this

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- Submultiplicativity, from `LipschitzWith.comp` and the attainment above.
`l * l'` is `l ∘ l'`, so `OrderIso.coe_trans` turns the composite into one. -/
theorem TimeChange.lipConst_mul_le (l l' : TimeChange ι) :
    (l * l').lipConst ≤ l.lipConst * l'.lipConst := by
  have hcomp : ⇑(l * l').toOrderIso = ⇑l.toOrderIso ∘ ⇑l'.toOrderIso := by
    show ⇑(l'.toOrderIso.trans l.toOrderIso) = _
    rw [OrderIso.coe_trans]
  have hmem : LipschitzWith (l.lipConst * l'.lipConst) ⇑(l * l').toOrderIso := by
    rw [hcomp]
    exact l.lipschitzWith_lipConst.comp l'.lipschitzWith_lipConst
  exact csInf_le' hmem

/-- `log` of the larger of the two Lipschitz constants. This is Billingsley's
`‖λ‖`, and it is a **global** quantity: the windowed `normOn` below is not a
length function, see `TimeChange.not_normOn_mul_le`. -/
noncomputable def TimeChange.norm (l : TimeChange ι) : ℝ :=
  Real.log (max l.lipConst l⁻¹.lipConst)

/-- The same, computed on `exhaustion t₀ m`. It is a lower bound for `norm` and
nothing more; the metric of Milestone 4 uses `norm`. -/
noncomputable def TimeChange.normOn (t₀ : ι) (m : ℕ) (l : TimeChange ι) : ℝ :=
  Real.log (max (TimeChange.lipConstOn t₀ m l) (TimeChange.lipConstOn t₀ m l⁻¹))

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.norm_inv (l : TimeChange ι) : (l⁻¹).norm = l.norm := by
  rw [TimeChange.norm, TimeChange.norm, inv_inv, max_comm]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.normOn_inv (t₀ : ι) (m : ℕ) (l : TimeChange ι) :
    TimeChange.normOn t₀ m l⁻¹ = TimeChange.normOn t₀ m l := by
  rw [TimeChange.normOn, TimeChange.normOn, inv_inv, max_comm]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The two cases the proof has to distinguish, and they are the reason the
statement is true at all: on an `exhaustion t₀ m` with two distinct points the
set of admissible constants for the identity is `Set.Ici 1`, so `lipConstOn` is
`1` and its logarithm is `0`; on a one point exhaustion -- `m = 0` in a discrete
index -- every constant is admissible, `lipConstOn` is `0`, and `Real.log 0 = 0`
by Mathlib's convention.  The junk value of `Real.log` is what carries the
degenerate case, which is worth saying out loud rather than leaving to the
reader. -/
theorem TimeChange.normOn_one (t₀ : ι) (m : ℕ) :
    TimeChange.normOn t₀ m (1 : TimeChange ι) = 0 := by
  have hone : ∀ t : ι, (1 : TimeChange ι).toOrderIso t = t := fun _ => rfl
  have key : TimeChange.lipConstOn t₀ m (1 : TimeChange ι) = 0 ∨
      TimeChange.lipConstOn t₀ m (1 : TimeChange ι) = 1 := by
    rw [TimeChange.lipConstOn]
    by_cases hs : (exhaustion t₀ m).Subsingleton
    · refine Or.inl (le_antisymm (csInf_le' ?_) zero_le)
      show LipschitzOnWith (0 : ℝ≥0) ⇑(1 : TimeChange ι).toOrderIso (exhaustion t₀ m)
      intro a ha b hb
      simp [hone, hs ha hb]
    · obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hs
      have hmem : LipschitzOnWith 1 ⇑(1 : TimeChange ι).toOrderIso (exhaustion t₀ m) := by
        intro a _ b _
        simp [hone]
      refine Or.inr (le_antisymm (csInf_le' hmem) (le_csInf ⟨1, hmem⟩ fun K hK => ?_))
      have h := hK hx hy
      simp only [hone] at h
      have h0 : edist x y ≠ 0 := by simpa [edist_eq_zero] using hxy
      have hfin : edist x y ≠ ⊤ := edist_ne_top x y
      refine ENNReal.one_le_coe_iff.1 ?_
      have := (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)).2 h
      rwa [ENNReal.div_self h0 hfin] at this
  rw [TimeChange.normOn, inv_one, max_self]
  rcases key with h | h <;> rw [h] <;> simp

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
theorem TimeChange.norm_one : (1 : TimeChange ι).norm = 0 := by
  rw [TimeChange.norm, inv_one, max_self]
  rcases subsingleton_or_nontrivial ι with _ | _
  · rw [TimeChange.lipConst_of_subsingleton]; simp
  · rw [TimeChange.lipConst_one]; simp

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The quantity `norm` takes the logarithm of is at least `1` as soon as the
index has two points: `l` and `l⁻¹` compose to the identity, whose constant is
`1`, so the product of the two constants is at least `1`, hence so is the square
of their maximum. This is what makes the logarithm below well behaved. -/
theorem TimeChange.one_le_max_lipConst [Nontrivial ι] (l : TimeChange ι) :
    1 ≤ max l.lipConst l⁻¹.lipConst := by
  have h := TimeChange.lipConst_mul_le l l⁻¹
  rw [mul_inv_cancel, TimeChange.lipConst_one] at h
  have h2 : l.lipConst * l⁻¹.lipConst ≤
      max l.lipConst l⁻¹.lipConst * max l.lipConst l⁻¹.lipConst :=
    mul_le_mul' (le_max_left _ _) (le_max_right _ _)
  by_contra hc
  rw [not_le] at hc
  have h3 : (1 : ℝ) ≤ (max l.lipConst l⁻¹.lipConst : ℝ≥0) * (max l.lipConst l⁻¹.lipConst : ℝ≥0) := by
    exact_mod_cast h.trans h2
  have h4 : ((max l.lipConst l⁻¹.lipConst : ℝ≥0) : ℝ) < 1 := by exact_mod_cast hc
  nlinarith [NNReal.coe_nonneg (max l.lipConst l⁻¹.lipConst)]

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The norm is nonnegative. Milestone 4 takes a `max` of it with a supremum of
distances, so this is what makes that `max` the intended quantity.

The windowed `normOn` does **not** have this property, which is a second symptom
of the failure recorded at `not_normOn_mul_le`: `lipConstOn` measures `l` on the
window and `l⁻¹` on the window as well, not on the image of the window, so both
can be `1/2` at once.  On `ℝ` with `B 1 = [-1,1]`, let `l` have slope `1/2` on
`[-1,1]` and slope `2` on `[-6,-5]`, where it takes the values `[-1,1]`, and
slope `1` far out.  Then `lipConstOn 0 1 l = 1/2` and `lipConstOn 0 1 l⁻¹ = 1/2`,
so `normOn 0 1 l = -log 2 < 0`. -/
theorem TimeChange.norm_nonneg (l : TimeChange ι) : 0 ≤ l.norm := by
  rcases subsingleton_or_nontrivial ι with _ | _
  · simp [TimeChange.norm, TimeChange.lipConst_of_subsingleton]
  · rw [TimeChange.norm]
    refine Real.log_nonneg ?_
    exact_mod_cast TimeChange.one_le_max_lipConst l

omit [OrderTopology ι] [AdditiveDist ι] [ProperSpace ι] in
/-- The norm is a length function. This is the triangle inequality of the metric
of Milestone 4, and it holds for the **global** norm only. -/
theorem TimeChange.norm_mul_le (l l' : TimeChange ι) :
    (l * l').norm ≤ l.norm + l'.norm := by
  rcases subsingleton_or_nontrivial ι with _ | _
  · simp [TimeChange.norm, TimeChange.lipConst_of_subsingleton]
  simp only [TimeChange.norm]
  set M := max (l.lipConst : ℝ) (l⁻¹.lipConst : ℝ) with hM
  set M' := max (l'.lipConst : ℝ) (l'⁻¹.lipConst : ℝ) with hM'
  have h1 : (1 : ℝ) ≤ M := by
    have := TimeChange.one_le_max_lipConst l
    rw [hM]; exact_mod_cast this
  have h1' : (1 : ℝ) ≤ M' := by
    have := TimeChange.one_le_max_lipConst l'
    rw [hM']; exact_mod_cast this
  have hA : ((l * l').lipConst : ℝ) ≤ M * M' := by
    have h3 : (l * l').lipConst ≤
        max l.lipConst l⁻¹.lipConst * max l'.lipConst l'⁻¹.lipConst :=
      (TimeChange.lipConst_mul_le l l').trans
        (mul_le_mul' (le_max_left _ _) (le_max_left _ _))
    rw [hM, hM']; exact_mod_cast h3
  have hB : (((l * l')⁻¹).lipConst : ℝ) ≤ M * M' := by
    have h3 : ((l * l')⁻¹).lipConst ≤
        max l.lipConst l⁻¹.lipConst * max l'.lipConst l'⁻¹.lipConst := by
      rw [mul_inv_rev]
      calc (l'⁻¹ * l⁻¹).lipConst ≤ l'⁻¹.lipConst * l⁻¹.lipConst :=
            TimeChange.lipConst_mul_le _ _
        _ ≤ max l'.lipConst l'⁻¹.lipConst * max l.lipConst l⁻¹.lipConst :=
            mul_le_mul' (le_max_right _ _) (le_max_right _ _)
        _ = max l.lipConst l⁻¹.lipConst * max l'.lipConst l'⁻¹.lipConst := mul_comm _ _
    rw [hM, hM']; exact_mod_cast h3
  have hpos : (0 : ℝ) < max ((l * l').lipConst : ℝ) (((l * l')⁻¹).lipConst : ℝ) := by
    have h := TimeChange.one_le_max_lipConst (l * l')
    have h' : (1 : ℝ) ≤ max ((l * l').lipConst : ℝ) (((l * l')⁻¹).lipConst : ℝ) := by
      exact_mod_cast h
    linarith
  calc Real.log (max ((l * l').lipConst : ℝ) (((l * l')⁻¹).lipConst : ℝ))
      ≤ Real.log (M * M') := Real.log_le_log hpos (max_le hA hB)
    _ = Real.log M + Real.log M' := Real.log_mul (by linarith) (by linarith)

/-- **The windowed norm is not a length function.** Measuring the Lipschitz
constants on `exhaustion t₀ m` alone destroys subadditivity, because the inner
factor of a composite need not map the window into itself, and outside it the
outer factor is unconstrained.

The counterexample lives on `ι = ℝ` with `t₀ = 0` and `m = 1`, so
`exhaustion 0 1 = [-1,1]`. Let `l'` be `x ↦ 2 * x` and let `l` be the piecewise
linear order isomorphism that is the identity on `Set.Iic 1` and has slope `100`
on `Set.Ici 1`. Then `l` is the identity on `[-1,1]` and so is `l⁻¹`, whence
`normOn 0 1 l = log 1 = 0`, and `normOn 0 1 l' = log 2`. But
`(l * l') x = l (2 * x)` sends `1/2` to `1` and `1` to `101`, so every admissible
constant on `[-1,1]` is at least `200` and `normOn 0 1 (l * l') ≥ log 200`.
Since `log 200 > log 2 = normOn 0 1 l + normOn 0 1 l'`, the inequality fails, and
it fails by an amount that the outer factor's behaviour outside the window can
make arbitrarily large.

Milestone 4 therefore builds its metric on `TimeChange.norm`, as Billingsley
does: his `d°ₘ` truncates the *paths* to the window and measures the time change
globally. -/
theorem TimeChange.not_normOn_mul_le :
    ¬ ∀ (ι : Type) (_ : LinearOrder ι) (_ : MetricSpace ι) (_ : OrderTopology ι)
        (_ : AdditiveDist ι) (_ : ProperSpace ι) (t₀ : ι) (m : ℕ) (l l' : TimeChange ι),
        TimeChange.normOn t₀ m (l * l') ≤
          TimeChange.normOn t₀ m l + TimeChange.normOn t₀ m l' := sorry

/-- A time change of small norm moves the points of `exhaustion t₀ m` little.
This is the estimate that makes the metric separate points.

It needs the time change to **fix the base point**, and without that hypothesis
it is false: a translation of `ℝ` is an order isomorphism with `lipConst = 1` in
both directions, so its norm is `0`, while it moves every point by the same
arbitrary amount.  Billingsley gets the anchor for free, because his `Λ` consists
of the increasing homeomorphisms of `[0,∞)` onto itself and they all fix `0`; on
a two sided index it has to be imposed.  The time changes fixing `t₀` are a
subgroup, so nothing else in Milestones 3 and 4 changes. -/
theorem TimeChange.dist_le_of_norm_le (t₀ : ι) (m : ℕ) {l : TimeChange ι} {γ : ℝ}
    (h₀ : l.toOrderIso t₀ = t₀) (h : l.norm ≤ γ) {t : ι} (ht : t ∈ exhaustion t₀ m) :
    dist (l.toOrderIso t) t ≤ (Real.exp γ - 1) * (2 * m) := sorry

/-- Càdlàg paths from `ι` to `E`. -/
structure SkorokhodSpace (ι E : Type*) [LinearOrder ι] [TopologicalSpace ι]
    [TopologicalSpace E] where
  toFun : ι → E
  isCadlag : IsCadlag toFun

@[inherit_doc] notation "D(" ι ", " E ")" => SkorokhodSpace ι E

noncomputable instance : MetricSpace D(ι, E) := sorry

instance [PolishSpace E] : CompleteSpace D(ι, E) := sorry
instance [PolishSpace E] : TopologicalSpace.SeparableSpace D(ι, E) := sorry
instance [PolishSpace E] : PolishSpace D(ι, E) := sorry

/-- Evaluation is continuous exactly at the paths that do not jump at `t`. -/
theorem SkorokhodSpace.continuousAt_eval {t : ι} {f : D(ι, E)} :
    ContinuousAt (fun g : D(ι, E) => g.toFun t) f ↔
      Function.leftLim f.toFun t = f.toFun t := sorry

/-! ## Milestone 6: the Borel structure

The measurable structure on `D(ι, E)` is the Borel one of the metric above, so
it is declared here rather than assumed; everything in this section is stated
against it. -/

noncomputable instance : MeasurableSpace D(ι, E) := borel _
instance : BorelSpace D(ι, E) := ⟨rfl⟩

variable [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

theorem SkorokhodSpace.measurableEmbedding_piDense {D : Set ι} (hD : D.Countable)
    (hD' : Dense D) :
    MeasurableEmbedding (fun f : D(ι, E) => fun t : D => f.toFun t) := sorry

theorem SkorokhodSpace.borel_eq_iSup_comap_eval :
    (borel D(ι, E)) =
      ⨆ t : ι, MeasurableSpace.comap (fun f : D(ι, E) => f.toFun t) inferInstance :=
  sorry

/-! ## Milestone 7: the modulus and compactness -/

/-- The càdlàg modulus on `exhaustion t₀ m`. -/
noncomputable def SkorokhodSpace.modulus (t₀ : ι) (m : ℕ) (f : D(ι, E)) (δ : ℝ) : ℝ := sorry

theorem SkorokhodSpace.tendsto_modulus (t₀ : ι) (m : ℕ) (f : D(ι, E)) :
    Tendsto (SkorokhodSpace.modulus t₀ m f) (𝓝[>] 0) (𝓝 0) := sorry

theorem SkorokhodSpace.isCompact_closure_iff (t₀ : ι) (A : Set D(ι, E)) :
    IsCompact (closure A) ↔ ∀ m : ℕ,
      IsCompact (closure {x | ∃ f ∈ A, ∃ t ∈ exhaustion t₀ m, f.toFun t = x}) ∧
      Tendsto (fun δ => ⨆ f ∈ A, SkorokhodSpace.modulus t₀ m f δ) (𝓝[>] 0) (𝓝 0) := sorry
