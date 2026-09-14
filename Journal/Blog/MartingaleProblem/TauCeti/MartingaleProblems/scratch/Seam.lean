/-
Scratch for the seam between Milestone 4 and Milestone 6.
Developed separately from `Suggested.lean`; see the run report of 2026-09-14.
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Scratch

/-- **From bounded integrals to the law.**  Two finite measures whose push forwards integrate
every bounded measurable real function alike are equal as measures. -/
theorem measure_map_eq_of_forall_integral_eq
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {g : Ω → E} {g' : Ω' → E} (hg : Measurable g) (hg' : Measurable g')
    (h : ∀ f : E → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
      ∫ ω, f (g ω) ∂P = ∫ ω, f (g' ω) ∂P') :
    P.map g = P'.map g' := by
  ext s hs
  have hf : Measurable (s.indicator (fun _ : E ↦ (1 : ℝ))) :=
    measurable_const.indicator hs
  have hb : ∀ x : E, |s.indicator (fun _ : E ↦ (1 : ℝ)) x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have key := h _ hf hb
  have e1 : ∀ ω : Ω, s.indicator (fun _ : E ↦ (1 : ℝ)) (g ω)
      = (g ⁻¹' s).indicator (fun _ : Ω ↦ (1 : ℝ)) ω := by
    intro ω; by_cases hx : g ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx,
      Set.mem_preimage]
  have e2 : ∀ ω : Ω', s.indicator (fun _ : E ↦ (1 : ℝ)) (g' ω)
      = (g' ⁻¹' s).indicator (fun _ : Ω' ↦ (1 : ℝ)) ω := by
    intro ω; by_cases hx : g' ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx,
      Set.mem_preimage]
  simp only [e1, e2] at key
  rw [integral_indicator_const (1 : ℝ) (hs.preimage hg),
    integral_indicator_const (1 : ℝ) (hs.preimage hg')] at key
  simp only [smul_eq_mul, mul_one] at key
  rw [Measure.map_apply hg hs, Measure.map_apply hg' hs]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 key

/-! ### Joint measurability of a right continuous coordinate process -/

/-- The dyadic approximation of `u` from above at resolution `2⁻ⁿ`.

`Nat.ceil` and not `Nat.floor`: `Nat.measurable_floor` carries `[IsStrictOrderedRing R]` and
`ℝ≥0` is a semiring, so it is not available here, while `Nat.measurable_ceil` has no such
hypothesis. -/
noncomputable def dyad (n : ℕ) (u : ℝ≥0) : ℝ≥0 := ((⌈(2 : ℝ≥0) ^ n * u⌉₊ : ℕ) : ℝ≥0) / 2 ^ n

theorem le_dyad (n : ℕ) (u : ℝ≥0) : u ≤ dyad n u := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  rw [dyad, le_div_iff₀ h2, mul_comm]
  exact Nat.le_ceil ((2 : ℝ≥0) ^ n * u)

theorem dyad_lt (n : ℕ) (u : ℝ≥0) : dyad n u < u + (1 / 2 : ℝ≥0) ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  rw [dyad, div_lt_iff₀ h2]
  have hce : (⌈(2 : ℝ≥0) ^ n * u⌉₊ : ℝ≥0) < (2 : ℝ≥0) ^ n * u + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hrw : (u + (1 / 2 : ℝ≥0) ^ n) * 2 ^ n = (2 : ℝ≥0) ^ n * u + 1 := by
    rw [add_mul, div_pow, one_pow, div_mul_cancel₀ _ (by positivity), mul_comm u]
  rw [hrw]
  exact hce

variable {F E : Type*} [MeasurableSpace F] [MeasurableSpace E]

/-- Every path is constant on a right neighbourhood of every time.  For a state space carrying
the discrete topology this is right continuity of the paths; it is the form in which a step
path process satisfies it. -/
def RightLocallyConstant (π : ℝ≥0 → F → E) : Prop :=
  ∀ (f : F) (u : ℝ≥0), ∃ ε : ℝ≥0, 0 < ε ∧ ∀ v, u ≤ v → v < u + ε → π v f = π u f

/-- **The coordinate process of a right continuous path space is jointly measurable.**  The
approximation `dyad n` takes countably many values, so each stage is jointly measurable by
`measurable_from_prod_countable_right`, and right continuity makes the stages eventually equal
to the limit. -/
theorem measurable_uncurry_of_rightLocallyConstant {π : ℝ≥0 → F → E}
    (hπ : ∀ t, Measurable (π t)) (hrc : RightLocallyConstant π)
    {h : E → ℝ} (hh : Measurable h) :
    Measurable fun p : ℝ≥0 × F ↦ h (π p.1 p.2) := by
  -- the `n`-th stage, read through the countable index of the dyadic grid
  have hstage : ∀ n : ℕ, Measurable fun p : ℝ≥0 × F ↦ h (π (dyad n p.1) p.2) := by
    intro n
    have hcnt : Measurable fun q : ℕ × F ↦ h (π ((q.1 : ℝ≥0) / 2 ^ n) q.2) :=
      measurable_from_prod_countable_right fun k ↦ hh.comp (hπ ((k : ℝ≥0) / 2 ^ n))
    have hscale : Measurable fun u : ℝ≥0 ↦ (2 : ℝ≥0) ^ n * u :=
      measurable_const.mul measurable_id
    have hceil : Measurable fun u : ℝ≥0 ↦ ⌈(2 : ℝ≥0) ^ n * u⌉₊ := Nat.measurable_ceil.comp hscale
    have hpair : Measurable fun p : ℝ≥0 × F ↦ ((⌈(2 : ℝ≥0) ^ n * p.1⌉₊ : ℕ), p.2) :=
      (hceil.comp measurable_fst).prodMk measurable_snd
    exact hcnt.comp hpair
  refine measurable_of_tendsto_metrizable hstage ?_
  rw [tendsto_pi_nhds]
  rintro ⟨u, f⟩
  obtain ⟨ε, hε, hconst⟩ := hrc f u
  obtain ⟨n₀, hn₀⟩ := NNReal.exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ≥0) < 1)
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
  have hsmall : (1 / 2 : ℝ≥0) ^ n < ε :=
    lt_of_le_of_lt (pow_le_pow_right_of_le_one' (by norm_num) hn) hn₀
  rw [hconst (dyad n u) (le_dyad n u)
    (lt_trans (dyad_lt n u) (by gcongr))]

end Scratch
