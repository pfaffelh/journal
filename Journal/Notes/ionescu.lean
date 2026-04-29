import Mathlib

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Dependent composition of kernels: `κ` followed by a kernel `η` whose input may also depend
on the parameter of `κ`. Definitionally the second projection of the composition product. -/
noncomputable def compDep
    (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] :
    Kernel α γ :=
  Kernel.snd (κ ⊗ₖ η)

/-- `compDep` evaluated at a point is the integral of the second kernel. -/
lemma compDep_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {s : Set γ} (hs : MeasurableSet s) :
    compDep κ η a s = ∫⁻ b, η (a, b) s ∂(κ a) := by
  rw [compDep, snd_apply' _ _ hs, compProd_apply (measurable_snd hs)]
  rfl

/-- Auxiliary kernel: pair the second component of the input with the output of `η`,
defined as `(deterministic Prod.snd ∥ₖ η) ∘ₖ copy (α × β)`. -/
noncomputable def compProdShort_aux (η : Kernel (α × β) γ) [IsSFiniteKernel η] :
    Kernel (α × β) (β × γ) :=
  (Kernel.deterministic Prod.snd measurable_snd ∥ₖ η) ∘ₖ Kernel.copy (α × β)

instance (η : Kernel (α × β) γ) [IsSFiniteKernel η] :
    IsSFiniteKernel (compProdShort_aux η) := by
  unfold compProdShort_aux; infer_instance

/-- Pointwise form of `compProdShort_aux`: pushforward of `η ab` along `Prod.mk ab.2`. -/
lemma compProdShort_aux_apply (η : Kernel (α × β) γ) [IsSFiniteKernel η] (ab : α × β) :
    compProdShort_aux η ab = (η ab).map fun c => (ab.2, c) := by
  rw [compProdShort_aux, comp_apply, copy_apply, Measure.dirac_bind (Kernel.measurable _),
    parallelComp_apply, deterministic_apply, Measure.dirac_prod]

/-- Short definition of `compProd` via dependent composition. -/
noncomputable def compProdShort
    (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] :
    Kernel α (β × γ) :=
  compDep κ (compProdShort_aux η)

/-- `compProdShort` agrees with the Mathlib definition `κ ⊗ₖ η`. -/
theorem compProdShort_eq_compProd (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] :
    compProdShort κ η = κ ⊗ₖ η := by
  ext a s hs
  simp_rw [compProdShort, compDep, snd_apply' _ _ hs, compProd_apply (measurable_snd hs), compProd_apply hs, compProdShort_aux_apply, ← Measure.map_apply measurable_prodMk_left hs]
  rfl

end ProbabilityTheory.Kernel
