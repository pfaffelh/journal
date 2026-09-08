/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The countable product of kernels is Ionescu–Tulcea without memory

`ProbabilityTheory.Kernel.traj` composes a sequence of kernels each of which may read the whole
past.  A *product* of kernels over a common base point is the special case in which they read
only the base point.  This file records that specialisation, so that the statement "Mathlib has
the countable product of kernels" is a proof and not a description.
-/

open Finset MeasureTheory Preorder

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The countable product of Markov kernels over a common base, as a special case of the
Ionescu–Tulcea theorem: there is a Markov kernel `η` from `E` to `ℕ → E` whose zeroth coordinate
is the base point and whose `(n+1)`-st coordinate has law `K n y`. -/
theorem exists_kernel_pi_of_markov (K : ℕ → Kernel E E) [∀ n, IsMarkovKernel (K n)] :
    ∃ η : Kernel E (ℕ → E), IsMarkovKernel η ∧
      (∀ y, (η y).map (fun x ↦ x 0) = Measure.dirac y) ∧
      ∀ n y, (η y).map (fun x ↦ x (n + 1)) = K n y := by
  set κ : (n : ℕ) → Kernel ((i : Iic n) → E) E := fun n ↦
    (K n).comap (fun x ↦ x ⟨0, mem_Iic.2 (Nat.zero_le n)⟩) (measurable_pi_apply _) with hκ
  have hbase : Measurable (fun (y : E) (_ : Iic 0) ↦ y) :=
    measurable_pi_lambda _ fun _ ↦ measurable_id
  refine ⟨(Kernel.traj (X := fun _ ↦ E) κ 0).comap _ hbase, inferInstance, ?_, ?_⟩
  · intro y
    have h0 : (fun z : ℕ → E ↦ z 0)
        = (fun w : (i : Iic 0) → E ↦ w ⟨0, mem_Iic.2 le_rfl⟩) ∘ Preorder.frestrictLe 0 := rfl
    rw [Kernel.comap_apply, h0, ← Measure.map_map
      (measurable_pi_apply (X := fun _ : Iic 0 ↦ E) ⟨0, mem_Iic.2 le_rfl⟩)
      (measurable_frestrictLe 0), ← Kernel.map_apply _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe_of_le (le_refl 0), Kernel.deterministic_apply,
      Measure.map_dirac' (measurable_pi_apply _)]
    rfl
  · intro n y
    have h1 : (Kernel.traj (X := fun _ ↦ E) κ 0).map (fun x ↦ x (n + 1))
        = (κ n) ∘ₖ (Kernel.partialTraj (X := fun _ ↦ E) κ 0 n) := by
      rw [← Kernel.traj_comp_partialTraj (Nat.zero_le n), Kernel.map_comp,
        Kernel.map_traj_succ_self]
    rw [Kernel.comap_apply, ← Kernel.map_apply _ (measurable_pi_apply _), h1]
    ext s hs
    rw [Kernel.comp_apply' _ _ _ hs]
    have hmeas : Measurable fun w : (i : Iic 0) → E ↦
        K n (w ⟨0, mem_Iic.2 le_rfl⟩) s := (Kernel.measurable_coe _ hs).comp
      (measurable_pi_apply _)
    have hint : ∀ z : (i : Iic n) → E, κ n z s
        = (fun w : (i : Iic 0) → E ↦ K n (w ⟨0, mem_Iic.2 le_rfl⟩) s)
          (frestrictLe₂ (π := fun _ : ℕ ↦ E) (Nat.zero_le n) z) := by
      intro z
      simp [hκ, Kernel.comap_apply]
    rw [lintegral_congr hint, ← lintegral_map hmeas (measurable_frestrictLe₂ _),
      Kernel.partialTraj_map_frestrictLe₂_apply _ (Nat.zero_le n),
      Kernel.partialTraj_le (le_refl 0), Kernel.deterministic_apply, lintegral_dirac' _ hmeas]
    rfl

end ProbabilityTheory
