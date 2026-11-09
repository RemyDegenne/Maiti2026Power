/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import LMLExplore.Probability.Distributions.Gaussian.Real

/-!
# Sums and averages of independent Gaussian variables

* `hasLaw_const_add_const_mul_sum_pi_gaussianReal`: under the product of `s` standard Gaussians,
  `m + c * ∑ ℓ, e ℓ` has law `N(m, c² s)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- Under the product of `s` standard Gaussians, `m + c * ∑ ℓ, e ℓ` has law `N(m, c² s)`. -/
lemma hasLaw_const_add_const_mul_sum_pi_gaussianReal {s : ℕ} (m c : ℝ) :
    HasLaw (fun e : Fin s → ℝ ↦ m + c * ∑ ℓ, e ℓ)
      (gaussianReal m (‖c‖₊ ^ 2 * s)) (Measure.pi fun _ : Fin s ↦ gaussianReal 0 1) := by
  have hc : NNReal.mk (c ^ 2) (sq_nonneg c) = ‖c‖₊ ^ 2 := by
    apply NNReal.eq
    simp [Real.norm_eq_abs, sq_abs]
  have h_indep : iIndepFun (fun (ℓ : Fin s) (e : Fin s → ℝ) ↦ e ℓ)
      (Measure.pi fun _ : Fin s ↦ gaussianReal 0 1) :=
    iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  have hsum := h_indep.hasLaw_sum_gaussianReal (m := fun _ ↦ 0) (v := fun _ ↦ 1)
    (fun ℓ ↦ ⟨(measurable_pi_apply ℓ).aemeasurable,
      (measurePreserving_eval (fun _ : Fin s ↦ gaussianReal 0 1) ℓ).map_eq⟩) Finset.univ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_zero, nsmul_eq_mul,
    mul_one] at hsum
  have h1 : HasLaw (fun e : Fin s → ℝ ↦ c * ∑ ℓ, e ℓ) (gaussianReal (c * 0) (‖c‖₊ ^ 2 * s))
      (Measure.pi fun _ : Fin s ↦ gaussianReal 0 1) := by
    have := HasLaw.comp ⟨(measurable_const_mul c).aemeasurable, gaussianReal_map_const_mul c⟩ hsum
    rw [hc] at this
    refine this.congr (ae_of_all _ fun e ↦ ?_)
    simp
  have h2 := HasLaw.comp ⟨(measurable_const_add m).aemeasurable, gaussianReal_map_const_add m⟩ h1
  simp only [mul_zero, zero_add] at h2
  exact h2

end ProbabilityTheory
