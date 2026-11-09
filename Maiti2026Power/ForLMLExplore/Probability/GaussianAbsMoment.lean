/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.ForLMLExplore.Probability.MultivariateGaussian
public import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# The absolute moments of a Gaussian vector and a lower bound on its expected norm

* `integral_abs_eval_multivariateGaussian`: `E|Yᵢ| = √(2 Sᵢᵢ / π)` for `Y ~ N(0, S)`, from Tau
  Ceti's `integral_abs_gaussianReal` (`E|Z| = √(2 v / π)` for `Z ~ N(0, v)`);
* `sum_mul_sqrt_diag_le_integral_norm_multivariateGaussian`: for `Y ~ N(0, S)` and nonnegative
  weights `c` with `∑ cᵢ² ≤ 1`, `E‖Y‖ ≥ ∑ cᵢ E|Yᵢ| = √(2/π) ∑ cᵢ √(Sᵢᵢ)`, by the pointwise
  Cauchy–Schwarz inequality `∑ cᵢ |yᵢ| ≤ ‖y‖`.
-/

@[expose] public section

open MeasureTheory Real

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- `E|Yᵢ| = √(2 Sᵢᵢ / π)` for `Y ~ N(0, S)`. -/
lemma integral_abs_eval_multivariateGaussian (hS : S.PosSemidef) (i : ι) :
    ∫ x, |x i| ∂multivariateGaussian 0 S = √(2 * S i i / π) := by
  have h : MeasurePreserving (fun x : EuclideanSpace ℝ ι ↦ x i) (multivariateGaussian 0 S)
      (gaussianReal 0 (S i i).toNNReal) := by
    simpa using measurePreserving_eval_multivariateGaussian (μ := 0) hS (i := i)
  have := integral_map (μ := multivariateGaussian 0 S) h.measurable.aemeasurable
    (f := fun y : ℝ ↦ |y|) (by fun_prop)
  rw [← this, h.map_eq, TauCeti.Probability.integral_abs_gaussianReal]
  simp [Real.coe_toNNReal _ hS.diag_nonneg]

/-- **Lower bound on the expected norm of a Gaussian vector**: for `Y ~ N(0, S)` and
nonnegative weights `c` with `∑ cᵢ² ≤ 1`, `√(2/π) ∑ cᵢ √(Sᵢᵢ) = ∑ cᵢ E|Yᵢ| ≤ E‖Y‖`. -/
lemma sum_mul_sqrt_diag_le_integral_norm_multivariateGaussian (hS : S.PosSemidef) {c : ι → ℝ}
    (hc0 : ∀ i, 0 ≤ c i) (hc : ∑ i, c i ^ 2 ≤ 1) :
    √(2 / π) * ∑ i, c i * √(S i i) ≤ ∫ x, ‖x‖ ∂multivariateGaussian 0 S := by
  have hpt : ∀ x : EuclideanSpace ℝ ι, ∑ i, c i * |x i| ≤ ‖x‖ := by
    intro x
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c fun i ↦ |x i|
    have h2 : ∑ i, |x i| ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [sq_abs]
    have h3 : (∑ i, c i * |x i|) ^ 2 ≤ ‖x‖ ^ 2 := by
      calc (∑ i, c i * |x i|) ^ 2 ≤ (∑ i, c i ^ 2) * ∑ i, |x i| ^ 2 := h1
        _ ≤ 1 * ‖x‖ ^ 2 := by rw [h2]; gcongr
        _ = ‖x‖ ^ 2 := one_mul _
    exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hc0 i) (abs_nonneg _))
      (norm_nonneg _) two_ne_zero).1 h3
  have hint : ∀ i, Integrable (fun x : EuclideanSpace ℝ ι ↦ |x i|) (multivariateGaussian 0 S) :=
    fun i ↦ ((IsGaussian.memLp_dual _ (EuclideanSpace.proj i) 2 (by simp)).integrable
      one_le_two).abs
  calc √(2 / π) * ∑ i, c i * √(S i i)
      = ∑ i, c i * ∫ x, |x i| ∂multivariateGaussian 0 S := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [integral_abs_eval_multivariateGaussian hS i, show 2 * S i i / π = 2 / π * S i i by ring,
          Real.sqrt_mul (by positivity)]
        ring
    _ = ∫ x, ∑ i, c i * |x i| ∂multivariateGaussian 0 S := by
        rw [integral_finsetSum _ fun i _ ↦ (hint i).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ ∫ x, ‖x‖ ∂multivariateGaussian 0 S :=
        integral_mono (integrable_finsetSum _ fun i _ ↦ (hint i).const_mul _)
          IsGaussian.integrable_id.norm hpt

end ProbabilityTheory
