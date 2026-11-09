/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TauCeti.Probability.Distributions.Chi.Gaussian
public import Maiti2026Power.ForLMLExplore.Probability.GaussianSquareMGF

/-!
# The squared norm of a standard Gaussian vector

The chi-squared distribution with `d` degrees of freedom is Tau Ceti's
`TauCeti.Probability.chiSquaredMeasure d`, and the law of the squared norm of a standard Gaussian
vector of a `d`-dimensional real inner product space is `chiSquaredMeasure d`
(`TauCeti.Probability.stdGaussian_map_norm_sq`). This is what justifies calling `‖g‖² - d` a
centered chi-square variable in `GaussianSquareMGF.lean`.

## Main results

* `chiSquaredMeasure d` is a probability measure for `d : ℕ` (an instance);
* `integrable_exp_mul_norm_sq_stdGaussian`: `exp (t ‖g‖²)` is integrable for `t < 1/2`;
* `mgf_norm_sq_stdGaussian`: the moment generating function of `‖g‖²` is that of
  `chiSquaredMeasure d`.
-/

@[expose] public section

open MeasureTheory Real TauCeti.Probability

namespace ProbabilityTheory

instance (d : ℕ) : IsProbabilityMeasure (chiSquaredMeasure d) :=
  isProbabilityMeasure_chiSquaredMeasure d.cast_nonneg

section StdGaussian

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `exp (t ‖∑ i, x i • b i‖²) = ∏ i, exp (t xᵢ²)` in an orthonormal basis `b`. -/
lemma exp_mul_norm_sum_smul_sq_eq_prod (b : OrthonormalBasis ι ℝ E) (t : ℝ) (x : ι → ℝ) :
    exp (t * ‖∑ i, x i • b i‖ ^ 2) = ∏ i, exp (t * x i ^ 2) := by
  rw [b.norm_sum_smul_sq, Finset.mul_sum, Real.exp_sum]

/-- For `t < 1/2`, `exp (t ‖g‖²)` is integrable for a standard Gaussian vector. -/
lemma integrable_exp_mul_norm_sq_stdGaussian {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun g ↦ exp (t * ‖g‖ ^ 2)) (stdGaussian E) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (stdOrthonormalBasis ℝ E),
    integrable_map_measure (by fun_prop) (measurable_sum_smul_orthonormalBasis _).aemeasurable]
  simp_rw [Function.comp_def, exp_mul_norm_sum_smul_sq_eq_prod]
  exact Integrable.fintype_prod fun _ ↦
    integrable_exp_mul_sq_gaussianReal 0 1 (by push_cast; linarith)

/-- **The squared norm of a standard Gaussian vector of a `d`-dimensional inner product space has
the moment generating function of the chi-squared distribution with `d` degrees of freedom.** -/
lemma mgf_norm_sq_stdGaussian (t : ℝ) :
    mgf (fun g ↦ ‖g‖ ^ 2) (stdGaussian E) t
      = mgf id (chiSquaredMeasure (Module.finrank ℝ E)) t := by
  rw [← stdGaussian_map_norm_sq E, mgf_id_map (by fun_prop)]

end StdGaussian

end ProbabilityTheory
