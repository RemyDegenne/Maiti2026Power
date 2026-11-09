/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Maiti2026Power.ForLMLExplore.Analysis.InnerProductSpace.EuclideanMatrix
public import Maiti2026Power.ForLMLExplore.Analysis.InnerProductSpace.OrthonormalBasisSubmodule
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.Gaussian.Sum
public import TauCeti.Probability.Distributions.Gaussian.Symmetry
public import TauCeti.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Distributions.Chi.Gaussian
public import TauCeti.Probability.Distributions.ChiSquared.Basic

/-!
# Transformations and moments of multivariate Gaussian measures

Tau Ceti proves that the multivariate Gaussian measures `multivariateGaussian μ S` on
`EuclideanSpace ℝ ι` are stable under convolution
(`TauCeti.Probability.multivariateGaussian_conv_multivariateGaussian`), affine maps given by
matrices (`TauCeti.Probability.map_affine_multivariateGaussian`,
`TauCeti.Probability.map_add_smul_multivariateGaussian`) and, when centered, negation
(`ProbabilityTheory.IsGaussian.map_neg_eq_self`). This file states the centered linear cases in
the forms used in this project and proves moment bounds.

## Main statements

* `multivariateGaussian_zero_map_toEuclideanCLM`, `multivariateGaussian_zero_map_toEuclideanLin`:
  the image of `N(0, S)` by the linear map with matrix `M` is `N(0, M S Mᵀ)`.
* `multivariateGaussian_zero_map_smul`: the image of `N(0, S)` by `x ↦ c • x` is
  `N(0, c ^ 2 • S)`.
* `integral_norm_sq_multivariateGaussian`: `E‖G‖² = tr S` for `G ~ N(0, S)`.
* `integral_norm_stdGaussian_le`: `E‖g‖ ≤ √d` for a standard Gaussian vector of dimension `d`.
-/

@[expose] public section

open MeasureTheory Matrix WithLp Complex
open scoped RealInnerProductSpace

namespace ProbabilityTheory

section charFun

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {mE : MeasurableSpace E} [OpensMeasurableSpace E] {mF : MeasurableSpace F} [BorelSpace F]

/-- The characteristic function of the image of a measure by a continuous linear map `L` between
Hilbert spaces is the characteristic function of the measure evaluated at `L† t`. -/
lemma charFun_map_clm (μ : Measure E) (L : E →L[ℝ] F) (t : F) :
    charFun (μ.map L) t = charFun μ (ContinuousLinearMap.adjoint L t) := by
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [ContinuousLinearMap.adjoint_inner_right]

end charFun

section multivariateGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- The image of the centered multivariate Gaussian measure `N(0, S)` by the linear map with
matrix `M` is `N(0, M S Mᵀ)`. -/
lemma multivariateGaussian_zero_map_toEuclideanCLM (hS : S.PosSemidef) (M : Matrix ι ι ℝ) :
    (multivariateGaussian 0 S).map (toEuclideanCLM (𝕜 := ℝ) M) =
      multivariateGaussian 0 (M * S * Mᵀ) := by
  have h : ⇑(toEuclideanCLM (𝕜 := ℝ) M) = ⇑(toEuclideanLin M) := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  simpa [h] using TauCeti.Probability.map_affine_multivariateGaussian 0 hS M 0

/-- The image of the centered multivariate Gaussian measure `N(0, S)` on `EuclideanSpace ℝ ι` by
the linear map with (rectangular) matrix `M` is `N(0, M S Mᵀ)`. -/
lemma multivariateGaussian_zero_map_toEuclideanLin {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hS : S.PosSemidef) (M : Matrix κ ι ℝ) :
    (multivariateGaussian 0 S).map (LinearMap.toContinuousLinearMap (toEuclideanLin M)) =
      multivariateGaussian 0 (M * S * Mᵀ) := by
  simpa using TauCeti.Probability.map_affine_multivariateGaussian 0 hS M 0

/-- The image of the centered multivariate Gaussian measure `N(0, S)` by `x ↦ c • x` is
`N(0, c ^ 2 • S)`. -/
lemma multivariateGaussian_zero_map_smul (hS : S.PosSemidef) (c : ℝ) :
    (multivariateGaussian 0 S).map (fun x ↦ c • x) = multivariateGaussian 0 (c ^ 2 • S) := by
  simpa using TauCeti.Probability.map_add_smul_multivariateGaussian 0 hS 0 c

end multivariateGaussian

section translation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Translating a centered multivariate Gaussian by `μ` gives `N(μ, S)`. -/
lemma multivariateGaussian_zero_map_const_add (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    (multivariateGaussian 0 S).map (fun v ↦ μ + v) = multivariateGaussian μ S := by
  rw [multivariateGaussian, multivariateGaussian, Measure.map_map (measurable_const_add μ)
    (by fun_prop)]
  simp [Function.comp_def]

/-- `N(μ, S)` shifted by `-μ` is `N(0, S)`. -/
lemma multivariateGaussian_map_sub_const (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    (multivariateGaussian μ S).map (fun v ↦ v - μ) = multivariateGaussian 0 S := by
  rw [← multivariateGaussian_zero_map_const_add μ S, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

end translation

section Moments

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- `E‖G‖² = tr S` for a centered Gaussian vector `G ~ N(0, S)`. -/
lemma integral_norm_sq_multivariateGaussian (hS : S.PosSemidef) :
    ∫ x, ‖x‖ ^ 2 ∂(multivariateGaussian 0 S) = S.trace := by
  rw [TauCeti.integral_norm_sq_eq_norm_integral_sq_add_trace_covMatrix (multivariateGaussian 0 S)
    IsGaussian.memLp_two_id, TauCeti.Probability.covMatrix_multivariateGaussian 0 hS,
    integral_id_multivariateGaussian]
  simp

/-- `E‖G‖ ≤ √(tr S)` for a centered Gaussian vector `G ~ N(0, S)`. -/
lemma integral_norm_le_sqrt_trace_multivariateGaussian (hS : S.PosSemidef) :
    ∫ x, ‖x‖ ∂(multivariateGaussian 0 S) ≤ √S.trace := by
  rw [← integral_norm_sq_multivariateGaussian hS,
    Real.le_sqrt (integral_nonneg fun _ ↦ norm_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)]
  have hL2 : MemLp (fun x : EuclideanSpace ℝ ι ↦ ‖x‖) 2 (multivariateGaussian 0 S) :=
    (IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)).norm
  have h := variance_eq_sub hL2
  have h0 := variance_nonneg (fun x : EuclideanSpace ℝ ι ↦ ‖x‖) (multivariateGaussian 0 S)
  simp only [Pi.pow_apply] at h
  linarith

section StdGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `E‖g‖ ≤ √d` for a standard Gaussian vector `g` of a `d`-dimensional inner product space. -/
lemma integral_norm_stdGaussian_le :
    ∫ x, ‖x‖ ∂(stdGaussian E) ≤ √(Module.finrank ℝ E) := by
  have hsq : ∫ x, ‖x‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
    have h := congrArg (fun ν : Measure ℝ ↦ ∫ x, x ∂ν)
      (TauCeti.Probability.stdGaussian_map_norm_sq E)
    rwa [integral_map (by fun_prop) (by fun_prop),
      TauCeti.Probability.integral_id_chiSquaredMeasure (by positivity)] at h
  rw [← hsq,
    Real.le_sqrt (integral_nonneg fun _ ↦ norm_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)]
  have hL2 : MemLp (fun x : E ↦ ‖x‖) 2 (stdGaussian E) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm
  have h := variance_eq_sub hL2
  have h0 := variance_nonneg (fun x : E ↦ ‖x‖) (stdGaussian E)
  simp only [Pi.pow_apply] at h
  linarith

end StdGaussian

end Moments

end ProbabilityTheory
