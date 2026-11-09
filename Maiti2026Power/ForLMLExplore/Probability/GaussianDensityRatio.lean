/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Density of a shifted Gaussian with respect to the standard Gaussian

The law `N(m, 1)` is `N(0, 1).withDensity (y ↦ exp (y m - m² / 2))`: this is Tau Ceti's
`TauCeti.Probability.gaussianReal_tilted_mul` (the exponential tilt of `N(0, 1)` by `y ↦ m y` is
`N(m, 1)`), with the normalizing constant `exp (m² / 2)` from `mgf_id_gaussianReal`.

* `measurable_gaussianDensityRatio`: joint measurability of the density ratio in `(m, y)`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- Joint measurability of the density ratio in `(m, y)`. -/
lemma measurable_gaussianDensityRatio :
    Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (rexp (p.2 * p.1 - p.1 ^ 2 / 2)) := by
  fun_prop

end ProbabilityTheory
