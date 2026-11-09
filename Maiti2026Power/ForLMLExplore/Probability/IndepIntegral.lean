/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of inner products with a bounded function

If `W` is an integrable random vector and `f` is a bounded measurable function of `V`, then
`⟪f (V ω), W ω⟫` is integrable (`integrable_inner_comp`). When moreover `V` is independent of `W`
and `W` is centered, the integral is zero: that is Mathlib's `IndepFun.integral_bilin_comp_comp`
with `B := innerSL ℝ`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω 𝓥 E : Type*} {mΩ : MeasurableSpace Ω} {m𝓥 : MeasurableSpace 𝓥}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} {V : Ω → 𝓥} {W : Ω → E} {f : 𝓥 → E} {C : ℝ}

/-- `⟪f (V ω), W ω⟫` is integrable when `W` is integrable and `f` is bounded and measurable. -/
lemma integrable_inner_comp (hV : AEMeasurable V P) (hf : Measurable f) (hC : ∀ v, ‖f v‖ ≤ C)
    (hW : Integrable W P) :
    Integrable (fun ω ↦ ⟪f (V ω), W ω⟫) P := by
  refine (hW.norm.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun ω ↦ ?_)
  · exact ((hf.comp_aemeasurable hV).aestronglyMeasurable.inner hW.aestronglyMeasurable)
  · rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))

end ProbabilityTheory
