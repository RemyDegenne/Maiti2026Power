/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Pinsker

/-!
# Pinsker's inequality for a single event, in real form

Tau Ceti's `TauCeti.two_mul_sq_measureReal_sub_le_klDiv` is **Pinsker's inequality**
`2 (μ A - ν A)² ≤ KL(μ ‖ ν)` for probability measures `μ ν` and a measurable set `A`. We record
its real form.

## Main results

* `InformationTheory.abs_sub_le_sqrt_klDiv`: `|μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2)`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {A : Set Ω}

/-- **Pinsker's inequality** for a single event, real form:
`|μ A - ν A| ≤ √(KL(μ ‖ ν) / 2)`. -/
lemma abs_sub_le_sqrt_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) (h : klDiv μ ν ≠ ∞) :
    |μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2) := by
  have := TauCeti.two_mul_sq_measureReal_sub_le_klDiv (μ := μ) (ν := ν) hA
  rw [ENNReal.ofReal_le_iff_le_toReal h] at this
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

end InformationTheory
