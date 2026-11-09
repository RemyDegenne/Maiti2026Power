/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TauCeti.Probability.Independence.InfinitePi

/-!
# Finite windows of an i.i.d. sequence

`ProbabilityTheory.indepFun_prefix_window`: the first `T` coordinates of an i.i.d. sequence are
independent of any family of coordinates of index `≥ T`. It is Tau Ceti's
`indepFun_domRestrict_infinitePi` read through the two coordinate maps.

The joint law of finitely many distinct coordinates of an i.i.d. family is Mathlib's
`Measure.map_infinitePi_infinitePi_of_inj`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The first `T` coordinates of an i.i.d. sequence are independent of any family of coordinates
of index at least `T`. -/
lemma indepFun_prefix_window {T : ℕ} {J : Type*} {f : J → ℕ} (hf : ∀ p, T ≤ f p) :
    IndepFun (fun ω (t : Fin T) ↦ ω t) (fun ω (p : J) ↦ ω (f p))
      (Measure.infinitePi fun _ : ℕ ↦ μ) := by
  have hST : Disjoint (Set.Iio T) (Set.range f) := by
    rw [Set.disjoint_left]
    rintro _ h ⟨p, rfl⟩
    exact absurd (hf p) (not_le.2 h)
  exact (TauCeti.Probability.indepFun_domRestrict_infinitePi (fun _ : ℕ ↦ μ) hST).comp
    (Measurable.of_eval fun (t : Fin T) ↦ measurable_pi_apply (⟨t, t.2⟩ : Set.Iio T))
    (Measurable.of_eval fun p ↦ measurable_pi_apply (⟨f p, p, rfl⟩ : Set.range f))

end ProbabilityTheory
