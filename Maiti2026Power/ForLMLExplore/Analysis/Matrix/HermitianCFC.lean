/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.Matrix.FunctionalCalculus

/-!
# Inverses and positivity of functions of a Hermitian matrix

For a Hermitian matrix `A` with eigenvalues `λ i`, the continuous functional calculus gives
`cfc f A = U diag(f (λ i)) U*`, whose trace is `∑ i, f (λ i)` (Tau Ceti's
`Matrix.IsHermitian.trace_cfc`). We record:

* for a Hermitian matrix `A` over `𝕜` and `l : ℝ`: `A - l • 1 = cfc (· - l) A`
  (`Matrix.IsHermitian.sub_smul_one_eq_cfc`), its inverse is `cfc (· - l)⁻¹ A` when `l` is not in
  the spectrum (`Matrix.IsHermitian.inv_sub_smul_one_eq_cfc`);
* `A - l • 1` is positive definite iff `l < x` on the spectrum
  (`Matrix.IsHermitian.posDef_sub_smul_one_iff`); the positive semidefinite case is Mathlib's
  `algebraMap_le_iff_le_spectrum`, since `algebraMap ℝ _ l = l • 1`;
* for a real symmetric matrix `B`, the trace of the square of `(B - l • 1)⁻¹` is the sum
  `∑ i, (λ i - l)⁻¹ ^ 2` (`Matrix.IsHermitian.trace_inv_sub_smul_one_sq`); the trace of
  `(B - l • 1)⁻¹` itself is Tau Ceti's `Matrix.IsHermitian.trace_inv_sub_smul_one`.

Together these express "the smallest eigenvalue of `A` is larger than `l`" as the spectral
condition `∀ x ∈ spectrum ℝ A, l < x`, without choosing an ordering of the eigenvalues.

## TODO

The trace identity `trace_inv_sub_smul_one_sq` is stated for real symmetric matrices only (its
real-valued right-hand side is what the barrier argument of the rounding procedure consumes);
over `𝕜` the same identity holds with the sum cast to `𝕜`, as in `trace_cfc`.
-/

@[expose] public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

section RCLike

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} {l : ℝ}

/-- Every real function is continuous on the (finite) spectrum of a matrix. -/
lemma continuousOn_spectrum_real (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) :=
  A.finite_real_spectrum.continuousOn f

/-- `A - l • 1 = cfc (· - l) A` for a Hermitian matrix `A`. -/
lemma IsHermitian.sub_smul_one_eq_cfc (hA : A.IsHermitian) (l : ℝ) :
    A - l • 1 = cfc (fun x ↦ x - l) A := by
  rw [cfc_sub _ _ A (continuousOn_spectrum_real _ _) (continuousOn_spectrum_real _ _), cfc_id' ℝ A,
    cfc_const l A, Algebra.algebraMap_eq_smul_one]

/-- `(A - l • 1)⁻¹ = cfc (· - l)⁻¹ A` for a Hermitian matrix `A` and `l` outside its
spectrum. -/
lemma IsHermitian.inv_sub_smul_one_eq_cfc (hA : A.IsHermitian) (hl : ∀ x ∈ spectrum ℝ A, x ≠ l) :
    (A - l • 1)⁻¹ = cfc (fun x ↦ (x - l)⁻¹) A := by
  rw [hA.sub_smul_one_eq_cfc, nonsing_inv_eq_ringInverse,
    ← cfc_inv (a := A) (f := fun x ↦ x - l) (fun x hx ↦ sub_ne_zero.2 (hl x hx))
      (continuousOn_spectrum_real _ _) hA.isSelfAdjoint]

/-- `A - l • 1` is positive definite iff `l < x` for every `x` in the spectrum of the Hermitian
matrix `A`. -/
lemma IsHermitian.posDef_sub_smul_one_iff (hA : A.IsHermitian) :
    (A - l • 1).PosDef ↔ ∀ x ∈ spectrum ℝ A, l < x := by
  constructor
  · intro h x hx
    have hx' : x - l ∈ spectrum ℝ (A - l • 1) := by
      rw [hA.sub_smul_one_eq_cfc, cfc_map_spectrum _ A hA.isSelfAdjoint
        (continuousOn_spectrum_real _ _)]
      exact ⟨x, hx, rfl⟩
    exact sub_pos.1 (h.isStrictlyPositive.spectrum_pos hx')
  · intro h
    have hle : l • (1 : Matrix n n 𝕜) ≤ A := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact (algebraMap_le_iff_le_spectrum hA.isSelfAdjoint).2 fun x hx ↦ (h x hx).le
    refine (le_iff.1 hle).posDef_iff_isUnit.2 ?_
    rw [hA.sub_smul_one_eq_cfc, isUnit_cfc_iff _ A (continuousOn_spectrum_real _ _)]
    exact fun x hx ↦ sub_ne_zero.2 (h x hx).ne'

end RCLike

section real

variable {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℝ} {l : ℝ}

/-- `tr ((B - l • 1)⁻¹ * (B - l • 1)⁻¹) = ∑ i, (λ i - l)⁻¹ ^ 2` for a symmetric matrix `B` with
eigenvalues `λ i` and `l` outside its spectrum. -/
lemma IsHermitian.trace_inv_sub_smul_one_sq (hB : B.IsHermitian)
    (hl : ∀ x ∈ spectrum ℝ B, x ≠ l) :
    ((B - l • 1)⁻¹ * (B - l • 1)⁻¹).trace = ∑ i, (hB.eigenvalues i - l)⁻¹ ^ 2 := by
  rw [hB.inv_sub_smul_one_eq_cfc hl, ← _root_.cfc_mul _ _ B (continuousOn_spectrum_real _ _)
    (continuousOn_spectrum_real _ _), hB.trace_cfc]
  simp_rw [sq, RCLike.ofReal_real_eq_id, id_eq]

end real

end Matrix
