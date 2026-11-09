/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal bases of a subspace, seen in the ambient space

For an orthonormal basis `b` of a subspace `V` of an inner product space `E` over `𝕜`:

* `OrthonormalBasis.sum_inner_coe_smul_coe`: `∑ i, ⟪b i, x⟫ • b i = x` for `x ∈ V`;
* `OrthonormalBasis.sum_conj_inner_coe_mul_inner_coe`: `∑ i, conj ⟪b i, x⟫ * ⟪b i, y⟫ = ⟪x, y⟫`
  for `x ∈ V` and any `y ∈ E` (Parseval), and its real form
  `OrthonormalBasis.sum_inner_coe_mul_inner_coe`.

We also record `OrthonormalBasis.norm_sum_smul_sq`: `‖∑ i, c i • b i‖ ^ 2 = ∑ i, c i ^ 2` for an
orthonormal basis `b` of a real inner product space (the coordinates of `∑ i, c i • b i` are the
`c i`: Mathlib's `OrthonormalBasis.sum_repr_symm` and `Orthonormal.inner_right_fintype`).
-/

@[expose] public section

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]
  {V : Submodule 𝕜 E} {x : E}

/-- Expansion of `x ∈ V` in an orthonormal basis of `V`, in the ambient space. -/
lemma sum_inner_coe_smul_coe (b : OrthonormalBasis ι 𝕜 V) (hx : x ∈ V) :
    ∑ i, ⟪(b i : E), x⟫_𝕜 • (b i : E) = x := by
  have h := congrArg Subtype.val (b.sum_repr' ⟨x, hx⟩)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] using h

/-- Parseval-type identity: for `x ∈ V` and any `y`,
`∑ i, conj ⟪b i, x⟫ * ⟪b i, y⟫ = ⟪x, y⟫`. -/
lemma sum_conj_inner_coe_mul_inner_coe (b : OrthonormalBasis ι 𝕜 V) (hx : x ∈ V) (y : E) :
    ∑ i, (starRingEnd 𝕜) ⟪(b i : E), x⟫_𝕜 * ⟪(b i : E), y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  conv_rhs => rw [← b.sum_inner_coe_smul_coe hx]
  rw [sum_inner]
  simp_rw [inner_smul_left]

/-- Parseval-type identity over `ℝ`: for `x ∈ V` and any `y`,
`∑ i, ⟪b i, x⟫ ⟪b i, y⟫ = ⟪x, y⟫`. -/
lemma sum_inner_coe_mul_inner_coe {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] {V : Submodule ℝ E} {x : E} (b : OrthonormalBasis ι ℝ V) (hx : x ∈ V) (y : E) :
    ∑ i, ⟪(b i : E), x⟫_ℝ * ⟪(b i : E), y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simpa using b.sum_conj_inner_coe_mul_inner_coe hx y

/-- The squared norm of a vector expanded in an orthonormal basis is the sum of the squares of its
coordinates. -/
lemma norm_sum_smul_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : OrthonormalBasis ι ℝ F) (c : ι → ℝ) : ‖∑ i, c i • b i‖ ^ 2 = ∑ i, c i ^ 2 := by
  rw [show ∑ i, c i • b i = b.repr.symm (WithLp.toLp 2 c) from b.sum_repr_symm _,
    LinearIsometryEquiv.norm_map, EuclideanSpace.real_norm_sq_eq]

end OrthonormalBasis
