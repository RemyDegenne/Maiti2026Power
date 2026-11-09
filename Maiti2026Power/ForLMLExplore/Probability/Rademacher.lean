/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Integration
public import TauCeti.Probability.Distributions.Rademacher
public import LMLExplore.Probability.Distributions.Bernoulli
public import Maiti2026Power.ForLMLExplore.Probability.SubgaussianSquare

/-!
# Rademacher vectors

The law of a uniform random sign is Tau Ceti's `TauCeti.Probability.rademacherMeasure`; since its
definition is not exposed, `rademacherMeasure_eq_bernoulliMeasure` records that it is the Bernoulli
law `Ber(-1, 1, 1/2)`.

* `rademacherVecMeasure ι`: the law of a Rademacher vector in `ι → ℝ`, i.e. i.i.d. uniform signs;
* `hasSubgaussianMGF_sum_mul_rademacherVecMeasure`: the linear form `∑ i, ε i * θ i` is
  sub-Gaussian with constant `‖θ‖²` (Hoeffding's lemma coordinatewise);
* `integral_sq_sum_mul_rademacherVecMeasure`: its second moment is `‖θ‖²`;
* `hasSubexponentialMGF_sq_sum_mul_sub_rademacherVecMeasure`: its centered square
  `(∑ i, ε i * θ i)² - ‖θ‖²` is sub-exponential with parameters `(4 ‖θ‖⁴, 4 ‖θ‖²)`;
* `uniformBoolVec ι`: the law of a vector of i.i.d. uniform Booleans, each coordinate
  `Ber(false, true, 1/2)`; its image by `signVec` is `rademacherVecMeasure ι`.
-/

@[expose] public section

open MeasureTheory Real Finset TauCeti.Probability
open scoped NNReal

namespace ProbabilityTheory

section Rademacher

variable {ι : Type*} [Fintype ι]

/-- The law of a Rademacher vector in `ι → ℝ`: i.i.d. uniform signs. -/
noncomputable def rademacherVecMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ ↦ rademacherMeasure

instance : IsProbabilityMeasure (rademacherVecMeasure ι) := by
  unfold rademacherVecMeasure
  infer_instance

lemma iIndepFun_eval_rademacherVecMeasure :
    iIndepFun (fun i (ε : ι → ℝ) ↦ ε i) (rademacherVecMeasure ι) :=
  iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id

lemma map_eval_rademacherVecMeasure (i : ι) :
    (rademacherVecMeasure ι).map (fun ε ↦ ε i) = rademacherMeasure :=
  (measurePreserving_eval (fun _ : ι ↦ rademacherMeasure) i).map_eq

/-- Tau Ceti's Rademacher law is the Bernoulli law `Ber(-1, 1, 1/2)`. -/
lemma rademacherMeasure_eq_bernoulliMeasure :
    rademacherMeasure = Ber((-1 : ℝ), 1, ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩) := by
  rw [rademacherMeasure_eq, bernoulliMeasure_def]
  congr 2
  ext
  norm_num

/-- A uniform random sign lies in `[-1, 1]`. -/
lemma ae_rademacherMeasure_mem_Icc : ∀ᵐ x ∂rademacherMeasure, x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [rademacherMeasure_eq_bernoulliMeasure]
  exact (LMLExplore.ae_mem_uIcc_bernoulliMeasure (-1 : ℝ) 1 _).mono fun _ hx ↦ by
    rwa [Set.uIcc_of_le (by norm_num)] at hx

lemma ae_rademacherVecMeasure_mem_Icc (i : ι) :
    ∀ᵐ ε ∂rademacherVecMeasure ι, ε i ∈ Set.Icc (-1 : ℝ) 1 := by
  refine ae_of_ae_map (measurable_pi_apply i).aemeasurable ?_
  rw [map_eval_rademacherVecMeasure]
  exact ae_rademacherMeasure_mem_Icc

lemma integral_eval_rademacherVecMeasure (i : ι) : ∫ ε, ε i ∂rademacherVecMeasure ι = 0 := by
  rw [← integral_id_rademacherMeasure, ← map_eval_rademacherVecMeasure i,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]

lemma integral_eval_sq_rademacherVecMeasure (i : ι) :
    ∫ ε, ε i ^ 2 ∂rademacherVecMeasure ι = 1 := by
  have h : ∫ x, x ^ 2 ∂rademacherMeasure = 1 := by simp
  rw [← h, ← map_eval_rademacherVecMeasure i,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]

lemma integral_eval_mul_eval_rademacherVecMeasure [DecidableEq ι] (i j : ι) :
    ∫ ε, ε i * ε j ∂rademacherVecMeasure ι = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    simpa only [sq] using integral_eval_sq_rademacherVecMeasure i
  · have hind : IndepFun (fun ε : ι → ℝ ↦ ε i) (fun ε ↦ ε j) (rademacherVecMeasure ι) :=
      iIndepFun_eval_rademacherVecMeasure.indepFun hij
    have := IndepFun.integral_mul_eq_mul_integral hind
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, integral_eval_rademacherVecMeasure, zero_mul]

lemma integrable_eval_mul_eval_rademacherVecMeasure (i j : ι) (θ : ι → ℝ) :
    Integrable (fun ε : ι → ℝ ↦ ε i * θ i * (ε j * θ j)) (rademacherVecMeasure ι) := by
  refine Integrable.of_bound (by fun_prop) (|θ i| * |θ j|) ?_
  filter_upwards [ae_rademacherVecMeasure_mem_Icc i, ae_rademacherVecMeasure_mem_Icc j]
    with ε hi hj
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  have h1 : |ε i| ≤ 1 := abs_le.2 hi
  have h2 : |ε j| ≤ 1 := abs_le.2 hj
  calc |ε i| * |θ i| * (|ε j| * |θ j|) ≤ 1 * |θ i| * (1 * |θ j|) := by gcongr
    _ = |θ i| * |θ j| := by ring

lemma integrable_eval_rademacherVecMeasure (i : ι) :
    Integrable (fun ε : ι → ℝ ↦ ε i) (rademacherVecMeasure ι) := by
  have h := integrable_rademacherMeasure (id : ℝ → ℝ)
  rw [← map_eval_rademacherVecMeasure i] at h
  exact (integrable_map_measure (f := fun ε : ι → ℝ ↦ ε i) (μ := rademacherVecMeasure ι)
    measurable_id.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h

lemma integrable_eval_mul_const_rademacherVecMeasure (i : ι) (a : ℝ) :
    Integrable (fun ε : ι → ℝ ↦ ε i * a) (rademacherVecMeasure ι) :=
  (integrable_eval_rademacherVecMeasure i).mul_const a

/-- A Rademacher linear form is centered. -/
lemma integral_sum_mul_rademacherVecMeasure (θ : ι → ℝ) :
    ∫ ε, ∑ i, ε i * θ i ∂rademacherVecMeasure ι = 0 := by
  rw [integral_finsetSum _ fun i _ ↦ integrable_eval_mul_const_rademacherVecMeasure i (θ i)]
  simp_rw [integral_mul_const, integral_eval_rademacherVecMeasure, zero_mul, Finset.sum_const_zero]

/-- Second moment of a Rademacher linear form: `E[(∑ i, ε i * θ i)²] = ∑ i, θ i ^ 2`. -/
lemma integral_sq_sum_mul_rademacherVecMeasure (θ : ι → ℝ) :
    ∫ ε, (∑ i, ε i * θ i) ^ 2 ∂rademacherVecMeasure ι = ∑ i, θ i ^ 2 := by
  classical
  have hint := integrable_eval_mul_eval_rademacherVecMeasure (ι := ι)
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j θ]
  simp_rw [integral_finsetSum _ fun j _ ↦ hint _ j θ]
  have h : ∀ i j, ∫ ε, ε i * θ i * (ε j * θ j) ∂rademacherVecMeasure ι
      = θ i * θ j * (if i = j then 1 else 0) := by
    intro i j
    rw [← integral_eval_mul_eval_rademacherVecMeasure, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ε ↦ ?_)
    ring
  simp_rw [h]
  simp [mul_ite, Finset.sum_ite_eq]

/-- **Rademacher linear forms are sub-Gaussian**: `∑ i, ε i * θ i` has a sub-Gaussian MGF with
constant `∑ i, ‖θ i‖₊ ^ 2`. -/
lemma hasSubgaussianMGF_sum_mul_rademacherVecMeasure (θ : ι → ℝ) :
    HasSubgaussianMGF (fun ε ↦ ∑ i, ε i * θ i) (∑ i, ‖θ i‖₊ ^ 2) (rademacherVecMeasure ι) := by
  have h_indep : iIndepFun (fun i (ε : ι → ℝ) ↦ ε i * θ i) (rademacherVecMeasure ι) :=
    iIndepFun_pi (X := fun i x ↦ x * θ i) fun i ↦ by fun_prop
  refine HasSubgaussianMGF.sum_of_iIndepFun h_indep (s := Finset.univ) fun i _ ↦ ?_
  have hI : HasSubgaussianMGF (fun x : ℝ ↦ x * θ i) ((‖|θ i| - -|θ i|‖₊ / 2) ^ 2)
      rademacherMeasure := by
    refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (by fun_prop) ?_ ?_
    · filter_upwards [ae_rademacherMeasure_mem_Icc] with x hx
      have : |x * θ i| ≤ |θ i| := by
        rw [abs_mul]
        calc |x| * |θ i| ≤ 1 * |θ i| := by
              gcongr
              exact abs_le.2 hx
          _ = |θ i| := one_mul _
      exact abs_le.1 this
    · rw [integral_mul_const, integral_id_rademacherMeasure, zero_mul]
  have e : (‖|θ i| - -|θ i|‖₊ / 2 : ℝ≥0) = ‖θ i‖₊ := by
    apply NNReal.coe_injective
    push_cast
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by positivity)]
    ring
  rw [e, ← map_eval_rademacherVecMeasure i] at hI
  exact HasSubgaussianMGF.of_map (X := fun x : ℝ ↦ x * θ i) (Y := fun ε : ι → ℝ ↦ ε i)
    (μ := rademacherVecMeasure ι) (measurable_pi_apply i).aemeasurable (by exact hI)

/-- **Rademacher linear forms are sub-Gaussian**, Euclidean form: for `θ ∈ ℝ^d`,
`∑ i, ε i * θ i` has a sub-Gaussian MGF with constant `‖θ‖²`. -/
lemma hasSubgaussianMGF_sum_mul_rademacherVecMeasure' (θ : EuclideanSpace ℝ ι) :
    HasSubgaussianMGF (fun ε ↦ ∑ i, ε i * θ i) (‖θ‖₊ ^ 2) (rademacherVecMeasure ι) := by
  have := hasSubgaussianMGF_sum_mul_rademacherVecMeasure (fun i ↦ θ i)
  rwa [EuclideanSpace.nnnorm_eq, NNReal.sq_sqrt]

/-- **The centered square of a Rademacher linear form is sub-exponential**: for `θ ∈ ℝ^d` with
`r = ‖θ‖`, `(∑ i, ε i * θ i)² - r²` has sub-exponential parameters `(4 r⁴, 4 r²)`. -/
lemma hasSubexponentialMGF_sq_sum_mul_sub_rademacherVecMeasure (θ : EuclideanSpace ℝ ι) :
    HasSubexponentialMGF (fun ε ↦ (∑ i, ε i * θ i) ^ 2 - ‖θ‖ ^ 2) (4 * ‖θ‖ ^ 4) (4 * ‖θ‖ ^ 2)
      (rademacherVecMeasure ι) := by
  have h := (hasSubgaussianMGF_sum_mul_rademacherVecMeasure' θ).hasSubexponentialMGF_sq_sub (by
    rw [integral_sq_sum_mul_rademacherVecMeasure (fun i ↦ θ i), ← EuclideanSpace.real_norm_sq_eq]
    push_cast
    rfl)
  have e1 : ((‖θ‖₊ ^ 2 : ℝ≥0) : ℝ) = ‖θ‖ ^ 2 := by push_cast; rfl
  rw [e1] at h
  exact h.mono (le_of_eq (by ring)) le_rfl

lemma inner_toLp_eq_sum (ε : ι → ℝ) (θ : EuclideanSpace ℝ ι) :
    inner ℝ (WithLp.toLp 2 ε) θ = ∑ i, ε i * θ i := by
  simp [PiLp.inner_apply, mul_comm]

end Rademacher

end ProbabilityTheory

namespace ProbabilityTheory

section BoolSeed

/-- The sign of a Boolean: `true ↦ 1`, `false ↦ -1`. -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

lemma measurable_signOf : Measurable signOf := measurable_of_countable _

variable {ι : Type*} [Fintype ι]

/-- The law of a vector of i.i.d. uniform Booleans: each coordinate has the Bernoulli law
`Ber(false, true, 1/2)`. -/
noncomputable def uniformBoolVec (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi fun _ ↦ Ber(false, true, ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩)

instance : IsProbabilityMeasure (uniformBoolVec ι) := by
  unfold uniformBoolVec
  infer_instance

/-- The sign vector of a Boolean vector. -/
def signVec (u : ι → Bool) : ι → ℝ := fun i ↦ signOf (u i)

omit [Fintype ι] in
lemma measurable_signVec : Measurable (signVec (ι := ι)) :=
  Measurable.of_eval fun i ↦ measurable_signOf.comp (measurable_pi_apply i)

lemma uniformBoolVec_map_signVec : (uniformBoolVec ι).map signVec = rademacherVecMeasure ι := by
  unfold uniformBoolVec rademacherVecMeasure signVec
  rw [Measure.pi_map_pi (fun _ ↦ measurable_signOf.aemeasurable)]
  congr 1
  funext
  rw [map_bernoulliMeasure' _ _ measurable_signOf, rademacherMeasure_eq_bernoulliMeasure]
  rfl

/-- **The centered square of a Rademacher linear form is sub-exponential**, Boolean-seed form:
for `θ ∈ ℝ^d` with `r = ‖θ‖`, `(∑ i, signOf (u i) * θ i)² - r²` has sub-exponential parameters
`(4 r⁴, 4 r²)` under `uniformBoolVec ι`. -/
lemma hasSubexponentialMGF_sq_sum_signOf_mul_sub_uniformBoolVec (θ : EuclideanSpace ℝ ι) :
    HasSubexponentialMGF (fun u : ι → Bool ↦ (∑ i, signOf (u i) * θ i) ^ 2 - ‖θ‖ ^ 2)
      (4 * ‖θ‖ ^ 4) (4 * ‖θ‖ ^ 2) (uniformBoolVec ι) := by
  have h := hasSubexponentialMGF_sq_sum_mul_sub_rademacherVecMeasure θ
  rw [← uniformBoolVec_map_signVec] at h
  exact HasSubexponentialMGF.of_map (X := fun ε : ι → ℝ ↦ (∑ i, ε i * θ i) ^ 2 - ‖θ‖ ^ 2)
    (Y := signVec) (μ := uniformBoolVec ι) measurable_signVec.aemeasurable (by exact h)

end BoolSeed

end ProbabilityTheory
