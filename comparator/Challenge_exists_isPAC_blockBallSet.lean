module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LMLExplore.Identification.FixedBudget
public import LMLExplore.SequentialLearning.Algorithms.OfSeq
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Probability.Distributions.Gaussian.Real
public import LeanMachineLearning.SequentialLearning.StoppedHistory
public import LMLExplore.SequentialLearning.StoppedHistory
public import LeanMachineLearning.SequentialLearning.Algorithm
public import Mathlib.Probability.HasCondDistrib
public import TauCeti.Probability.Kernel.Randomization
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MapComap
public import LMLExplore.Probability.HasCondDistrib
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Complex.ExponentialBounds
public import LMLExplore.Probability.Distributions.Gaussian.Real
public import TauCeti.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.Gaussian.Sum
public import TauCeti.Probability.Distributions.Gaussian.Symmetry
public import TauCeti.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Distributions.Chi.Gaussian
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Data.Fintype.Order
public import LMLExplore.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Order.PartialSups
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import TauCeti.Probability.Distributions.Gaussian.Transforms
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import TauCeti.Analysis.Calculus.Gradient
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Independence.Integration
public import TauCeti.Probability.Distributions.Rademacher
public import LMLExplore.Probability.Distributions.Bernoulli
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubExponential
public import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
public import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
public import TauCeti.MeasureTheory.Constructions.Pi
public import TauCeti.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.InfinitePi
public import LMLExplore.InformationTheory.KullbackLeibler.BretagnolleHuber
public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition
public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian
public import LMLExplore.Topology.Algebra.InfiniteSum.NatInt
public import LMLExplore.Probability.Moments.SubGaussian.Basic
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.Convex
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import LMLExplore.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import TauCeti.Probability.Distributions.Gaussian.L2
public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.Analysis.Matrix.FunctionalCalculus
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import TauCeti.Probability.Distributions.Gaussian.Moments
public import Mathlib.Analysis.Real.Pi.Bounds
public import LMLExplore.Probability.Distributions.Gaussian.Tail
public import LMLExplore.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Standalone extraction for `Maiti2026Power.exists_isPAC_blockBallSet`
Definitions are copied verbatim; theorem proofs are replaced by `sorry`.
Auto-generated by ChallengeGen. -/

set_option quotPrecheck false

-- The options the project is built with.
set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Namespace stubs (so later `open`s resolve).
namespace MeasureTheory
end MeasureTheory
namespace ProbabilityTheory
end ProbabilityTheory
namespace Learning.LinearBandit
end Learning.LinearBandit
namespace Maiti2026Power
end Maiti2026Power
namespace Real
end Real
namespace Learning
end Learning
namespace Finset
end Finset

-- ═══ Maiti2026Power.ForLMLExplore.Identification.LinearBandit.LinearBandit ═══
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
universe u
namespace Learning.LinearBandit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- Reward kernel of the linear Gaussian bandit on `𝒳` with reward vector `θ`: playing `x` gives an
observation with law `N(⟪x, θ⟫, 1)`. -/
noncomputable def linearGaussianKernel (𝒳 : Set E) (θ : E) : Kernel 𝒳 ℝ where
  toFun x := gaussianReal ⟪(x : E), θ⟫ 1
  measurable' := by
    change Measurable (gaussianReal.uncurry ∘ fun x : 𝒳 ↦ (⟪(x : E), θ⟫, (1 : ℝ≥0)))
    exact measurable_gaussianReal.comp (by fun_prop)

/-- The linear Gaussian environment on the action set `𝒳` with reward vector `θ`: the stationary
environment with reward kernel `linearGaussianKernel 𝒳 θ`.

The Markov-kernel argument of `Environment.bandit` is given inline rather than through the instance
above: the nested proof of an exposed `def` becomes a public auxiliary constant, whereas the proof
inside an instance (a theorem) becomes a module-private one, which the standalone comparator
challenges (`comparator/`) could not reproduce. -/
noncomputable def linearGaussianEnv (𝒳 : Set E) (θ : E) : Environment Unit 𝒳 ℝ :=
  @Environment.bandit _ _ _ _ (linearGaussianKernel 𝒳 θ)
    ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (gaussianReal _ 1))⟩

/-- Simple regret of the arm `x` for the reward vector `θ` on the action set `𝒳`:
`sup_{y ∈ 𝒳} ⟪y, θ⟫ - ⟪x, θ⟫`. -/
noncomputable def simpleRegret (𝒳 : Set E) (θ x : E) : ℝ :=
  (⨆ y : 𝒳, ⟪(y : E), θ⟫) - ⟪x, θ⟫

/-- An identification algorithm (with actions in `𝒳`, real feedbacks and recommendations in
`𝒳`) is `(ε, δ)`-PAC on `𝒳` if for every reward vector `θ`, run against the linear Gaussian
environment `linearGaussianEnv 𝒳 θ`, its recommendation has simple regret more than `ε` with
probability at most `δ`. -/
def IsPAC (𝒳 : Set E) (A : IdentAlg Unit 𝒳 ℝ 𝒳) (ε δ : ℝ) : Prop :=
  A.IsPAC (linearGaussianEnv 𝒳) (fun θ x ↦ ε < simpleRegret 𝒳 θ x) δ

end Learning.LinearBandit
end

-- ═══ Maiti2026Power.MXJ2026.StructuredSets ═══
@[expose] public section
namespace Maiti2026Power
variable (ι : Type*) [Fintype ι]
variable {ι}

/-- The block-ball set in `ℝ^(Fin k × Fin d)`: the union over the `k` blocks `i` of the unit balls
`{x : ‖x‖ ≤ 1, x supported on block i}`. -/
def blockBallSet (k d : ℕ) : Set (EuclideanSpace ℝ (Fin k × Fin d)) :=
  {x | ‖x‖ ≤ 1 ∧ ∃ i, ∀ j, j ≠ i → ∀ l, x (j, l) = 0}

end Maiti2026Power
end

-- ═══ Maiti2026Power.MXJ2026.Separation ═══
@[expose] public section
open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit Finset
open LMLExplore.Identification
open scoped RealInnerProductSpace
namespace Maiti2026Power

/-- **Theorem 7, adaptive upper bound** [MXJ26, Theorem 7]: for `k ≥ 1`, `ε ∈ (0, 1]` and `δ ∈ (0,
1)`, there is an (adaptive) `(ε, δ)`-PAC identification algorithm on the block-ball set of `ℝ^{kd}`
with budget `T ≤ 2·10⁶ (kd log(8k/δ) + d²) / ε²`. -/
theorem exists_isPAC_blockBallSet (k d : ℕ) (hk : 1 ≤ k) {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 2000000 * (k * d * log (8 * k / δ) + (d : ℝ) ^ 2) / ε ^ 2 ∧
      ∃ A : IdentAlg Unit (blockBallSet k d) ℝ (blockBallSet k d), IsFixedBudget A T ∧
        IsPAC (blockBallSet k d) A ε δ := sorry

end Maiti2026Power
end
