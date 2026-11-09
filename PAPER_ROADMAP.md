# Paper roadmap: On the Power of Adaptivity for ε-Best Arm Identification in Linear Bandits

Paper: RemyDegenne/Maiti2026Power · LMLExplore afd365492580 · LMLRoadmaps d01bdd6b89ce · Refreshed 2026-11-09

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Fixed-budget and fixed-design identification algorithms, canonical runs, transfer of PAC guarantees to runs and partial runs | exists | `LMLExplore.Identification.fixedBudget` | – | |
| R2 | Gaussian linear environments and the divergence of their histories | exists | `LMLExplore.Bandits.gaussianLinearEnv` | – | |
| R3 | Kiefer–Wolfowitz theorem: G-optimal designs on compact spanning sets | exists | `LMLExplore.exists_design_inner_ringInverse_le_finrank` | – | |
| R4 | Sub-exponential random variables, unconditional, kernel and conditional, with Bernstein-type tails | exists | `ProbabilityTheory.HasSubexponentialMGF` | – | |
| R5 | Pinsker and Bretagnolle–Huber inequalities, divergence between Gaussian laws | exists | `LMLExplore.exp_neg_klDiv_div_two_le` | – | |
| R6 | Divergence decomposition at a stopping time, equality case, and data processing for the outputs of runs | target | Identification 2.1 | proved | `ForLMLExplore/SequentialLearning/DivergenceDecomposition.lean`, `ForLMLExplore/SequentialLearning/StoppedHistory.lean`, `ForLMLExplore/SequentialLearning/HistoryLaw.lean`, `ForLMLExplore/Identification/RunDivergence.lean`, `ForLMLExplore/Identification/FixedBudget.lean` |
| R7 | Phased algorithms: fixed designs per phase, state updates, run lemma | target | Identification 0.5 | proved | `ForLMLExplore/SequentialLearning/Phased.lean` |
| R8 | Log-sum-exp and softmax: gradient, Hessian, smoothing of the maximum | target | ReinforcementLearning 5.1 | proved | `ForLMLExplore/Analysis/SpecialFunctions/LogSumExp.lean`, `ForLMLExplore/Algebra/Order/BigOperators/Covariance.lean` |
| R9 | Rounding a design to a fixed design by a barrier argument | target | Identification 9.3 | proved | `ForLMLExplore/Analysis/BarrierSum.lean`, `MXJ2026/Rounding.lean` |
| R10 | Support functions, Gaussian widths and measurable approximate maximizers of linear forms | staged | S1 | proved | `ForLMLExplore/Analysis/InnerProductSpace/SupportFn.lean`, `ForLMLExplore/Analysis/InnerProductSpace/SupportFnDense.lean`, `ForLMLExplore/Probability/GaussianWidth.lean`, `ForLMLExplore/MeasureTheory/ApproxArgmax.lean` |
| R11 | Gaussian concentration of Lipschitz functions (Maurey–Pisier) and the Borell–TIS inequality | staged | S2 | proved | `ForLMLExplore/Analysis/Calculus/Gradient.lean`, `ForLMLExplore/Analysis/Calculus/QuarterCircle.lean`, `ForLMLExplore/Analysis/InnerProductSpace/LogSumExp.lean`, `ForLMLExplore/Probability/MaureyPisier.lean`, `ForLMLExplore/Probability/BorellTIS.lean` |
| R12 | Stein's identity, Gaussian interpolation and the Sudakov–Fernique inequality | staged | S3 | proved | `ForLMLExplore/Probability/SteinReal.lean`, `ForLMLExplore/Probability/SteinIdentity.lean`, `ForLMLExplore/Probability/SteinExpGrowth.lean`, `ForLMLExplore/Probability/GaussianInterpolation.lean`, `ForLMLExplore/Probability/SudakovFernique.lean` |
| R13 | Expected maxima of finitely many sub-Gaussian and Gaussian variables | staged | S4 | proved | `ForLMLExplore/Probability/SubgaussianMax.lean`, `ForLMLExplore/Probability/GaussianMaxLower.lean`, `ForLMLExplore/Order/CiSupFinite.lean` |
| R14 | Squares of Gaussian and sub-Gaussian variables, chi-squared tails, Rademacher vectors | staged | S5 | proved | `ForLMLExplore/Probability/GaussianSquareMGF.lean`, `ForLMLExplore/Probability/Distributions/ChiSquared.lean`, `ForLMLExplore/Probability/SubgaussianSquare.lean`, `ForLMLExplore/Probability/Rademacher.lean` |
| R15 | Gaussian vectors: exponential moments, linear images, independence of uncorrelated images, absolute moments | staged | S6 | proved | `ForLMLExplore/Probability/GaussianMGF.lean`, `ForLMLExplore/Probability/MultivariateGaussian.lean`, `ForLMLExplore/Probability/StdGaussianProd.lean`, `ForLMLExplore/Probability/GaussianAbsMoment.lean`, `ForLMLExplore/Probability/GaussianSum.lean`, `ForLMLExplore/Analysis/InnerProductSpace/OrthonormalBasisSubmodule.lean`, `ForLMLExplore/Analysis/InnerProductSpace/EuclideanMatrix.lean` |
| R16 | Constant conditional laws, i.i.d. sequences and their windows | staged | S7 | proved | `ForLMLExplore/Probability/CondDistrib.lean`, `ForLMLExplore/Probability/CondDistribConst.lean`, `ForLMLExplore/Probability/IidOfCondDistrib.lean`, `ForLMLExplore/Probability/InfinitePiWindow.lean` |
| R17 | Loewner order on matrices: quadratic forms, congruence, antitone inversion, square roots, trace of the inverse | staged | S8 | proved | `ForLMLExplore/Analysis/Matrix/Loewner.lean`, `ForLMLExplore/Analysis/Matrix/LoewnerInv.lean`, `ForLMLExplore/Analysis/Matrix/HermitianCFC.lean`, `ForLMLExplore/Analysis/Matrix/TraceInv.lean` |
| R18 | The noise along every run of an environment with additive Gaussian noise | staged | S9 | proved | `ForLMLExplore/Identification/LinearBandit/GaussianNoise.lean`, `ForLMLExplore/Identification/LinearBandit/FixedDesignRun.lean` |
| R19 | Seeded algorithms, noise environments and the seed representation of runs | staged | S10 | proved | `ForLMLExplore/SequentialLearning/Seeded.lean` |
| R20 | Playing an algorithm, then repeating an action drawn from its history | staged | S11 | proved | `ForLMLExplore/SequentialLearning/RepeatTest.lean` |
| R21 | Law of the history under a change of the feedback kernel by a density | staged | S12 | proved | `ForLMLExplore/SequentialLearning/EnvDensity.lean` |
| R22 | Law of the least-squares estimate under a fixed design with Gaussian noise | staged | S13 | proved | `MXJ2026/LeastSquares.lean` |
| R23 | Finite mixtures of probability measures and their Radon–Nikodym derivatives | staged | S14 | proved | `ForLMLExplore/MeasureTheory/MixtureMeasure.lean` |
| R24 | The linear Gaussian bandit on an action set, simple regret, (ε, δ)-PAC identification, and its fixed-design, two-point and test lemmas | paper | | proved | `ForLMLExplore/Identification/LinearBandit/LinearBandit.lean`, `ForLMLExplore/Identification/LinearBandit/FixedDesignLaw.lean`, `ForLMLExplore/Identification/LinearBandit/FixedDesignTransport.lean`, `ForLMLExplore/Identification/LinearBandit/TwoPoint.lean`, `ForLMLExplore/Identification/LinearBandit/RepeatTestGaussian.lean`, `ForLMLExplore/InformationTheory/Pinsker.lean` |
| R25 | Median Elimination on candidate arms of a linear Gaussian bandit, as a phased algorithm | paper | | proved | `ForLMLExplore/Identification/MedianElimination/MedianEliminationSchedule.lean`, `ForLMLExplore/Identification/MedianElimination/MedianEliminationRound.lean`, `ForLMLExplore/Identification/MedianElimination/MedianElimination.lean`, `ForLMLExplore/Data/Finset/TopBy.lean` |
| R26 | Design matrices, design sets, Kiefer–Wolfowitz in matrix form, normalized and mixed designs, and the width term w(𝒳) | paper | | proved | `MXJ2026/OuterSelf.lean`, `MXJ2026/DesignSet.lean`, `MXJ2026/OptimalDesign.lean`, `MXJ2026/NormalizedDesign.lean`, `MXJ2026/MixedDesign.lean`, `MXJ2026/Width.lean`, `MXJ2026/WidthDesign.lean`, `ForLMLExplore/Analysis/Calculus/LocalExtr.lean` |
| R27 | The Bayesian model of the non-adaptive lower bound: likelihood of linear Gaussian histories, the run as a kernel in the parameter, Gaussian posteriors | paper | | proved | `MXJ2026/GaussianLikelihood.lean`, `MXJ2026/BayesKernel.lean`, `MXJ2026/BayesModel.lean`, `MXJ2026/PosteriorGaussian.lean`, `ForLMLExplore/Probability/Kernel/PriorAverage.lean` |
| R28 | Small lemmas used by single proofs of the paper | paper | | proved | `ForLMLExplore/Analysis/InnerProductSpace/IsotropicSeparated.lean`, `ForLMLExplore/Data/Set/CoverSmall.lean`, `ForLMLExplore/Data/Finset/PowersetCardSum.lean`, `ForLMLExplore/Data/Fintype/PiSplitAt.lean`, `ForLMLExplore/MeasureTheory/Measure/Real.lean`, `ForLMLExplore/Probability/IndepIntegral.lean` |

## Notes

- R1: the project uses LMLExplore's `IsFixedBudget`, `fixedBudget`, `IsFixedDesign`,
  `Learning.Algorithm.ofSeq`, the canonical run `runMeasure` and
  `IdentAlg.IsPAC.measureReal_bad_of_isAlgEnvSeqUntil` directly, on top of LML's `IdentAlg`.
- R2: the paper's `LinearBandit.linearGaussianEnv 𝒳 θ` (R24) is the case of
  `LMLExplore.Bandits.gaussianLinearEnv` with no contexts (`Measure.dirac ()`), the features
  `(↑) : 𝒳 → E` and `σ2 = 1`, and its `LinearBandit.klDiv_map_history` is the corresponding case of
  `klDiv_map_history_gaussianLinearEnv`. The headline statements are frozen on the paper's
  definition, so the paper keeps it.
- R3: the paper keeps a matrix version on `EuclideanSpace ℝ ι` (R26), with a Carathéodory support
  bound `card ι ^ 2 + 1`, used by its proofs. LMLExplore's operator version covers it; switching the
  paper's proofs to it is internal to the paper.
- R4, R5: LML's `ForMathlib/Probability/Moments/SubExponential.lean` (sub-exponential variables),
  Tau Ceti's `TauCeti.two_mul_sq_measureReal_sub_le_klDiv` (Pinsker), LMLExplore's
  `exp_neg_klDiv_div_two_le` (Bretagnolle–Huber) and
  `klDiv_gaussianReal_gaussianReal_same_var`. The chi-squared law and its moment generating
  function are Tau Ceti's `chiSquaredMeasure` and `stdGaussian_map_norm_sq`.
- R6: LMLExplore already has the inequality of Identification 2.1 for any two
  algorithm–environment pairs (`Learning.klDiv_stoppedHistMeasure_le_tsum`,
  `Learning.klDiv_stoppedHistMeasure_le_lintegral`) and the output bound for one algorithm against
  two stationary bandits (`LMLExplore.Identification.klDiv_histOutputMeasure_le`). What the paper
  adds is the equality when the stopping time is almost surely finite under both laws
  (`IsAlgEnvSeq.klDiv_map_stoppedValue_sigmaHistory_stepKernel` and its integral and
  composition-product forms), the histories stopped at a bounded time (`stoppedProcess`), and the
  data processing for the joint law of the stopped history and the output of runs in arbitrary
  environments (`IdentAlg.IsRun.klDiv_map_stoppedHist_out`, `IsRun.klDiv_map_out_le_stoppedHist`).
  The paper proves these for one algorithm against two environments: the port states them for any
  two pairs `(alg, env)`, `(alg', env')`, on LML's `stoppedHistMeasure` and
  `IdentAlg.outputMeasure`, transferred to runs, and derives the equality case of
  `klDiv_stoppedHistMeasure_le` for two stationary bandits on finite arms. The `LinearBandit.*`
  lemmas of `DivergenceDecomposition.lean` and `FixedBudget.lean` (linear Gaussian specializations,
  Bretagnolle–Huber on the outputs) stay in the paper with R24.
- R7: Identification 0.5 asks for the phased-elimination constructor (a finite type of answers, an
  initial active set, pull schedules `n_r : Finset ℐ → α → ℕ` that depend on the active set,
  measurable elimination maps, an output in the final active set, fixed-confidence and fixed-budget
  versions), its run lemmas for every stationary environment (the start of each phase is a stopping
  time; given the history at the start of a phase, its observations are independent, arm `a`
  contributing `n_r(S_r)(a)` observations of law `ν_a`) and the survival bound. The paper's
  `PhasedAlg` has phase lengths that do not depend on the state, an arbitrary state, and its run
  lemma only in a linear Gaussian bandit (`PhasedAlg.hasCondDistrib_phaseNoise`). The port lets the
  phase lengths depend on the state, proves the run lemma for `Environment.bandit ν`, and builds
  the phased-elimination constructor as the case where the state is the active set.
- R8: LMLExplore already has `LMLExplore.OnlineLearning.softmax` (with values in `simplex`); the port
  uses it, without the paper's temperature `β` (the paper's forms are the case `β • z`), defines
  `logSumExp`, and adds the convexity of `logSumExp`, which ReinforcementLearning 5.1 asks for and
  the paper does not prove. The Jacobian `diag(π) - ππᵀ` is `fderiv_fderiv_logSumExp_apply`;
  `Covariance.lean` bounds its norm. The composition with linear forms
  (`Analysis/InnerProductSpace/LogSumExp.lean`) belongs to R11.
- R9: Identification 9.3 asks for RAGE and "the rounding of designs it uses". The paper's
  `exists_rounding`: for a design `w` with invertible design matrix on `EuclideanSpace ℝ ι` and
  `T ≥ 4 d`, there are `T` points of the support of `w` with `∑ x xᵀ ⪰ (T/4) V(w)` (a one-sided
  Batson–Spielman–Srivastava barrier). A constant-factor rounding gives the sample complexity of
  RAGE up to the constant, which the `O(·)` of Identification 9.3 allows. The port states it for
  LMLExplore's `designOperator` of a design `w : StdSimplex ℝ E` on a finite-dimensional inner
  product space, with the Loewner order of positive operators, and the singular case through the
  span of the support. It currently lives in the paper folder, on the paper's `designMatrix` (R26)
  and matrix lemmas (R17).
- R10–R17: Part II of the blueprint (`prereq_gaussian`, `prereq_concentration`, `prereq_sudakov`,
  `prereq_subexp`). No roadmap covers Gaussian processes, Gaussian concentration or matrix analysis;
  `notes/upstreaming-candidates.md` assesses these files as Mathlib candidates.
- R15: Tau Ceti has the closure of `multivariateGaussian` under affine maps, convolution and
  negation (`map_affine_multivariateGaussian`, `multivariateGaussian_conv_multivariateGaussian`),
  `E|Z| = √(2v/π)` (`integral_abs_gaussianReal`) and the Gaussian moment generating function of
  linear forms (`IsGaussian.mgf_dual`); the port keeps only what they do not cover.
- R18: stated in the paper for its `linearGaussianEnv` (R24); the port states it for LMLExplore's
  `gaussianLinearEnv` and, more generally, the additive-noise environments of S9.
- R19: related to LML's array model (`Bandits.ArrayModel`), LMLExplore's table model
  (`Bandits/TableModel.lean`) and the keyed streams of ReinforcementLearning 6.1, none of which
  reads the feedback as a function of the action and a fresh noise.
- R22: the estimator is LMLExplore's `leastSquaresEstimate` (Moore–Penrose form), and LMLExplore's
  `Probability/Moments/SubGaussian/LeastSquares.lean` has the sub-Gaussian fixed-design bound of
  Bandits 8.5. The paper's exact Gaussian law is stated on matrices, for a spanning design.
- R24: Identification 9.1 asks for linear tasks as pullbacks of the unstructured tasks along the
  mean functional, with no separate definitions, and the Identification roadmap covers finitely
  many arms only, while the paper works on compact, possibly infinite, action sets. The model, the
  simple regret and `LinearBandit.IsPAC` stay in the paper, which freezes its headline statements
  on them. `Pinsker.lean` (the real form `|μ A - ν A| ≤ √(KL/2)`) is a one-line corollary of Tau
  Ceti's Pinsker inequality used only by `TwoPoint.lean`.
- R25: LMLExplore has Median Elimination for σ²-sub-Gaussian arms
  (`LMLExplore.Identification.medianElimination`), and Generalization 1.3 rebuilds it through the
  constructor of Identification 0.5. The paper's version is a different implementation (the arms
  are candidate actions `c : Fin K → 𝒳`, its own tie-breaking `Finset.topBy`), written as a phased
  algorithm (R7) so that the region algorithm of Theorem 6 can prepend a fixed-design phase. It
  already uses LMLExplore's schedule (`MedianElimination.armsCount`, `pullSchedule 1`,
  `numPhases`, `phaseEnd`). It is not to be ported.
- R26: the matrix forms the headline statements and proofs use (`designSet`, `gwMat`, `gw`). The
  operator Kiefer–Wolfowitz is R3; `LocalExtr.lean` (one-sided Fermat rule) serves only the
  paper's matrix Kiefer–Wolfowitz.
- R27: Bayesian (posterior-based) guarantees are outside the Identification roadmap. The likelihood
  ratio of histories it uses in general form is R21; Stein's identity for functions of exponential
  growth is R12.
- R28: tailored to single proofs (`IsotropicSeparated.lean`: Theorem 5's width lower bound;
  `CoverSmall.lean`: Theorem 6; `PowersetCardSum.lean`: the `m`-set lower bound; `PiSplitAt.lean`:
  the multi-task set; `Measure/Real.lean`: one complement bound). `IndepIntegral.lean` backs the
  blueprint's `lem:indep_integral_zero` and is imported by no other module.

## Proposed targets

### S1. Support functions and Gaussian widths

For a set `K` of a real inner product space `E`, define the support function
`supportFn K ξ = ⨆ x : K, ⟪x, ξ⟫` and, for a measure `μ` on `E`, the Gaussian width
`gaussianWidth K μ = ∫ ξ, supportFn K ξ ∂μ`, whose case `μ = stdGaussian E` is the Gaussian (mean)
width of `K` [Ver18, Section 7.5].
- Basic API of the support function: the defining inequalities, `R`-Lipschitz and convex for a
  nonempty set in the ball of radius `R`, positively homogeneous, monotone in `K`, additive under
  Minkowski sums, `supportFn (L '' K) = supportFn K ∘ L†` for a continuous linear map `L`,
  attained on a compact set, and the supremum over a dense sequence of a compact set in a separable
  space.
- Gaussian widths: integrability for every measure with integrable norm (Gaussian measures in
  particular), monotonicity in `K`, homogeneity, images by linear maps (`gaussianWidth (L '' K) μ =
  gaussianWidth K (μ.map L†)`), Minkowski sums, nonnegativity for a centered `μ`, and the width of
  the difference set `K - K` as twice the width of `K` for a symmetric `μ`.
- For a compact set `K` and `γ > 0`, a measurable map `s : E → K` with
  `supportFn K v - γ ≤ ⟪s v, v⟫` for all `v`, and a measurable exact maximizer when `K` is finite.

The support function of a set of a normed space is naturally a function on the dual; state the
inner-product form as the case of the Riesz identification, or choose one convention once.

### S2. Gaussian concentration and the Borell–TIS inequality

On a finite-dimensional real inner product space `E` with its standard Gaussian measure:
- **Gaussian concentration** [Pis86, Theorem 2.2; BLM13, Theorem 5.6]: for `f` of class `C¹`
  with `‖∇f‖ ≤ L`, `f - ∫ f` is sub-Gaussian (`HasSubgaussianMGF`) with variance proxy `c L²`, with
  the explicit constant of the proof (`c = π²/4` by the Maurey–Pisier interpolation along the
  quarter circle; `c = 1` for the Tsirelson–Ibragimov–Sudakov form), and for every `L`-Lipschitz
  `f` by smoothing.
- The log-sum-exp smoothing of a finite maximum of linear forms (from ReinforcementLearning 5.1):
  its gradient is the softmax-weighted combination of the vectors and has norm at most their
  largest norm.
- **Borell–TIS** [AT07, Theorem 2.1.1]: for a nonempty compact `K` in the ball of radius `R`,
  `supportFn K - ∫ supportFn K` is sub-Gaussian with variance proxy `c R²` under `stdGaussian E`,
  with both tails; for a centered Gaussian measure with covariance `S`, the same with `R²` replaced
  by `sup_{x ∈ K} ⟪x, S x⟫`.

### S3. Stein's identity, Gaussian interpolation and Sudakov–Fernique

- **Gaussian integration by parts** [Ver18, Lemma 7.2.5]: `E[(ξ - m) f(ξ)] = v E[f'(ξ)]` for
  `ξ ~ N(m, v)` and every absolutely continuous `f` with `f'` integrable against the law and
  `(x - m) f(x)` integrable (in particular for derivatives of exponential growth); its
  multivariate form `E[⟪a, X⟫ F(X)] = E[DF(X) (S a)]` for a centered Gaussian vector `X` of
  covariance `S` on a finite-dimensional inner product space.
- **Gaussian interpolation** [Ver18, Lemma 7.2.7]: for independent centered Gaussian vectors `X`,
  `Y` and `Z_t = √t X + √(1 - t) Y`, the derivative of `t ↦ E[F(Z_t)]` for `F` of class `C²` with
  bounded (or exponentially growing) second derivative.
- **Sudakov–Fernique** [Ver18, Theorem 7.2.11]: for centered Gaussian vectors `X`, `Y` indexed by a
  finite set with `E[(X_i - X_j)²] ≤ E[(Y_i - Y_j)²]`, `E[max_i X_i] ≤ E[max_i Y_i]`; then for
  separable Gaussian processes indexed by a countable set, through finite subsets, and in the form
  of a comparison of Gaussian widths for two covariances.

### S4. Expected maxima of sub-Gaussian and Gaussian variables

- For finitely many real variables `Z_i`, `i ∈ ι`, each sub-Gaussian with variance proxy `c`, with
  no assumption on their joint law: `E[max_i Z_i] ≤ √(2 c log |ι|)` [BLM13, Section 2.5].
- For `m ≥ 2` independent standard Gaussians, `E[max_i ξ_i] ≥ c √(log m)` with an explicit `c`
  (the paper's proof gives `1/4`), and `E[max(ξ_1, ξ_2)] = 1/√π` [Ver18, Section 2.5].
- Corollary: the Gaussian width of a finite set in the ball of radius `σ` is at most
  `σ √(2 log |K|)` (S1).

### S5. Squares of Gaussian and sub-Gaussian variables and Rademacher vectors

- The moment generating function of the square of `X ~ N(m, v)`:
  `E[exp(a X²)] = (1 - 2 v a)^(-1/2) exp(m² a / (1 - 2 v a))` for `2 v a < 1`; `X² - (m² + v)` is
  sub-exponential (LML's `HasSubexponentialMGF`) with explicit parameters, and `‖g‖² - d` is for a
  standard Gaussian vector of dimension `d`, with the chi-squared tail bounds [LM00, Lemma 1].
- For a sub-Gaussian `Z` with variance proxy `c`: `E[exp(a Z²)] ≤ (1 - 2 c a)^(-1/2)` for
  `0 ≤ a < 1/(2c)` (by the Gaussian trick), `E[Z⁴] ≤ 14 c²` (and `≤ 4 c²` when `E[Z²] = c`), and
  `Z² - E[Z²]` is sub-exponential with explicit parameters [Ver18, Lemma 2.7.6].
- Rademacher vectors on a finite type, as the product of Tau Ceti's `rademacherMeasure`: the linear
  form `∑ ε_i θ_i` is sub-Gaussian with variance proxy `‖θ‖²`, has second moment `‖θ‖²`, and its
  centered square is sub-exponential.

### S6. Gaussian vectors

On a finite-dimensional real inner product space, for Gaussian measures with a covariance operator
(`IsGaussian`), with the matrix forms on `EuclideanSpace ℝ ι` as corollaries:
- `exp(c ‖x‖)` is integrable for every `c` (from Fernique's theorem), hence so is `exp(t F)` for
  every `F` of linear growth, and every function of polynomial growth is integrable;
- the law of a linear form `⟪a, ·⟫` under `stdGaussian E` is `N(0, ‖a‖²)`; the image of a centered
  Gaussian of covariance `S` by a linear map `L` has covariance `L S L†`; sums and averages of
  independent standard Gaussians;
- two linear images of a pair of independent standard Gaussian vectors are independent when their
  cross-covariance vanishes, with the covariance formula for such images;
- `E|⟪e, Y⟫| = √(2 ⟪e, S e⟫ / π)` and `E‖Y‖ ≥ √(2/π) ∑ c_i √(⟪e_i, S e_i⟫)` for an orthonormal family
  `e` and `∑ c_i² ≤ 1`, `E‖Y‖ ≤ √(tr S)`.

### S7. Constant conditional laws and i.i.d. sequences

- If `W 0` has law `ν` and the conditional law of `W (n + 1)` given `(W 0, …, W n)` is the
  constant `ν` for every `n` (`HasCondDistrib` with a constant kernel), then `(W 0, …, W (n - 1))`
  has law `Measure.pi (fun _ ↦ ν)` and the `W i` are independent; the same with an extra
  conditioning variable `Z`, which gives independence of `(W i)_{i<n}` from `Z`. State the
  measurable-space generality of Mathlib's `HasCondDistrib` (standard Borel only where the
  conditional kernel needs it).
- A constant conditional law given `Z` is a constant conditional law given any measurable function
  of `Z`; conditional laws of `G X Y` given `X` for `Y` with a constant conditional law; images of
  composition-products by maps `(a, b) ↦ (G a, F a b)`; a uniform bound on conditional
  probabilities bounds the probability.
- The first `T` coordinates of an i.i.d. sequence are independent of any family of later
  coordinates (from Tau Ceti's `indepFun_domRestrict_infinitePi`).

### S8. The Loewner order on matrices and positive operators

Over `RCLike 𝕜`, for positive operators on a finite-dimensional inner product space and for
matrices with the order of `MatrixOrder`:
- `A ≤ B` iff `⟪x, A x⟫ ≤ ⟪x, B x⟫` for all `x` (for self-adjoint `A`, `B`); congruence
  `A ≤ B → M A M* ≤ M B M*`; an operator above a positive definite one is positive definite;
- inversion is antitone: `0 < A ≤ B → B⁻¹ ≤ A⁻¹` [HJ13, Corollary 7.7.4] (Mathlib's
  `CStarAlgebra.inv_le_inv` excludes real matrices), and its scalar form `c A ≤ B → B⁻¹ ≤ c⁻¹ A⁻¹`;
- square roots: `√A √A = A`, `√A⁻¹ A √A⁻¹ = 1`, and the norm of `√A x`;
- functions of a Hermitian matrix: `A - l • 1 = cfc (· - l) A`, its inverse and positivity through
  the spectrum, and the trace of `(A - l • 1)⁻²` as a sum over the eigenvalues;
- the arithmetic–harmonic mean inequality `(dim)² ≤ tr A · tr A⁻¹`.

### S9. Environments with additive noise

For a measurable mean function `m : 𝓐 → ℝ` and a noise law `ν` on `ℝ`, the stationary environment
whose feedback at the action `a` has the law of `m a + η` with `η ~ ν` (LMLExplore's
`gaussianLinearEnv` with `m a = ⟪θ, φ a⟫` and `ν = N(0, σ²)` is the case of interest). For every
algorithm and every run, with the noise `η_t = Y_t - m(A_t)` [LS, Section 4.6]:
- given the history of the first `t` rounds and `A_t`, `η_t` has law `ν`; the noise vector of the
  first `n` rounds has law `ν^n`, and the noise of the rounds `m, …, m + n - 1` is independent of
  the history of the first `m` rounds, with law `ν^n`;
- for sub-Gaussian `ν`, the noise is conditionally sub-Gaussian for `IsAlgEnvSeq.filtrationAction`,
  with the Azuma–Hoeffding bounds on its block sums;
- under a fixed design (`Algorithm.ofSeq x`), the feedback vector of the first `n` rounds is
  `(m (x t))_t` plus a vector of law `ν^n`.

### S10. Seeded algorithms and the seed representation of runs

- A *seeded algorithm* draws at each round a fresh seed `u ~ seed` and plays `next n h u`, a
  measurable function of the history and the seed; a *noise environment* answers the action `x`
  with `F x e` for a fresh `e ~ μe`. Both are LML algorithms and environments.
- **Seed representation** [LS, Section 4.6]: on the product space `ℕ → U × E` with the product
  measure, the rounds defined recursively from the seeds and the noises form an
  algorithm–environment sequence; by the uniqueness of the law of the history, the history of every
  run of a seeded algorithm in a noise environment has the law of the seeded history.
- Corollary: the guarantees of fixed-budget seeded algorithms with a deterministic output reduce to
  computations on the product space. Relate the construction to LML's array model and LMLExplore's
  table model.

### S11. Playing an algorithm, then repeating an action

For an algorithm `alg`, `n : ℕ` and a kernel `ρ` from the histories of `n + 1` rounds to actions,
the algorithm `alg.thenRepeat n ρ` plays `alg` for `n + 1` rounds, draws an action from `ρ` and
repeats it forever. Prove its run lemmas: it follows `alg` until round `n + 1`, its action at round
`n + 1` has conditional law `ρ` given the history, and its later actions equal that action almost
surely. For a fixed-budget identification algorithm with actions as outputs, the test algorithm
that plays it and then repeats its recommendation inherits its PAC guarantee on the action of round
`n + 1`. This is the reduction from identification to testing of the adaptive lower bounds of
[MXJ26].

### S12. Likelihood ratios of histories under a change of environment

For Markov kernels `κ₀`, `κ` with `κ = κ₀.withDensity ρ` for a jointly measurable `ρ`, and every
algorithm, the law of the history of the first `n` rounds against `κ` has density
`∏_{t<n} ρ(x_t, y_t)` with respect to the law against `κ₀` (the environment analogue of LML's
`Algorithm.density`). State it for every environment whose feedback kernels have densities
`ρ_t` with respect to those of a reference environment, with the history-dependent product of
densities, and give the Gaussian instance (`N(⟪x, θ⟫, σ²)` against `N(0, σ²)`).

### S13. Least squares under a fixed design with Gaussian noise

For a fixed design `x_0, …, x_{T-1}` of a finite-dimensional inner product space and independent
`N(0, σ²)` noise, the least-squares estimate (LMLExplore's `leastSquaresEstimate 0 x Y T`) is a
Gaussian vector with mean the projection of `θ` on the span of the design and covariance
`σ² V_T(0)⁺` [LS, Section 20.1]; when the design spans the space, its law is `N(θ, σ² V_T(0)⁻¹)`.
Give the matrix form on `EuclideanSpace ℝ ι` as a corollary.

### S14. Finite mixtures of probability measures

A finite mixture `∑ i, c i • ν i` of probability measures with nonnegative weights summing to `1`
is a probability measure, and its Radon–Nikodym derivative with respect to a measure `μ` is the
mixture of the Radon–Nikodym derivatives, `μ`-almost everywhere, for s-finite `ν i` and `μ`. These
are basic API lemmas for `Finset.sum` of measures, Mathlib-shaped.

References: [AT07] R. J. Adler and J. E. Taylor, *Random Fields and Geometry*, Springer (2007).
[BLM13] S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University
Press (2013). [HJ13] R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd edition, Cambridge
University Press (2013). [LM00] B. Laurent and P. Massart, Adaptive estimation of a quadratic
functional by model selection, *Ann. Statist.* 28 (2000). [LS] T. Lattimore and Cs. Szepesvári,
*Bandit Algorithms*, Cambridge University Press (2020). [MXJ26] the paper of this repository.
[Pis86] G. Pisier, Probabilistic methods in the geometry of Banach spaces, *Lecture Notes in Math.*
1206 (1986). [Ver18] R. Vershynin, *High-Dimensional Probability*, Cambridge University Press
(2018).
