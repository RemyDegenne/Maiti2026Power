/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.ForLMLExplore.Identification.IdentAlg
public import Maiti2026Power.ForLMLExplore.Probability.CondDistrib
public import LMLExplore.Identification.Correctness

/-!
# Existence of runs of identification algorithms

Every identification algorithm `A` has a run in every environment, on the space
`(ℕ → Round 𝓞 𝓐 𝓨) × 𝓓` of (trajectory, output) pairs: the trajectory has the law
`trajMeasure A.alg env` of the Ionescu-Tulcea construction and the output is drawn from the
output rule applied to the history at the stopping time (`IdentAlg.runMeasure`,
`IdentAlg.isRun_runMeasure`); the output rule being a Markov kernel, this is a probability
measure.

The transport of runs along a measure-preserving map (`IdentAlg.IsRun.comp_hasLaw`) and the
PAC property from a bound on every run (`IdentAlg.IsPAC.of_forall_isRun`) are LMLExplore's.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓}

namespace IdentAlg

variable (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨)

/-- The canonical probability space of a run of `A` in the environment `env`: the trajectory
`ℕ → Round 𝓞 𝓐 𝓨` has the law `trajMeasure A.alg env` and, given the trajectory, the output is
drawn from the output rule applied to the history at the stopping time. -/
noncomputable def runMeasure : Measure ((ℕ → Round 𝓞 𝓐 𝓨) × 𝓓) :=
  trajMeasure A.alg env ⊗ₘ A.output.comap (A.stoppedHist IT.obs IT.action IT.feedback)
    (A.measurable_stoppedHist IT.measurable_obs IT.measurable_action IT.measurable_feedback)
deriving IsProbabilityMeasure

/-- Every identification algorithm has a run in every environment: the canonical run on
`runMeasure`. -/
lemma isRun_runMeasure :
    A.IsRun env (fun n ω ↦ IT.obs n ω.1) (fun n ω ↦ IT.action n ω.1) (fun n ω ↦ IT.feedback n ω.1)
      Prod.snd (A.runMeasure env) where
  isAlgEnvSeq := (IT.isAlgEnvSeq_trajMeasure A.alg env).comp_hasLaw
    ⟨measurable_fst.aemeasurable, Measure.fst_compProd _ _⟩ measurable_fst
  hasCondDistrib_output :=
    hasCondDistrib_snd_compProd_comap (trajMeasure A.alg env) A.output
      (A.measurable_stoppedHist IT.measurable_obs IT.measurable_action IT.measurable_feedback)
      fun _ ↦ inferInstance

end IdentAlg

end Learning
