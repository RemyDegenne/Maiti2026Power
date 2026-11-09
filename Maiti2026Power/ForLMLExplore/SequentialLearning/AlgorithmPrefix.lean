/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.ForLMLExplore.Identification.Run

/-!
# Algorithms agreeing on a prefix; transfer of PAC guarantees

If two algorithms `alg`, `alg'` have the same policies at times `n < N` (they choose the first
`N` actions in the same way), an algorithm-environment sequence for `alg` is an
algorithm-environment sequence for `alg'` until time `N` (LML
`IsAlgEnvSeq.isAlgEnvSeqUntil_of_policy_eq`, `IsAlgEnvSeqUntil`), and the law of the history of
the first `N` rounds is the one of the canonical trajectory measure of `alg'` (LML
`IsAlgEnvSeqUntil.map_history`).

For a fixed-budget identification algorithm `A` with budget `T`, an algorithm-environment
sequence for `A.alg` until time `T` together with an output `out` whose conditional law given the
history of the first `T` rounds is the output rule of `A` on histories of length `T` has the
same joint law of (history, output) as the canonical run of `A` (`IdentAlg.map_history_out_eq`);
in particular every PAC guarantee of `A` applies to `out`
(`IdentAlg.IsPAC.measureReal_bad_of_isAlgEnvSeqUntil`). This is how a PAC algorithm is used as
the first phase of a composed algorithm (the test of the adaptive lower bound, blueprint
`lem:test_from_alg`) without a general composition lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {env : Environment Unit 𝓐 𝓨}

namespace IdentAlg

variable {𝓓 : Type*} {m𝓓 : MeasurableSpace 𝓓} {A : IdentAlg Unit 𝓐 𝓨 𝓓} {T : ℕ} {out : Ω → 𝓓}

/-- If `A` has budget `T`, `(O, X, Y)` is an algorithm-environment sequence for `A.alg` until
time `T` and `out` has conditional law `A.output.comap (Sigma.mk T) _` (the output rule on
histories of length `T`) given the history of the first `T` rounds, then (history, output) has
the same law as under the canonical run of `A` (`runMeasure`). -/
lemma map_history_out_eq [IsProbabilityMeasure P] (hA : A.IsFixedBudget T)
    (h : IsAlgEnvSeqUntil O X Y A.alg env P T)
    (hout : HasCondDistrib out (history O X Y T)
      (A.output.comap (Sigma.mk T) (measurable_sigmaMk T)) P) :
    P.map (fun ω ↦ (history O X Y T ω, out ω)) =
      (A.runMeasure env).map (fun ω ↦ (history IT.obs IT.action IT.feedback T ω.1, ω.2)) := by
  have h1 : (A.runMeasure env).map (fun ω ↦ history IT.obs IT.action IT.feedback T ω.1) =
      ((A.runMeasure env).map Prod.fst).map (history IT.obs IT.action IT.feedback T) :=
    (Measure.map_map (measurable_history_traj T) measurable_fst).symm
  calc P.map (fun ω ↦ (history O X Y T ω, out ω))
      = P.map (history O X Y T) ⊗ₘ A.output.comap (Sigma.mk T) (measurable_sigmaMk T) :=
        hout.map_eq
    _ = (A.runMeasure env).map (fun ω ↦ history IT.obs IT.action IT.feedback T ω.1) ⊗ₘ
          A.output.comap (Sigma.mk T) (measurable_sigmaMk T) := by
        rw [h.map_history, h1,
          show (A.runMeasure env).map Prod.fst = trajMeasure A.alg env from
            Measure.fst_compProd _ _]
        rfl
    _ = (A.runMeasure env).map (fun ω ↦ (history IT.obs IT.action IT.feedback T ω.1, ω.2)) :=
        ((A.isRun_runMeasure env).hasCondDistrib_output_history hA).map_eq.symm

/-- **Transfer of a PAC guarantee to a partial run.** If `A` is PAC at level `δ` with budget
`T`, `(O, X, Y)` is an algorithm-environment sequence for `A.alg` until time `T` in `env θ` and
`out` has conditional law `A.output.comap (Sigma.mk T) _` (the output rule on histories of
length `T`) given the history of the first `T` rounds, then `out` is `bad θ` with probability at
most `δ`. -/
lemma IsPAC.measureReal_bad_of_isAlgEnvSeqUntil [IsProbabilityMeasure P] {Θ : Type*}
    {env : Θ → Environment Unit 𝓐 𝓨} {bad : Θ → 𝓓 → Prop} {δ : ℝ}
    (hpac : A.IsPAC env bad δ) (hA : A.IsFixedBudget T) (θ : Θ)
    (h : IsAlgEnvSeqUntil O X Y A.alg (env θ) P T)
    (hout : HasCondDistrib out (history O X Y T)
      (A.output.comap (Sigma.mk T) (measurable_sigmaMk T)) P)
    (hbad : MeasurableSet {d | bad θ d}) :
    P.real {ω | bad θ (out ω)} ≤ δ := by
  have hp := hpac.measureReal_bad_of_isRun hbad (A.isRun_runMeasure (env θ))
  have hmap := map_history_out_eq hA h hout
  have hg : Measurable fun ω : (ℕ → Round Unit 𝓐 𝓨) × 𝓓 ↦
      (history IT.obs IT.action IT.feedback T ω.1, ω.2) :=
    ((measurable_history_traj T).comp measurable_fst).prodMk measurable_snd
  have hf : AEMeasurable (fun ω ↦ (history O X Y T ω, out ω)) P := hout.aemeasurable
  calc P.real {ω | bad θ (out ω)}
      = (P.map (fun ω ↦ (history O X Y T ω, out ω))).real (Prod.snd ⁻¹' {d | bad θ d}) := by
        rw [measureReal_def, measureReal_def,
          Measure.map_apply_of_aemeasurable hf (measurable_snd hbad)]
        rfl
    _ = ((A.runMeasure (env θ)).map
          (fun ω ↦ (history IT.obs IT.action IT.feedback T ω.1, ω.2))).real
          (Prod.snd ⁻¹' {d | bad θ d}) := by
        rw [hmap]
    _ = (A.runMeasure (env θ)).real {ω | bad θ ω.2} := by
        rw [measureReal_def, measureReal_def, Measure.map_apply hg (measurable_snd hbad)]
        rfl
    _ ≤ δ := hp

end IdentAlg

end Learning
