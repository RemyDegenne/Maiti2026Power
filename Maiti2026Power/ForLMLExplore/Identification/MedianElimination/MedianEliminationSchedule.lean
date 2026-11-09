/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import LMLExplore.Identification.MedianElimination

/-!
# The schedule of Median Elimination

Median Elimination runs in rounds `ℓ = 0, 1, …, L - 1`. In round `ℓ` it pulls each of the
`s_ℓ` surviving arms `n_ℓ` times, then discards the worse half of them (rounded down), so that
`s_{ℓ+1} = ⌈s_ℓ / 2⌉` (LMLExplore's `MedianElimination.armsCount K ℓ`, `armsCount_succ_eq`). The
round accuracies and confidences are `ε_ℓ = (ε / 4) (3/4)^ℓ` and `δ_ℓ = δ / 2^(ℓ+1)`, with
`∑ ε_ℓ ≤ ε` and `∑ δ_ℓ ≤ δ`, and the number of pulls is `n_ℓ = ⌈8 log(3/δ_ℓ) / ε_ℓ²⌉₊`
(LMLExplore's `MedianElimination.pullSchedule 1 ε δ ℓ`, `le_pullSchedule`). After
`L = ⌈log₂ K⌉` rounds (`MedianElimination.numPhases K`) a single arm survives
(`MedianElimination.armsCount_numPhases`).

This file defines the accuracies and confidences and proves, from LMLExplore's budget bound
`MedianElimination.phaseEnd_pullSchedule_le`, the bound
`N_ME(K, ε, δ) = ∑_{ℓ < L} s_ℓ n_ℓ ≤ 16000 K log(3/δ) / ε²` for `ε ≤ 1` (the budget
`N_ME(K, ε, δ)` is `MedianElimination.phaseEnd K (pullSchedule 1 ε δ) L`).

Blueprint: `def:me_schedule`, `lem:me_schedule_sums`, `def:pm_halving`, `lem:me_budget`.
-/

@[expose] public section

open Finset
open LMLExplore.Identification.MedianElimination (armsCount armsCount_succ numPhases pullSchedule
  pullSchedule_def phaseEnd phaseEnd_pullSchedule_le)

namespace Learning.MedianElim

variable {ε δ : ℝ} {K ℓ : ℕ}

/-! ### Accuracy and confidence schedules -/

/-- Accuracy of round `ℓ`: `ε_ℓ = (ε / 4) (3/4)^ℓ`. -/
noncomputable def epsSched (ε : ℝ) (ℓ : ℕ) : ℝ := ε / 4 * (3 / 4) ^ ℓ

/-- Confidence of round `ℓ`: `δ_ℓ = δ / 2^(ℓ+1)`. -/
noncomputable def deltaSched (δ : ℝ) (ℓ : ℕ) : ℝ := δ / 2 ^ (ℓ + 1)

lemma epsSched_pos (hε : 0 < ε) (ℓ : ℕ) : 0 < epsSched ε ℓ := by
  unfold epsSched; positivity

lemma deltaSched_pos (hδ : 0 < δ) (ℓ : ℕ) : 0 < deltaSched δ ℓ := by
  unfold deltaSched; positivity

lemma deltaSched_lt_one (hδ : δ < 1) (ℓ : ℕ) : deltaSched δ ℓ < 1 := by
  rw [deltaSched, div_lt_one (by positivity)]
  exact hδ.trans_le (one_le_pow₀ (by norm_num))

/-- The sum of the round accuracies is at most `ε`. -/
lemma sum_epsSched_le (hε : 0 ≤ ε) (L : ℕ) : ∑ ℓ ∈ range L, epsSched ε ℓ ≤ ε := by
  simp_rw [epsSched, ← mul_sum]
  have h := geom_sum_Ico_le_of_lt_one (x := (3 / 4 : ℝ)) (m := 0) (n := L) (by norm_num)
    (by norm_num)
  rw [← range_eq_Ico] at h
  calc ε / 4 * ∑ ℓ ∈ range L, (3 / 4 : ℝ) ^ ℓ ≤ ε / 4 * ((3 / 4) ^ 0 / (1 - 3 / 4)) := by gcongr
  _ = ε := by ring

/-- The sum of the round confidences is at most `δ`. -/
lemma sum_deltaSched_le (hδ : 0 ≤ δ) (L : ℕ) : ∑ ℓ ∈ range L, deltaSched δ ℓ ≤ δ := by
  have h : ∀ ℓ, deltaSched δ ℓ = δ / 2 * (1 / 2) ^ ℓ := fun ℓ ↦ by
    rw [deltaSched, pow_succ, one_div_pow]; ring
  simp_rw [h, ← mul_sum]
  calc δ / 2 * ∑ ℓ ∈ range L, (1 / 2 : ℝ) ^ ℓ ≤ δ / 2 * 2 := by
        gcongr; exact sum_geometric_two_le L
  _ = δ := by ring

lemma log_deltaSched (hδ : 0 < δ) (ℓ : ℕ) :
    Real.log (3 / deltaSched δ ℓ) = Real.log (3 / δ) + (ℓ + 1) * Real.log 2 := by
  rw [deltaSched, div_div_eq_mul_div, mul_div_right_comm,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

lemma log_deltaSched_pos (hδ : δ ∈ Set.Ioo 0 1) (ℓ : ℕ) :
    0 < Real.log (3 / deltaSched δ ℓ) := by
  refine Real.log_pos ?_
  rw [one_lt_div (deltaSched_pos hδ.1 ℓ)]
  linarith [deltaSched_lt_one hδ.2 ℓ]

/-! ### Number of pulls per round -/

/-- The number of pulls of each surviving arm in round `ℓ`, LMLExplore's
`MedianElimination.pullSchedule 1 ε δ ℓ`, is `n_ℓ = ⌈8 log(3/δ_ℓ) / ε_ℓ²⌉₊`. -/
lemma le_pullSchedule (ε δ : ℝ) (ℓ : ℕ) :
    8 * Real.log (3 / deltaSched δ ℓ) / epsSched ε ℓ ^ 2 ≤ pullSchedule 1 ε δ ℓ := by
  calc 8 * Real.log (3 / deltaSched δ ℓ) / epsSched ε ℓ ^ 2
      = 8 * 1 / (ε / 4 * (3 / 4) ^ ℓ) ^ 2 * Real.log (3 * 2 ^ (ℓ + 1) / δ) := by
        rw [deltaSched, epsSched, div_div_eq_mul_div]
        ring
    _ ≤ (pullSchedule 1 ε δ ℓ : ℝ) := by
        rw [pullSchedule_def]
        exact Nat.le_ceil _

lemma pullSchedule_pos (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1) (ℓ : ℕ) :
    0 < pullSchedule 1 ε δ ℓ := by
  have := log_deltaSched_pos hδ ℓ
  have := epsSched_pos hε ℓ
  exact Nat.cast_pos.1 ((by positivity : (0 : ℝ) < 8 * Real.log (3 / deltaSched δ ℓ) /
    epsSched ε ℓ ^ 2).trans_le (le_pullSchedule ε δ ℓ))

/-! ### Surviving arms -/

/-- The number of arms surviving round `ℓ` of Median Elimination with `K` arms, LMLExplore's
`MedianElimination.armsCount K (ℓ + 1)`, is `s_{ℓ+1} = ⌈s_ℓ / 2⌉`. -/
lemma armsCount_succ_eq (K ℓ : ℕ) : armsCount K (ℓ + 1) = (armsCount K ℓ + 1) / 2 := by
  rw [armsCount_succ]
  omega

/-! ### Total budget -/

/-- Budget bound (blueprint `lem:me_budget`): for `ε ≤ 1`, the budget
`N_ME(K, ε, δ) = ∑_{ℓ < L} s_ℓ n_ℓ` of Median Elimination with `K` arms, LMLExplore's
`MedianElimination.phaseEnd K (pullSchedule 1 ε δ) (numPhases K)`, is at most
`16000 K log(3/δ) / ε²`. -/
lemma budget_le_of_le_one (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) (K : ℕ) :
    (phaseEnd K (pullSchedule 1 ε δ) (numPhases K) : ℝ) ≤
      16000 * K * Real.log (3 / δ) / ε ^ 2 := by
  have h := phaseEnd_pullSchedule_le (σ2 := 1) (ε := ε) zero_le_one hδ.1 (by linarith [hδ.2]) K
  have hlog : Real.log (1536 / δ) = Real.log (3 / δ) + 9 * Real.log 2 := by
    rw [show (1536 : ℝ) / δ = 3 / δ * 2 ^ 9 by ring,
      Real.log_mul (div_pos (by norm_num) hδ.1).ne' (by positivity), Real.log_pow]
    norm_num
  rw [hlog] at h
  have hA : 1.0986122885 < Real.log (3 / δ) :=
    Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) (le_div_self (by norm_num) hδ.1 hδ.2.le))
  have hB := Real.log_two_lt_d9
  set A := Real.log (3 / δ) with hA_def
  set B := Real.log 2 with hB_def
  set c := (K : ℝ) / ε ^ 2 with hc_def
  have hc : 0 ≤ c := by positivity
  have hKc : (K : ℝ) ≤ c := by
    rw [hc_def, le_div_iff₀ (pow_pos hε.1 2)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg K) (pow_le_one₀ hε.1.le hε.2)
  have h1 := mul_le_mul_of_nonneg_left hB.le hc
  have h2 := mul_le_mul_of_nonneg_left hA.le hc
  calc (phaseEnd K (pullSchedule 1 ε δ) (numPhases K) : ℝ)
      ≤ 2304 * K * 1 / ε ^ 2 * (A + 9 * B) + 4 * K := h
  _ = 2304 * c * (A + 9 * B) + 4 * K := by rw [hc_def]; ring
  _ ≤ 16000 * c * A := by nlinarith
  _ = 16000 * K * A / ε ^ 2 := by rw [hc_def]; ring

end Learning.MedianElim
