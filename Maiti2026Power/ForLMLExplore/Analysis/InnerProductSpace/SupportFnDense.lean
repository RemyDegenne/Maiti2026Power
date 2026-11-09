/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.ForLMLExplore.Analysis.InnerProductSpace.SupportFn
public import LMLExplore.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Order.PartialSups

/-!
# The support function as a supremum over a dense sequence

For a nonempty compact set `K` of a separable inner product space there is a sequence
`q : ℕ → K` dense in `K`, and the support function `supportFn K v = sup_{x ∈ K} ⟪x, v⟫` is the
supremum of the sequence `⟪q n, v⟫` (`exists_forall_supportFn_eq_iSup`), hence the limit of the
nondecreasing partial maxima `partialSups (fun i ↦ ⟪q i, v⟫) n = max_{i ≤ n} ⟪q i, v⟫` (Mathlib's
`partialSups`, `tendsto_partialSups_inner`). This is the countable reduction used to pass from
finite to compact index sets in the Borell–TIS inequality (blueprint `lem:sup_countable_dense`).
-/

@[expose] public section

open Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {R : ℝ}

lemma bddAbove_range_inner_seq {q : ℕ → E} (hq : ∀ n, q n ∈ K) (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (v : E) : BddAbove (Set.range fun n ↦ ⟪q n, v⟫) :=
  ⟨R * ‖v‖, by
    rintro _ ⟨n, rfl⟩
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR _ (hq n)) (norm_nonneg _))⟩

lemma abs_partialSups_inner_le {q : ℕ → E} (hq : ∀ n, q n ∈ K) (hR : ∀ x ∈ K, ‖x‖ ≤ R) (n : ℕ)
    (v : E) : |partialSups (fun i ↦ ⟪q i, v⟫) n| ≤ R * ‖v‖ := by
  have : Nonempty (Set.Iic n) := ⟨⟨n, Set.mem_Iic.2 le_rfl⟩⟩
  rw [partialSups_eq_ciSup_Iic]
  exact abs_ciSup_le fun i ↦ (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hR _ (hq i)) (norm_nonneg _))

lemma partialSups_inner_le_supportFn {q : ℕ → E} (hq : ∀ n, q n ∈ K) (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (n : ℕ) (v : E) : partialSups (fun i ↦ ⟪q i, v⟫) n ≤ supportFn K v :=
  partialSups_le _ _ _ fun i _ ↦ inner_le_supportFn hR (hq i) v

/-- **The support function of a compact set is a supremum over a dense sequence**
(blueprint `lem:sup_countable_dense`): for a nonempty compact `K` in a separable space there is
a sequence `q` of points of `K` with `supportFn K v = ⨆ n, ⟪q n, v⟫` for every `v`. -/
lemma exists_forall_supportFn_eq_iSup [SecondCountableTopology E] (hK : IsCompact K)
    (hne : K.Nonempty) :
    ∃ q : ℕ → E, (∀ n, q n ∈ K) ∧ ∀ v, supportFn K v = ⨆ n, ⟪q n, v⟫ := by
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ K, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : E)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  have : Nonempty K := hne.to_subtype
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq K
  refine ⟨fun n ↦ (q n : E), fun n ↦ (q n).2, fun v ↦ le_antisymm ?_ ?_⟩
  · obtain ⟨x, hx, hxv⟩ := exists_supportFn_eq_inner hK hne v
    rw [hxv]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hq ⟨x, hx⟩ (ε / (1 + ‖v‖)) (by positivity)
    rw [Subtype.dist_eq, dist_eq_norm] at hn
    have h1 : ⟪x, v⟫ - ⟪(q n : E), v⟫ ≤ ε := by
      calc ⟪x, v⟫ - ⟪(q n : E), v⟫ = ⟪x - q n, v⟫ := (inner_sub_left _ _ _).symm
        _ ≤ ‖x - q n‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ ε / (1 + ‖v‖) * ‖v‖ := by gcongr
        _ ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg v]
    calc ⟪x, v⟫ ≤ ⟪(q n : E), v⟫ + ε := by linarith
      _ ≤ (⨆ n, ⟪(q n : E), v⟫) + ε := by
          gcongr
          exact le_ciSup (bddAbove_range_inner_seq (fun n ↦ (q n).2) hR v) n
  · exact ciSup_le fun n ↦ inner_le_supportFn hR (q n).2 v

/-- The partial maxima `max_{i ≤ n} ⟪q i, v⟫` converge to `supportFn K v` when `q` is dense in
the compact set `K` (in the sense of `exists_forall_supportFn_eq_iSup`). -/
lemma tendsto_partialSups_inner {q : ℕ → E} (hq : ∀ n, q n ∈ K) (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hsup : ∀ v, supportFn K v = ⨆ n, ⟪q n, v⟫) (v : E) :
    Tendsto (fun n ↦ partialSups (fun i ↦ ⟪q i, v⟫) n) atTop (𝓝 (supportFn K v)) := by
  rw [hsup v, ← ciSup_partialSups_eq' (fun i ↦ ⟪q i, v⟫)]
  exact tendsto_atTop_ciSup (partialSups _).monotone
    (bddAbove_range_partialSups.2 (bddAbove_range_inner_seq hq hR v))

end
