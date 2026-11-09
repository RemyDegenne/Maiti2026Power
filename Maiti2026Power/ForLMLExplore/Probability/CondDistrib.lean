/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MapComap
public import LMLExplore.Probability.HasCondDistrib

/-!
# Lemmas on conditional distributions and kernels

General facts about `HasCondDistrib` used throughout the sequential-learning developments:

* `HasCondDistrib.const_comp_right`: a constant conditional law given `Z` is a constant
  conditional law given any measurable function of `Z` (Mathlib's `HasCondDistrib.comp_right`
  with LML's `Kernel.comap_const`);
* `map_snd_compProd_comap`: the law of the second coordinate under `μ ⊗ₘ η.comap f` (through Tau
  Ceti's `Measure.map_prodMap_compProd_comap`; the conditional law of that coordinate is
  LMLExplore's `hasCondDistrib_snd_compProd_comap`);
* `HasCondDistrib.measureReal_le_mul`, `HasCondDistrib.measureReal_sub_le`: a uniform bound on
  the conditional probability of an event given `Z` bounds its probability (Fubini);
* `Measure.map_compProd_of_forall_map_eq`, `HasCondDistrib.map_of_forall_map_eq`: the image of a
  composition-product `μ ⊗ₘ κ` by a map `(a, b) ↦ (G a, F a b)` is the composition-product
  `μ.map G ⊗ₘ K` when `K (G a) = (κ a).map (F a)`;
* `HasCondDistrib.restrict_preimage`: a conditional law given `X` is preserved by restricting the
  measure to an event determined by `X` (through Tau Ceti's `Measure.compProd_restrict_left`).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

section const

variable {Ω β 𝓧 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} {ν : Measure β} {Y : Ω → β}

/-- A constant conditional law given `Z` is a constant conditional law given any measurable
function of `Z`. -/
lemma HasCondDistrib.const_comp_right [SFinite P] [SFinite ν] {Z : Ω → 𝓩}
    (h : HasCondDistrib Y Z (Kernel.const 𝓩 ν) P)
    {f : 𝓩 → 𝓧} (hf : Measurable f) : HasCondDistrib Y (f ∘ Z) (Kernel.const 𝓧 ν) P := by
  refine HasCondDistrib.comp_right (hf := hf) ?_
  rwa [Kernel.comap_const]

end const

section compProd

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- The image of `μ ⊗ₘ κ` by `(a, b) ↦ (G a, F a b)` is `μ.map G ⊗ₘ K` as soon as `K (G a)` is
the image of `κ a` by `F a` for every `a`. -/
lemma _root_.MeasureTheory.Measure.map_compProd_of_forall_map_eq {δ : Type*}
    {mδ : MeasurableSpace δ} (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {G : α → γ} (hG : Measurable G)
    {F : α → β → δ} (hF : Measurable (Function.uncurry F)) (K : Kernel γ δ) [IsSFiniteKernel K]
    (hK : ∀ a, K (G a) = (κ a).map (F a)) :
    (μ ⊗ₘ κ).map (fun p ↦ (G p.1, F p.1 p.2)) = μ.map G ⊗ₘ K := by
  have hφ : Measurable fun p : α × β ↦ (G p.1, F p.1 p.2) := (hG.comp measurable_fst).prodMk hF
  ext s hs
  rw [Measure.map_apply hφ hs, Measure.compProd_apply (hφ hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hG]
  refine lintegral_congr fun a ↦ ?_
  have hFa : Measurable (F a) := hF.comp measurable_prodMk_left
  rw [hK a, Measure.map_apply hFa (measurable_prodMk_left hs)]
  rfl

/-- The law of the second coordinate under `μ ⊗ₘ η.comap f` is its law under `μ.map f ⊗ₘ η`. -/
lemma map_snd_compProd_comap (μ : Measure α) [SFinite μ] (η : Kernel β γ) [IsSFiniteKernel η]
    {f : α → β} (hf : Measurable f) :
    (μ ⊗ₘ η.comap f hf).map Prod.snd = (μ.map f ⊗ₘ η).map Prod.snd := by
  rw [← Measure.map_prodMap_compProd_comap μ η hf,
    Measure.map_map measurable_snd (hf.prodMap measurable_id)]
  rfl

end compProd

section map

variable {Ω α β γ δ : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {P : Measure Ω}
  [SFinite P] {X : Ω → α} {Y : Ω → β} {κ : Kernel α β} [IsSFiniteKernel κ]

/-- If `Y` has conditional law `κ` given `X`, then `F X Y` has conditional law `K` given `G X`
as soon as `K (G a)` is the image of `κ a` by `F a` for every `a`. -/
lemma HasCondDistrib.map_of_forall_map_eq (h : HasCondDistrib Y X κ P) {G : α → γ}
    (hG : Measurable G) {F : α → β → δ} (hF : Measurable (Function.uncurry F)) (K : Kernel γ δ)
    [IsSFiniteKernel K] (hK : ∀ a, K (G a) = (κ a).map (F a)) :
    HasCondDistrib (fun ω ↦ F (X ω) (Y ω)) (G ∘ X) K P := by
  refine ⟨(hG.comp_aemeasurable h.aemeasurable_fst).prodMk (hF.comp_aemeasurable h.aemeasurable),
    ?_⟩
  have hφ : Measurable fun p : α × β ↦ (G p.1, F p.1 p.2) := (hG.comp measurable_fst).prodMk hF
  calc P.map (fun ω ↦ ((G ∘ X) ω, F (X ω) (Y ω)))
      = (P.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ (G p.1, F p.1 p.2)) := by
        rw [AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable h.aemeasurable]
        rfl
    _ = (P.map X ⊗ₘ κ).map (fun p ↦ (G p.1, F p.1 p.2)) := by rw [h.map_eq]
    _ = (P.map X).map G ⊗ₘ K := Measure.map_compProd_of_forall_map_eq _ _ hG hF K hK
    _ = P.map (G ∘ X) ⊗ₘ K := by
        rw [AEMeasurable.map_map_of_aemeasurable hG.aemeasurable h.aemeasurable_fst]

/-- A conditional law given `X` is a conditional law given `X` under the restriction of `P` to an
event determined by `X`. -/
lemma HasCondDistrib.restrict_preimage (hX : Measurable X) (hY : Measurable Y)
    (h : HasCondDistrib Y X κ P) {s : Set α} (hs : MeasurableSet s) :
    HasCondDistrib Y X κ (P.restrict (X ⁻¹' s)) := by
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  have h1 : (fun ω ↦ (X ω, Y ω)) ⁻¹' (s ×ˢ Set.univ) = X ⁻¹' s := by ext ω; simp
  calc (P.restrict (X ⁻¹' s)).map (fun ω ↦ (X ω, Y ω))
      = (P.map (fun ω ↦ (X ω, Y ω))).restrict (s ×ˢ Set.univ) := by
        rw [Measure.restrict_map (hX.prodMk hY) (hs.prod MeasurableSet.univ), h1]
    _ = (P.map X ⊗ₘ κ).restrict (s ×ˢ Set.univ) := by rw [h.map_eq]
    _ = (P.map X).restrict s ⊗ₘ κ := (Measure.compProd_restrict_left _ _ hs).symm
    _ = (P.restrict (X ⁻¹' s)).map X ⊗ₘ κ := by rw [Measure.restrict_map hX hs]

end map

section bound

variable {Ω β 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} [IsFiniteMeasure P] {W : Ω → β} {Z : Ω → 𝓩}
  {κ : Kernel 𝓩 β} {G : Set 𝓩} {G' : Set (𝓩 × β)} {δ : ℝ}

/-- If the conditional law of `W` given `Z` is `κ` and, for every `z` in the measurable set `G`,
the section of the measurable set `G'` at `z` has `κ z`-probability at most `δ`, then
`P(Z ∈ G, (Z, W) ∈ G') ≤ δ P(Z ∈ G)`. -/
lemma HasCondDistrib.measureReal_le_mul [IsFiniteKernel κ] (h : HasCondDistrib W Z κ P)
    (hG : MeasurableSet G) (hG' : MeasurableSet G') (hδ0 : 0 ≤ δ)
    (hδ : ∀ z ∈ G, (κ z).real (Prod.mk z ⁻¹' G') ≤ δ) :
    P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') ≤ δ * P.real (Z ⁻¹' G) := by
  have hS : MeasurableSet ((G ×ˢ Set.univ) ∩ G') := (hG.prod MeasurableSet.univ).inter hG'
  have h1 : Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G' =
      (fun ω ↦ (Z ω, W ω)) ⁻¹' ((G ×ˢ Set.univ) ∩ G') := by
    ext ω
    simp
  have h2 : ∀ z, κ z (Prod.mk z ⁻¹' ((G ×ˢ Set.univ) ∩ G')) =
      G.indicator (fun z ↦ κ z (Prod.mk z ⁻¹' G')) z := fun z ↦ by
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_mem hz]
      congr 1
      ext w
      simp [hz]
    · rw [Set.indicator_of_notMem hz]
      convert measure_empty (μ := κ z)
      ext w
      simp [hz]
  rw [h1, measureReal_def, measureReal_def,
    ← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hG,
    ← Measure.map_apply_of_aemeasurable h.aemeasurable hS, h.map_eq, Measure.compProd_apply hS]
  simp_rw [h2]
  rw [lintegral_indicator hG, ← ENNReal.toReal_ofReal hδ0, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) ?_
  rw [← setLIntegral_const]
  refine setLIntegral_mono' hG fun z hz ↦ ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top (κ z) _)]
  exact ENNReal.ofReal_le_ofReal (hδ z hz)

/-- If the conditional law of `W` given `Z` is `κ` and, for every `z` in the measurable set `G`,
the section of the measurable set `G'` at `z` has `κ z`-probability at least `1 - δ`, then
`P((Z, W) ∈ G') ≥ P(Z ∈ G) - δ`. -/
lemma HasCondDistrib.measureReal_sub_le [IsProbabilityMeasure P] [IsMarkovKernel κ]
    (h : HasCondDistrib W Z κ P) (hG : MeasurableSet G) (hG' : MeasurableSet G') (hδ0 : 0 ≤ δ)
    (hδ : ∀ z ∈ G, 1 - δ ≤ (κ z).real (Prod.mk z ⁻¹' G')) :
    P.real (Z ⁻¹' G) - δ ≤ P.real ((fun ω ↦ (Z ω, W ω)) ⁻¹' G') := by
  have h1 := h.measureReal_le_mul hG hG'.compl hδ0 fun z hz ↦ by
    rw [Set.preimage_compl, measureReal_compl (measurable_prodMk_left hG'), probReal_univ]
    linarith [hδ z hz]
  have h2 : P.real (Z ⁻¹' G) ≤ P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') +
      P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G'ᶜ) := by
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro ω hω
    by_cases hω' : (Z ω, W ω) ∈ G' <;> simp [hω]
  have h3 : P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') ≤
      P.real ((fun ω ↦ (Z ω, W ω)) ⁻¹' G') := measureReal_mono Set.inter_subset_right
  have h4 : δ * P.real (Z ⁻¹' G) ≤ δ := by
    calc δ * P.real (Z ⁻¹' G) ≤ δ * 1 := by gcongr; exact measureReal_le_one
      _ = δ := mul_one δ
  linarith

end bound

end ProbabilityTheory
