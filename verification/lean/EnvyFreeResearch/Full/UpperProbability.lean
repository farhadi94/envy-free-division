import Mathlib

/-!
# Continuous sampling for the randomized upper bound

These statements prove distributional consequences of the ordinary legal-root
equation. The root selector may depend on the complete preceding history. No
strict monotonicity, unique-root convention, or assumed sampling law occurs in
the hypotheses. Physical circular pieces and the full oracle protocol are not
constructed in this module.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperProbability

/-- A strict intermediate target forces every legal root strictly inside the
recorded component, even when the cumulative function has plateaus. -/
theorem legal_root_mem_Ioo {F : ℝ → ℝ} (hF : Monotone F)
    {a b target root : ℝ} (ha : F a < target) (hb : target < F b)
    (hroot : F root = target) : root ∈ Ioo a b := by
  constructor
  · by_contra h
    have := hF (le_of_not_gt h)
    rw [hroot] at this
    exact (not_le_of_gt ha) this
  · by_contra h
    have := hF (le_of_not_gt h)
    rw [hroot] at this
    exact (not_le_of_gt hb) this

/-- At any fixed test coordinate, the order of a legal root and that coordinate
is determined by the target, except at the single target level of that
coordinate. This is the precise plateau-safe comparison used below. -/
theorem legal_root_le_iff {F : ℝ → ℝ} (hF : Monotone F)
    {target root x : ℝ} (hroot : F root = target) (hne : target ≠ F x) :
    root ≤ x ↔ target ≤ F x := by
  constructor
  · intro h
    simpa only [hroot] using hF h
  · intro h
    by_contra hr
    have hxr : x ≤ root := (lt_of_not_ge hr).le
    have hh := hF hxr
    rw [hroot] at hh
    exact hne (le_antisymm h hh)

/-- Distinct target levels have strictly ordered legal roots. -/
theorem legal_roots_strictly_ordered {F : ℝ → ℝ} (hF : Monotone F)
    {s t x y : ℝ} (hst : s < t) (hx : F x = s) (hy : F y = t) : x < y := by
  by_contra h
  have hxy := hF (le_of_not_gt h)
  rw [hx, hy] at hxy
  exact (not_le_of_gt hst) hxy

/-- Any measurable choice of legal CDF roots maps a fresh uniform value draw
to the prescribed probability measure. The hypothesis is only the legal-root
equation; the distributional conclusion is proved, not supplied as an interface.

The source is the ordinary Lebesgue probability measure on the unit interval.
The selector may behave arbitrarily on the two null endpoint targets. -/
theorem arbitrary_legal_root_map (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (root : I → ℝ) (hmeas : Measurable root)
    (hlegal : ∀ᵐ t ∂(volume : Measure I), cdf μ (root t) = (t : ℝ)) :
    (volume : Measure I).map root = μ := by
  apply Measure.ext_of_Iic
  intro x
  let c : I := ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩
  have hne : ∀ᵐ t ∂(volume : Measure I), t ≠ c := Measure.ae_ne volume c
  have hsets : root ⁻¹' Iic x =ᵐ[(volume : Measure I)] Iic c := by
    filter_upwards [hlegal, hne] with t ht htc
    change (root t ≤ x) = (t ≤ c)
    apply propext
    apply legal_root_le_iff (monotone_cdf μ) ht
    intro heq
    exact htc (Subtype.ext heq)
  rw [Measure.map_apply hmeas measurableSet_Iic,
    measure_congr hsets, unitInterval.volume_Iic]
  exact ofReal_cdf μ x

/-- In particular, the endpoint law is independent of every fixed preceding
history, even when that history changes the legal root selected on plateaus. -/
theorem history_dependent_legal_root_map {History : Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (root : History → I → ℝ)
    (hmeas : ∀ h, Measurable (root h))
    (hlegal : ∀ h, ∀ᵐ t ∂(volume : Measure I), cdf μ (root h t) = (t : ℝ))
    (h : History) : (volume : Measure I).map (root h) = μ :=
  arbitrary_legal_root_map μ (root h) (hmeas h) (hlegal h)

/-- A fresh uniform target remains an exact independent sample of a fixed row
measure even when the legal root is chosen using the complete previous random
history. This proves the joint law, rather than merely a marginal law. -/
theorem history_root_joint_law {History : Type*} [MeasurableSpace History]
    (historyLaw : Measure History) [SFinite historyLaw]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (root : History → I → ℝ)
    (hmeas : Measurable (Function.uncurry root))
    (hlegal : ∀ᵐ h ∂historyLaw,
      ∀ᵐ t ∂(volume : Measure I), cdf μ (root h t) = (t : ℝ)) :
    MeasurePreserving (fun p : History × I => (p.1, root p.1 p.2))
      (historyLaw.prod (volume : Measure I)) (historyLaw.prod μ) := by
  apply (MeasurePreserving.id historyLaw).skew_product hmeas
  filter_upwards [hlegal] with h hh
  exact arbitrary_legal_root_map μ (root h) hmeas.of_uncurry_left hh

/-- Any measurable target random variable with the uniform value law gives the
same result. The returned root may depend on additional randomness and history
on the source space; it need not be a function of the target alone. -/
theorem arbitrary_legal_root_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (target : Ω → I) (htarget : HasLaw target (volume : Measure I) P)
    (root : Ω → ℝ) (hroot : Measurable root)
    (hlegal : ∀ᵐ ω ∂P, cdf μ (root ω) = (target ω : ℝ)) :
    HasLaw root μ P := by
  refine ⟨hroot.aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro x
  let c : I := ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩
  have hne : ∀ᵐ ω ∂P, target ω ≠ c := by
    apply (htarget.ae_iff (measurableSet_setOfPred.mp
      (measurableSet_singleton c).compl)).mpr
    exact Measure.ae_ne volume c
  have hsets : root ⁻¹' Iic x =ᵐ[P] target ⁻¹' Iic c := by
    filter_upwards [hlegal, hne] with ω hω hωne
    change (root ω ≤ x) = (target ω ≤ c)
    apply propext
    apply legal_root_le_iff (monotone_cdf μ) hω
    intro heq
    exact hωne (Subtype.ext heq)
  rw [Measure.map_apply hroot measurableSet_Iic, measure_congr hsets,
    ← Measure.map_apply_of_aemeasurable htarget.aemeasurable measurableSet_Iic,
    htarget.map_eq, unitInterval.volume_Iic]
  exact ofReal_cdf μ x

/-- The same theorem as an integral identity for every nonnegative measurable
endpoint charge, including unbounded charges. -/
theorem legal_root_lintegral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (root : I → ℝ) (hmeas : Measurable root)
    (hlegal : ∀ᵐ t ∂(volume : Measure I), cdf μ (root t) = (t : ℝ))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t, f (root t) ∂(volume : Measure I)) = ∫⁻ x, f x ∂μ := by
  rw [← arbitrary_legal_root_map μ root hmeas hlegal]
  exact (lintegral_map hf hmeas).symm

end EnvyFreeResearch.Full.UpperProbability
