import EnvyFreeResearch.Full.UpperAggregateInterpolationTape
import EnvyFreeResearch.Full.UpperCorrectionLoop

/-!
# Laws and predictable domination of actual correction endpoints

The two endpoints are the real ordinary-oracle `firstRun` and `secondRun`
outputs. The second observes the first endpoint and its recordings. Their
marginal laws are derived from their CDF equations for the original raw
oracle measure, and normalization is handled only in the measure bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperCircular UpperRecordedDomain UpperUnionSampling UpperCircularStage
  UpperUnionCircular UpperStageMeasurable Chores

/-- Restriction plus a lower raw-mass bound controls the normalized law. -/
theorem cond_le_restrict (μ : Measure ℝ) [IsFiniteMeasure μ] (S R : Set ℝ)
    (hsub : S ⊆ R) (lower : ℝ) (hlower : 0 < lower) (hmass : lower ≤ μ.real S) :
    cond μ S ≤ ENNReal.ofReal (1 / lower) • μ.restrict R := by
  have hlo : ENNReal.ofReal lower ≤ μ S := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ S)] using
      ENNReal.ofReal_le_ofReal hmass
  have hinv : (μ S)⁻¹ ≤ ENNReal.ofReal (1 / lower) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hlower]
    exact ENNReal.inv_le_inv.mpr hlo
  apply Measure.le_iff.mpr
  intro E hE
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' hinv (Measure.restrict_mono_set μ hsub E)

variable {n : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (hmeas : MeasurablePolicy policy) (history : History n) (cutter : Fin n)
  (cached : Component → ℝ) (cells : List Component)
  (hordered : Ordered cells) (hdisjoint : DisjointComponents cells)
  (hcache : ∀ c ∈ cells, cached c = mass (μ cutter) c)
  (hpositive : 0 < (μ cutter).real (domain cells))

include hpolicy hmeas hordered hdisjoint hcache hpositive

theorem first_endpoint_hasLaw :
    HasLaw (fun start : UpperCircular.Circle =>
      (firstRun policy history cutter cached ((μ cutter).real (domain cells)) cells start).1)
      (cond (μ cutter) (domain cells)) (volume : Measure UpperCircular.Circle) := by
  let : IsProbabilityMeasure (cond (μ cutter) (domain cells)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero _ _ hpositive)
  apply circular_endpoint_law _ 0 _
    (measurable_fst.comp (firstRun_measurable policy hmeas history cutter cached _ cells))
  apply ae_of_all
  intro start
  simpa only [add_zero, Function.comp_apply] using first_cdf μ policy hpolicy history cutter cached cells
    hordered hdisjoint hcache hpositive start

theorem second_endpoint_hasLaw (amount : I) :
    HasLaw (fun start : UpperCircular.Circle =>
      (secondRun policy history cutter cached ((μ cutter).real (domain cells)) cells amount start).1)
      (cond (μ cutter) (domain cells)) (volume : Measure UpperCircular.Circle) := by
  let : IsProbabilityMeasure (cond (μ cutter) (domain cells)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero _ _ hpositive)
  exact circular_endpoint_law _ (project amount) _
    (measurable_fst.comp (secondRun_measurable policy hmeas history cutter cached _ cells amount))
    (ae_of_all _ (second_cdf μ policy hpolicy history cutter cached cells
      hordered hdisjoint hcache hpositive amount))

/-- Both endpoint charges are counted before the correction is accepted or
rejected. Their equality requires no independence between the two endpoints. -/
theorem endpoint_charge_lintegral (amount : I) (u : ℝ → ℝ≥0∞) (hu : Measurable u) :
    (∫⁻ start : UpperCircular.Circle,
      (u (firstRun policy history cutter cached ((μ cutter).real (domain cells)) cells start).1 +
       u (secondRun policy history cutter cached ((μ cutter).real (domain cells)) cells amount start).1)
      ∂volume) = 2 * ∫⁻ z, u z ∂cond (μ cutter) (domain cells) := by
  have hfirst : Measurable (fun start : UpperCircular.Circle =>
      u (firstRun policy history cutter cached ((μ cutter).real (domain cells)) cells start).1) :=
    hu.comp (measurable_fst.comp (firstRun_measurable policy hmeas history cutter cached _ cells))
  rw [lintegral_add_left hfirst]
  rw [(first_endpoint_hasLaw μ policy hpolicy hmeas history cutter cached cells hordered hdisjoint
    hcache hpositive).lintegral_comp hu.aemeasurable,
    (second_endpoint_hasLaw μ policy hpolicy hmeas history cutter cached cells hordered hdisjoint
      hcache hpositive amount).lintegral_comp hu.aemeasurable, two_mul]

/-- A predictable raw supply bound gives the domination needed by aggregate
charging on a larger fixed physical buffer. -/
theorem endpoint_charge_le (amount : I) (u : ℝ → ℝ≥0∞) (hu : Measurable u)
    (R : Set ℝ) (hsub : domain cells ⊆ R) (lower : ℝ) (hlower : 0 < lower)
    (hmass : lower ≤ (μ cutter).real (domain cells)) :
    (∫⁻ start : UpperCircular.Circle,
      (u (firstRun policy history cutter cached ((μ cutter).real (domain cells)) cells start).1 +
       u (secondRun policy history cutter cached ((μ cutter).real (domain cells)) cells amount start).1)
      ∂volume) ≤ (2 * ENNReal.ofReal (1 / lower)) * ∫⁻ z, u z ∂(μ cutter).restrict R := by
  rw [endpoint_charge_lintegral μ policy hpolicy hmeas history cutter cached cells hordered hdisjoint
    hcache hpositive amount u hu]
  have h := lintegral_mono' (cond_le_restrict (μ cutter) (domain cells) R hsub lower hlower hmass)
    (f := u) le_rfl
  rw [lintegral_smul_measure] at h
  exact (mul_le_mul' (le_refl (2 : ℝ≥0∞)) h).trans_eq (mul_assoc _ _ _).symm

end EnvyFreeResearch.Full.UpperAggregateInterpolation
