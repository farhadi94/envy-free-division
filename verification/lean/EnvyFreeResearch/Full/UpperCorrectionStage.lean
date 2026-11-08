import EnvyFreeResearch.Full.UpperUnionCircular
import EnvyFreeResearch.Full.UpperSignedCircular
import EnvyFreeResearch.Full.UpperCorrections

/-!
# The actual circular correction stage

The requested amount is the owner deficit divided by the physical remaining
mass. Exact own value, real foreign expectation, and its Markov bound are
derived for the concrete two ordinary-Cut implementation against every
jointly measurable legal full-history reply policy.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperCorrectionStage

open UpperCircular UpperPhysical UpperCircularStage UpperRecordedDomain UpperUnionSampling
  UpperStageMeasurable UpperUnionMeasurable UpperUnionCircular Chores

abbrev Circle := UpperCircular.Circle

def fraction (eps total : ℝ) (heps : 0 ≤ eps) (hfit : eps ≤ total) (hpos : 0 < total) : I :=
  ⟨eps / total, div_nonneg heps hpos.le, (div_le_one hpos).mpr hfit⟩

theorem fraction_mul_total (eps total : ℝ) (heps : 0 ≤ eps) (hfit : eps ≤ total)
    (hpos : 0 < total) : (fraction eps total heps hfit hpos : ℝ) * total = eps :=
  div_mul_cancel₀ eps hpos.ne'

variable {n : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (history : History n) (cutter : Fin n) (cached : Component → ℝ)
  (cells : List Component) (hordered : Ordered cells) (hdisjoint : DisjointComponents cells)
  (hcache : ∀ c ∈ cells, cached c = mass (μ cutter) c)
  (hpositive : 0 < (μ cutter).real (domain cells))

include hpolicy hordered hdisjoint hcache hpositive in
theorem exact_deficit (eps : ℝ) (heps : 0 ≤ eps) (hfit : eps ≤ (μ cutter).real (domain cells))
    (start : Circle) :
    (μ cutter).real (piece policy history cutter cached ((μ cutter).real (domain cells)) cells
      (fraction eps _ heps hfit hpositive) start) = eps := by
  rw [exact_cutter_mass μ policy hpolicy history cutter cached cells
    hordered hdisjoint hcache hpositive]
  exact fraction_mul_total ..

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)] in
theorem foreign_integrable (hmeas : MeasurablePolicy policy) (amount : I)
    (foreign : Measure ℝ) [IsFiniteMeasure foreign] :
    Integrable (fun start => foreign.real
      (piece policy history cutter cached ((μ cutter).real (domain cells)) cells amount start))
      (volume : Measure Circle) :=
  UpperSignedCircular.foreign_real_mass_integrable (domain cells) (domain_measurable cells) amount
    _ _
    (measurable_fst.comp (firstRun_measurable policy hmeas history cutter cached _ cells))
    (measurable_fst.comp (secondRun_measurable policy hmeas history cutter cached _ cells amount)) foreign

include hpolicy hordered hdisjoint hcache hpositive in
theorem foreign_real_expectation (hmeas : MeasurablePolicy policy) (amount : I)
    (foreign : Measure ℝ) [IsFiniteMeasure foreign] :
    (∫ start, foreign.real
      (piece policy history cutter cached ((μ cutter).real (domain cells)) cells amount start)
      ∂(volume : Measure Circle)) = (amount : ℝ) * foreign.real (domain cells) := by
  let : IsProbabilityMeasure (cond (μ cutter) (domain cells)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero _ _ hpositive)
  apply UpperSignedCircular.foreign_real_mass_expectation
    (domain cells) (domain_measurable cells) amount _ _
    (measurable_fst.comp (firstRun_measurable policy hmeas history cutter cached _ cells))
    (measurable_fst.comp (secondRun_measurable policy hmeas history cutter cached _ cells amount))
    (monotone_cdf (cond (μ cutter) (domain cells)))
  · intro z _
    exact ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  · exact ae_of_all _ (first_cdf μ policy hpolicy history cutter cached cells
      hordered hdisjoint hcache hpositive)
  · exact ae_of_all _ (second_cdf μ policy hpolicy history cutter cached cells
      hordered hdisjoint hcache hpositive amount)

include hpolicy hordered hdisjoint hcache hpositive in
/-- The estimate is valid at the entire pre-start history. The underlying
policy may respond to the second Cut using every answer from the first. -/
theorem foreign_expectation_le (hmeas : MeasurablePolicy policy)
    (eps N : ℝ) (heps : 0 ≤ eps) (hfit : eps ≤ (μ cutter).real (domain cells))
    (hsupply : 1 / 2 ≤ (μ cutter).real (domain cells))
    (foreign : Measure ℝ) [IsFiniteMeasure foreign] (hN : foreign.real (domain cells) ≤ N) :
    (∫ start, foreign.real (piece policy history cutter cached ((μ cutter).real (domain cells))
      cells (fraction eps _ heps hfit hpositive) start) ∂(volume : Measure Circle)) ≤ 2 * eps * N := by
  rw [foreign_real_expectation μ policy hpolicy history cutter cached cells
    hordered hdisjoint hcache hpositive hmeas]
  have hf : eps / (μ cutter).real (domain cells) ≤ 2 * eps := by
    apply (div_le_iff₀ hpositive).mpr
    nlinarith
  exact mul_le_mul hf hN measureReal_nonneg (by positivity)

include hpolicy hordered hdisjoint hcache hpositive in
/-- Markov for one actually executed correction. The cost includes all
queries even when this correction is the first one to reject. -/
theorem foreign_exceed_probability (hmeas : MeasurablePolicy policy)
    (eps N lam : ℝ) (heps : 0 ≤ eps) (hfit : eps ≤ (μ cutter).real (domain cells))
    (hsupply : 1 / 2 ≤ (μ cutter).real (domain cells)) (hlam : 0 < lam)
    (foreign : Measure ℝ) [IsFiniteMeasure foreign] (hN : foreign.real (domain cells) ≤ N) :
    (volume : Measure Circle) {start | lam / 4 < foreign.real
      (piece policy history cutter cached ((μ cutter).real (domain cells))
        cells (fraction eps _ heps hfit hpositive) start)} ≤ ENNReal.ofReal (8 * eps * N / lam) := by
  let amount := fraction eps ((μ cutter).real (domain cells)) heps hfit hpositive
  let f (start : Circle) := foreign.real
    (piece policy history cutter cached ((μ cutter).real (domain cells)) cells amount start)
  have hi : Integrable f (volume : Measure Circle) :=
    foreign_integrable μ policy history cutter cached cells hmeas amount foreign
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (volume : Measure Circle) (fun start => (show 0 ≤ f start from measureReal_nonneg)))
    hi (lam / 4)
  have hmean := foreign_expectation_le μ policy hpolicy history cutter cached cells
    hordered hdisjoint hcache hpositive hmeas eps N heps hfit hsupply foreign hN
  have hbound : (volume : Measure Circle).real {start | lam / 4 ≤ f start} ≤ 8 * eps * N / lam := by
    apply (le_div_iff₀ hlam).mpr
    change lam / 4 * (volume : Measure Circle).real {start | lam / 4 ≤ f start} ≤ _ at hm
    change (∫ start, f start ∂(volume : Measure Circle)) ≤ _ at hmean
    nlinarith
  calc
    _ ≤ (volume : Measure Circle) {start | lam / 4 ≤ f start} := by
      apply measure_mono
      intro start h
      change lam / 4 < f start at h
      exact h.le
    _ = ENNReal.ofReal ((volume : Measure Circle).real {start | lam / 4 ≤ f start}) :=
      (ofReal_measureReal (by finiteness)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

end EnvyFreeResearch.Full.UpperCorrectionStage
