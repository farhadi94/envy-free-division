import EnvyFreeResearch.Full.UpperExpectedRuntime

/-! Turning a fresh-draw bound at every complete history into an unconditional
paid-attempt inequality. The success set can depend arbitrarily on history. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace EnvyFreeResearch.Full.UpperExpectedRuntime

variable {History Draw : Type*} [MeasurableSpace History] [MeasurableSpace Draw]

theorem fiber_attempt_bound (μ : Measure History) (ν : Measure Draw) [SFinite ν]
    (active : Set History) (ha : MeasurableSet active)
    (success : Set (History × Draw)) (hs : MeasurableSet success)
    (factor : ℝ≥0∞) (hf : factor ≠ ∞)
    (hchance : ∀ h ∈ active, 1 ≤ factor * ν {d | (h,d) ∈ success}) :
    μ active ≤ factor * (μ.prod ν) success := by
  calc
    μ active = ∫⁻ h, active.indicator (fun _ => (1 : ℝ≥0∞)) h ∂μ := by
      simp [lintegral_indicator_const ha]
    _ ≤ ∫⁻ h, factor * ν {d | (h,d) ∈ success} ∂μ := by
      apply lintegral_mono
      intro h
      by_cases hh : h ∈ active
      · simpa only [indicator_of_mem hh] using hchance h hh
      · simp only [indicator_of_notMem hh]
        exact zero_le
    _ = factor * (μ.prod ν) success := by
      rw [lintegral_const_mul' factor _ hf, Measure.prod_apply hs]
      rfl

/-- A measurable law-preserving representation transports the history/fresh
coordinate calculation back to the original execution tape. -/
theorem original_tape_attempt_bound {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (μ : Measure History) (ν : Measure Draw) [SFinite ν]
    (project : Ω → History × Draw) (hp : MeasurePreserving project ρ (μ.prod ν))
    (active : Set History) (ha : MeasurableSet active)
    (success : Set (History × Draw)) (hs : MeasurableSet success)
    (factor : ℝ≥0∞) (hf : factor ≠ ∞)
    (hchance : ∀ h ∈ active, 1 ≤ factor * ν {d | (h,d) ∈ success}) :
    μ active ≤ factor * ρ (project ⁻¹' success) := by
  rw [hp.measure_preimage hs.nullMeasurableSet]
  exact fiber_attempt_bound μ ν active ha success hs factor hf hchance

end EnvyFreeResearch.Full.UpperExpectedRuntime
