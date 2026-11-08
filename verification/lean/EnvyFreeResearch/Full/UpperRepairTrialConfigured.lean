import EnvyFreeResearch.Full.UpperRepairTrialProbability
import EnvyFreeResearch.Full.UpperRepairParameters

/-! The literal manuscript parameters bound the actual compiled trial's
unconditional rejection probability, uniformly over all legal Borel
full-history oracle policies and both allocation orientations. -/

noncomputable section

open MeasureTheory
open scoped Classical unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperRepairTrialConfigured

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairPreparationChecks UpperRepairTrialProgram UpperRepairTrialLaw
  UpperRepairTrialRejection UpperRepairParameters UpperRepairJobs

variable {n k s ell : ℕ} [Nonempty (Fin k)]

theorem failure_lt (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell)
    (hscale : (2^40 : ℝ) * k ≤ s) (hlog : Real.log (2 * (k : ℝ)) ≤ ell)
    (hnear : Near chores μ active origin old (oldError s ell)) :
    trialLaw k (coarseCount s ell) (samples s ell) (repetitions s ell)
      (Failed policy hk chores active origin old (coarseCount s ell) (samples s ell) (repetitions s ell)
        (reserveMark hs hell) (retainedCap s ell) (fineCap s ell) (multiplier s)) < 1 / 64 := by
  have hf := arithmetic_facts hs hell hscale hk hlog
  have hp := UpperRepairTrialProbability.probability_le μ policy hpolicy hmeas hk chores active hinj
    origin hgood hpositive old hold (coarseCount s ell) (samples s ell) (repetitions s ell)
    hf.representative_budget (by simpa only [UpperRecordedQuantiles.count, Fintype.card_prod, Fintype.card_fin] using hf.logical_grid_budget)
    (reserveMark hs hell) (reserve_positive hs hell) (retainedCap s ell) (fineCap s ell) (multiplier s)
    (interpolationBudget s ell) (oldError s ell) (retainedCap_positive hs hell) (fineCap_positive hs hell).le
    (multiplier_positive hs) (interpolation_positive hs hell) (oldError_positive hs hell).le hnear
    hf.normalized_cell_cap hf.total_target_budget hf.rounding_margin hf.interpolation_margin hf.correction_extra
  apply hp.trans_lt
  simpa only [reserveMark, Nat.cast_add, Nat.cast_one] using
    original_failure_sum_small hs hell hscale hk hlog

theorem original_population_failure_lt (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : Near chores μ active origin old (oldError (scale n) (logarithm (scale n)))) :
    let hs := scale_large n
    let hell : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
    trialLaw k (coarseCount (scale n) (logarithm (scale n))) (samples (scale n) (logarithm (scale n)))
      (repetitions (scale n) (logarithm (scale n)))
      (Failed policy hk chores active origin old
        (coarseCount (scale n) (logarithm (scale n))) (samples (scale n) (logarithm (scale n)))
        (repetitions (scale n) (logarithm (scale n))) (reserveMark hs hell)
        (retainedCap (scale n) (logarithm (scale n))) (fineCap (scale n) (logarithm (scale n)))
        (multiplier (scale n))) < 1 / 64 := by
  dsimp only
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  apply failure_lt μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive old hold
    (scale_large n) _ (active_scale n k hkn)
  · exact logarithm_dominates_log (scale_large n) (by omega) (active_scale n k hkn)
  · exact hnear

end EnvyFreeResearch.Full.UpperRepairTrialConfigured
