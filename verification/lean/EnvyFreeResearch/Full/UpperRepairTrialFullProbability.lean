import EnvyFreeResearch.Full.UpperRepairTrialFull
import EnvyFreeResearch.Full.UpperRepairTrialConfigured
import EnvyFreeResearch.Full.UpperSnapshotCandidatesGuardProbability

/-! The actual trial with both reserve mass checks has the same failure
budget. Both tails use one original-label mass exception. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperRepairTrialFull

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairTrialProgram UpperRepairTrialLaw UpperLogicalIsolation UpperLogicalPreparationGuard
  UpperRepairPreparationChecks UpperRepairPreparationProbability UpperRepairCorrectionProbability
  UpperRepairJobs UpperSnapshotCandidates UpperRepairParameters

variable {n k q m L : ℕ} [Nonempty (Fin k)]

theorem preparation_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (q m L : ℕ)
    (hrepresentatives : 2 * (jobCount k * L) < q + 1)
    (hgrid : UpperRecordedQuantiles.count (Agent := Fin k) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (hcap : 0 < cap) :
    trialLaw k q m L {p | snapshotGuard policy active origin q m (requests k L) theta cap p.2.1.1 p.1 = false} ≤
      ENNReal.ofReal (failureBudget (Agent := Fin k) q m (jobCount k * L) theta cap) := by
  have hv := UpperProductViews.preparation_view
    (UpperReserve.labelLaw : Measure (Labels k q))
    (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m)
    (isolationLaw k L) (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle)))
  have hbad := measurableSet_eq_fun
    (snapshotGuard_measurable policy hmeas active origin q m (requests k L) theta cap) (measurable_const (a := false))
  have heq := hv.measure_preimage hbad.nullMeasurableSet
  change trialLaw k q m L {p | snapshotGuard policy active origin q m (requests k L) theta cap p.2.1.1 p.1 = false} =
    originalLaw (Agent := Fin k) q m {p | snapshotGuard policy active origin q m (requests k L) theta cap p.1 p.2 = false} at heq
  rw [heq]
  simpa only [requests_length] using snapshotGuard_original_probability μ policy hpolicy hmeas active origin hgood hpositive
    q m (requests k L) (by simpa only [requests_length] using hrepresentatives) hgrid theta htheta cap hcap

theorem probability_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j)) (q m L : ℕ)
    (hrepresentatives : 2 * (jobCount k * L) < q + 1)
    (hgrid : UpperRecordedQuantiles.count (Agent := Fin k) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap eta lam b tau : ℝ)
    (hcap : 0 < cap) (heta : 0 ≤ eta) (hlam : 0 < lam) (hb : 0 < b) (htau : 0 ≤ tau)
    (hnear : Near chores μ active origin old tau)
    (hcell : cellCap q theta ≤ eta) (hbudget : (k : ℝ) * targetBudget k q L theta tau lam < 1 / 16)
    (hsize : (k : ℝ)^2 ≤ lam / 2) (hquarter : b * cap ≤ lam / 4)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16) :
    trialLaw k q m L (Failed policy hk chores active origin old q m L theta cap eta lam) ≤
      ENNReal.ofReal (failureBudget (Agent := Fin k) q m (jobCount k * L) theta cap) +
      ENNReal.ofReal (isolationBound k L lam) +
      ENNReal.ofReal (8 * k * eta * cap / lam +
        16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / ((theta : ℝ) * b * (m + 1 : ℕ))) := by
  have hg := preparation_probability μ policy hpolicy hmeas active origin hgood hpositive
    q m L hrepresentatives hgrid theta htheta cap hcap
  have hc := cycle_probability μ policy hpolicy hmeas hk chores active origin hgood hpositive old
    q m L hrepresentatives theta cap lam hlam.le
  have hp := UpperRepairCorrectionProbability.probability_le μ policy hpolicy hmeas hk chores active hinj
    origin hgood hpositive old hold q m L theta htheta cap eta lam b tau heta hlam hcap.le hb htau
    hnear hcell hbudget hsize hquarter hmargin
  rw [failed_eq]
  have h := strengthened_trial_union (trialLaw k q m L)
    (UpperRepairTrialRejection.Failed policy hk chores active origin old q m L theta cap eta lam)
    (BadCycle policy hk chores active origin old q m L theta cap lam)
    {p | correctionRejected policy hk chores active origin old q m L theta cap eta lam p = true}
    (fun p => guard policy active origin q m (requests k L) theta cap p.2.1.1 p.1)
    (fun p => upperReserve active origin (UpperGridData.reserve (data policy active origin q p.2.1) theta p.1) theta)
    _ _ _ (UpperRepairTrialProbability.failed_subset policy hk chores active origin old q m L theta cap eta lam)
    (by simpa only [data, UpperGridData.reserve_execute, snapshotGuard] using hg) hc hp
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hfirst : 0 ≤ 8 * ((k : ℝ) * eta) * cap / lam := by positivity
  have hsecond : 0 ≤ 16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / ((theta : ℝ) * b * (m + 1 : ℕ)) := by positivity
  convert h using 1
  rw [← ENNReal.ofReal_add hfirst hsecond]
  congr 2
  ring

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
  let hs := scale_large n
  have hell : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have hf := original_population_facts n k hk hkn
  have hp := probability_le μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive old hold
    (coarseCount (scale n) (logarithm (scale n))) (samples (scale n) (logarithm (scale n)))
    (repetitions (scale n) (logarithm (scale n))) hf.representative_budget
    (by simpa only [UpperRecordedQuantiles.count, Fintype.card_prod, Fintype.card_fin] using hf.logical_grid_budget)
    (reserveMark hs hell) (reserve_positive hs hell) _ _ _ _ _ (retainedCap_positive hs hell)
    (fineCap_positive hs hell).le (multiplier_positive hs) (interpolation_positive hs hell)
    (oldError_positive hs hell).le hnear hf.normalized_cell_cap hf.total_target_budget hf.rounding_margin
    hf.interpolation_margin hf.correction_extra
  apply hp.trans_lt
  simpa only [reserveMark, Nat.cast_add, Nat.cast_one] using original_failure_sum_small hs hell
    (active_scale n k hkn) hk (logarithm_dominates_log hs (by omega) (active_scale n k hkn))

end EnvyFreeResearch.Full.UpperRepairTrialFull
