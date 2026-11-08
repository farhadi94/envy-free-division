import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateZeroFailure

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperAggregateInterpolation UpperGridInterpolation UpperSortedGrid UpperSnapshotSmall Chores
variable {n k q s ell : ℕ} [Nonempty (Fin k)]

theorem zero_numeric_failure_small (hk : 0 < k) (hs : (4 : ℝ) ≤ s)
    (hell : (1 : ℝ) ≤ ell) (hks : (k : ℝ) ≤ s) :
    ENNReal.ofReal (2 * ((k : ℝ) - 1) * (k : ℝ)^2 * (1 + snapshotAccuracy s) /
      (snapshotAccuracy s * (UpperRepairParameters.samples s ell + 1 : ℕ))) < 1/64 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ)^2 := one_le_pow₀ hk1
  have hkk := mul_le_mul_of_nonneg_left hk2 (sq_nonneg (k : ℝ))
  have hscalar : (k : ℝ)^2 ≤ 64 * (k : ℝ)^4 := by
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ k by positivity) 4]
  have hep : 0 < snapshotAccuracy s := by
    unfold snapshotAccuracy
    have hsp : (0 : ℝ) < s := by linarith
    positivity
  apply (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar (by nlinarith : 0 ≤ 2*((k : ℝ)-1)))
      (by linarith : 0 ≤ 1+snapshotAccuracy s)) (by positivity))).trans_lt
  exact snapshot_full_budget_failure_small hs hell hks

theorem actual_zero_rejection_small
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (hk : 0 < k) (chores : Bool) (cutter : Fin k)
    (hs : (4 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hks : (k : ℝ) ≤ s) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k))
        (UpperRepairParameters.samples s ell)).prod (volume : Measure UpperSnapshotSmall.Circle))
      {p | UpperSnapshotCandidates.selectedDistance hk
        (UpperGridCache.table policy active origin q (UpperRepairParameters.samples s ell) p.1) cutter = 0 ∧
        (UpperSnapshotProtocol.zeroExecute policy hk chores active
          (UpperGridCache.aligned policy active origin q (UpperRepairParameters.samples s ell) p.1) cutter p.2).2.2 = true} < 1/64 := by
  have hsp : 0 < s := by exact_mod_cast (show (0 : ℝ) < s by linarith)
  exact (actual_zero_rejection_probability μ active policy hpolicy hmeas origin hgood hpositive
    hk chores cutter (snapshotAccuracy s) (snapshot_accuracy_positive hsp)).trans_lt
    (zero_numeric_failure_small hk hs hell hks)

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
