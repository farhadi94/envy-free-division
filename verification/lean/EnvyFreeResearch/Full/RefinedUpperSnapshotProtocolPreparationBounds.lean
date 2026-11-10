import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateSmallProbability
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateZeroBound
import EnvyFreeResearch.Full.RefinedUpperSnapshotParameters

/-! Original-grid zero-branch and small-branch interpolation exceptions at
the revised sample count. All adaptive endpoint and iid sampler premises
are discharged by the actual ordinary candidate constructions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolPreparationBounds
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperAggregateInterpolation UpperGridInterpolation UpperSortedGrid UpperSnapshotSmall
  UpperSnapshotRepetition UpperSnapshotEndpointAggregate Chores
variable {n k q s ell : ℕ} [Nonempty (Fin k)]
  {Draw Generated : Type*} [MeasurableSpace Draw] [Fintype Generated]

theorem snapshot_full_budget_failure_small {s ell k : ℕ}
    (hd : 128 ∣ s) (hs : (4096 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hk : (k : ℝ) ≤ s) :
    ENNReal.ofReal (2 * ((k : ℝ) - 1) * (64 * (k : ℝ)^4) * (1 + snapshotAccuracy s) /
      (snapshotAccuracy s * (RefinedUpperParameterCounts.samples s ell + 1 : ℕ))) < 1/64 := by
  have hep : 0 < snapshotAccuracy s := by
    unfold snapshotAccuracy
    have hsp : (0 : ℝ) < s := by linarith
    positivity
  have hn : 2 * ((k : ℝ) - 1) * (64 * (k : ℝ)^4) ≤ 128 * (k : ℝ)^5 := by
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ k by positivity) 4]
  have hm := mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ 1 + snapshotAccuracy s)
  have hb := div_le_div_of_nonneg_right hm
    (show 0 ≤ snapshotAccuracy s * (RefinedUpperParameterCounts.samples s ell + 1 : ℕ) by positivity)
  have hreal : 2 * ((k : ℝ) - 1) * (64 * (k : ℝ)^4) * (1 + snapshotAccuracy s) /
      (snapshotAccuracy s * (RefinedUpperParameterCounts.samples s ell + 1 : ℕ)) < 1/64 := by
    exact hb.trans_lt (by simpa only [snapshotAccuracy,RefinedUpperSnapshotParameters.accuracy,Nat.cast_add,Nat.cast_one] using
      RefinedUpperSnapshotParameters.snapshot_failure_small hd hs hell hk)
  have he := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1/64)).mpr hreal
  have h64 : ENNReal.ofReal (1/64 : ℝ) = (1/64 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [h64] at he
  exact he

theorem zero_numeric_failure_small (hk : 0 < k) (hd : 128 ∣ s) (hs : (4096 : ℝ) ≤ s)
    (hell : (1 : ℝ) ≤ ell) (hks : (k : ℝ) ≤ s) :
    ENNReal.ofReal (2 * ((k : ℝ) - 1) * (k : ℝ)^2 * (1 + snapshotAccuracy s) /
      (snapshotAccuracy s * (RefinedUpperParameterCounts.samples s ell + 1 : ℕ))) < 1/64 := by
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
  exact snapshot_full_budget_failure_small hd hs hell hks

theorem actual_zero_rejection_small
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (hk : 0 < k) (chores : Bool) (cutter : Fin k)
    (hd : 128 ∣ s) (hs : (4096 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hks : (k : ℝ) ≤ s) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k))
        (RefinedUpperParameterCounts.samples s ell)).prod (volume : Measure UpperSnapshotSmall.Circle))
      {p | UpperSnapshotCandidates.selectedDistance hk
        (UpperGridCache.table policy active origin q (RefinedUpperParameterCounts.samples s ell) p.1) cutter = 0 ∧
        (UpperSnapshotProtocol.zeroExecute policy hk chores active
          (UpperGridCache.aligned policy active origin q (RefinedUpperParameterCounts.samples s ell) p.1) cutter p.2).2.2 = true} < 1/64 := by
  have hsp : 0 < s := by exact_mod_cast (show (0 : ℝ) < s by linarith)
  exact (actual_zero_rejection_probability μ active policy hpolicy hmeas origin hgood hpositive
    hk chores cutter (snapshotAccuracy s) (snapshot_accuracy_positive hsp)).trans_lt
    (zero_numeric_failure_small hk hd hs hell hks)

theorem original_grid_full_budget_small
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (normalizer : Fin k → ℝ) (errorDomain : List Component)
    (drawLaw : Measure Draw) [IsProbabilityMeasure drawLaw]
    (points : (Fin (RefinedUpperParameterCounts.samples s ell) → Fin k × I) × Draw → Generated → ℝ)
    (hpoints : ∀ j, Measurable (fun p => points p j))
    (hd : 128 ∣ s) (hs : (4096 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hks : (k : ℝ) ≤ s)
    (hfiber : ∀ᵐ p ∂UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k))
        (RefinedUpperParameterCounts.samples s ell),
      ∀ u : ℝ → ℝ≥0∞, Measurable u → u 0 = 0 →
      (∫⁻ draw, ∑ j, u (points (p, draw) j) ∂drawLaw) ≤
        ENNReal.ofReal (64*(k : ℝ)^4) * ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k))
      (RefinedUpperParameterCounts.samples s ell)).prod drawLaw)
      {p | BadSupportedRecordedUnion (fun i => μ (active i)) normalizer errorDomain
        (UpperGridMerge.cuts policy active origin q (RefinedUpperParameterCounts.samples s ell) p.1)
        (points p) (snapshotAccuracy s)} < 1/64 := by
  have hsp : 0 < s := by exact_mod_cast (show (0 : ℝ) < s by linarith)
  have h := original_grid_supported_probability (q := q) μ active policy hpolicy hmeas origin hgood hpositive
    normalizer errorDomain drawLaw points hpoints (64*(k : ℝ)^4) (snapshotAccuracy s)
    (by positivity) (snapshot_accuracy_positive hsp) hfiber
  simp only [Fintype.card_fin] at h
  exact h.trans_lt (snapshot_full_budget_failure_small hd hs hell hks)

theorem actual_small_original_interpolation_small
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (hk : 2 ≤ k) (cutter : Fin k)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (tau : ℝ) (htau : 0 < tau)
    (hd : 128 ∣ s) (hs : (4096 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hks : (k : ℝ) ≤ s) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k))
      (RefinedUpperParameterCounts.samples s ell)).prod
      (law (volume.prod volume : Measure (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle)) (16*k)))
      {p | BadSupportedRecordedUnion (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
        (UpperGridMerge.cuts policy active origin q (RefinedUpperParameterCounts.samples s ell) p.1)
        (smallOriginalPoints hk policy active origin cutter q (RefinedUpperParameterCounts.samples s ell) tau p)
        (snapshotAccuracy s)} < 1/64 := by
  apply original_grid_full_budget_small μ active policy hpolicy hmeas origin hgood hpositive
    (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
    (law (volume.prod volume : Measure (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle)) (16*k))
    (smallOriginalPoints hk policy active origin cutter q (RefinedUpperParameterCounts.samples s ell) tau)
    (smallOriginalPoints_measurable hk policy hmeas active origin cutter q (RefinedUpperParameterCounts.samples s ell) tau)
    hd hs hell hks
  exact ae_of_all _ (fun draw u hu hu0 => actual_small_original_fiber μ active hk cutter policy hpolicy hmeas
    origin hgood hpositive tau htau draw u hu hu0)


end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolPreparationBounds
