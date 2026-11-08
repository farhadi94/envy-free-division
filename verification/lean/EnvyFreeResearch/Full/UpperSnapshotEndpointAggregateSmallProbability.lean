import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateSmallMeasurable

/-! The complete actual small-branch original-tape endpoint interpolation
exception: original sample law, adaptive rejection histories, branch target
supply, all reached endpoints, and joint measurability are proved internally. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperAggregateInterpolation UpperSnapshotSmall UpperSnapshotRepetition Chores
variable {n k q s ell : ℕ} [Nonempty (Fin k)]

/-- The selected-distance test in the actual program uses D≠0; its cached
absolute-distance definition makes this exactly the strict-positive branch. -/
theorem smallBranch_iff_nonzero (hk : 2 ≤ k) (policy : Policy n)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) (q m : ℕ)
    (tau : ℝ) (draw : GridSeed k m) :
    smallBranch hk policy active origin cutter q m tau draw ↔
      smallD hk policy active origin cutter q m draw ≠ 0 ∧
        smallD hk policy active origin cutter q m draw < tau/16 := by
  have hn : 0 ≤ smallD hk policy active origin cutter q m draw := by
    unfold smallD UpperSnapshotCandidates.selectedDistance
    exact UpperSnapshotCandidates.rowDistance_nonnegative _ _ _
  exact and_congr (lt_iff_le_and_ne.trans (by simp [hn, ne_comm])) Iff.rfl

/-- No interpolation, conditional endpoint law, sampler projection, joint
measurability, or endpoint-budget premise is assumed for the actual execution. -/
theorem actual_small_original_interpolation_small
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (hk : 2 ≤ k) (cutter : Fin k)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (tau : ℝ) (htau : 0 < tau)
    (hs : (4 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hks : (k : ℝ) ≤ s) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k))
      (UpperRepairParameters.samples s ell)).prod
      (law (volume.prod volume : Measure (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle)) (16*k)))
      {p | BadSupportedRecordedUnion (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
        (UpperGridMerge.cuts policy active origin q (UpperRepairParameters.samples s ell) p.1)
        (smallOriginalPoints hk policy active origin cutter q (UpperRepairParameters.samples s ell) tau p)
        (snapshotAccuracy s)} < 1/64 := by
  apply original_grid_full_budget_small μ active policy hpolicy hmeas origin hgood hpositive
    (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
    (law (volume.prod volume : Measure (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle)) (16*k))
    (smallOriginalPoints hk policy active origin cutter q (UpperRepairParameters.samples s ell) tau)
    (smallOriginalPoints_measurable hk policy hmeas active origin cutter q (UpperRepairParameters.samples s ell) tau)
    hs hell hks
  exact ae_of_all _ (fun draw u hu hu0 => actual_small_original_fiber μ active hk cutter policy hpolicy hmeas
    origin hgood hpositive tau htau draw u hu hu0)

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
