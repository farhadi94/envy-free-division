import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateSmallData
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpointBudget

/-! The actual original-grid branch test discharges the complete-history
small-candidate endpoint budget. Rejected candidates are counted, and the
complementary branch contributes only immutable zero padding. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperSnapshotRepetition Chores
variable {n k q m : ℕ}

theorem actual_small_original_fiber
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (hk : 2 ≤ k) (cutter : Fin k)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (tau : ℝ) (htau : 0 < tau) (draw : GridSeed k m)
    (u : ℝ → ℝ≥0∞) (hu : Measurable u) (hu0 : u 0=0) :
    (∫⁻ tape, ∑ j, u (smallOriginalPoints hk policy active origin cutter q m tau (draw,tape) j)
      ∂law (volume.prod volume : Measure (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle)) (16*k)) ≤
      ENNReal.ofReal (64*(k : ℝ)^4)*∫⁻ x,u x ∂UpperMixtureSampling.mixture μ active origin.cells := by
  by_cases hb : smallBranch hk policy active origin cutter q m tau draw
  · simp only [smallOriginalPoints, hb, ite_true]
    have ht := actual_small_target_checks hk policy active origin cutter q m tau htau draw hb
    have he := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
    have h := actual_small_endpoints_population_bound μ active cutter policy hpolicy hmeas
      (domain origin.cells) (hpositive cutter) (UpperGridMerge.cuts policy active origin q m draw)
      he.1 (UpperCommonGrid.grid_monotone _) (smallScore hk policy active origin cutter q m draw)
      (smallTarget hk policy active origin cutter q m tau draw) ht.1 ht.2.1 hk ht.2.2
      (UpperGridCache.aligned policy active origin q m draw)
      (actual_small_initial_valid μ policy hpolicy active origin hgood hpositive q m draw) u hu hu0
    simpa only [UpperMixtureSampling.mixture, UpperGridCache.aligned_domain] using h
  · simp only [smallOriginalPoints, hb, ite_false, hu0, Finset.sum_const_zero, lintegral_zero]
    exact bot_le

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
