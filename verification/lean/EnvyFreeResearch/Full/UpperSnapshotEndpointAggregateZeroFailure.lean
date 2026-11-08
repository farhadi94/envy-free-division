import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateZero
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateParameters
import EnvyFreeResearch.Full.UpperSnapshotCandidatesSmall

/-! The actual zero-distance branch rejection event is bounded on the
original unconditioned sampler tape, rather than conditioning on D=0. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperAggregateInterpolation UpperGridInterpolation UpperSortedGrid UpperSnapshotSmall
  UpperGridSensitivity Chores
variable {n k q m : ℕ} [Nonempty (Fin k)]

set_option maxHeartbeats 1200000 in
theorem zero_rejection_implies_bad
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (hk : 0 < k) (chores : Bool) (cutter : Fin k) (b : ℝ)
    (p : (Fin m → Fin k × I) × UpperSnapshotSmall.Circle)
    (hD : UpperSnapshotCandidates.selectedDistance hk
      (UpperGridCache.table policy active origin q m p.1) cutter = 0)
    (hreject : (UpperSnapshotProtocol.zeroExecute policy hk chores active
      (UpperGridCache.aligned policy active origin q m p.1) cutter p.2).2.2 = true) :
    BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
      (UpperGridMerge.cuts policy active origin q m p.1)
      (zeroPoints policy active origin q m cutter p) b := by
  by_contra hnot
  have hw := UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m p.1
  have hd := UpperGridCache.aligned_domain policy active origin q m p.1
  have he := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m p.1
  have hp : ∀ i, 0 < (μ (active i)).real
      (domain (UpperGridCache.aligned policy active origin q m p.1).cells) := by
    simpa only [hd] using hpositive
  have htable : physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain (UpperGridCache.aligned policy active origin q m p.1).cells))
      (UpperGridCache.aligned policy active origin q m p.1).cells
      (UpperGridMerge.cuts policy active origin q m p.1) = UpperGridCache.table policy active origin q m p.1 := by
    funext i e
    simp only [physicalRows, hd]
    exact (UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive q m p.1 i e).symm
  have hdist : ∀ i, distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain (UpperGridCache.aligned policy active origin q m p.1).cells))
      (UpperGridCache.aligned policy active origin q m p.1).cells
      (UpperGridMerge.cuts policy active origin q m p.1)) i cutter = 0 := by
    rw [htable]
    intro i
    simp only [distance, UpperSnapshotCandidates.zero_table hk _ cutter hD i,
      sub_self, abs_zero, Finset.sum_const_zero]
  have hrows (normalizer : Fin k → ℝ) : physicalRows (fun i => μ (active i)) normalizer
      (UpperGridCache.aligned policy active origin q m p.1).cells
      (UpperGridMerge.cuts policy active origin q m p.1) =
      physicalRows (fun i => μ (active i)) normalizer origin.cells
      (UpperGridMerge.cuts policy active origin q m p.1) := by
    funext i e
    simp only [physicalRows, hd]
  have hnot' : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain (UpperGridCache.aligned policy active origin q m p.1).cells))
      (UpperGridCache.aligned policy active origin q m p.1).cells
      (UpperGridMerge.cuts policy active origin q m p.1)
      (partitionRun policy (UpperGridCache.aligned policy active origin q m p.1)
        (active cutter) (equalTargets k) p.2).1 b := by
    simpa only [BadSupportedRecordedUnion, hd, hrows, zeroPoints] using hnot
  have haccept := UpperSnapshotProtocol.zero_accepts_of_interpolation μ policy hpolicy hk chores active
    (UpperGridCache.aligned policy active origin q m p.1) hw cutter hp
    (UpperGridMerge.cuts policy active origin q m p.1) he.1 he.2 p.2 b hdist hnot'
  simp [haccept] at hreject

/-- The original-tape probability of rejection on the actual selected D=0
branch. No positive probability for that branch is required. -/
theorem actual_zero_rejection_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (hk : 0 < k) (chores : Bool) (cutter : Fin k) (b : ℝ) (hb : 0 < b) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m).prod
      (volume : Measure UpperSnapshotSmall.Circle))
      {p | UpperSnapshotCandidates.selectedDistance hk
        (UpperGridCache.table policy active origin q m p.1) cutter = 0 ∧
        (UpperSnapshotProtocol.zeroExecute policy hk chores active
          (UpperGridCache.aligned policy active origin q m p.1) cutter p.2).2.2 = true} ≤
      ENNReal.ofReal (2 * ((k : ℝ) - 1) * (k : ℝ)^2 * (1 + b) /
        (b * (m + 1 : ℕ))) := by
  apply (measure_mono (show _ ⊆ {p | BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
      (UpperGridMerge.cuts policy active origin q m p.1)
      (zeroPoints policy active origin q m cutter p) b} from ?_)).trans
    (actual_zero_interpolation_probability μ active policy hpolicy hmeas origin hgood hpositive cutter b hb)
  intro p hp
  exact zero_rejection_implies_bad μ active policy hpolicy origin hgood hpositive hk chores cutter b p hp.1 hp.2

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
