import EnvyFreeResearch.Full.UpperSnapshotProtocolPreparationEvents
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallOriginal
import EnvyFreeResearch.Full.UpperSnapshotIntegrationThreshold
import EnvyFreeResearch.Full.UpperSnapshotProtocolSafety

/-! Fixed complete preparation histories have a uniform actual fresh-trial
chance outside the three proved preparation exceptions. No independence of
oracle replies, candidate selection, or previous rejection events is used. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotCandidates UpperSnapshotEndpointAggregate UpperAggregateInterpolation UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

theorem prepared_fiber_chance
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (cutter : Fin k)
    (p : PreparationTape n k)
    (hzbad : p ∉ preparationBadZero policy hk chores active origin cutter)
    (hcbad : p ∉ preparationBadCandidates policy hk active origin cutter)
    (hibad : p ∉ preparationBadInterpolation μ policy hk active origin cutter) :
    ENNReal.ofReal ((3:ℝ)/8) ≤ (UpperRepair.law n k)
      {fresh | (snapshotExecute policy hk chores active origin cutter (joinTape (p,fresh))).2.2=false} := by
  let data := UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) p.1
  let values := UpperGridData.table active origin data
  let D := selectedDistance (by omega) values cutter
  have hnonneg : 0 ≤ D := rowDistance_nonnegative values cutter _
  change ENNReal.ofReal ((3:ℝ)/8) ≤ (UpperRepair.law n k)
    {fresh | (fromDataExecute policy hk chores active origin cutter data p.2.1 p.2.2 fresh).2.2=false}
  by_cases hz : D=0
  · have hzero : (zeroExecute policy (by omega) chores active (UpperGridData.aligned data) cutter p.2.1).2.2=false := by
      apply Bool.eq_false_iff.mpr
      intro hf
      exact hzbad ⟨hz,hf⟩
    unfold fromDataExecute
    dsimp only [D,values] at hz
    simp only [hz,ite_true,hzero,Set.setOf_true,measure_univ]
    norm_num
  · have hD : 0<D := lt_of_le_of_ne hnonneg (Ne.symm hz)
    by_cases hsmall : D<UpperRepair.nearError n/16
    · have hbranch : smallBranch (by omega) policy active origin cutter (UpperRepair.coarse n)
          (UpperRepair.fine n) (UpperRepair.nearError n) p.1 := ⟨hD,hsmall⟩
      have hpacket : (UpperSnapshotEndpointCandidateFailure.packetResult (by omega) policy active origin cutter
          (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.nearError n) (p.1,p.2.2)).2≠none := by
        intro hnone
        exact hcbad ⟨hbranch,hnone⟩
      have hp := fixed_small_original_probability μ policy hpolicy hmeas (by omega) chores active hinj origin hgood hpositive
        cutter (UpperRepair.coarse n) (UpperRepair.fine n) p.1 p.2.2 hbranch hpacket hibad
      unfold fromDataExecute
      dsimp only [D,values] at hz hsmall
      simp only [hz,hsmall,ite_false,ite_true]
      apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
      exact ((show (3:ℝ)/8 < 31/64 by norm_num).trans hp).le
    · have hp := configured_large_probability μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive
        p.1 cutter (le_of_not_gt hsmall)
      unfold fromDataExecute
      dsimp only [D,values] at hz hsmall
      simp only [hz,hsmall,ite_false,restoreRejected_success]
      apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
      exact ((show (3:ℝ)/8 < 31/64 by norm_num).trans hp).le
end EnvyFreeResearch.Full.UpperSnapshotProtocol
