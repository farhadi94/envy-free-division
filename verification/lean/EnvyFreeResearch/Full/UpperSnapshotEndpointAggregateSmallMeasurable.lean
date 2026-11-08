import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateSmallCharge
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpointJoint

/-! Joint Borel dependence of the actual branch-masked endpoint vector on
both the original immutable-grid seed tape and every later candidate start. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperSnapshotRepetition
variable {n k q m : ℕ}

theorem smallOriginalPoints_measurable
    (hk : 2 ≤ k) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k)
    (q m : ℕ) (tau : ℝ) (j : Fin ((16*k)*(2+k))) :
    Measurable (fun p => smallOriginalPoints hk policy active origin cutter q m tau p j) := by
  have horigin : Measurable (fun draw : GridSeed k m => UpperGridCache.aligned policy active origin q m draw) :=
    fixed_first_measurable (fun p : State n × GridSeed k m => UpperGridCache.aligned policy active p.1 q m p.2)
      (UpperGridCache.aligned_measurable policy hmeas active q m) origin
  have hcuts (e : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 2)) :
      Measurable (fun draw : GridSeed k m => UpperGridMerge.cuts policy active origin q m draw e) :=
    fixed_first_measurable (fun p : State n × GridSeed k m => UpperGridMerge.cuts policy active p.1 q m p.2 e)
      ((measurable_pi_apply e).comp (UpperGridMerge.cuts_measurable policy hmeas active q m)) origin
  have h := smallEndpointVector_joint_measurable hk policy hmeas (active cutter) (domain origin.cells)
    (domain_measurable origin.cells) (fun draw : GridSeed k m => UpperGridCache.aligned policy active origin q m draw)
    (fun draw => UpperGridMerge.cuts policy active origin q m draw)
    (smallScore hk policy active origin cutter q m) (smallTarget hk policy active origin cutter q m tau)
    horigin hcuts (smallScore_measurable hk policy hmeas active origin cutter q m)
    (smallTarget_measurable hk policy hmeas active origin cutter q m tau) j
  have hm : MeasurableSet {p : GridSeed k m × Tape (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle) (16*k) |
      smallBranch hk policy active origin cutter q m tau p.1} :=
    (smallBranch_measurableSet hk policy hmeas active origin cutter q m tau).preimage measurable_fst
  simpa only [smallOriginalPoints, ite_apply] using h.ite hm (measurable_const (a := (0 : ℝ)))

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
