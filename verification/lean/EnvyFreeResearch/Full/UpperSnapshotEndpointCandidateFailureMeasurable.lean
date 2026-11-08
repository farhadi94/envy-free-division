import EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailureData
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallRunJoint

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailure
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperSnapshotRepetition UpperSnapshotEndpointAggregate
variable {n k : ℕ}

theorem option_none_measurableSet {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Option Y) (hf : Measurable f) : MeasurableSet {x | f x = none} := by
  have hm : Measurable (fun x => (f x).isNone) := by
    have h := ProtocolMeasurable.measurable_option_cases (β := Bool)
      (present := fun _ _ => false) (absent := fun _ => true) hf measurable_const measurable_const
    convert h using 1
    funext x
    cases f x <;> rfl
  have hs := measurableSet_eq_fun hm (measurable_const (a := true))
  have heq : {x | f x = none} = {x | (f x).isNone = true} := by
    ext x
    cases hout : f x <;> simp [hout]
  rw [heq]
  exact hs

theorem packetResult_measurable
    (hk : 2 ≤ k) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) (q m : ℕ) (tau : ℝ) :
    Measurable (packetResult hk policy active origin cutter q m tau) := by
  have horigin : Measurable (fun draw : GridSeed k m => UpperGridCache.aligned policy active origin q m draw) :=
    fixed_first_measurable (fun p : State n × GridSeed k m => UpperGridCache.aligned policy active p.1 q m p.2)
      (UpperGridCache.aligned_measurable policy hmeas active q m) origin
  have hcuts (e : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 2)) :
      Measurable (fun draw : GridSeed k m => UpperGridMerge.cuts policy active origin q m draw e) :=
    fixed_first_measurable (fun p : State n × GridSeed k m => UpperGridMerge.cuts policy active p.1 q m p.2 e)
      ((measurable_pi_apply e).comp (UpperGridMerge.cuts_measurable policy hmeas active q m)) origin
  exact actual_small_packet_joint_measurable hk policy hmeas (active cutter) (domain origin.cells)
    (domain_measurable origin.cells) (fun draw : GridSeed k m => UpperGridCache.aligned policy active origin q m draw)
    (fun draw => UpperGridMerge.cuts policy active origin q m draw)
    (smallScore hk policy active origin cutter q m) (smallTarget hk policy active origin cutter q m tau)
    horigin hcuts (smallScore_measurable hk policy hmeas active origin cutter q m)
    (smallTarget_measurable hk policy hmeas active origin cutter q m tau)

theorem exhaustion_measurableSet
    (hk : 2 ≤ k) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) (q m : ℕ) (tau : ℝ) :
    MeasurableSet {p | smallBranch hk policy active origin cutter q m tau p.1 ∧
      (packetResult hk policy active origin cutter q m tau p).2 = none} := by
  have hb : MeasurableSet {p : GridSeed k m × Tape (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle) (16*k) |
      smallBranch hk policy active origin cutter q m tau p.1} :=
    (smallBranch_measurableSet hk policy hmeas active origin cutter q m tau).preimage measurable_fst
  exact hb.inter (option_none_measurableSet _
    (measurable_snd.comp (packetResult_measurable hk policy hmeas active origin cutter q m tau)))

end EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailure
