import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableBridge
import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurableExecute

/-! Complete actual Snapshot attempt at a fixed active set. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
open MeasureTheory UpperGlobalPhysical UpperZeroRows UpperCircularStage UpperStageMeasurable
variable {n : ℕ}

def snapshotAt (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hk : 3 ≤ active.card) (chores : Bool) (a : Anchor n)
    (tape : UpperSnapshotProtocol.Tape n active.card) : Phase n :=
  finishSnapshotAt active (by omega) chores a
    (UpperSnapshotProtocol.snapshotExecute policy hk chores (enumerate active) a.residue ⟨0,by omega⟩ tape)

theorem snapshotAt_measurable (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (hk : 3 ≤ active.card) (chores : Bool) :
    Measurable (fun z : Anchor n × UpperSnapshotProtocol.Tape n active.card =>
      snapshotAt active policy hk chores z.1 z.2) := by
  have hr := UpperSnapshotProtocol.snapshotExecute_measurable policy hpolicy hk chores (enumerate active)
    (fun z : Anchor n × UpperSnapshotProtocol.Tape n active.card => z.1.residue)
    ⟨0,by omega⟩ Prod.snd (anchor_residue_measurable.comp measurable_fst) measurable_snd
  exact (finishSnapshotAt_measurable active (by omega) chores).comp (measurable_fst.prodMk hr)

theorem snapshotAt_eq (a : Anchor n) [Nonempty (Fin a.active.card)]
    (policy : Policy n) (hk : 3 ≤ a.active.card) (chores : Bool)
    (tape : UpperSnapshotProtocol.Tape n a.active.card) :
    snapshotAt a.active policy hk chores a tape = a.snapshotAttempt policy hk chores tape := rfl

end EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
