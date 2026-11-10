import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunDispatchMeasurableBridge
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolJointMeasurableProgram
import EnvyFreeResearch.Full.RefinedUpperShrinkMeasurable
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolRepairAction

/-! Actual paid-stage programs at a fixed finite active set. Pure finishes
are the literal physical transitions, including rejection history refresh. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.ProgramCertified
open RefinedUpperGlobalPhysical DispatchMeasurable UpperZeroRows UpperCircularStage UpperStageMeasurable
  UpperQueryPrograms Chores.QueryProgram ProgramMeasurable UpperCorrectionExecution RefinedUpperRepairProgram
variable {n : ℕ}

def snapshotAtProgram (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 3 ≤ active.card) (chores : Bool) (a : Anchor n) (tape : RefinedUpperSnapshotProtocol.Tape n active.card) : QProgram n (Phase n) :=
  (RefinedUpperSnapshotProtocol.snapshotProgram hk chores (enumerate active) a.residue ⟨0,by omega⟩ tape).bind
    (fun out => .returned (finishSnapshotAt active (by omega) chores a out))

def firstAtProgram (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 2 ≤ active.card) (chores : Bool) (p : Pending n) (G : ℝ) (tape : RefinedUpperRepair.Tape n active.card) : QProgram n (Phase n) :=
  (RefinedUpperShrink.program hk chores (enumerate active) p.buffer G tape).bind
    (fun out => .returned (finishFirstAt active p chores G out))

def secondAtProgram (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 2 ≤ active.card) (chores : Bool) (p : Pending n) (tape : RefinedUpperRepair.Tape n active.card) : QProgram n (Phase n) :=
  (RefinedUpperShrink.program hk chores (enumerate active) p.buffer (2/RefinedUpperRepair.nearError n) tape).bind
    (fun out => .returned (finishSecondAt active p out))

def repairAtProgram (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 2 ≤ active.card) (chores : Bool) (p : Pending n) (tape : RefinedUpperRepair.Tape n active.card) : QProgram n (Phase n) :=
  (RefinedUpperRepair.program hk chores (enumerate active) p.buffer (localEndowmentsAt active p) tape).bind
    (fun out => .returned (finishRepairAt active p out))

theorem snapshotAtProgram_certified (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 3 ≤ active.card) (chores : Bool) :
    Certified (fun z : Anchor n × RefinedUpperSnapshotProtocol.Tape n active.card => snapshotAtProgram active hk chores z.1 z.2) := by
  have h := RefinedUpperSnapshotProtocol.snapshot_program_certified hk chores (enumerate active)
    (fun z : Anchor n × RefinedUpperSnapshotProtocol.Tape n active.card => z.1.residue) ⟨0,by omega⟩ Prod.snd
    (anchor_residue_measurable.comp measurable_fst) measurable_snd
  exact h.bind _ (Certified.returned _ ((finishSnapshotAt_measurable active (by omega) chores).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))

theorem firstAtProgram_certified (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 2 ≤ active.card) (chores : Bool) :
    Certified (fun z : (Pending n × ℝ) × RefinedUpperRepair.Tape n active.card => firstAtProgram active hk chores z.1.1 z.1.2 z.2) := by
  have h := RefinedUpperShrink.program_certified hk chores (enumerate active)
    (fun z : (Pending n × ℝ) × RefinedUpperRepair.Tape n active.card => z.1.1.buffer) (fun z => z.1.2) Prod.snd
    (pending_buffer_measurable.comp (measurable_fst.comp measurable_fst)) (measurable_snd.comp measurable_fst) measurable_snd
  exact h.bind _ (Certified.returned _ ((finishFirstAt_measurable active chores).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))

theorem secondAtProgram_certified (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 2 ≤ active.card) (chores : Bool) :
    Certified (fun z : Pending n × RefinedUpperRepair.Tape n active.card => secondAtProgram active hk chores z.1 z.2) := by
  have h := RefinedUpperShrink.program_certified hk chores (enumerate active)
    (fun z : Pending n × RefinedUpperRepair.Tape n active.card => z.1.buffer) (fun _ => 2/RefinedUpperRepair.nearError n) Prod.snd
    (pending_buffer_measurable.comp measurable_fst) measurable_const measurable_snd
  exact h.bind _ (Certified.returned _ ((finishSecondAt_measurable active).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))

theorem repairAtProgram_certified (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 2 ≤ active.card) (chores : Bool) :
    Certified (fun z : Pending n × RefinedUpperRepair.Tape n active.card => repairAtProgram active hk chores z.1 z.2) := by
  have h := RefinedUpperRepair.program_certified hk chores (enumerate active)
    (fun z : Pending n × RefinedUpperRepair.Tape n active.card => z.1.buffer)
    (fun z => localEndowmentsAt active z.1) Prod.snd (pending_buffer_measurable.comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp ((localEndowmentsAt_measurable active).comp measurable_fst)) measurable_snd
  exact h.bind _ (Certified.returned _ ((finishRepairAt_measurable active).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))

theorem snapshotAtProgram_eq (a : Anchor n) [Nonempty (Fin a.active.card)] (hk : 3 ≤ a.active.card)
    (chores : Bool) (tape : RefinedUpperSnapshotProtocol.Tape n a.active.card) :
    snapshotAtProgram a.active hk chores a tape = a.snapshotProgram hk chores tape := rfl

theorem firstAtProgram_eq (p : Pending n) [Nonempty (Fin p.anchor.active.card)] (hk : 2 ≤ p.anchor.active.card)
    (chores : Bool) (G : ℝ) (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    firstAtProgram p.anchor.active hk chores p G tape = p.firstShrinkProgram hk chores G tape := by
  unfold firstAtProgram Pending.firstShrinkProgram
  congr 1
  funext result
  rw [finishFirstAt_eq]

theorem secondAtProgram_eq (p : Pending n) [Nonempty (Fin p.anchor.active.card)] (hk : 2 ≤ p.anchor.active.card)
    (chores : Bool) (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    secondAtProgram p.anchor.active hk chores p tape = p.secondShrinkProgram hk chores tape := rfl

theorem repairAtProgram_eq (p : Pending n) [Nonempty (Fin p.anchor.active.card)] (hk : 2 ≤ p.anchor.active.card)
    (chores : Bool) (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    repairAtProgram p.anchor.active hk chores p tape = p.repairProgram hk chores tape := rfl
end EnvyFreeResearch.Full.RefinedUpperGlobalRun.ProgramCertified
