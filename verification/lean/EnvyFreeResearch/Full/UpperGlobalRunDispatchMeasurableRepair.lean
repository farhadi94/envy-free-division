import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableFinish
import EnvyFreeResearch.Full.UpperRepairOutputMeasurable

/-! Actual Repair result and final phase on a fixed active-set stratum. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
open MeasureTheory UpperGlobalPhysical UpperCorrectionExecution UpperGlobalNormalize
open UpperZeroRows UpperCircularStage UpperStageMeasurable UpperRepairProgram
variable {n : ℕ}

def repairResultAt (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hk : 2 ≤ active.card) (chores : Bool) (p : Pending n)
    (tape : UpperRepair.Tape n active.card) : PhysicalResult n active.card :=
  UpperRepair.execute policy hk chores (enumerate active) p.buffer (localEndowmentsAt active p) tape

theorem repairResultAt_measurable (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (hk : 2 ≤ active.card) (chores : Bool) :
    Measurable (fun z : Pending n × UpperRepair.Tape n active.card =>
      repairResultAt active policy hk chores z.1 z.2) := by
  exact UpperRepairOutputMeasurable.execute_measurable policy hpolicy hk chores (enumerate active)
    (fun z : Pending n × UpperRepair.Tape n active.card => z.1.buffer)
    (fun z => localEndowmentsAt active z.1)
    (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.repeats n) (UpperRepair.reserveMark n)
    (UpperRepair.cutoff n) (UpperRepair.cellBound n) (UpperRepair.gapMultiplier n) Prod.snd
    (pending_buffer_measurable.comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp ((localEndowmentsAt_measurable active).comp measurable_fst))
    measurable_snd

def repairAt (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hk : 2 ≤ active.card) (chores : Bool) (p : Pending n)
    (tape : UpperRepair.Tape n active.card) : Phase n :=
  finishRepairAt active p (repairResultAt active policy hk chores p tape)

theorem repairAt_measurable (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (hk : 2 ≤ active.card) (chores : Bool) :
    Measurable (fun z : Pending n × UpperRepair.Tape n active.card => repairAt active policy hk chores z.1 z.2) :=
  (finishRepairAt_measurable active).comp
    (measurable_fst.prodMk (repairResultAt_measurable active policy hpolicy hk chores))

theorem repairAt_eq (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : UpperRepair.Tape n p.anchor.active.card) :
    repairAt p.anchor.active policy hk chores p tape = p.repairAttempt policy hk chores tape := rfl

end EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
