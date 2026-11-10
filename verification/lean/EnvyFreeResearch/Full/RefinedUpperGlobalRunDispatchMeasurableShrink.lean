import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunDispatchMeasurableBridge
import EnvyFreeResearch.Full.RefinedUpperShrinkMeasurable

/-! Joint Borel actual first/second Shrink attempts, retaining the whole input
state, factor and selected fresh tape. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
open MeasureTheory RefinedUpperGlobalPhysical UpperZeroRows UpperCircularStage UpperStageMeasurable
variable {n : ℕ}

def firstShrinkAt (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hk : 2 ≤ active.card) (chores : Bool) (p : Pending n) (G : ℝ)
    (tape : RefinedUpperRepair.Tape n active.card) : Phase n :=
  finishFirstAt active p chores G
    (RefinedUpperShrink.execute policy hk chores (enumerate active) p.buffer G tape)

theorem firstShrinkAt_measurable (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (hk : 2 ≤ active.card) (chores : Bool) :
    Measurable (fun z : (Pending n × ℝ) × RefinedUpperRepair.Tape n active.card =>
      firstShrinkAt active policy hk chores z.1.1 z.1.2 z.2) := by
  have hr := RefinedUpperShrink.execute_measurable policy hpolicy hk chores (enumerate active)
    (fun z : (Pending n × ℝ) × RefinedUpperRepair.Tape n active.card => z.1.1.buffer)
    (fun z => z.1.2) Prod.snd
    (pending_buffer_measurable.comp (measurable_fst.comp measurable_fst))
    (measurable_snd.comp measurable_fst) measurable_snd
  exact (finishFirstAt_measurable active chores).comp (measurable_fst.prodMk hr)

def secondShrinkAt (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hk : 2 ≤ active.card) (chores : Bool) (p : Pending n)
    (tape : RefinedUpperRepair.Tape n active.card) : Phase n :=
  finishSecondAt active p
    (RefinedUpperShrink.execute policy hk chores (enumerate active) p.buffer (2/RefinedUpperRepair.nearError n) tape)

theorem secondShrinkAt_measurable (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (hk : 2 ≤ active.card) (chores : Bool) :
    Measurable (fun z : Pending n × RefinedUpperRepair.Tape n active.card =>
      secondShrinkAt active policy hk chores z.1 z.2) := by
  have hr := RefinedUpperShrink.execute_measurable policy hpolicy hk chores (enumerate active)
    (fun z : Pending n × RefinedUpperRepair.Tape n active.card => z.1.buffer)
    (fun _ => 2/RefinedUpperRepair.nearError n) Prod.snd
    (pending_buffer_measurable.comp measurable_fst) measurable_const measurable_snd
  exact (finishSecondAt_measurable active).comp (measurable_fst.prodMk hr)

theorem firstShrinkAt_eq (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    firstShrinkAt p.anchor.active policy hk chores p G tape =
      p.firstShrinkAttempt policy hk chores G tape :=
  finishFirstAt_eq p chores G _

theorem secondShrinkAt_eq (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    secondShrinkAt p.anchor.active policy hk chores p tape =
      p.secondShrinkAttempt policy hk chores tape := rfl

end EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
