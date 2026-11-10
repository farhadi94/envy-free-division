import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolRepairValidityInput

/-! The actual final-Repair phase has the primitive rejection bound using
only its established RepairReady invariant and a measurable legal policy. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows RefinedUpperGlobalPhysicalFinish UpperCircularStage
variable {n : ℕ}

theorem repairAttempt_failure_lt (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (chores : Bool) (hp : p.RepairReady μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : UpperStageMeasurable.MeasurablePolicy policy) (hk : 2 ≤ p.anchor.active.card) :
    RefinedUpperRepair.law n p.anchor.active.card
      {tape | (p.repairResult policy hk chores tape).2.2 = true} < 1/64 := by
  exact RefinedUpperRepair.failure_lt μ policy hpolicy hmeas hk chores (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.physical.buffer_wf
    (repairReady_positive μ whole p chores hp) (localEndowments p)
    (localEndowments_wf μ whole p hp.physical) (repairReady_near μ whole p chores hp)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
