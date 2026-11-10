import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolRepairValidityAccepted
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolValidityRefresh

/-! The actual paid final-Repair attempt preserves the global phase invariant
on rejection and acceptance; acceptance also provides strict progress. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows RefinedUpperGlobalPhysicalFinish UpperCircularStage
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
  [Nonempty (Fin p.anchor.active.card)] (chores : Bool) (hp : p.RepairReady μ chores whole)
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ p.anchor.active.card) (tape : RefinedUpperRepair.Tape n p.anchor.active.card)
include hp hpolicy

theorem repairAttempt_reject_valid
    (hreject : (p.repairResult policy hk chores tape).2.2 = true) :
    Phase.Valid μ chores whole (p.repairAttempt policy hk chores tape) := by
  have hphysical := refreshRepair_physical μ whole p hp.physical policy hpolicy hk chores
    (repairReady_positive μ whole p chores hp) (repairReady_near μ whole p chores hp) tape
  have hready := pending_refresh_repairReady_of_physical μ whole p chores hp
    (p.repairResult policy hk chores tape).2.1.history hphysical
  simpa only [Pending.repairAttempt,Pending.finishRepair,hreject,ite_true,Phase.Valid] using hready

theorem repairAttempt_valid : Phase.Valid μ chores whole (p.repairAttempt policy hk chores tape) := by
  cases hr : (p.repairResult policy hk chores tape).2.2 with
  | false => exact (repairAttempt_accept_valid_progress μ whole p chores hp policy hpolicy hk tape hr).1
  | true => exact repairAttempt_reject_valid μ whole p chores hp policy hpolicy hk tape hr

theorem repairAttempt_valid_progress :
    Phase.Valid μ chores whole (p.repairAttempt policy hk chores tape) ∧
    ((p.repairResult policy hk chores tape).2.2 = false →
      p.anchor.cachedPotential (if chores then .chore else .cake) + 1 ≤
        (p.repairAttempt policy hk chores tape).anchor.cachedPotential (if chores then .chore else .cake)) := by
  exact ⟨repairAttempt_valid μ whole p chores hp policy hpolicy hk tape,
    fun hs => (repairAttempt_accept_valid_progress μ whole p chores hp policy hpolicy hk tape hs).2⟩

omit hp hpolicy in
theorem repairAttempt_rejected_anchor
    (hreject : (p.repairResult policy hk chores tape).2.2 = true) :
    (p.repairAttempt policy hk chores tape).anchor = p.anchor := by
  simp only [Pending.repairAttempt,Pending.finishRepair,hreject,ite_true,Phase.anchor,Pending.refresh]

omit hp hpolicy in
theorem repairResult_rejected_restore
    (hreject : (p.repairResult policy hk chores tape).2.2 = true) :
    (p.repairResult policy hk chores tape).1 = localEndowments p ∧
      (p.repairResult policy hk chores tape).2.1.cells = p.buffer.cells :=
  RefinedUpperRepair.rejected_restore policy hk chores (enumerate p.anchor.active) p.buffer
    (localEndowments p) tape hreject

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
