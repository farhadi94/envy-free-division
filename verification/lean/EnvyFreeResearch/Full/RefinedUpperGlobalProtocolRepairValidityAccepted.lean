import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolRepairValidityInput
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolProgressActual

/-! An accepted final Repair restores a valid normalization state and
strictly raises the saved global potential, for the actual returned anchor. -/
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
  (hsuccess : (p.repairResult policy hk chores tape).2.2 = false)
include hp hpolicy hsuccess

theorem repairAttempt_accept_valid_progress :
    Phase.Valid μ chores whole (p.repairAttempt policy hk chores tape) ∧
    p.anchor.cachedPotential (if chores then .chore else .cake) + 1 ≤
      (p.repairAttempt policy hk chores tape).anchor.cachedPotential (if chores then .chore else .cake) := by
  have hpositive := repairReady_positive μ whole p chores hp
  have hnear := repairReady_near μ whole p chores hp
  have hg := actual_cached_finish_progress μ whole p hp.physical policy hpolicy hk chores
    hp.anchor_valid hpositive hp.shrunk_ef hp.snapshot_ef hp.own_loss hp.edge hp.large tape hsuccess
  have hh := actual_finish_history μ whole p hp.physical policy hpolicy hk chores hpositive hnear tape hsuccess
  have he : p.repairAttempt policy hk chores tape =
      .normalize (finish p (p.repairResult policy hk chores tape)) := by
    simp only [Pending.repairAttempt,Pending.finishRepair,hsuccess,Bool.false_eq_true,ite_false]
  rw [he]
  exact ⟨⟨hg.1,hh,repairReady_nonempty μ whole p chores hp⟩,hg.2⟩

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
