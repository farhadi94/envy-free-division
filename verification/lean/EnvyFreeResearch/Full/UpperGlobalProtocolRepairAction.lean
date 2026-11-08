import EnvyFreeResearch.Full.UpperGlobalPhysicalFinishActual
import EnvyFreeResearch.Full.UpperGlobalPhysicalPendingStart
import EnvyFreeResearch.Full.UpperRepairHistory

/-! The final paid Repair action returns an actual globally committed anchor
on acceptance and retains the saved physical phase on rejection. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage
open UpperQueryPrograms Chores.QueryProgram UpperGlobalPhysicalFinish
variable {n : ℕ}

def Pending.repairResult (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : UpperRepair.Tape n p.anchor.active.card) :=
  UpperRepair.execute policy hk chores (enumerate p.anchor.active) p.buffer (localEndowments p) tape

def Pending.finishRepair (p : Pending n)
    (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card) : Phase n :=
  if result.2.2 then .finalRepair (p.refresh result.2.1.history)
  else .normalize (UpperGlobalPhysicalFinish.finish p result)

def Pending.repairAttempt (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : UpperRepair.Tape n p.anchor.active.card) : Phase n :=
  p.finishRepair (p.repairResult policy hk chores tape)

def Pending.repairProgram (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : UpperRepair.Tape n p.anchor.active.card) : QProgram n (Phase n) :=
  (UpperRepair.program hk chores (enumerate p.anchor.active) p.buffer (localEndowments p) tape).bind
    (fun result => .returned (p.finishRepair result))

theorem repairAttempt_executes (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : UpperRepair.Tape n p.anchor.active.card) :
    ∃ trace, Executes (totalPolicy policy) (p.repairProgram hk chores tape) p.buffer.history
      (p.repairAttempt policy hk chores tape) trace ∧
      (p.repairResult policy hk chores tape).2.1.history=p.buffer.history++trace ∧
      trace.length ≤ 6*n*UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3*UpperRepair.fine n := by
  obtain ⟨tr,he,hh,hq,hc⟩ := UpperRepair.program_cost policy hk chores
    (enumerate p.anchor.active) (enumerate_injective _) p.buffer (localEndowments p) tape
  refine ⟨tr,?_,hh,hq,hc⟩
  simpa only [Pending.repairProgram,Pending.repairAttempt,Pending.repairResult,List.append_nil] using
    he.bind (fun result => .returned (p.finishRepair result)) (Executes.returned _ _)

theorem refreshRepair_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
    (hnear : UpperRepairPreparationChecks.Near chores μ (enumerate p.anchor.active) p.buffer
      (localEndowments p) (UpperRepair.nearError n))
    (tape : UpperRepair.Tape n p.anchor.active.card) :
    (p.refresh (p.repairResult policy hk chores tape).2.1.history).Physical μ whole := by
  apply pending_refresh_physical μ whole p hp
  · exact UpperRepairHistory.original_history_truthful μ policy hpolicy hk chores
      (enumerate p.anchor.active) (enumerate_injective _) p.buffer hp.buffer_wf hpositive
      (localEndowments p) (localEndowments_wf μ whole p hp) hnear tape
  · obtain ⟨tr,_,hh,_,_⟩ := repairAttempt_executes p policy hk chores tape
    rw [hh]
    exact List.subset_append_left _ _

end EnvyFreeResearch.Full.UpperGlobalPhysical
