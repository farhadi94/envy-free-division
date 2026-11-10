import EnvyFreeResearch.Full.UpperSnapshotProtocolRepair
import EnvyFreeResearch.Full.RefinedUpperRepair

/-! A fresh physical Repair followed by the actual cached Snapshot margin
check. A failed check restores the old material while retaining the complete
history of all attempted queries. No extra query is issued by the check. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotRepair UpperSnapshotContrast UpperRepairPreparationChecks
  UpperQueryPrograms Chores.QueryProgram
variable {n k : ℕ} [Nonempty (Fin k)]

abbrev finish := @UpperSnapshotProtocol.finish
abbrev finish_history := @UpperSnapshotProtocol.finish_history
abbrev finish_accepted := @UpperSnapshotProtocol.finish_accepted
abbrev finish_success_eq := @UpperSnapshotProtocol.finish_success_eq
abbrev finish_rejected := @UpperSnapshotProtocol.finish_rejected
abbrev finish_measurable := @UpperSnapshotProtocol.finish_measurable

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (p : RefinedUpperRepair.Tape n k) : QProgram n (PhysicalResult n k) :=
  (RefinedUpperRepair.program hk chores active origin old p).bind
    (fun result => .returned (finish (by omega) chores active gamma origin old result))

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (p : RefinedUpperRepair.Tape n k) : PhysicalResult n k :=
  finish (by omega) chores active gamma origin old
    (RefinedUpperRepair.execute policy hk chores active origin old p)

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (hinj : Function.Injective active) (gamma : ℝ) (origin : State n) (old : Fin k → State n)
    (p : RefinedUpperRepair.Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active gamma origin old p) origin.history
      (execute policy hk chores active gamma origin old p) trace ∧
      (execute policy hk chores active gamma origin old p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6*n*RefinedUpperRepair.fine n ∧
      (trace.map Prod.fst).countP isCut ≤ 3*RefinedUpperRepair.fine n := by
  obtain ⟨trace,he,hh,hq,hc⟩ := RefinedUpperRepair.program_cost policy hk chores active hinj origin old p
  refine ⟨trace, ?_, ?_, hq,hc⟩
  · simpa only [program, execute, List.append_nil] using he.bind
      (fun result => Program.returned (finish (by omega) chores active gamma origin old result))
      (Executes.returned _ _)
  · exact (finish_history _ _ _ _ _ _ _).trans hh

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
