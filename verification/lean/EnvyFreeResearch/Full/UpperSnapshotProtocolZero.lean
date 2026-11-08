import EnvyFreeResearch.Full.UpperSnapshotSmallProgram
import EnvyFreeResearch.Full.UpperSnapshotProtocolRepair

/-! Snapshot's zero-disagreement branch queries a complete cutter-equal
partition and checks actual cached envy inequalities. Accepted outputs are
complete allocations; rejected outputs retain the original domain/history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperQueryPrograms Chores.QueryProgram UpperSnapshotSmall
variable {n k : ℕ}

def equalPieces (hk : 0 < k) (start : UpperSnapshotSmall.Circle) (out : (Fin k → ℝ) × State n) : Fin k → State n :=
  fun j => selectState out.2 (fun c =>
    prefixAtom (equalTargets k j.succ) start (out.1 ⟨0,hk⟩) (boundary hk out.1 j.succ) c &&
    !prefixAtom (equalTargets k j.castSucc) start (out.1 ⟨0,hk⟩) (boundary hk out.1 j.castSucc) c)

def completeCheck (chores : Bool) (active : Fin k → Fin n) (pieces : Fin k → State n) : Bool :=
  decide (∀ i j, if chores then total (pieces i) (active i) ≤ total (pieces j) (active i)
    else total (pieces j) (active i) ≤ total (pieces i) (active i))

def zeroFinish (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (start : UpperSnapshotSmall.Circle)
    (out : (Fin k → ℝ) × State n) : PhysicalResult n k :=
  if completeCheck chores active (equalPieces hk start out) then
    (equalPieces hk start out, ⟨[],out.2.history⟩,false)
  else (fun _ => ⟨[],out.2.history⟩,out.2,true)

def zeroProgram (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k) (start : UpperSnapshotSmall.Circle) : QProgram n (PhysicalResult n k) :=
  (partitionProgram origin (active cutter) (equalTargets k) start).bind
    (fun out => .returned (zeroFinish hk chores active start out))

def zeroExecute (policy : Policy n) (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k) (start : UpperSnapshotSmall.Circle) : PhysicalResult n k :=
  zeroFinish hk chores active start (partitionRun policy origin (active cutter) (equalTargets k) start)

theorem zeroFinish_history (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (start : UpperSnapshotSmall.Circle)
    (out : (Fin k → ℝ) × State n) :
    (zeroFinish hk chores active start out).2.1.history = out.2.history := by
  unfold zeroFinish
  split <;> rfl

theorem zeroFinish_success (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (start : UpperSnapshotSmall.Circle)
    (out : (Fin k → ℝ) × State n) :
    (zeroFinish hk chores active start out).2.2 = false ↔
      completeCheck chores active (equalPieces hk start out) = true := by
  unfold zeroFinish
  split <;> simp_all

theorem zero_program_cost (policy : Policy n) (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k) (start : UpperSnapshotSmall.Circle) :
    ∃ trace, Executes (totalPolicy policy) (zeroProgram hk chores active origin cutter start) origin.history
      (zeroExecute policy hk chores active origin cutter start) trace ∧
      (zeroExecute policy hk chores active origin cutter start).2.1.history = origin.history ++ trace ∧
      trace.length ≤ k*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ k := by
  obtain ⟨trace,he,hh,hq,hc⟩ := circle_program_cost policy origin (active cutter) (shifts (equalTargets k)) start
  refine ⟨trace,?_,?_,hq,hc⟩
  · simpa only [zeroProgram,zeroExecute,partitionProgram,partitionRun,List.append_nil] using
      he.bind (fun out => Program.returned (zeroFinish hk chores active start out)) (Executes.returned _ _)
  · exact (zeroFinish_history _ _ _ _ _).trans hh

theorem completeCheck_iff (chores : Bool) (active : Fin k → Fin n) (pieces : Fin k → State n) :
    completeCheck chores active pieces = true ↔
      ∀ i j, if chores then total (pieces i) (active i) ≤ total (pieces j) (active i)
        else total (pieces j) (active i) ≤ total (pieces i) (active i) := by
  exact decide_eq_true_iff
end EnvyFreeResearch.Full.UpperSnapshotProtocol
