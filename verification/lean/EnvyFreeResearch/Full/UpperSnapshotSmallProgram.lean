import EnvyFreeResearch.Full.UpperSnapshotSmallFirstExecution
import EnvyFreeResearch.Full.UpperRecordedGridProgram

/-! Ordinary query programs for shared-circle and first-stage executions.
Program construction uses recorded input data and private random starts,
never a response policy. Operational correspondence retains every query. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperQueryPrograms Chores.QueryProgram UpperDomainDifference UpperGridRecords
variable {n m J : ℕ}

def circleProgram (origin : State n) (cutter : Fin n) (shifts : Fin J → Circle) (start : Circle) :
    QProgram n ((Fin J → ℝ) × State n) :=
  UpperRecordedGridProgram.grid (fun _ : Unit => cutter) origin J (endpointTape shifts start)

def partitionProgram (origin : State n) (cutter : Fin n) (q : Fin (J+1) → I) (start : Circle) :
    QProgram n ((Fin J → ℝ) × State n) := circleProgram origin cutter (shifts q) start

theorem circle_program_cost (policy : Policy n) (origin : State n) (cutter : Fin n)
    (shifts : Fin J → Circle) (start : Circle) :
    ∃ trace, Executes (totalPolicy policy) (circleProgram origin cutter shifts start) origin.history
      (execute policy origin cutter shifts start) trace ∧
      (execute policy origin cutter shifts start).2.history = origin.history ++ trace ∧
      trace.length ≤ J*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ J := by
  obtain ⟨trace,he,hh⟩ := UpperRecordedGridProgram.grid_executes policy (fun _ : Unit => cutter)
    origin J (endpointTape shifts start)
  have hq := execute_query_bound policy origin cutter shifts start
  have hc := execute_cut_bound policy origin cutter shifts start
  change (execute policy origin cutter shifts start).2.history = _ at hh
  rw [hh, List.length_append] at hq
  rw [hh, List.map_append, List.countP_append] at hc
  exact ⟨trace,he,hh,by omega,by omega⟩

def firstProgram (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (start : Circle) :
    QProgram n ((Fin 2 → ℝ) × State n) :=
  partitionProgram (firstSource origin cutter cuts selected t) cutter
    (singleTargets (firstAmount origin cutter cuts selected t)) start

theorem first_program_cost (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (start : Circle) :
    ∃ trace, Executes (totalPolicy policy) (firstProgram origin cutter cuts selected t start) origin.history
      (firstRun policy origin cutter cuts selected t start) trace ∧
      (firstRun policy origin cutter cuts selected t start).2.history = origin.history ++ trace ∧
      trace.length ≤ 2*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ 2 := by
  simpa only [firstProgram, firstRun, partitionProgram, partitionRun, firstSource_history] using
    circle_program_cost policy (firstSource origin cutter cuts selected t) cutter
      (shifts (singleTargets (firstAmount origin cutter cuts selected t))) start

/-- Restore the original components after querying on the selected source. -/
def restoredFrom (origin : State n) (result : (Fin 2 → ℝ) × State n) : State n :=
  ⟨refineEndpoints origin.cells (List.ofFn result.1), result.2.history⟩

def flagFrom (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (start : Circle)
    (result : (Fin 2 → ℝ) × State n) (c : Component) : Bool :=
  let arc := prefixAtom (firstAmount origin cutter cuts selected t) start (result.1 0) (result.1 1) c
  if firstFill origin cutter cuts selected t then positiveFlag cuts selected c || arc
  else positiveFlag cuts selected c && arc

def remainderFrom (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (start : Circle)
    (result : (Fin 2 → ℝ) × State n) : State n :=
  selectState (restoredFrom origin result) (fun c => !flagFrom origin cutter cuts selected t start result c)

theorem remainderFrom_actual (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (start : Circle) :
    remainderFrom origin cutter cuts selected t start (firstRun policy origin cutter cuts selected t start) =
      firstRemainder policy origin cutter cuts selected t start := rfl

end EnvyFreeResearch.Full.UpperSnapshotSmall
