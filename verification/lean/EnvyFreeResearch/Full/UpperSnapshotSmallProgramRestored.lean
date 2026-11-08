import EnvyFreeResearch.Full.UpperSnapshotSmallSecondProgram
import EnvyFreeResearch.Full.UpperSnapshotSmallSecondRestored

/-! The physical rejection state is computed from actual first- and
second-stage replies, preserving all endpoints and the original material. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperQueryPrograms Chores.QueryProgram UpperDomainDifference UpperGridRecords
variable {n m J : ℕ}

def secondRestoredFrom (origin : State n) (first : (Fin 2 → ℝ) × State n)
    (second : (Fin J → ℝ) × State n) : State n :=
  ⟨refineEndpoints (restoredFrom origin first).cells (List.ofFn second.1),second.2.history⟩

def secondRestoredProgram (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) : QProgram n (State n) :=
  (firstProgram origin cutter cuts selected t first).bind (fun out1 =>
    (partitionProgram (remainderFrom origin cutter cuts selected t first out1) cutter
      (remainderTargets J t) second).bind (fun out2 => .returned (secondRestoredFrom origin out1 out2)))

theorem second_restored_program_cost (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) :
    ∃ trace, Executes (totalPolicy policy) (secondRestoredProgram (J:=J) origin cutter cuts selected t first second)
      origin.history (secondRestored (J:=J) policy origin cutter cuts selected t first second) trace ∧
      (secondRestored (J:=J) policy origin cutter cuts selected t first second).history = origin.history ++ trace ∧
      trace.length ≤ (J+2)*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ J+2 := by
  obtain ⟨t1,he1,hh1,hq1,hc1⟩ := first_program_cost policy origin cutter cuts selected t first
  obtain ⟨t2,he2,hh2,hq2,hc2⟩ := circle_program_cost policy
    (firstRemainder policy origin cutter cuts selected t first) cutter (shifts (remainderTargets J t)) second
  have hr : (firstRemainder policy origin cutter cuts selected t first).history = origin.history ++ t1 := hh1
  let firstOut := firstRun policy origin cutter cuts selected t first
  let secondOut := secondRun (J:=J) policy origin cutter cuts selected t first second
  have he2' : Executes (totalPolicy policy)
      ((partitionProgram (remainderFrom origin cutter cuts selected t first firstOut) cutter
        (remainderTargets J t) second).bind (fun out => .returned (secondRestoredFrom origin firstOut out)))
      (origin.history ++ t1) (secondRestored (J:=J) policy origin cutter cuts selected t first second) t2 := by
    rw [show remainderFrom origin cutter cuts selected t first firstOut =
      firstRemainder policy origin cutter cuts selected t first from rfl, ← hr]
    have h := he2.bind (fun out => Program.returned (secondRestoredFrom origin firstOut out))
      (Executes.returned (secondRestoredFrom origin firstOut secondOut)
        ((firstRemainder policy origin cutter cuts selected t first).history ++ t2))
    simpa only [partitionProgram, secondRestored, secondRestoredFrom, restoredFrom,
      firstOut, secondOut, firstRestored, List.append_nil] using h
  refine ⟨t1++t2,he1.bind _ he2',?_,?_,?_⟩
  · change (execute policy (firstRemainder policy origin cutter cuts selected t first) cutter
      (shifts (remainderTargets J t)) second).2.history = _
    rw [hh2,hr,List.append_assoc]
  · rw [List.length_append]
    nlinarith
  · rw [List.map_append,List.countP_append]
    omega
end EnvyFreeResearch.Full.UpperSnapshotSmall
