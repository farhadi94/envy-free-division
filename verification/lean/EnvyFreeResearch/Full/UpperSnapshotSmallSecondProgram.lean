import EnvyFreeResearch.Full.UpperSnapshotSmallProgram
import EnvyFreeResearch.Full.UpperSnapshotSmallSecondExecution

/-! Actual sequential first/second circle program, with exactly the
full-history executor used by the conditional probability proof. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperQueryPrograms Chores.QueryProgram UpperDomainDifference UpperGridRecords
variable {n m J : ℕ}

def secondProgram (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) :
    QProgram n ((Fin J → ℝ) × State n) :=
  (firstProgram origin cutter cuts selected t first).bind (fun result =>
    partitionProgram (remainderFrom origin cutter cuts selected t first result) cutter
      (remainderTargets J t) second)

theorem second_program_cost (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) :
    ∃ trace, Executes (totalPolicy policy) (secondProgram (J:=J) origin cutter cuts selected t first second) origin.history
      (secondRun (J:=J) policy origin cutter cuts selected t first second) trace ∧
      (secondRun (J:=J) policy origin cutter cuts selected t first second).2.history = origin.history ++ trace ∧
      trace.length ≤ (J+2)*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ J+2 := by
  obtain ⟨t1,he1,hh1,hq1,hc1⟩ := first_program_cost policy origin cutter cuts selected t first
  obtain ⟨t2,he2,hh2,hq2,hc2⟩ := circle_program_cost policy
    (firstRemainder policy origin cutter cuts selected t first) cutter (shifts (remainderTargets J t)) second
  have hr : (firstRemainder policy origin cutter cuts selected t first).history = origin.history ++ t1 := hh1
  have he2' : Executes (totalPolicy policy)
      (partitionProgram (remainderFrom origin cutter cuts selected t first
        (firstRun policy origin cutter cuts selected t first)) cutter (remainderTargets J t) second)
      (origin.history ++ t1) (secondRun (J:=J) policy origin cutter cuts selected t first second) t2 := by
    rw [remainderFrom_actual, ← hr]
    exact he2
  refine ⟨t1++t2,he1.bind _ he2',?_,?_,?_⟩
  · change (execute policy (firstRemainder policy origin cutter cuts selected t first) cutter
      (shifts (remainderTargets J t)) second).2.history = _
    rw [hh2,hr,List.append_assoc]
  · rw [List.length_append]
    nlinarith
  · rw [List.map_append,List.countP_append]
    omega
end EnvyFreeResearch.Full.UpperSnapshotSmall
