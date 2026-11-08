import EnvyFreeResearch.Full.UpperSnapshotSmallSecondProgram

/-! Any deterministic cache-only postprocessing of the two actual circle
outputs has the same full trace and incremental query budget. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperQueryPrograms Chores.QueryProgram UpperDomainDifference UpperGridRecords
variable {n m J : ℕ} {Output : Type}

def twoStageProgram (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle)
    (post : ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Output) : QProgram n Output :=
  (firstProgram origin cutter cuts selected t first).bind (fun out1 =>
    (partitionProgram (remainderFrom origin cutter cuts selected t first out1) cutter
      (remainderTargets J t) second).bind (fun out2 => .returned (post out1 out2)))

theorem two_stage_program_cost (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle)
    (post : ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Output) :
    ∃ trace, Executes (totalPolicy policy) (twoStageProgram origin cutter cuts selected t first second post)
      origin.history (post (firstRun policy origin cutter cuts selected t first)
        (secondRun (J:=J) policy origin cutter cuts selected t first second)) trace ∧
      (secondRun (J:=J) policy origin cutter cuts selected t first second).2.history = origin.history ++ trace ∧
      trace.length ≤ (J+2)*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ J+2 := by
  obtain ⟨t1,he1,hh1,hq1,hc1⟩ := first_program_cost policy origin cutter cuts selected t first
  obtain ⟨t2,he2,hh2,hq2,hc2⟩ := circle_program_cost policy
    (firstRemainder policy origin cutter cuts selected t first) cutter (shifts (remainderTargets J t)) second
  have hr : (firstRemainder policy origin cutter cuts selected t first).history = origin.history ++ t1 := hh1
  let firstOut := firstRun policy origin cutter cuts selected t first
  let secondOut := secondRun (J:=J) policy origin cutter cuts selected t first second
  have he2' : Executes (totalPolicy policy)
      ((partitionProgram (remainderFrom origin cutter cuts selected t first firstOut) cutter
        (remainderTargets J t) second).bind (fun out => .returned (post firstOut out)))
      (origin.history ++ t1) (post firstOut secondOut) t2 := by
    rw [show remainderFrom origin cutter cuts selected t first firstOut =
      firstRemainder policy origin cutter cuts selected t first from rfl, ← hr]
    have h := he2.bind (fun out => Program.returned (post firstOut out))
      (Executes.returned (post firstOut secondOut)
        ((firstRemainder policy origin cutter cuts selected t first).history ++ t2))
    simpa only [partitionProgram, List.append_nil] using h
  refine ⟨t1++t2,he1.bind _ he2',?_,?_,?_⟩
  · change (execute policy (firstRemainder policy origin cutter cuts selected t first) cutter
      (shifts (remainderTargets J t)) second).2.history = _
    rw [hh2,hr,List.append_assoc]
  · rw [List.length_append]
    nlinarith
  · rw [List.map_append,List.countP_append]
    omega
end EnvyFreeResearch.Full.UpperSnapshotSmall
