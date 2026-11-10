import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolSmallCost

/-! Uniform continuation cost across all three concrete Snapshot branches. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperQueryPrograms Chores.QueryProgram UpperSnapshotCandidates
open UpperSnapshotProtocol (zero_program_cost zeroProgram zeroExecute)
variable {n k : ℕ} [Nonempty (Fin k)]

theorem fromData_program_cost (policy : Policy n) (hk : 3 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (cutter : Fin k)
    (data : UpperGridData.Data n (UpperRecordedQuantiles.count (Agent:=Fin k) (RefinedUpperRepair.coarse n)) (RefinedUpperRepair.fine n))
    (zeroStart : UpperCircular.Circle) (smallTape : CandidateTape k) (fresh : RefinedUpperRepair.Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (fromDataProgram hk chores active origin cutter data zeroStart smallTape fresh)
      data.2.2.history (fromDataExecute policy hk chores active origin cutter data zeroStart smallTape fresh) trace ∧
      (fromDataExecute policy hk chores active origin cutter data zeroStart smallTape fresh).2.1.history = data.2.2.history ++ trace ∧
      trace.length ≤ (16*k)*((k+2)*(n+1)) + 6*n*RefinedUpperRepair.fine n ∧
      (trace.map Prod.fst).countP isCut ≤ (16*k)*(k+2) + 3*RefinedUpperRepair.fine n := by
  let values := UpperGridData.table active origin data
  let D := selectedDistance (by omega) values cutter
  unfold fromDataProgram fromDataExecute
  by_cases hz : D=0
  · dsimp only [D,values] at hz
    simp only [hz,ite_true]
    obtain ⟨trace,he,hh,hq,hc⟩ := zero_program_cost policy (by omega) chores active (UpperGridData.aligned data) cutter zeroStart
    refine ⟨trace,he,hh,?_,?_⟩
    · have hle : k*(n+1) ≤ (16*k)*((k+2)*(n+1)) := by nlinarith
      omega
    · have hle : k ≤ (16*k)*(k+2) := by nlinarith
      omega
  · dsimp only [D,values] at hz
    simp only [hz,ite_false]
    by_cases hs : D<RefinedUpperRepair.nearError n/16
    · dsimp only [D,values] at hs
      simp only [hs,ite_true]
      exact small_program_cost policy (by omega) chores active hinj (UpperGridData.aligned data) cutter
        (UpperGridData.cuts data) (fun e => values (selectedRow (by omega) values cutter) e-values cutter e) D smallTape fresh
    · dsimp only [D,values] at hs
      simp only [hs,ite_false]
      obtain ⟨trace,he,hh,hq,hc⟩ := restored_repair_cost policy (by omega) chores active hinj origin
        (candidateBuffer (by omega) active origin data cutter) (candidateOld (by omega) active origin data cutter) fresh
      have hhistory : (candidateBuffer (by omega) active origin data cutter).history = data.2.2.history := by
        rw [candidateBuffer_history]
      rw [hhistory] at he hh
      exact ⟨trace,he,hh,by omega,by omega⟩
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
