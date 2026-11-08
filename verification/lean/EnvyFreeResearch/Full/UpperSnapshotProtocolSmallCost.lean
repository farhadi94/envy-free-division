import EnvyFreeResearch.Full.UpperSnapshotProtocolActualRun
import EnvyFreeResearch.Full.UpperSnapshotProtocolSafety
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallPacketCost
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallPacketHistory

/-! Complete query accounting for the small branch: every rejected candidate,
the accepted candidate, and the optional fresh Repair share one ordinary
query trace. Pure guards and output restoration use no extra oracle calls. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperQueryPrograms Chores.QueryProgram
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem restored_repair_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (whole buffer : State n) (old : Fin k → State n) (fresh : UpperRepair.Tape n k) :
    ∃ trace, Executes (totalPolicy policy)
      ((program hk chores active (margin n) buffer old fresh).bind (fun out => .returned (restoreRejected whole out)))
      buffer.history (restoreRejected whole (execute policy hk chores active (margin n) buffer old fresh)) trace ∧
      (restoreRejected whole (execute policy hk chores active (margin n) buffer old fresh)).2.1.history = buffer.history ++ trace ∧
      trace.length ≤ 6*n*UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3*UpperRepair.fine n := by
  obtain ⟨trace,he,hh,hq,hc⟩ := program_cost policy hk chores active hinj (margin n) buffer old fresh
  refine ⟨trace,?_,(restoreRejected_history whole _).trans hh,hq,hc⟩
  simpa only [List.append_nil] using he.bind (fun out => Program.returned (restoreRejected whole out))
    (Executes.returned _ _)

theorem small_program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (cutter : Fin k) (cuts : Fin (m+2) → ℝ)
    (score : Fin (m+1) → ℝ) (D : ℝ) (tape : CandidateTape k) (fresh : UpperRepair.Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (smallProgram hk chores active origin cutter cuts score D tape fresh)
      origin.history (smallExecute policy hk chores active origin cutter cuts score D tape fresh) trace ∧
      (smallExecute policy hk chores active origin cutter cuts score D tape fresh).2.1.history = origin.history ++ trace ∧
      trace.length ≤ (16*k)*((k+2)*(n+1)) + 6*n*UpperRepair.fine n ∧
      (trace.map Prod.fst).countP isCut ≤ (16*k)*(k+2) + 3*UpperRepair.fine n := by
  let t := smallAmount n k D
  let selected := UpperSnapshotSmall.positiveIndices score
  let check := UpperSnapshotRepetition.interpolationCheck hk (active cutter) cuts score (domain origin.cells) t
  let result := UpperSnapshotRepetition.run
    (UpperSnapshotRepetition.packetStep (UpperSnapshotRepetition.smallStep policy (active cutter) cuts selected t check))
    (UpperSnapshotRepetition.drawList tape) origin
  obtain ⟨firstTrace,he,hh,hq,hc⟩ := UpperSnapshotRepetition.actual_small_packet_cost policy (active cutter) cuts selected t check origin tape
  change result.1.history = origin.history ++ firstTrace at hh
  let post := fun result : State n × Option (UpperSnapshotRepetition.SmallPacket n k) =>
    match result.2 with
    | none => (Program.returned (rejectWhole origin result.1.history) : QProgram n (PhysicalResult n k))
    | some packet =>
      let candidate := UpperSnapshotRepetition.smallPacketAllocation (by omega) (active cutter) cuts selected t packet
      if candidateSafe chores active candidate.1 candidate.2.1 then
        (program hk chores active (margin n) candidate.2.1 candidate.1 fresh).bind
          (fun out => .returned (restoreRejected origin out))
      else .returned (rejectWhole origin result.1.history)
  let output := fun result : State n × Option (UpperSnapshotRepetition.SmallPacket n k) =>
    match result.2 with
    | none => rejectWhole (k:=k) origin result.1.history
    | some packet =>
      let candidate := UpperSnapshotRepetition.smallPacketAllocation (by omega) (active cutter) cuts selected t packet
      if candidateSafe chores active candidate.1 candidate.2.1 then
        restoreRejected origin (execute policy hk chores active (margin n) candidate.2.1 candidate.1 fresh)
      else rejectWhole origin result.1.history
  have hout : smallExecute policy hk chores active origin cutter cuts score D tape fresh = output result := rfl
  have ht : ∃ tail, Executes (totalPolicy policy) (post result) result.1.history
      (smallExecute policy hk chores active origin cutter cuts score D tape fresh) tail ∧
      (smallExecute policy hk chores active origin cutter cuts score D tape fresh).2.1.history = result.1.history ++ tail ∧
      tail.length ≤ 6*n*UpperRepair.fine n ∧ (tail.map Prod.fst).countP isCut ≤ 3*UpperRepair.fine n := by
    rw [hout]
    cases hp : result.2 with
    | none =>
      simp only [post,output,hp]
      exact ⟨[],Executes.returned _ _,by simp [rejectWhole],by simp,by simp⟩
    | some packet =>
      let candidate := UpperSnapshotRepetition.smallPacketAllocation (by omega) (active cutter) cuts selected t packet
      have hhist : candidate.2.1.history = result.1.history :=
        (UpperSnapshotRepetition.small_packet_allocation_history (by omega) policy (active cutter) cuts selected t check
          (UpperSnapshotRepetition.drawList tape) origin packet hp).2.1
      simp only [post,output,hp]
      change ∃ tail, Executes (totalPolicy policy)
        (if candidateSafe chores active candidate.1 candidate.2.1 then
          (program hk chores active (margin n) candidate.2.1 candidate.1 fresh).bind
            (fun out => .returned (restoreRejected origin out))
        else .returned (rejectWhole origin result.1.history)) result.1.history
        (if candidateSafe chores active candidate.1 candidate.2.1 then
          restoreRejected origin (execute policy hk chores active (margin n) candidate.2.1 candidate.1 fresh)
        else rejectWhole origin result.1.history) tail ∧
        (if candidateSafe chores active candidate.1 candidate.2.1 then
          restoreRejected origin (execute policy hk chores active (margin n) candidate.2.1 candidate.1 fresh)
        else rejectWhole origin result.1.history).2.1.history = result.1.history ++ tail ∧
        tail.length ≤ 6*n*UpperRepair.fine n ∧ (tail.map Prod.fst).countP isCut ≤ 3*UpperRepair.fine n
      by_cases hs : candidateSafe chores active candidate.1 candidate.2.1 = true
      · simp only [hs,ite_true]
        obtain ⟨tail,hte,hth,htq,htc⟩ := restored_repair_cost policy hk chores active hinj origin candidate.2.1 candidate.1 fresh
        rw [hhist] at hte hth
        exact ⟨tail,hte,hth,htq,htc⟩
      · simp only [hs,ite_false]
        exact ⟨[],Executes.returned _ _,by simp [rejectWhole],by simp,by simp⟩
  obtain ⟨tail,htail,hfinal,htq,htc⟩ := ht
  refine ⟨firstTrace++tail,?_,?_,?_,?_⟩
  · rw [hh] at htail
    exact he.bind post htail
  · rw [hfinal,hh,List.append_assoc]
  · simpa only [List.length_append] using Nat.add_le_add hq htq
  · simpa only [List.map_append,List.countP_append] using Nat.add_le_add hc htc
end EnvyFreeResearch.Full.UpperSnapshotProtocol
