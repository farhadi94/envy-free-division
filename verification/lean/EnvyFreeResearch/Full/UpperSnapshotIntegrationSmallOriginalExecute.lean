import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallReadyPacket
import EnvyFreeResearch.Full.UpperSnapshotProtocolSafety
import EnvyFreeResearch.Full.UpperSnapshotProtocolActualRun

/-! Pure semantic reduction of the actual small branch after its reached
packet passes the recorded safety guard. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperSnapshotRepetition UpperRepairProgram
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem small_execute_of_packet (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) (cuts : Fin (m+2) → ℝ)
    (score : Fin (m+1) → ℝ) (D : ℝ) (tape : CandidateTape k) (packet : SmallPacket n k)
    (hp : (run (packetStep (smallStep policy (active cutter) cuts (positiveIndices score) (smallAmount n k D)
      (interpolationCheck hk (active cutter) cuts score (domain origin.cells) (smallAmount n k D))))
      (drawList tape) origin).2=some packet)
    (hsafe : candidateSafe chores active
      (smallPacketAllocation (by omega) (active cutter) cuts (positiveIndices score) (smallAmount n k D) packet).1
      (smallPacketAllocation (by omega) (active cutter) cuts (positiveIndices score) (smallAmount n k D) packet).2.1=true)
    (fresh : UpperRepair.Tape n k) :
    smallExecute policy hk chores active origin cutter cuts score D tape fresh =
      restoreRejected origin (execute policy hk chores active (margin n)
        (smallPacketAllocation (by omega) (active cutter) cuts (positiveIndices score) (smallAmount n k D) packet).2.1
        (smallPacketAllocation (by omega) (active cutter) cuts (positiveIndices score) (smallAmount n k D) packet).1 fresh) := by
  simp only [smallExecute,hp]
  exact if_pos hsafe

end EnvyFreeResearch.Full.UpperSnapshotProtocol
