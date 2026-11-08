import EnvyFreeResearch.Full.UpperSnapshotProtocolActual

/-! State-execution facade for the complete Snapshot program. These functions
are connected to the policy-free Program by operational correspondence. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotCandidates UpperQueryPrograms Chores.QueryProgram
variable {n k : ℕ} [Nonempty (Fin k)]

def smallExecute (policy : Policy n) {m : ℕ} (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k) (cuts : Fin (m+2) → ℝ)
    (score : Fin (m+1) → ℝ) (D : ℝ) (tape : CandidateTape k)
    (fresh : UpperRepair.Tape n k) : PhysicalResult n k :=
  let t := smallAmount n k D
  let selected := UpperSnapshotSmall.positiveIndices score
  let step := UpperSnapshotRepetition.smallStep policy (active cutter) cuts selected t
    (UpperSnapshotRepetition.interpolationCheck hk (active cutter) cuts score (domain origin.cells) t)
  let result := UpperSnapshotRepetition.run (UpperSnapshotRepetition.packetStep step)
    (UpperSnapshotRepetition.drawList tape) origin
  match result.2 with
  | none => rejectWhole origin result.1.history
  | some packet =>
    let candidate := UpperSnapshotSmall.allocationFrom (by omega) packet.1 (active cutter) cuts selected t
      packet.2.1.1 packet.2.1.2 packet.2.2.1 packet.2.2.2
    if candidateSafe chores active candidate.1 candidate.2.1 then
      restoreRejected origin (execute policy hk chores active (margin n) candidate.2.1 candidate.1 fresh)
    else rejectWhole origin result.1.history

def fromDataExecute (policy : Policy n) (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k)
    (data : UpperGridData.Data n (UpperRecordedQuantiles.count (Agent:=Fin k) (UpperRepair.coarse n))
      (UpperRepair.fine n))
    (zeroStart : UpperCircular.Circle) (smallTape : CandidateTape k) (fresh : UpperRepair.Tape n k) :
    PhysicalResult n k :=
  let values := UpperGridData.table active origin data
  let D := selectedDistance (by omega) values cutter
  if D=0 then zeroExecute policy (by omega) chores active (UpperGridData.aligned data) cutter zeroStart
  else if D < UpperRepair.nearError n / 16 then
    smallExecute policy (by omega) chores active (UpperGridData.aligned data) cutter (UpperGridData.cuts data)
      (fun e => values (selectedRow (by omega) values cutter) e-values cutter e) D smallTape fresh
  else restoreRejected origin (execute policy (by omega) chores active (margin n)
      (candidateBuffer (by omega) active origin data cutter)
      (candidateOld (by omega) active origin data cutter) fresh)

def snapshotExecute (policy : Policy n) (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k) (tape : Tape n k) : PhysicalResult n k :=
  fromDataExecute policy hk chores active origin cutter
    (UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) tape.1)
    tape.2.1 tape.2.2.1 tape.2.2.2
end EnvyFreeResearch.Full.UpperSnapshotProtocol
