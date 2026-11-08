import EnvyFreeResearch.Full.UpperSnapshotProtocolLaw
import EnvyFreeResearch.Full.UpperSnapshotProtocolZero
import EnvyFreeResearch.Full.UpperSnapshotIntegrationThreshold
import EnvyFreeResearch.Full.UpperSnapshotRepetitionPacket
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallCheck
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocation

/-! The complete ordinary-query Snapshot program. Every returned candidate
is assembled from recorded replies. Actual near-EF and buffer checks precede
the single fresh Repair, and any rejection restores the whole input domain
with the complete attempted-query history. Correctness/law adapters follow
in separate modules. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotCandidates UpperQueryPrograms Chores.QueryProgram
variable {n k : ℕ} [Nonempty (Fin k)]

def rejectWhole (origin : State n) (history : History n) : PhysicalResult n k :=
  (fun _ => ⟨[],history⟩,⟨origin.cells,history⟩,true)

def restoreRejected (origin : State n) (out : PhysicalResult n k) : PhysicalResult n k :=
  if out.2.2 then rejectWhole origin out.2.1.history else out

def candidateSafe (chores : Bool) (active : Fin k → Fin n)
    (old : Fin k → State n) (buffer : State n) : Bool :=
  decide ((∀ i, 0 < total buffer (active i)) ∧ ∀ i j,
    if chores then total (old i) (active i) - total (old j) (active i) ≤
      UpperRepair.nearError n * total buffer (active i)
    else total (old j) (active i) - total (old i) (active i) ≤
      UpperRepair.nearError n * total buffer (active i))

def smallAmount (n k : ℕ) (D : ℝ) : ℝ := (1-(8/UpperRepair.nearError n)*D)/k

def smallProgram {m : ℕ} (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k) (cuts : Fin (m+2) → ℝ)
    (score : Fin (m+1) → ℝ) (D : ℝ) (tape : CandidateTape k)
    (fresh : UpperRepair.Tape n k) : QProgram n (PhysicalResult n k) :=
  let t := smallAmount n k D
  let selected := UpperSnapshotSmall.positiveIndices score
  let attempt := UpperSnapshotRepetition.smallAttempt (active cutter) cuts selected t
    (UpperSnapshotRepetition.interpolationCheck hk (active cutter) cuts score (domain origin.cells) t)
  (UpperSnapshotRepetition.program (UpperSnapshotRepetition.packetAttempt attempt)
    (UpperSnapshotRepetition.drawList tape) origin).bind (fun result =>
      match result.2 with
      | none => .returned (rejectWhole origin result.1.history)
      | some packet =>
        let candidate := UpperSnapshotSmall.allocationFrom (by omega) packet.1 (active cutter) cuts selected t
          packet.2.1.1 packet.2.1.2 packet.2.2.1 packet.2.2.2
        if candidateSafe chores active candidate.1 candidate.2.1 then
          (program hk chores active (margin n) candidate.2.1 candidate.1 fresh).bind
            (fun out => .returned (restoreRejected origin out))
        else .returned (rejectWhole origin result.1.history))

def fromDataProgram (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k)
    (data : UpperGridData.Data n (UpperRecordedQuantiles.count (Agent:=Fin k) (UpperRepair.coarse n))
      (UpperRepair.fine n))
    (zeroStart : UpperCircular.Circle) (smallTape : CandidateTape k) (fresh : UpperRepair.Tape n k) :
    QProgram n (PhysicalResult n k) :=
  let values := UpperGridData.table active origin data
  let D := selectedDistance (by omega) values cutter
  if D=0 then zeroProgram (by omega) chores active (UpperGridData.aligned data) cutter zeroStart
  else if D < UpperRepair.nearError n / 16 then
    smallProgram (by omega) chores active (UpperGridData.aligned data) cutter (UpperGridData.cuts data)
      (fun e => values (selectedRow (by omega) values cutter) e-values cutter e) D smallTape fresh
  else
    (program (by omega) chores active (margin n)
      (candidateBuffer (by omega) active origin data cutter)
      (candidateOld (by omega) active origin data cutter) fresh).bind
      (fun out => .returned (restoreRejected origin out))

def snapshotProgram (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k) (tape : Tape n k) : QProgram n (PhysicalResult n k) :=
  (UpperRecordedGridProgram.prepare active origin (UpperRepair.coarse n) (UpperRepair.fine n) tape.1).bind
    (fun data => fromDataProgram hk chores active origin cutter data tape.2.1 tape.2.2.1 tape.2.2.2)
end EnvyFreeResearch.Full.UpperSnapshotProtocol
