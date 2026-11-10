import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionData
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTerminal
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolActualRun
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalPendingStart

/-! Concrete Snapshot response handling: full allocations are committed,
nonterminal allocations start the pending phase, and failures preserve history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows UpperCircularStage
open UpperQueryPrograms Chores.QueryProgram
variable {n : ℕ}

def Anchor.snapshotResult (a : Anchor n) [Nonempty (Fin a.active.card)]
    (policy : Policy n) (hk : 3 ≤ a.active.card) (chores : Bool)
    (tape : RefinedUpperSnapshotProtocol.Tape n a.active.card) :=
  RefinedUpperSnapshotProtocol.snapshotExecute policy hk chores (enumerate a.active) a.residue
    ⟨0,by omega⟩ tape

def Anchor.snapshotPending (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0 < a.active.card) (chores : Bool)
    (result : RefinedUpperRepairProgram.PhysicalResult n a.active.card) : Pending n :=
  let witness := UpperSnapshotRepair.pair hk chores (enumerate a.active) result
  Pending.start a (extendPieces a.active result.1 result.2.1.history) result.2.1
    (enumerate a.active witness.1) (enumerate a.active witness.2)

def Anchor.finishSnapshot (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0 < a.active.card) (chores : Bool)
    (result : RefinedUpperRepairProgram.PhysicalResult n a.active.card) : Phase n :=
  if result.2.2 then .snapshot (refresh a result.2.1.history)
  else if result.2.1.cells=[] then
    .done (terminal a (extendPieces a.active result.1 result.2.1.history) result.2.1.history)
  else
    let p := a.snapshotPending hk chores result
    letI : Nonempty (Fin p.anchor.active.card) := inferInstanceAs (Nonempty (Fin a.active.card))
    .firstShrink p (p.firstFactor (if chores then .chore else .cake))

def Anchor.snapshotAttempt (a : Anchor n) [Nonempty (Fin a.active.card)]
    (policy : Policy n) (hk : 3 ≤ a.active.card) (chores : Bool)
    (tape : RefinedUpperSnapshotProtocol.Tape n a.active.card) : Phase n :=
  a.finishSnapshot (by omega) chores (a.snapshotResult policy hk chores tape)

def Anchor.snapshotProgram (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 3 ≤ a.active.card) (chores : Bool)
    (tape : RefinedUpperSnapshotProtocol.Tape n a.active.card) : QProgram n (Phase n) :=
  (RefinedUpperSnapshotProtocol.snapshotProgram hk chores (enumerate a.active) a.residue ⟨0,by omega⟩ tape).bind
    (fun result => .returned (a.finishSnapshot (by omega) chores result))

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
