import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolStageActions
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSnapshotAction
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolRepairAction
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeProgram
import EnvyFreeResearch.Full.RefinedUpperGlobalTapeRequests

/-! The concrete global dispatcher. Each paid phase draws the actual local
primitive's tape for its current population from the universal fresh draw. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperQueryPrograms
variable {n : ℕ}

def Anchor.request (a : Anchor n) (hk : 2 ≤ a.active.card) (kind : Kind) : Request n :=
  (⟨⟨a.active.card,by have := UpperZeroRows.active_size_bound a.active; omega⟩,hk⟩,kind)

def Phase.history : Phase n → History n
  | .normalize a | .snapshot a | .done a => a.residue.history
  | .firstShrink p _ | .secondShrink p | .finalRepair p => p.buffer.history

def Phase.step (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (phase : Phase n) (draw : Universal n) : Phase n :=
  match phase with
  | .normalize a => RefinedUpperGlobalNormalize.execute policy fallback chores a
  | .snapshot a =>
    if hk : 3 ≤ a.active.card then
      letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
      a.snapshotAttempt policy hk chores (draw (a.request (by omega) .snapshot))
    else .done a
  | .firstShrink p G =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      p.firstShrinkAttempt policy (by omega) chores G (draw (p.anchor.request (by omega) .shrink))
    else .done p.anchor
  | .secondShrink p =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      p.secondShrinkAttempt policy (by omega) chores (draw (p.anchor.request (by omega) .shrink))
    else .done p.anchor
  | .finalRepair p =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      p.repairAttempt policy (by omega) chores (draw (p.anchor.request (by omega) .repair))
    else .done p.anchor
  | .done a => .done a

def Phase.stepProgram (fallback : Fin n) (chores : Bool)
    (phase : Phase n) (draw : Universal n) : QProgram n (Phase n) :=
  match phase with
  | .normalize a => RefinedUpperGlobalNormalize.program fallback chores a
  | .snapshot a =>
    if hk : 3 ≤ a.active.card then
      letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
      a.snapshotProgram hk chores (draw (a.request (by omega) .snapshot))
    else .returned (.done a)
  | .firstShrink p G =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      p.firstShrinkProgram (by omega) chores G (draw (p.anchor.request (by omega) .shrink))
    else .returned (.done p.anchor)
  | .secondShrink p =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      p.secondShrinkProgram (by omega) chores (draw (p.anchor.request (by omega) .shrink))
    else .returned (.done p.anchor)
  | .finalRepair p =>
    if hk : 3 ≤ p.anchor.active.card then
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      p.repairProgram (by omega) chores (draw (p.anchor.request (by omega) .repair))
    else .returned (.done p.anchor)
  | .done a => .returned (.done a)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
