import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolShrinkAction
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionData

/-! Actual first- and second-Shrink phase transitions. The finite cached
selector is applied only after an accepted call. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCorrectionExecution UpperCircularStage UpperQueryPrograms UpperZeroRows Chores.QueryProgram
variable {n : ℕ}

def Pending.finishFirstShrink (p : Pending n) (chores : Bool) (G : ℝ)
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card) : Phase n :=
  let next := p.finishShrink result
  if result.2.2 then .firstShrink next G
  else match next.selectTransfer (if chores then .chore else .cake) with
    | some candidate => next.dispatchTransfer candidate
    | none => .firstShrink next G

def Pending.finishSecondShrink (p : Pending n)
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card) : Phase n :=
  let next := p.finishShrink result
  if result.2.2 then .secondShrink next else .finalRepair next

def Pending.firstShrinkProgram (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) : QProgram n (Phase n) :=
  (RefinedUpperShrink.program hk chores (enumerate p.anchor.active) p.buffer G tape).bind
    (fun result => .returned (p.finishFirstShrink chores G result))

def Pending.secondShrinkProgram (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) : QProgram n (Phase n) :=
  (RefinedUpperShrink.program hk chores (enumerate p.anchor.active) p.buffer (2/RefinedUpperRepair.nearError n) tape).bind
    (fun result => .returned (p.finishSecondShrink result))

def Pending.firstShrinkAttempt (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) : Phase n :=
  p.finishFirstShrink chores G (p.shrinkResult policy hk chores G tape)

def Pending.secondShrinkAttempt (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) : Phase n :=
  p.finishSecondShrink (p.shrinkResult policy hk chores (2/RefinedUpperRepair.nearError n) tape)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
