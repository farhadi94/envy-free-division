import EnvyFreeResearch.Full.UpperGlobalRunBudgetHandlers
import EnvyFreeResearch.Full.UpperGlobalProtocolEvents

/-! Indicators of accepted calls and normalization tokens on the actual
machine stream. A normalization is created only by an accepted final Repair. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalRunBudget
open UpperGlobalPhysical UpperCircularStage UpperGlobalTape
variable {n : ℕ}

def successIndicator (policy : Policy n) (chores : Bool) (kind : Kind)
    (phase : Phase n) (draw : Universal n) : ℕ :=
  if phase.paidKind=some kind ∧ Phase.accepted policy chores phase draw=true then 1 else 0

def normalizeToken : Phase n → ℕ
  | .normalize _ => 1
  | _ => 0

theorem snapshot_normalizeToken (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0<a.active.card) (chores : Bool)
    (result : UpperRepairProgram.PhysicalResult n a.active.card) :
    normalizeToken (a.finishSnapshot hk chores result)=0 := by
  unfold Anchor.finishSnapshot
  split
  · rfl
  · split <;> rfl

theorem first_normalizeToken (p : Pending n) (chores : Bool) (G : ℝ)
    (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    normalizeToken (p.finishFirstShrink chores G result)=0 := by
  cases hr : result.2.2 with
  | true => simp only [Pending.finishFirstShrink,hr,ite_true,normalizeToken]
  | false =>
    simp only [Pending.finishFirstShrink,hr,Bool.false_eq_true,ite_false]
    cases hs : (p.finishShrink result).selectTransfer (if chores then .chore else .cake) with
    | none => simp only [hs,normalizeToken]
    | some c => simp only [hs]; cases c <;> rfl

theorem second_normalizeToken (p : Pending n)
    (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    normalizeToken (p.finishSecondShrink result)=0 := by
  unfold Pending.finishSecondShrink
  split <;> rfl

theorem normalize_next_token (policy : Policy n) (fallback : Fin n) (chores : Bool) (a : Anchor n) :
    normalizeToken (UpperGlobalNormalize.execute policy fallback chores a)=0 := by
  unfold UpperGlobalNormalize.execute
  generalize UpperGlobalNormalize.normalize fallback chores n a=request
  cases request <;> rfl

theorem step_normalizeToken (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (phase : Phase n) (draw : Universal n) :
    normalizeToken (Phase.step policy fallback chores phase draw)=
      successIndicator policy chores .repair phase draw := by
  cases phase with
  | normalize a =>
    exact normalize_next_token policy fallback chores a
  | done a => rfl
  | snapshot a =>
    simp only [Phase.step,successIndicator,Phase.paidKind,Option.some.injEq,reduceCtorEq,
      false_and,ite_false]
    split
    · rename_i hk
      letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
      exact snapshot_normalizeToken _ _ _ _
    · rfl
  | firstShrink p G =>
    simp only [Phase.step,successIndicator,Phase.paidKind,Option.some.injEq,reduceCtorEq,
      false_and,ite_false]
    split
    · exact first_normalizeToken _ _ _ _
    · rfl
  | secondShrink p =>
    simp only [Phase.step,successIndicator,Phase.paidKind,Option.some.injEq,reduceCtorEq,
      false_and,ite_false]
    split
    · exact second_normalizeToken _ _
    · rfl
  | finalRepair p =>
    simp only [Phase.step,successIndicator,Phase.paidKind,true_and,Phase.accepted]
    split
    · rename_i hk
      letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [dif_pos hk,Pending.repairAttempt,Pending.finishRepair]
      cases hr : (p.repairResult policy (by omega) chores
        (draw (p.anchor.request (by omega) .repair))).2.2 <;>
        simp [hr,normalizeToken]
    · rename_i hk
      simp [dif_neg hk,normalizeToken]

end EnvyFreeResearch.Full.UpperGlobalRunBudget
