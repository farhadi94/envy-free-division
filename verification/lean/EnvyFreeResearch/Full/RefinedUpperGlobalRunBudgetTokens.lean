import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunBudgetEvents

/-! One in-flight token is created by an accepted Snapshot and spent by an
accepted final Repair. This bounds normalization overhead independently of time. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
open RefinedUpperGlobalPhysical UpperCircularStage RefinedUpperGlobalTape
variable {n : ℕ}

theorem snapshot_pendingCredit (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0<a.active.card) (chores : Bool)
    (result : RefinedUpperRepairProgram.PhysicalResult n a.active.card) :
    pendingCredit (a.finishSnapshot hk chores result) ≤ acceptedBit result.2.2 := by
  unfold Anchor.finishSnapshot
  split
  · rename_i hr; simp [pendingCredit,acceptedBit,hr]
  · rename_i hr; split <;> simp [pendingCredit,acceptedBit,hr]

theorem first_pendingCredit (p : Pending n) (chores : Bool) (G : ℝ)
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    pendingCredit (p.finishFirstShrink chores G result)=1 := by
  cases hr : result.2.2 with
  | true => simp only [Pending.finishFirstShrink,hr,ite_true,pendingCredit]
  | false =>
    simp only [Pending.finishFirstShrink,hr,Bool.false_eq_true,ite_false]
    cases hs : (p.finishShrink result).selectTransfer (if chores then .chore else .cake) with
    | none => rfl
    | some c => cases c <;> rfl

theorem second_pendingCredit (p : Pending n)
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    pendingCredit (p.finishSecondShrink result)=1 := by
  unfold Pending.finishSecondShrink
  split <;> rfl

theorem normalize_pendingCredit (policy : Policy n) (fallback : Fin n) (chores : Bool) (a : Anchor n) :
    pendingCredit (RefinedUpperGlobalNormalize.execute policy fallback chores a)=0 := by
  unfold RefinedUpperGlobalNormalize.execute
  generalize RefinedUpperGlobalNormalize.normalize fallback chores n a=request
  cases request <;> rfl

theorem step_pending_balance (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (phase : Phase n) (draw : Universal n) :
    successIndicator policy chores .repair phase draw +
      pendingCredit (Phase.step policy fallback chores phase draw) ≤
      successIndicator policy chores .snapshot phase draw + pendingCredit phase := by
  cases phase with
  | normalize a =>
    change 0+pendingCredit (RefinedUpperGlobalNormalize.execute policy fallback chores a) ≤ 0+0
    rw [normalize_pendingCredit]
  | done a => exact le_rfl
  | snapshot a =>
    simp only [Phase.step,successIndicator,Phase.paidKind,Phase.accepted,Option.some.injEq,
      reduceCtorEq,false_and,ite_false,true_and,pendingCredit,Nat.zero_add,Nat.add_zero]
    by_cases hk : 3≤a.active.card
    · letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [dite_eq_left hk]
      have h := snapshot_pendingCredit a (by omega) chores
        (a.snapshotResult policy hk chores (draw (a.request (by omega) .snapshot)))
      cases hr : (a.snapshotResult policy hk chores (draw (a.request (by omega) .snapshot))).2.2 <;>
        simpa only [Anchor.snapshotAttempt,hr,acceptedBit,Bool.not_false,Bool.not_true,
          Bool.false_eq_true,ite_true,ite_false,pendingCredit] using h
    · simp [dite_eq_right hk,pendingCredit]
  | firstShrink p G =>
    simp only [Phase.step,successIndicator,Phase.paidKind,Option.some.injEq,
      reduceCtorEq,false_and,ite_false,pendingCredit,Nat.zero_add]
    split <;> omega
  | secondShrink p =>
    simp only [Phase.step,successIndicator,Phase.paidKind,Option.some.injEq,
      reduceCtorEq,false_and,ite_false,pendingCredit,Nat.zero_add]
    split <;> omega
  | finalRepair p =>
    simp only [Phase.step,successIndicator,Phase.paidKind,Phase.accepted,Option.some.injEq,
      reduceCtorEq,false_and,ite_false,true_and,pendingCredit,Nat.zero_add]
    by_cases hk : 3≤p.anchor.active.card
    · letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [dite_eq_left hk,Pending.repairAttempt,Pending.finishRepair]
      cases hr : (p.repairResult policy (by omega) chores (draw (p.anchor.request (by omega) .repair))).2.2 <;>
        norm_num [hr,pendingCredit]
    · simp [dite_eq_right hk,pendingCredit]

end EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
