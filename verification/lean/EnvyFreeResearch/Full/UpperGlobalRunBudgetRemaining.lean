import EnvyFreeResearch.Full.UpperGlobalRunBudgetStep
import EnvyFreeResearch.Full.UpperGlobalProtocolFirstValidityShape

/-! The actual accepted-call graph is acyclic within an iteration: at most
first Shrink, second Shrink, and final Repair follow an accepted Snapshot. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalRunBudget
open UpperGlobalPhysical UpperCircularStage UpperGlobalTape
variable {n : ℕ}

theorem normalize_remaining (policy : Policy n) (fallback : Fin n) (chores : Bool) (a : Anchor n) :
    remainingCalls (UpperGlobalNormalize.execute policy fallback chores a)=0 := by
  unfold UpperGlobalNormalize.execute
  generalize UpperGlobalNormalize.normalize fallback chores n a=request
  cases request <;> rfl

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
  (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy) (fallback : Fin n)
include hp

theorem step_remaining_calls (phase : Phase n) (hv : phase.Valid μ chores whole) (draw : Universal n) :
    successIndicator policy chores .shrink phase draw + successIndicator policy chores .repair phase draw +
      remainingCalls (Phase.step policy fallback chores phase draw) ≤
      3*successIndicator policy chores .snapshot phase draw + remainingCalls phase := by
  cases phase with
  | normalize a =>
    change 0+0+remainingCalls (UpperGlobalNormalize.execute policy fallback chores a) ≤ 3*0+0
    rw [normalize_remaining]
  | done a => exact le_rfl
  | snapshot a =>
    have hk : 3≤a.active.card := hv.2.2.1
    letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
    simpa only [Phase.step,dite_eq_left hk,successIndicator,Phase.paidKind,Phase.accepted,
      Option.some.injEq,reduceCtorEq,false_and,ite_false,true_and,complement_indicator,
      Nat.zero_add,Nat.add_zero,remainingCalls,Anchor.snapshotAttempt] using
      snapshot_handler_remaining a (by omega) chores
        (a.snapshotResult policy hk chores (draw (a.request (by omega) .snapshot)))
  | firstShrink p G =>
    have hk : 3≤p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simp only [Phase.step,dite_eq_left hk,successIndicator,Phase.paidKind,Phase.accepted,
      Option.some.injEq,reduceCtorEq,false_and,ite_false,true_and,complement_indicator,
      Nat.zero_add,Nat.add_zero,Nat.mul_zero,remainingCalls]
    cases hr : (p.shrinkResult policy (by omega) chores G (draw (p.anchor.request (by omega) .shrink))).2.2 with
    | true =>
      simp only [acceptedBit,ite_true,Pending.firstShrinkAttempt,Pending.finishFirstShrink,
        hr,remainingCalls,Nat.zero_add,le_refl]
    | false =>
      obtain ⟨q,_,he | he⟩ := firstShrinkAttempt_accepted_shape μ whole chores p G hv policy hp
        (draw (p.anchor.request (by omega) .shrink)) hr
      · rw [he]; norm_num [acceptedBit,remainingCalls]
      · rw [he]; norm_num [acceptedBit,remainingCalls]
  | secondShrink p =>
    have hk : 3≤p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simp only [Phase.step,dite_eq_left hk,successIndicator,Phase.paidKind,Phase.accepted,
      Option.some.injEq,reduceCtorEq,false_and,ite_false,true_and,complement_indicator,
      Nat.zero_add,Nat.add_zero,Nat.mul_zero,remainingCalls,Pending.secondShrinkAttempt,
      Pending.finishSecondShrink]
    cases hr : (p.shrinkResult policy (by omega) chores (2/UpperRepair.nearError n)
      (draw (p.anchor.request (by omega) .shrink))).2.2 <;> norm_num [hr,acceptedBit,remainingCalls]
  | finalRepair p =>
    have hk : 3≤p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simp only [Phase.step,dite_eq_left hk,successIndicator,Phase.paidKind,Phase.accepted,
      Option.some.injEq,reduceCtorEq,false_and,ite_false,true_and,complement_indicator,
      Nat.zero_add,Nat.add_zero,Nat.mul_zero,remainingCalls,Pending.repairAttempt,Pending.finishRepair]
    cases hr : (p.repairResult policy (by omega) chores (draw (p.anchor.request (by omega) .repair))).2.2 <;>
      norm_num [hr,acceptedBit,remainingCalls]

end EnvyFreeResearch.Full.UpperGlobalRunBudget
