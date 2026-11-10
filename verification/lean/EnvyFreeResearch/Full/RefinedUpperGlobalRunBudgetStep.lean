import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunBudgetEvents
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizePotential
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolCorrectness

/-! Every actual step increases the credited saved potential by its accepted
Snapshot indicator. All local invariants come from the concrete dispatcher. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
open RefinedUpperGlobalPhysical UpperCircularStage RefinedUpperGlobalTape GlobalCompletion
variable {n : ℕ}

theorem complement_indicator (b : Bool) : (if (!b)=true then 1 else 0 : ℕ)=acceptedBit b := by
  cases b <;> rfl

theorem normalize_credit (policy : Policy n) (fallback : Fin n) (chores : Bool) (a : Anchor n) :
    credit chores (RefinedUpperGlobalNormalize.execute policy fallback chores a)=
      (RefinedUpperGlobalNormalize.execute policy fallback chores a).anchor.cachedPotential
        (if chores then .chore else .cake) := by
  unfold RefinedUpperGlobalNormalize.execute
  generalize RefinedUpperGlobalNormalize.normalize fallback chores n a=request
  cases request <;> rfl

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
  (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy) (fallback : Fin n)
include hp

theorem step_credit (phase : Phase n) (hv : phase.Valid μ chores whole) (draw : Universal n) :
    credit chores phase+successIndicator policy chores .snapshot phase draw ≤
      credit chores (Phase.step policy fallback chores phase draw) := by
  cases phase with
  | normalize a =>
    change a.cachedPotential _+0 ≤ credit chores (RefinedUpperGlobalNormalize.execute policy fallback chores a)
    rw [Nat.add_zero,normalize_credit]
    exact RefinedUpperGlobalNormalize.execute_potential μ policy hp fallback chores whole a hv.1 hv.2.1 hv.2.2
  | done a => exact le_rfl
  | snapshot a =>
    have hk : 3≤a.active.card := hv.2.2.1
    letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
    have hvnext := snapshotAttempt_valid μ a policy hp hk chores whole hv
      (draw (a.request (by omega) .snapshot))
    have hb := snapshot_handler_credit μ whole a (by omega) chores
      (a.snapshotResult policy hk chores (draw (a.request (by omega) .snapshot))) hv hvnext
    simpa only [Phase.step,dite_eq_left hk,successIndicator,Phase.paidKind,Phase.accepted,
      true_and,complement_indicator,Anchor.snapshotAttempt] using hb
  | firstShrink p G =>
    have hk : 3≤p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simp only [Phase.step,dite_eq_left hk,successIndicator,Phase.paidKind,Option.some.injEq,
      reduceCtorEq,false_and,ite_false,Nat.add_zero,Pending.firstShrinkAttempt]
    rw [first_handler_credit]
  | secondShrink p =>
    have hk : 3≤p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simp only [Phase.step,dite_eq_left hk,successIndicator,Phase.paidKind,Option.some.injEq,
      reduceCtorEq,false_and,ite_false,Nat.add_zero,Pending.secondShrinkAttempt]
    rw [second_handler_credit]
  | finalRepair p =>
    have hk : 3≤p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simp only [Phase.step,dite_eq_left hk,successIndicator,Phase.paidKind,Option.some.injEq,
      reduceCtorEq,false_and,ite_false,Nat.add_zero]
    cases hr : (p.repairResult policy (by omega) chores (draw (p.anchor.request (by omega) .repair))).2.2 with
    | true =>
      simp only [Pending.repairAttempt,Pending.finishRepair,hr,ite_true,credit,pendingCredit,
        Phase.anchor,Pending.refresh,le_refl]
    | false =>
      have hprog := (repairAttempt_valid_progress μ whole p chores hv policy hp (by omega)
        (draw (p.anchor.request (by omega) .repair))).2 hr
      simpa only [Pending.repairAttempt,Pending.finishRepair,hr,Bool.false_eq_true,ite_false,
        credit,pendingCredit,Phase.anchor,Nat.add_zero] using hprog

end EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
