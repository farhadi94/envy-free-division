import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableBranches
import EnvyFreeResearch.Full.UpperGlobalProtocolMachineProjectionMeasurable

/-! Joint Borel measurability of the actual global physical state transition,
including changing active populations and all rejected-query histories. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
open MeasureTheory UpperGlobalPhysical UpperGlobalTape UpperCircularStage UpperStageMeasurable
open UpperGlobalNormalize
open scoped Classical
variable {n : ℕ}

theorem stepAt_eq (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (phase : Phase n) (draw : Universal n) :
    stepAt phase.anchor.active policy fallback chores phase draw = Phase.step policy fallback chores phase draw := by
  cases phase with
  | normalize a => rfl
  | done a => rfl
  | snapshot a =>
    change snapshotBranch a.active policy chores a draw = Phase.step policy fallback chores (.snapshot a) draw
    by_cases hk : 3 ≤ a.active.card
    · letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [snapshotBranch,Phase.step,dite_eq_left hk]
      apply snapshotAt_eq
    · simp only [snapshotBranch,Phase.step,dite_eq_right hk]
  | firstShrink p G =>
    change firstBranch p.anchor.active policy chores p G draw = Phase.step policy fallback chores (.firstShrink p G) draw
    by_cases hk : 3 ≤ p.anchor.active.card
    · letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [firstBranch,Phase.step,dite_eq_left hk]
      apply firstShrinkAt_eq
    · simp only [firstBranch,Phase.step,dite_eq_right hk]
  | secondShrink p =>
    change secondBranch p.anchor.active policy chores p draw = Phase.step policy fallback chores (.secondShrink p) draw
    by_cases hk : 3 ≤ p.anchor.active.card
    · letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [secondBranch,Phase.step,dite_eq_left hk]
      apply secondShrinkAt_eq
    · simp only [secondBranch,Phase.step,dite_eq_right hk]
  | finalRepair p =>
    change repairBranch p.anchor.active policy chores p draw = Phase.step policy fallback chores (.finalRepair p) draw
    by_cases hk : 3 ≤ p.anchor.active.card
    · letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [repairBranch,Phase.step,dite_eq_left hk]
      apply repairAt_eq
    · simp only [repairBranch,Phase.step,dite_eq_right hk]

theorem step_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) :
    Measurable (Function.uncurry (Phase.step policy fallback chores)) := by
  have h := finite_select_measurable
    (fun z : Phase n × Universal n => z.1.anchor.active)
    (anchor_active_measurable.comp (phase_anchor_measurable.comp measurable_fst))
    (fun active z => stepAt active policy fallback chores z.1 z.2)
    (fun active => stepAt_measurable active policy hpolicy fallback chores)
  convert h using 1
  funext z
  exact (stepAt_eq policy fallback chores z.1 z.2).symm

end EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
