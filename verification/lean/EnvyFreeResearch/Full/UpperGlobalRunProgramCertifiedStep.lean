import EnvyFreeResearch.Full.UpperGlobalRunProgramCertifiedBranches
import EnvyFreeResearch.Full.UpperGlobalProtocolMachineProjectionMeasurable

/-! The literal varying-population dispatcher is an ordinary Borel query
program. Finite conditioning only reads the recorded active-agent set. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.ProgramCertified
open MeasureTheory UpperGlobalPhysical UpperGlobalTape UpperCircularStage UpperStageMeasurable
  UpperGlobalNormalize ProgramMeasurable DispatchMeasurable
open scoped Classical
variable {n : ℕ}

theorem stepAtProgram_eq (fallback : Fin n) (chores : Bool)
    (phase : Phase n) (draw : Universal n) :
    stepAtProgram phase.anchor.active fallback chores phase draw = Phase.stepProgram fallback chores phase draw := by
  cases phase with
  | normalize a => rfl
  | done a => rfl
  | snapshot a =>
    change snapshotBranchProgram a.active chores a draw = Phase.stepProgram fallback chores (.snapshot a) draw
    by_cases hk : 3 ≤ a.active.card
    · letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [snapshotBranchProgram,Phase.stepProgram,dite_eq_left hk]
      apply snapshotAtProgram_eq
    · simp only [snapshotBranchProgram,Phase.stepProgram,dite_eq_right hk]
  | firstShrink p G =>
    change firstBranchProgram p.anchor.active chores p G draw = Phase.stepProgram fallback chores (.firstShrink p G) draw
    by_cases hk : 3 ≤ p.anchor.active.card
    · letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [firstBranchProgram,Phase.stepProgram,dite_eq_left hk]
      apply firstAtProgram_eq
    · simp only [firstBranchProgram,Phase.stepProgram,dite_eq_right hk]
  | secondShrink p =>
    change secondBranchProgram p.anchor.active chores p draw = Phase.stepProgram fallback chores (.secondShrink p) draw
    by_cases hk : 3 ≤ p.anchor.active.card
    · letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [secondBranchProgram,Phase.stepProgram,dite_eq_left hk]
      apply secondAtProgram_eq
    · simp only [secondBranchProgram,Phase.stepProgram,dite_eq_right hk]
  | finalRepair p =>
    change repairBranchProgram p.anchor.active chores p draw = Phase.stepProgram fallback chores (.finalRepair p) draw
    by_cases hk : 3 ≤ p.anchor.active.card
    · letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
      simp only [repairBranchProgram,Phase.stepProgram,dite_eq_left hk]
      apply repairAtProgram_eq
    · simp only [repairBranchProgram,Phase.stepProgram,dite_eq_right hk]

theorem stepProgram_certified (fallback : Fin n) (chores : Bool) :
    Certified (Function.uncurry (Phase.stepProgram fallback chores)) := by
  have h := finite_select_certified
    (fun z : Phase n × Universal n => z.1.anchor.active)
    (anchor_active_measurable.comp (phase_anchor_measurable.comp measurable_fst))
    (fun active z => stepAtProgram active fallback chores z.1 z.2)
    (fun active => stepAtProgram_certified active fallback chores)
  apply h.congr
  intro z
  exact stepAtProgram_eq fallback chores z.1 z.2

theorem stepProgram_family_certified {X : Type} [MeasurableSpace X]
    (fallback : Fin n) (chores : Bool) (phase : X → Phase n) (draw : X → Universal n)
    (hp : Measurable phase) (hd : Measurable draw) :
    Certified (fun x => Phase.stepProgram fallback chores (phase x) (draw x)) :=
  (stepProgram_certified fallback chores).comp (fun x => (phase x,draw x)) (hp.prodMk hd)

theorem stepProgram_next_measurable (fallback : Fin n) (chores : Bool) :
    Measurable (fun z : (Phase n × Universal n) × History n =>
      ((Phase.stepProgram fallback chores z.1.1 z.1.2).after z.2).action) :=
  (stepProgram_certified fallback chores).measurable_next
end EnvyFreeResearch.Full.UpperGlobalRun.ProgramCertified
