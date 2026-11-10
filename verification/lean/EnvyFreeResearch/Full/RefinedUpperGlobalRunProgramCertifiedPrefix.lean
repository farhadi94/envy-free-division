import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunProgramCertifiedStep
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolUnitRun

/-! Every actual finite global prefix has Borel next-action control,
including the paid unit-interval entry and all failed local attempts. -/
noncomputable section
open MeasureTheory
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.ProgramCertified
open RefinedUpperGlobalPhysical RefinedUpperGlobalTape UpperCircularStage UpperQueryPrograms
  Chores.QueryProgram ProgramMeasurable DispatchMeasurable
variable {n : ℕ} {X : Type} [MeasurableSpace X]

theorem prefixProgram_certified (fallback : Fin n) (chores : Bool)
    (initial : X → Phase n) (omega : X → Stream (Universal n))
    (hi : Measurable initial) (ho : Measurable omega) (t : ℕ) :
    Certified (fun x => prefixProgram fallback chores (initial x) (omega x) t) := by
  induction t with
  | zero => exact Certified.returned _ hi
  | succ t ih =>
    have hnext := stepProgram_family_certified fallback chores
      (fun z : X × Phase n => z.2) (fun z => omega z.1 t) measurable_snd
      (((measurable_pi_apply t).comp ho).comp measurable_fst)
    exact ih.bind _ hnext

theorem prefixProgram_next_measurable (fallback : Fin n) (chores : Bool)
    (initial : X → Phase n) (omega : X → Stream (Universal n))
    (hi : Measurable initial) (ho : Measurable omega) (t : ℕ) :
    Measurable (fun z : X × History n =>
      ((prefixProgram fallback chores (initial z.1) (omega z.1) t).after z.2).action) :=
  (prefixProgram_certified fallback chores initial omega hi ho t).measurable_next

theorem unitPrefixProgram_certified (fallback : Fin n) (chores : Bool)
    (omega : X → Stream (Universal n)) (ho : Measurable omega) (t : ℕ) :
    Certified (fun x => unitPrefixProgram fallback chores (omega x) t) := by
  have hboot := (RefinedUpperGlobalUnit.program_certified (n:=n)).comp (fun _ : X => ()) measurable_const
  have hnext := prefixProgram_certified fallback chores
    (fun z : X × Anchor n => Phase.normalize z.2) (fun z => omega z.1)
    (phase_normalize_measurable.comp measurable_snd) (ho.comp measurable_fst) t
  exact hboot.bind _ hnext

theorem unitPrefixProgram_next_measurable (fallback : Fin n) (chores : Bool)
    (omega : X → Stream (Universal n)) (ho : Measurable omega) (t : ℕ) :
    Measurable (fun z : X × History n =>
      ((unitPrefixProgram fallback chores (omega z.1) t).after z.2).action) :=
  (unitPrefixProgram_certified fallback chores omega ho t).measurable_next
end EnvyFreeResearch.Full.RefinedUpperGlobalRun.ProgramCertified
