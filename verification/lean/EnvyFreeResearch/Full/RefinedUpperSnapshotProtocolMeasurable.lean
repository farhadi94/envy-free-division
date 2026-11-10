import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolRepair

/-! The fresh Repair and cached margin check are one jointly measurable
ordinary-query protocol, including all rejected and unreachable histories. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperQueryPrograms Chores.QueryProgram ProgramMeasurable
variable {n k : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem program_certified (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : X → State n) (old : X → Fin k → State n) (p : X → RefinedUpperRepair.Tape n k)
    (ho : Measurable origin) (ha : Measurable old) (hp : Measurable p) :
    Certified (fun x => program hk chores active gamma (origin x) (old x) (p x)) := by
  have hbase := RefinedUpperRepair.program_certified hk chores active origin old p ho
    (fun j => (measurable_pi_apply j).comp ha) hp
  exact hbase.bind (fun z => .returned (finish (by omega) chores active gamma (origin z.1) (old z.1) z.2))
    (Certified.returned _ (finish_measurable (by omega) chores active gamma
      (fun z : X × PhysicalResult n k => origin z.1) (fun z => old z.1) Prod.snd
      (ho.comp measurable_fst) (ha.comp measurable_fst) measurable_snd))

theorem measurable_next (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) :
    Measurable (fun z : RefinedUpperRepair.Tape n k × History n =>
      ((program hk chores active gamma origin old z.1).after z.2).action) :=
  (program_certified hk chores active gamma (fun _ => origin) (fun _ => old) id
    measurable_const measurable_const measurable_id).measurable_next

theorem execute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : X → State n) (old : X → Fin k → State n) (p : X → RefinedUpperRepair.Tape n k)
    (ho : Measurable origin) (ha : Measurable old) (hp : Measurable p) :
    Measurable (fun x => execute policy hk chores active gamma (origin x) (old x) (p x)) := by
  have hr := RefinedUpperRepair.execute_measurable policy hmeas hk chores active origin old p ho
    (fun j => (measurable_pi_apply j).comp ha) hp
  exact finish_measurable (by omega) chores active gamma origin old _ ho ha hr
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
