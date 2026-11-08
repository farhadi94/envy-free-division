import EnvyFreeResearch.Full.UpperRecordedGridProgramMeasurable
import EnvyFreeResearch.Full.UpperSnapshotSmallProgram
import EnvyFreeResearch.Full.UpperSnapshotSmallMeasurable

/-! Borel next-action certificate for the actual shared-circle program,
including the complete ordinary-query history on unreachable transcripts. -/
noncomputable section
open MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open Chores.QueryProgram ProgramMeasurable UpperCircularStage
  UpperQueryPrograms UpperQueryProgramsMeasurable UpperRecordedDomain UpperDomainDifference
  UpperCorrectionExecution UpperProgramIterationMeasurable UpperRecordedGridProgram UpperGridRecords
  UpperStageMeasurable
variable {n J : ℕ} {X : Type} [MeasurableSpace X]
theorem unit_grid_certified (active : Unit → Fin n) (origin : X → State n)
    (m : ℕ) (draw : X → Fin m → Unit × I)
    (horigin : Measurable origin) (hdraw : ∀ i, Measurable (fun x => draw x i)) :
    Certified (fun x => grid active (origin x) m (draw x)) := by
  let step := fun (origin : State n) (history : History n) (d : Unit × I) =>
    sample history (active d.1) (values origin (active d.1)) (total origin (active d.1)) origin.cells d.2
  have hstep : Certified (fun z : State n × History n × (Unit × I) => step z.1 z.2.1 z.2.2) := by
    have hcutter : Measurable (fun z : State n × History n × (Unit × I) => active z.2.2.1) :=
      (measurable_of_countable active).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
    exact sample_certified _ _ _ _ _ _ (measurable_fst.comp measurable_snd) hcutter
      (values_measurable _ _ measurable_fst hcutter) (total_measurable _ _ measurable_fst hcutter)
      (state_cells_measurable.comp measurable_fst) (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hrun := runProgram_family_certified step hstep m origin (fun x => (origin x).history) draw
    horigin (state_history_measurable.comp horigin) hdraw
  have hresult : Measurable (fun z : X × ((Fin m → ℝ) × History n) =>
      (z.2.1, (⟨refineEndpoints (origin z.1).cells (List.ofFn z.2.1), z.2.2⟩ : State n))) := by
    apply (measurable_fst.comp measurable_snd).prodMk
    apply measurable_comap_iff.mpr
    exact (refineEndpoints_measurable _ _ (state_cells_measurable.comp (horigin.comp measurable_fst))
      ((UpperRecordedGrid.ofFn_measurable m).comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  exact hrun.bind _ (Certified.returned _ hresult)

theorem circle_program_certified (cutter : Fin n) (origin : X → State n)
    (shift : X → Fin J → Circle) (start : X → Circle)
    (ho : Measurable origin) (hs : ∀ j, Measurable (fun x => shift x j)) (ht : Measurable start) :
    Certified (fun x => circleProgram (origin x) cutter (shift x) (start x)) :=
  unit_grid_certified (fun _ => cutter) origin J _ ho
    (fun j => (measurable_pi_apply j).comp (endpointTape_measurable shift start hs ht))
end EnvyFreeResearch.Full.UpperSnapshotSmall
