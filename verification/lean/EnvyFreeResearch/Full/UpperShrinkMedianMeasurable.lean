import EnvyFreeResearch.Full.UpperShrinkMedian
import EnvyFreeResearch.Full.UpperQueryProgramsMeasurable

noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrink
open UpperCorrectionExecution UpperRecordedDomain UpperGridRecords UpperQueryPrograms
  UpperQueryProgramsMeasurable ProtocolMeasurable ProgramMeasurable Chores.QueryProgram UpperCircularStage UpperStageMeasurable

variable {n : ℕ} {X : Type} [MeasurableSpace X]

theorem median_certified (state : X → State n) (cutter : X → Fin n)
    (hs : Measurable state) (hc : Measurable cutter) :
    Certified (fun x => medianProgram (state x) (cutter x)) := by
  have hsample := sample_certified (fun x => (state x).history) cutter
    (fun x => values (state x) (cutter x)) (fun x => total (state x) (cutter x))
    (fun x => (state x).cells) (fun _ => half)
    (state_history_measurable.comp hs) hc (values_measurable state cutter hs hc)
    (total_measurable state cutter hs hc) (state_cells_measurable.comp hs) measurable_const
  have hresult : Measurable (fun z : X × (ℝ × History n) =>
      (some z.2.1, (⟨refineEndpoints (state z.1).cells [z.2.1], z.2.2⟩ : State n))) := by
    apply (measurable_some.comp (measurable_fst.comp measurable_snd)).prodMk
    apply measurable_comap_iff.mpr
    apply (refineEndpoints_measurable _ _
      (state_cells_measurable.comp (hs.comp measurable_fst)) ?_).prodMk
      (measurable_snd.comp measurable_snd)
    exact measurable_list_singleton.comp (measurable_fst.comp measurable_snd)
  have hbranch := hsample.bind _ (Certified.returned _ hresult)
  have hzero : Measurable (fun x => decide (total (state x) (cutter x) ≤ 0)) :=
    UpperDomainDifference.decide_measurable _ (measurableSet_le (total_measurable state cutter hs hc) measurable_const)
  have h := Certified.branch _ hzero _ _
    (Certified.returned (fun x => (none, state x)) (measurable_const.prodMk hs)) hbranch
  apply h.congr
  intro x
  simp only [medianProgram, decide_eq_true_eq]

end EnvyFreeResearch.Full.UpperShrink
