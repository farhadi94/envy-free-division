import EnvyFreeResearch.Full.UpperShrinkCarveMeasurableProgram
import EnvyFreeResearch.Full.UpperDynamicExecutor

/-! Joint Borel output maps for actual median calls and their full-history
sequential composition. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperDomainDifference
  UpperSamplingRecords UpperStageMeasurable ProtocolMeasurable UpperDynamicExecutor
  UpperGridRecords UpperUnionSampling
variable {n k : ℕ} {X : Type} [MeasurableSpace X]

theorem median_execute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (state : X → State n) (cutter : X → Fin n) (hs : Measurable state) (hc : Measurable cutter) :
    Measurable (fun x => UpperShrink.median policy (state x) (cutter x)) := by
  have hr := sampleExecution_joint_measurable policy hmeas
    (fun x => (state x).history) cutter (fun x => values (state x) (cutter x))
    (fun x => total (state x) (cutter x)) (fun x => (state x).cells) (fun _ => UpperShrink.half)
    (state_history_measurable.comp hs) hc (values_measurable state cutter hs hc)
    (total_measurable state cutter hs hc) (state_cells_measurable.comp hs) measurable_const
  have hout : Measurable (fun x =>
      (some (sampleExecution policy (state x).history (cutter x) (values (state x) (cutter x))
        (total (state x) (cutter x)) (state x).cells UpperShrink.half).1,
      (⟨refineEndpoints (state x).cells [(sampleExecution policy (state x).history (cutter x)
        (values (state x) (cutter x)) (total (state x) (cutter x)) (state x).cells UpperShrink.half).1],
        (sampleExecution policy (state x).history (cutter x) (values (state x) (cutter x))
          (total (state x) (cutter x)) (state x).cells UpperShrink.half).2⟩ : State n))) := by
    apply (measurable_some.comp (measurable_fst.comp hr)).prodMk
    apply measurable_comap_iff.mpr
    exact (refineEndpoints_measurable _ _ (state_cells_measurable.comp hs)
      (measurable_list_singleton.comp (measurable_fst.comp hr))).prodMk (measurable_snd.comp hr)
  exact (measurable_const.prodMk hs).ite
    (measurableSet_le (total_measurable state cutter hs hc) measurable_const) hout

theorem medianChainExecute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (cutters : List (Fin n)) : ∀ (state : X → State n), Measurable state →
      Measurable (fun x => medianChainExecute policy cutters (state x)) := by
  induction cutters with
  | nil => intro state hs; exact hs
  | cons i rest ih =>
    intro state hs
    exact ih _ (measurable_snd.comp (median_execute_measurable policy hmeas state
      (fun _ => i) hs measurable_const))

end EnvyFreeResearch.Full.UpperShrinkCarve
