import EnvyFreeResearch.Full.UpperBaseCasesProtocol
import EnvyFreeResearch.Full.UpperRecordedGridProgramMeasurable
import EnvyFreeResearch.Full.UpperSnapshotSmallMeasurable

/-! Borel cached choice and the actual two-agent protocol's certified next
queries, including every original-observer endpoint record. -/
noncomputable section
open Set MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperBaseCases
open UpperRecordedDomain UpperCorrectionExecution UpperDomainDifference UpperComponentAssembly
open UpperCircularStage UpperQueryPrograms UpperQueryProgramsMeasurable UpperGridRecords
open Chores.QueryProgram ProgramMeasurable UpperProgramIterationMeasurable
variable {n : ℕ} {X : Type} [MeasurableSpace X]

theorem leftState_measurable (state : X → State n) (point : X → ℝ)
    (hs : Measurable state) (hp : Measurable point) :
    Measurable (fun x => leftState (state x) (point x)) := by
  apply UpperSnapshotSmall.selectState_measurable state _ hs
  exact decide_measurable _ (measurableSet_le
    (component_right_measurable.comp measurable_snd) (hp.comp measurable_fst))

theorem rightState_measurable (state : X → State n) (point : X → ℝ)
    (hs : Measurable state) (hp : Measurable point) :
    Measurable (fun x => rightState (state x) (point x)) := by
  apply UpperSnapshotSmall.selectState_measurable state _ hs
  exact (measurable_of_countable Bool.not).comp (decide_measurable _ (measurableSet_le
    (component_right_measurable.comp measurable_snd) (hp.comp measurable_fst)))

theorem choice_measurable (chores : Bool) (left right : X → State n)
    (hl : Measurable left) (hr : Measurable right) (cutter chooser j : Fin n) :
    Measurable (fun x => choice chores (left x) (right x) cutter chooser j) := by
  have hc : MeasurableSet {x | chooseLeft chores (left x) (right x) chooser} := by
    cases chores
    · exact measurableSet_le (total_measurable right (fun _ => chooser) hr measurable_const)
        (total_measurable left (fun _ => chooser) hl measurable_const)
    · exact measurableSet_le (total_measurable left (fun _ => chooser) hl measurable_const)
        (total_measurable right (fun _ => chooser) hr measurable_const)
  unfold choice
  by_cases hj : j=cutter
  · simp only [hj,ite_true]
    exact hr.ite hc hl
  · simp only [hj,ite_false]
    by_cases hj' : j=chooser
    · simp only [hj',ite_true]
      exact hl.ite hc hr
    · simp only [hj',ite_false]
      exact empty_measurable _ (state_history_measurable.comp hl)

theorem finish_measurable (chores : Bool) (cutter chooser : Fin n)
    (out : X → (Fin 1 → ℝ) × State n) (hout : Measurable out) :
    Measurable (fun x => finish chores cutter chooser (out x)) := by
  apply Measurable.of_eval
  intro j
  have hs := measurable_snd.comp hout
  have hp := (measurable_pi_apply (0 : Fin 1)).comp (measurable_fst.comp hout)
  exact choice_measurable chores _ _ (leftState_measurable _ _ hs hp)
    (rightState_measurable _ _ hs hp) cutter chooser j

theorem half_certified (origin : X → State n) (horigin : Measurable origin) (cutter : Fin n) :
    Certified (fun x => halfProgram (origin x) cutter) := by
  let step := fun (state : State n) (history : History n) (d : Unit × I) =>
    sample history cutter (values state cutter) (total state cutter) state.cells d.2
  have hstep : Certified (fun z : State n × History n × (Unit × I) => step z.1 z.2.1 z.2.2) :=
    sample_certified _ _ _ _ _ _ (measurable_fst.comp measurable_snd) measurable_const
      (values_measurable _ _ measurable_fst measurable_const)
      (total_measurable _ _ measurable_fst measurable_const)
      (state_cells_measurable.comp measurable_fst)
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hrun := runProgram_family_certified step hstep 1 origin (fun x => (origin x).history)
    (fun _ _ => ((),half)) horigin (state_history_measurable.comp horigin) (fun _ => measurable_const)
  have hresult : Measurable (fun z : X × ((Fin 1 → ℝ) × History n) =>
      (z.2.1, (⟨refineEndpoints (origin z.1).cells (List.ofFn z.2.1), z.2.2⟩ : State n))) := by
    apply (measurable_fst.comp measurable_snd).prodMk
    apply measurable_comap_iff.mpr
    exact (refineEndpoints_measurable _ _ (state_cells_measurable.comp (horigin.comp measurable_fst))
      ((UpperRecordedGrid.ofFn_measurable 1).comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  exact hrun.bind _ (Certified.returned _ hresult)

theorem cutAndChoose_certified (chores : Bool) (origin : X → State n)
    (horigin : Measurable origin) (cutter chooser : Fin n) :
    Certified (fun x => cutAndChooseProgram chores (origin x) cutter chooser) :=
  (half_certified origin horigin cutter).bind _
    (Certified.returned _ (finish_measurable chores cutter chooser _ measurable_snd))

end EnvyFreeResearch.Full.UpperBaseCases
