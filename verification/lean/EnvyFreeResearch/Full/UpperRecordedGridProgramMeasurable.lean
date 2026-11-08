import EnvyFreeResearch.Full.UpperQueryProgramsMeasurable
import EnvyFreeResearch.Full.UpperProgramIterationMeasurable
import EnvyFreeResearch.Full.UpperRecordedGridProgram

/-! The original coarse/fine sampling program has a Borel next action.
The full history remains an observable real-coded list throughout. -/

noncomputable section

open MeasureTheory
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRecordedGridProgramMeasurable

open Chores.QueryProgram ProgramMeasurable ProtocolMeasurable UpperCircularStage
  UpperQueryPrograms UpperQueryProgramsMeasurable UpperRecordedDomain UpperDomainDifference
  UpperCorrectionExecution UpperProgramIterationMeasurable UpperRecordedGridProgram UpperGridRecords

variable {n k : ℕ} {X : Type} [MeasurableSpace X]

theorem grid_certified (active : Fin k → Fin n) (origin : X → State n)
    (m : ℕ) (draw : X → Fin m → Fin k × I)
    (horigin : Measurable origin) (hdraw : ∀ i, Measurable (fun x => draw x i)) :
    Certified (fun x => grid active (origin x) m (draw x)) := by
  let step := fun (origin : State n) (history : History n) (d : Fin k × I) =>
    sample history (active d.1) (values origin (active d.1)) (total origin (active d.1)) origin.cells d.2
  have hstep : Certified (fun z : State n × History n × (Fin k × I) => step z.1 z.2.1 z.2.2) := by
    have hcutter : Measurable (fun z : State n × History n × (Fin k × I) => active z.2.2.1) :=
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

theorem quantiles_certified (active : Fin k → Fin n) (origin : X → State n) (q : ℕ)
    (horigin : Measurable origin) : Certified (fun x => quantiles active (origin x) q) :=
  grid_certified active origin _ _ horigin (fun _ => measurable_const)

theorem prepare_certified (active : Fin k → Fin n) (origin : X → State n)
    (q m : ℕ) (draw : X → Fin m → Fin k × I)
    (horigin : Measurable origin) (hdraw : ∀ i, Measurable (fun x => draw x i)) :
    Certified (fun x => prepare active (origin x) q m (draw x)) := by
  have hcoarse := quantiles_certified active origin q horigin
  let Coarse := (Fin (UpperRecordedQuantiles.count (Agent := Fin k) q) → ℝ) × State n
  have hfine : Certified (fun z : X × Coarse => grid active z.2.2 m (draw z.1)) :=
    grid_certified active _ m _ (measurable_snd.comp measurable_snd)
      (fun i => (hdraw i).comp measurable_fst)
  have htail := hfine.bind (fun z => Program.returned (z.1.2.1, z.2))
    (Certified.returned _ ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
  exact hcoarse.bind _ htail

theorem boot_certified : Certified (fun _ : Unit => (boot : QProgram n (State n))) := by
  have hqueries : Certified (fun _ : Unit => queries [] (UpperInitialState.queries n)) :=
    queries_certified _ _ measurable_const measurable_const
  apply hqueries.bind
    (fun z : Unit × History n => Program.returned (⟨[UpperInitialState.unitComponent], z.2⟩ : State n))
  apply Certified.returned
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk measurable_snd

theorem fromUnit_certified (active : Fin k → Fin n) (q m : ℕ)
    (draw : X → Fin m → Fin k × I) (hdraw : ∀ i, Measurable (fun x => draw x i)) :
    Certified (fun x => fromUnit active q m (draw x)) := by
  have hb := (boot_certified (n := n)).comp (fun _ : X => ()) measurable_const
  have hp := prepare_certified active (fun z : X × State n => z.2) q m
    (fun z => draw z.1) measurable_snd (fun i => (hdraw i).comp measurable_fst)
  exact hb.bind _ hp

end EnvyFreeResearch.Full.UpperRecordedGridProgramMeasurable
