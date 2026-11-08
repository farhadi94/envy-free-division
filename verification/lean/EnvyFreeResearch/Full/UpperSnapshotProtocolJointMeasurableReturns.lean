import EnvyFreeResearch.Full.UpperSnapshotProtocolActualRun
import EnvyFreeResearch.Full.UpperSnapshotProtocolSafety
import EnvyFreeResearch.Full.UpperSnapshotProtocolMeasurable

/-! Joint Borel zero/rejection exits of the concrete Snapshot dispatcher. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall UpperQueryPrograms
variable {n k : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem rejectWhole_measurable (origin : X → State n) (history : X → History n)
    (ho : Measurable origin) (hh : Measurable history) :
    Measurable (fun x => rejectWhole (k:=k) (origin x) (history x)) := by
  have hempty := UpperComponentAssembly.empty_measurable history hh
  have hr : Measurable (fun x => (⟨(origin x).cells,history x⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    exact (state_cells_measurable.comp ho).prodMk hh
  exact (Measurable.of_eval (fun _ => hempty)).prodMk (hr.prodMk measurable_const)

theorem restoreRejected_measurable (origin : X → State n) (out : X → PhysicalResult n k)
    (ho : Measurable origin) (hr : Measurable out) :
    Measurable (fun x => restoreRejected (origin x) (out x)) :=
  (rejectWhole_measurable origin (fun x => (out x).2.1.history) ho
    (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp hr)))).ite
      (measurableSet_eq_fun (measurable_snd.comp (measurable_snd.comp hr)) measurable_const) hr

theorem zeroExecute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (origin : X → State n)
    (cutter : Fin k) (start : X → UpperCircular.Circle) (ho : Measurable origin) (hs : Measurable start) :
    Measurable (fun x => zeroExecute policy hk chores active (origin x) cutter (start x)) :=
  zeroFinish_measurable hk chores active start _ hs
    (partitionRun_measurable policy hmeas origin (active cutter) (fun _ => equalTargets k) start
      ho (fun _ => measurable_const) hs)
end EnvyFreeResearch.Full.UpperSnapshotProtocol
