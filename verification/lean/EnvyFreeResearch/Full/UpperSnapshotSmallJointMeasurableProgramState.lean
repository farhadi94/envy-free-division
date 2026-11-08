import EnvyFreeResearch.Full.UpperSnapshotSmallProgramCertified
import EnvyFreeResearch.Full.UpperSnapshotSmallFirstMeasurable

/-! Pure first-stage state constructors are Borel on every raw reply packet,
including packets that no legal policy ever returns. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m : ℕ} {X : Type*} [MeasurableSpace X]

theorem restoredFrom_joint_measurable (origin : X → State n) (raw : X → (Fin 2 → ℝ) × State n)
    (ho : Measurable origin) (hr : Measurable raw) :
    Measurable (fun x => restoredFrom (origin x) (raw x)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x => (refineEndpoints (origin x).cells (List.ofFn (raw x).1), (raw x).2.history))
  exact (refineEndpoints_measurable _ _ (state_cells_measurable.comp ho)
    ((UpperRecordedGrid.ofFn_measurable 2).comp (measurable_fst.comp hr))).prodMk
    (state_history_measurable.comp (measurable_snd.comp hr))

variable (origin : X → State n) (cutter : Fin n) (cuts : X → Fin (m+2) → ℝ)
  (selected : X → Finset (Fin (m+1))) (t : X → ℝ) (start : X → Circle)
  (raw : X → (Fin 2 → ℝ) × State n)
  (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e))
  (hs : Measurable selected) (ht : Measurable t) (hstart : Measurable start) (hr : Measurable raw)
include ho hc hs ht hstart hr

theorem flagFrom_joint_measurable :
    Measurable (fun p : X × Component => flagFrom (origin p.1) cutter (cuts p.1)
      (selected p.1) (t p.1) (start p.1) (raw p.1) p.2) := by
  have hp := UpperPendingExclusion.selected_measurable cuts (fun x (_ : Unit) => selected x)
    hc (fun _ => hs)
  have ha := prefixAtom_measurable _ _ _ _ _
    ((firstAmount_measurable origin cutter cuts selected t ho hc hs ht).comp measurable_fst)
    (hstart.comp measurable_fst)
    (((measurable_pi_apply 0).comp (measurable_fst.comp hr)).comp measurable_fst)
    (((measurable_pi_apply 1).comp (measurable_fst.comp hr)).comp measurable_fst) measurable_snd
  exact ((measurable_of_countable (fun p : Bool × Bool => p.1 || p.2)).comp (hp.prodMk ha)).ite
    (measurableSet_eq_fun ((firstFill_measurable origin cutter cuts selected t ho hc hs ht).comp
      measurable_fst) measurable_const)
    ((measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp (hp.prodMk ha))

theorem remainderFrom_joint_measurable :
    Measurable (fun x => remainderFrom (origin x) cutter (cuts x) (selected x) (t x) (start x) (raw x)) :=
  selectState_measurable _ _ (restoredFrom_joint_measurable origin raw ho hr)
    ((measurable_of_countable (fun b : Bool => !b)).comp
      (flagFrom_joint_measurable origin cutter cuts selected t start raw ho hc hs ht hstart hr))
end EnvyFreeResearch.Full.UpperSnapshotSmall
