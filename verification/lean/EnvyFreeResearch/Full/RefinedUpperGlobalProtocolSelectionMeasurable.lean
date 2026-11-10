import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionData
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolMachineMeasurable

/-! Borel selection on each fixed active-population stratum. The input is the
actual Pending state, and all numerical tests use its finite query cache. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows GlobalCompletion
open RefinedUpperGlobal.Transfer
variable {n : ℕ}

theorem snapshotGap_measurable (direction : Direction) (i j : Fin n) :
    Measurable (fun p : Pending n => p.snapshotGap direction i j) := by
  have hm (j : Fin n) : Measurable (fun p : Pending n => total (p.snapshot j) i) :=
    total_measurable _ (fun _ => i) ((measurable_pi_apply j).comp pending_snapshot_measurable) measurable_const
  cases direction
  · exact (hm i).sub (hm j)
  · exact (hm j).sub (hm i)

theorem anchor_edge_measurable (direction : Direction) (i j : Fin n) :
    Measurable (fun a : Anchor n => decide (a.edge direction i j)) := by
  classical
  have hm (i : Fin n) : MeasurableSet {a : Anchor n | i ∈ a.active} :=
    anchor_active_measurable (show MeasurableSet {a : Finset (Fin n) | i ∈ a} from MeasurableSet.of_discrete)
  have hmargin : Measurable (fun a : Anchor n => margin direction a.cachedValue i j) := by
    cases direction
    · exact (cachedValue_measurable id measurable_id i i).sub (cachedValue_measurable id measurable_id i j)
    · exact (cachedValue_measurable id measurable_id i j).sub (cachedValue_measurable id measurable_id i i)
  have hne : MeasurableSet {a : Anchor n | j ≠ i} := by
    by_cases h : j=i <;> simp [h]
  have he : MeasurableSet {a : Anchor n | a.edge direction i j} := by
    exact (hm i).inter ((hm j).inter (hne.inter
      (measurableSet_lt hmargin (cachedResidue_measurable id measurable_id i))))
  convert (Measurable.ite he (measurable_const : Measurable (fun _ : Anchor n => true))
      (measurable_const : Measurable (fun _ : Anchor n => false))) using 1
  funext a
  by_cases h : a.edge direction i j <;> simp [h]
  all_goals exact Classical.decPred _

def Pending.selectionDataAt (p : Pending n) (active : Finset (Fin n)) (direction : Direction) :
    Selection.CachedData active.card :=
  (fun i j => decide (p.anchor.edge direction (enumerate active i) (enumerate active j)),
    (fun i j => p.snapshotGap direction (enumerate active i) (enumerate active j)),
    fun i => total p.buffer (enumerate active i))

theorem selectionDataAt_eq (p : Pending n) (direction : Direction) :
    p.selectionDataAt p.anchor.active direction=p.selectionData direction := rfl

theorem selectionDataAt_measurable (active : Finset (Fin n)) (direction : Direction) :
    Measurable (fun p : Pending n => p.selectionDataAt active direction) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (anchor_edge_measurable direction _ _).comp pending_anchor_measurable
  · apply Measurable.prodMk
    · exact measurable_pi_lambda (fun i => measurable_pi_lambda (fun j => snapshotGap_measurable direction _ _))
    · exact measurable_pi_lambda (fun i => total_measurable _ (fun _ => enumerate active i)
        pending_buffer_measurable measurable_const)

theorem selectTransferAt_measurable (active : Finset (Fin n)) (direction : Direction) :
    Measurable (fun p : Pending n => Selection.select (RefinedUpperRepair.nearError n)
      (p.selectionDataAt active direction)) :=
  (Selection.select_measurable _).comp (selectionDataAt_measurable active direction)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
