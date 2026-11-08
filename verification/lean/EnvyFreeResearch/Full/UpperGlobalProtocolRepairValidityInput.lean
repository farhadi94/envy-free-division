import EnvyFreeResearch.Full.UpperGlobalProtocolValidity
import EnvyFreeResearch.Full.UpperGlobalPhysicalFinishHistory

/-! RepairReady supplies the actual physical positivity and near-EF input
conditions, derived from recorded comparisons and the saved valid anchor. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperGlobalPhysicalFinish GlobalCompletion
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) (chores : Bool)
  (hp : p.RepairReady μ chores whole)
include hp

theorem repairReady_positive : ∀ i,
    0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells) := by
  intro i
  have h := hp.positive (enumerate p.anchor.active i) (UpperZeroRows.enumerate_mem _ _)
  rwa [total_correct μ p.buffer hp.physical.buffer_wf] at h

theorem repairReady_nonempty : p.anchor.active.Nonempty := by
  apply Finset.card_pos.mp
  have h := hp.population
  omega

theorem repairReady_near [Nonempty (Fin p.anchor.active.card)] :
    UpperRepairPreparationChecks.Near chores μ (enumerate p.anchor.active)
      p.buffer (localEndowments p) (UpperRepair.nearError n) := by
  have hW : ActiveEF (if chores then .chore else .cake)
      (value μ p.anchor.bundles) p.anchor.active := by
    intro i hi j hj
    exact hp.anchor_valid.2.2.1 i j
  exact (pending_cached_repair_input μ whole p hp.physical chores (enumerate p.anchor.active)
    (UpperZeroRows.enumerate_mem _) (UpperRepair.nearError n) hW hp.shrunk_ef hp.snapshot_ef
    hp.own_loss hp.edge.1 hp.edge.2.1 hp.large).1

end EnvyFreeResearch.Full.UpperGlobalPhysical
