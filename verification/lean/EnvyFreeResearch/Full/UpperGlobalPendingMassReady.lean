import EnvyFreeResearch.Full.UpperGlobalPendingMassPhysical

/-! Actual Repair preconditions obtained from the finite cached transfer test. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution GlobalCompletion
variable {n k : ℕ}

theorem pending_cached_repair_input [Nonempty (Fin k)]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
    (chores : Bool) (active : Fin k → Fin n) (hactive : ∀ i, active i ∈ p.anchor.active)
    (tau : ℝ)
    (hW : ActiveEF (if chores then .chore else .cake) (value μ p.anchor.bundles) p.anchor.active)
    (hH : ActiveEF (if chores then .chore else .cake) (value μ p.shrunk) p.anchor.active)
    (hX : ActiveEF (if chores then .chore else .cake) (value μ p.snapshot) p.anchor.active)
    (hown : ∀ i ∈ p.anchor.active,
      margin (if chores then .chore else .cake) (fun a b => total (p.snapshot b) a)
        i (p.permutation i) ≤ tau * total p.buffer i)
    (hb : p.witness ∈ p.anchor.active) (hh : p.target ∈ p.anchor.active)
    (hlarge : 2 * total p.buffer p.witness ≤
      margin (if chores then .chore else .cake) (fun a b => total (p.snapshot b) a)
        p.witness (p.permutation p.target)) :
    UpperRepairPreparationChecks.Near chores μ active p.buffer
      (fun j => p.endowments (active j)) tau ∧
    (2-tau) * (μ p.witness).real (domain p.buffer.cells) ≤
      margin (if chores then .chore else .cake) (value μ p.endowments) p.witness p.target := by
  have ho : ∀ i ∈ p.anchor.active,
      margin (if chores then .chore else .cake) (value μ p.snapshot) i (p.permutation i) ≤
        tau * (μ i).real (domain p.buffer.cells) := by
    intro i hi
    simpa only [pending_snapshot_margin_cache μ whole p hp,pending_buffer_cache μ whole p hp]
      using hown i hi
  have hl : 2 * (μ p.witness).real (domain p.buffer.cells) ≤
      margin (if chores then .chore else .cake) (value μ p.snapshot) p.witness (p.permutation p.target) := by
    simpa only [pending_snapshot_margin_cache μ whole p hp,pending_buffer_cache μ whole p hp]
      using hlarge
  have hn := pending_near_margin μ p (pending_saved_shrunk_disjoint μ whole p hp)
    (pending_saved_snapshot_disjoint μ whole p hp) (fun j => hp.cross j _)
    (if chores then .chore else .cake) hW hH tau ho hX (pending_permutation_active μ whole p hp)
  constructor
  · exact pending_repair_near μ p tau chores active hactive (fun i hi j hj => hn i j hi hj)
  · exact pending_strong_margin μ p (pending_saved_shrunk_disjoint μ whole p hp)
      (pending_saved_snapshot_disjoint μ whole p hp) (fun j => hp.cross j _)
      (if chores then .chore else .cake) hW hH tau ho hb hh hl

end EnvyFreeResearch.Full.UpperGlobalPhysical
