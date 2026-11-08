import EnvyFreeResearch.Full.UpperGlobalNormalizeMeasurableState
import EnvyFreeResearch.Full.UpperGlobalProtocolMachineMeasurable
import EnvyFreeResearch.Full.UpperGlobalProtocolShrinkAction
import EnvyFreeResearch.Full.UpperGlobalProtocolRepairAction

/-! Borel physical assembly on a fixed active-set stratum. Overriding the
finite active label set makes all local tape and allocation dimensions fixed. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
open MeasureTheory UpperGlobalPhysical UpperCorrectionExecution UpperRecordedDomain
open UpperComponentAssembly UpperZeroRows UpperGlobalNormalize UpperCircularStage
open scoped Classical
variable {n : ℕ} {X : Type} [MeasurableSpace X]

def anchorAt (active : Finset (Fin n)) (a : Anchor n) : Anchor n := {a with active := active}
def pendingAt (active : Finset (Fin n)) (p : Pending n) : Pending n :=
  {p with anchor := anchorAt active p.anchor}

theorem anchorAt_self (a : Anchor n) : anchorAt a.active a = a := by cases a; rfl
theorem pendingAt_self (p : Pending n) : pendingAt p.anchor.active p = p := by
  cases p with
  | mk anchor snapshot shrunk buffer permutation witness target => cases anchor; rfl

theorem anchorAt_measurable (active : Finset (Fin n)) : Measurable (anchorAt active) := by
  apply anchor_mk_measurable
  · intro j
    exact (measurable_pi_apply j).comp anchor_bundles_measurable
  · exact anchor_residue_measurable
  · exact measurable_const

theorem pendingAt_measurable (active : Finset (Fin n)) : Measurable (pendingAt active) :=
  pending_mk_measurable _ _ _ _ _ _ _
    ((anchorAt_measurable active).comp pending_anchor_measurable)
    pending_snapshot_measurable pending_shrunk_measurable pending_buffer_measurable
    pending_permutation_measurable pending_witness_measurable pending_target_measurable

theorem refresh_measurable (a : X → Anchor n) (ha : Measurable a)
    (history : X → History n) (hh : Measurable history) :
    Measurable (fun x => refresh (a x) (history x)) := by
  apply anchor_mk_measurable
  · intro j
    exact (measurable_pi_apply j).comp (anchor_bundles_measurable.comp ha)
  · apply measurable_comap_iff.mpr
    exact (state_cells_measurable.comp (anchor_residue_measurable.comp ha)).prodMk hh
  · exact anchor_active_measurable.comp ha

theorem pending_refresh_measurable (p : X → Pending n) (hp : Measurable p)
    (history : X → History n) (hh : Measurable history) :
    Measurable (fun x => (p x).refresh (history x)) := by
  apply pending_mk_measurable
  · exact pending_anchor_measurable.comp hp
  · exact pending_snapshot_measurable.comp hp
  · exact pending_shrunk_measurable.comp hp
  · apply measurable_comap_iff.mpr
    exact (state_cells_measurable.comp (pending_buffer_measurable.comp hp)).prodMk hh
  · exact pending_permutation_measurable.comp hp
  · exact pending_witness_measurable.comp hp
  · exact pending_target_measurable.comp hp

theorem pending_start_measurable (a : X → Anchor n) (ha : Measurable a)
    (pieces : X → Fin n → State n) (hp : Measurable pieces)
    (residue : X → State n) (hr : Measurable residue)
    (b h : X → Fin n) (hb : Measurable b) (hh : Measurable h) :
    Measurable (fun x => Pending.start (a x) (pieces x) (residue x) (b x) (h x)) :=
  pending_mk_measurable _ _ _ _ _ _ _ ha hp
    (Measurable.of_eval (fun _ => empty_measurable _ (state_history_measurable.comp hr)))
    hr measurable_const hb hh

theorem pending_addShrink_measurable (p : X → Pending n) (hp : Measurable p)
    (pieces : X → Fin n → State n) (hpieces : Measurable pieces)
    (residue : X → State n) (hr : Measurable residue) :
    Measurable (fun x => (p x).addShrink (pieces x) (residue x)) := by
  apply pending_mk_measurable
  · exact pending_anchor_measurable.comp hp
  · exact pending_snapshot_measurable.comp hp
  · apply Measurable.of_eval
    intro j
    exact join_measurable _ _ _
      ((measurable_pi_apply j).comp (pending_shrunk_measurable.comp hp))
      ((measurable_pi_apply j).comp hpieces) (state_history_measurable.comp hr)
  · exact hr
  · exact pending_permutation_measurable.comp hp
  · exact pending_witness_measurable.comp hp
  · exact pending_target_measurable.comp hp

theorem extendPieces_measurable (active : Finset (Fin n))
    (pieces : X → Fin active.card → State n) (hp : Measurable pieces)
    (history : X → History n) (hh : Measurable history) :
    Measurable (fun x => extendPieces active (pieces x) (history x)) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j ∈ active
  · simpa only [extendPieces,dite_eq_left hj,Function.comp_def] using
      (measurable_pi_apply ((active.orderIsoOfFin rfl).symm ⟨j,hj⟩)).comp hp
  · simpa only [extendPieces,dite_eq_right hj] using empty_measurable history hh

theorem endowments_measurable : Measurable (Pending.endowments (n := n)) := by
  apply Measurable.of_eval
  intro j
  have hindex : Measurable (fun p : Pending n => p.permutation j) :=
    (measurable_of_countable (fun f : Equiv.Perm (Fin n) => f j)).comp pending_permutation_measurable
  have hs : Measurable (fun p : Pending n => p.snapshot (p.permutation j)) :=
    finite_select_measurable _ hindex _
      (fun i => (measurable_pi_apply i).comp pending_snapshot_measurable)
  exact join_measurable _ _ _
    ((measurable_pi_apply j).comp (anchor_bundles_measurable.comp pending_anchor_measurable))
    (join_measurable _ _ _ ((measurable_pi_apply j).comp pending_shrunk_measurable) hs
      (state_history_measurable.comp pending_buffer_measurable))
    (state_history_measurable.comp pending_buffer_measurable)

end EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
