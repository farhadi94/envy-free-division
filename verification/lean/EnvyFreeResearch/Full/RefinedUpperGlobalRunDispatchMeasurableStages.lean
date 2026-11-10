import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunDispatchMeasurableFinish
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionDispatch
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolStageActions
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSnapshotAction

/-! Actual cached phase decisions after a local call, at a fixed active set. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
open MeasureTheory RefinedUpperGlobalPhysical UpperCorrectionExecution RefinedUpperGlobalNormalize
open UpperZeroRows UpperCircularStage RefinedUpperRepairProgram ProtocolMeasurable
open scoped Classical
variable {n : ℕ}

def finishFirstAt (active : Finset (Fin n)) (p : Pending n) (chores : Bool) (G : ℝ)
    (result : PhysicalResult n active.card) : Phase n :=
  let next := finishShrinkAt active p result
  if result.2.2 then .firstShrink next G
  else match next.selectPhaseAt active (direction chores) with
    | some phase => phase
    | none => .firstShrink next G

theorem finishFirstAt_measurable (active : Finset (Fin n)) (chores : Bool) :
    Measurable (fun z : (Pending n × ℝ) × PhysicalResult n active.card =>
      finishFirstAt active z.1.1 chores z.1.2 z.2) := by
  let next := fun z : (Pending n × ℝ) × PhysicalResult n active.card =>
    finishShrinkAt active z.1.1 z.2
  have hn : Measurable next := (finishShrinkAt_measurable active).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hr : Measurable (fun z : (Pending n × ℝ) × PhysicalResult n active.card =>
      Phase.firstShrink (next z) z.1.2) :=
    phase_firstShrink_measurable.comp (hn.prodMk (measurable_snd.comp measurable_fst))
  have hv := (selectPhaseAt_measurable active (direction chores)).comp hn
  have ho := measurable_option_cases (present := fun _ phase => phase) hv measurable_snd hr
  have hm : Measurable (fun z : (Pending n × ℝ) × PhysicalResult n active.card =>
      match (next z).selectPhaseAt active (direction chores) with
      | some phase => phase
      | none => Phase.firstShrink (next z) z.1.2) := by
    convert ho using 1
    funext z
    cases h : (next z).selectPhaseAt active (direction chores) <;> simp [Function.comp_def,h]
  exact hr.ite
    ((measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton true)) hm

def finishSecondAt (active : Finset (Fin n)) (p : Pending n)
    (result : PhysicalResult n active.card) : Phase n :=
  let next := finishShrinkAt active p result
  if result.2.2 then .secondShrink next else .finalRepair next

theorem finishSecondAt_measurable (active : Finset (Fin n)) :
    Measurable (fun z : Pending n × PhysicalResult n active.card => finishSecondAt active z.1 z.2) :=
  (phase_secondShrink_measurable.comp (finishShrinkAt_measurable active)).ite
    ((measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton true))
    (phase_finalRepair_measurable.comp (finishShrinkAt_measurable active))

def snapshotPendingAt (active : Finset (Fin n)) (hk : 0 < active.card) (chores : Bool)
    (a : Anchor n) (result : PhysicalResult n active.card) : Pending n :=
  let witness := UpperSnapshotRepair.pair hk chores (enumerate active) result
  Pending.start a (extendPieces active result.1 result.2.1.history) result.2.1
    (enumerate active witness.1) (enumerate active witness.2)

theorem snapshotPendingAt_measurable (active : Finset (Fin n)) (hk : 0 < active.card)
    (chores : Bool) : Measurable (fun z : Anchor n × PhysicalResult n active.card =>
      snapshotPendingAt active hk chores z.1 z.2) := by
  have hr : Measurable (fun z : Anchor n × PhysicalResult n active.card => z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hh := state_history_measurable.comp hr
  have hp := UpperSnapshotRepair.pair_measurable hk chores (enumerate active)
    (fun z : Anchor n × PhysicalResult n active.card => z.2) measurable_snd
  exact pending_start_measurable Prod.fst measurable_fst _
    (extendPieces_measurable active _ (measurable_fst.comp measurable_snd) _ hh) _ hr _ _
    ((measurable_of_countable (enumerate active)).comp (measurable_fst.comp hp))
    ((measurable_of_countable (enumerate active)).comp (measurable_snd.comp hp))

def finishSnapshotAt (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 0 < active.card) (chores : Bool) (a : Anchor n)
    (result : PhysicalResult n active.card) : Phase n :=
  if result.2.2 then .snapshot (refresh a result.2.1.history)
  else if result.2.1.cells=[] then
    .done (terminal a (extendPieces active result.1 result.2.1.history) result.2.1.history)
  else
    let p := snapshotPendingAt active hk chores a result
    .firstShrink p (p.firstFactorAt active (direction chores))

theorem finishSnapshotAt_measurable (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (hk : 0 < active.card) (chores : Bool) :
    Measurable (fun z : Anchor n × PhysicalResult n active.card =>
      finishSnapshotAt active hk chores z.1 z.2) := by
  have hr : Measurable (fun z : Anchor n × PhysicalResult n active.card => z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hh := state_history_measurable.comp hr
  have hp := snapshotPendingAt_measurable active hk chores
  have he : MeasurableSet {z : Anchor n × PhysicalResult n active.card | z.2.2.1.cells=[]} := by
    simpa only [List.length_eq_zero_iff,Function.comp_def] using
      measurableSet_eq_fun (measurable_list_length.comp (state_cells_measurable.comp hr))
        (measurable_const (a := 0))
  exact (phase_snapshot_measurable.comp (refresh_measurable Prod.fst measurable_fst _ hh)).ite
    ((measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton true))
    ((phase_done_measurable.comp (terminal_measurable Prod.fst measurable_fst _
      (extendPieces_measurable active _ (measurable_fst.comp measurable_snd) _ hh) _ hh)).ite he
      (phase_firstShrink_measurable.comp (hp.prodMk
        ((firstFactorAt_measurable active (direction chores)).comp hp))))

end EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
