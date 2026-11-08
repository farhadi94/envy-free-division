import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableState

/-! Fixed active-set versions of the actual physical Shrink/Repair finishes.
They agree definitionally with the dispatcher functions on their stratum. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
open MeasureTheory UpperGlobalPhysical UpperGlobalPhysicalFinish UpperCorrectionExecution
open UpperZeroRows UpperGlobalNormalize UpperCircularStage UpperRepairProgram
open scoped Classical
variable {n : ℕ}

def finishShrinkAt (active : Finset (Fin n)) (p : Pending n)
    (result : PhysicalResult n active.card) : Pending n :=
  if result.2.2 then p.refresh result.2.1.history
  else p.addShrink (extendPieces active result.1 result.2.1.history) result.2.1

theorem finishShrinkAt_eq (p : Pending n) (result : PhysicalResult n p.anchor.active.card) :
    finishShrinkAt p.anchor.active p result = p.finishShrink result := rfl

theorem finishShrinkAt_measurable (active : Finset (Fin n)) :
    Measurable (fun z : Pending n × PhysicalResult n active.card => finishShrinkAt active z.1 z.2) := by
  have hr : Measurable (fun z : Pending n × PhysicalResult n active.card => z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hh := state_history_measurable.comp hr
  exact (pending_refresh_measurable Prod.fst measurable_fst _ hh).ite
    ((measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton true))
    (pending_addShrink_measurable Prod.fst measurable_fst _
      (extendPieces_measurable active _ (measurable_fst.comp measurable_snd) _ hh) _ hr)

def outputAt (active : Finset (Fin n)) (p : Pending n)
    (localOutput : Fin active.card → State n) (j : Fin n) : State n :=
  if hj : j ∈ active then localOutput ((active.orderIsoOfFin rfl).symm ⟨j,hj⟩)
  else p.anchor.bundles j

theorem outputAt_eq (p : Pending n) (localOutput : Fin p.anchor.active.card → State n) :
    outputAt p.anchor.active p localOutput = output p localOutput := rfl

theorem outputAt_measurable (active : Finset (Fin n)) :
    Measurable (fun z : Pending n × (Fin active.card → State n) => outputAt active z.1 z.2) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j ∈ active
  · simpa only [outputAt,dite_eq_left hj,Function.comp_def] using
      (measurable_pi_apply ((active.orderIsoOfFin rfl).symm ⟨j,hj⟩)).comp measurable_snd
  · simpa only [outputAt,dite_eq_right hj,Function.comp_def] using
      (measurable_pi_apply j).comp (anchor_bundles_measurable.comp
        (pending_anchor_measurable.comp measurable_fst))

def finishAt (active : Finset (Fin n)) (p : Pending n)
    (result : PhysicalResult n active.card) : Anchor n :=
  received p.anchor (outputAt active p result.1) result.2.1

theorem finishAt_eq (p : Pending n) (result : PhysicalResult n p.anchor.active.card) :
    finishAt p.anchor.active p result = finish p result := rfl

theorem finishAt_measurable (active : Finset (Fin n)) :
    Measurable (fun z : Pending n × PhysicalResult n active.card => finishAt active z.1 z.2) := by
  apply anchor_mk_measurable
  · intro j
    exact (measurable_pi_apply j).comp ((outputAt_measurable active).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
  · exact anchor_active_measurable.comp (pending_anchor_measurable.comp measurable_fst)

def finishRepairAt (active : Finset (Fin n)) (p : Pending n)
    (result : PhysicalResult n active.card) : Phase n :=
  if result.2.2 then .finalRepair (p.refresh result.2.1.history)
  else .normalize (finishAt active p result)

theorem finishRepairAt_eq (p : Pending n) (result : PhysicalResult n p.anchor.active.card) :
    finishRepairAt p.anchor.active p result = p.finishRepair result := rfl

theorem finishRepairAt_measurable (active : Finset (Fin n)) :
    Measurable (fun z : Pending n × PhysicalResult n active.card => finishRepairAt active z.1 z.2) := by
  exact (phase_finalRepair_measurable.comp (pending_refresh_measurable Prod.fst measurable_fst _
      (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))))).ite
    ((measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton true))
    (phase_normalize_measurable.comp (finishAt_measurable active))

def localEndowmentsAt (active : Finset (Fin n)) (p : Pending n) : Fin active.card → State n :=
  fun i => p.endowments (enumerate active i)

theorem localEndowmentsAt_eq (p : Pending n) :
    localEndowmentsAt p.anchor.active p = localEndowments p := rfl

theorem localEndowmentsAt_measurable (active : Finset (Fin n)) :
    Measurable (localEndowmentsAt active) :=
  Measurable.of_eval (fun i => (measurable_pi_apply (enumerate active i)).comp endowments_measurable)

end EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
