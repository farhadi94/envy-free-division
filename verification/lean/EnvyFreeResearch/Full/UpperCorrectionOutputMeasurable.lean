import EnvyFreeResearch.Full.UpperCorrectionOutcome

/-! Joint Borel measurability of actual successful-or-failed correction outputs. -/

noncomputable section

open MeasureTheory
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionOutputMeasurable

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  UpperCorrectionSetup UpperCorrectionAccepted UpperCorrectionOutcome UpperCorrectionPieces
  UpperCircularStage UpperStageMeasurable ProtocolMeasurable

variable {n k m : ℕ} {X : Type*} [MeasurableSpace X]

/-- Jobs may depend jointly on the full previous sampler transcript. -/
theorem run_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (jobs : X → Fin k → Job n) (initial : X → LoopState n) (tape : X → Fin k → UpperCircular.Circle)
    (hjobs : ∀ j, Measurable (fun z => jobs z j)) (hinitial : Measurable initial)
    (htape : ∀ j, Measurable (fun z => tape z j)) :
    Measurable (fun z => run policy (jobs z) (initial z) (tape z)) := by
  have hdraw : Measurable (fun z => fun j : Fin k => (jobs z j, tape z j)) :=
    Measurable.of_eval (fun j => (hjobs j).prodMk (htape j))
  exact (UpperFreshSamples.run_measurable (step policy) (step_measurable policy hpolicy) k).comp
    (hinitial.prodMk hdraw)

theorem getD_measurable {α : Type*} [MeasurableSpace α] (value : X → Option α)
    (hv : Measurable value) (fallback : α) : Measurable (fun z => (value z).getD fallback) := by
  have h := measurable_option_cases (present := fun (_ : X) a => a) (absent := fun _ : X => fallback)
    hv measurable_snd measurable_const
  convert h using 1
  funext z
  cases value z <;> rfl

variable [Nonempty (Fin k)]

theorem wholeAtoms_measurable (active : Fin k → Fin n) (reserve : X → State n)
    (cuts : X → Fin (m + 2) → ℝ) (t : X → Fin k → ℝ) (eta : X → ℝ)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) (j : Fin k) :
    Measurable (fun z => wholeAtoms active (reserve z) (cuts z) (t z) (eta z) j) := by
  have hwhole : Measurable (fun z : X => whole active (reserve z) (cuts z) (t z) (eta z)) :=
    whole_measurable active reserve cuts t eta hreserve hcuts ht heta
  have hpred : Measurable (fun p : X × Component => UpperPendingExclusion.selected (cuts p.1)
      (fun _ : Unit => whole active (reserve p.1) (cuts p.1) (t p.1) (eta p.1) j) p.2) :=
    UpperPendingExclusion.selected_measurable cuts
      (fun z (_ : Unit) => whole active (reserve z) (cuts z) (t z) (eta z) j) hcuts
      (fun _ => (measurable_pi_apply j).comp hwhole)
  exact list_filter_measurable
    (fun z c => UpperPendingExclusion.selected (cuts z)
      (fun _ : Unit => whole active (reserve z) (cuts z) (t z) (eta z) j) c)
    (fun z => (reserve z).cells) hpred (state_cells_measurable.comp hreserve)

theorem corrections_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Fin k → Fin n) (reserve : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (t : X → Fin k → ℝ) (eta lam : X → ℝ) (tape : X → Fin k → UpperCircular.Circle)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) (hlam : Measurable lam)
    (htape : ∀ j, Measurable (fun z => tape z j)) :
    Measurable (fun z => corrections policy active (reserve z) (cuts z) (t z) (eta z) (lam z) (tape z)) := by
  have hstart := startState_measurable active reserve cuts t eta hreserve hcuts ht heta
  have hjobs := tasks_measurable active reserve cuts t eta lam hreserve hcuts ht heta hlam
  have hrun := run_measurable policy hpolicy _ _ tape
    (fun j => (measurable_pi_apply j).comp hjobs) hstart htape
  exact payments_measurable _ _ (state_cells_measurable.comp (loop_current_measurable.comp hstart))
    (loop_accepted_measurable.comp (measurable_snd.comp hrun))

theorem output_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Fin k → Fin n) (reserve : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (t : X → Fin k → ℝ) (eta lam : X → ℝ) (tape : X → Fin k → UpperCircular.Circle)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) (hlam : Measurable lam)
    (htape : ∀ j, Measurable (fun z => tape z j)) :
    Measurable (fun z => output policy active (reserve z) (cuts z) (t z) (eta z) (lam z) (tape z)) := by
  have hc := corrections_measurable policy hpolicy active reserve cuts t eta lam tape hreserve hcuts ht heta hlam htape
  apply Measurable.of_eval
  intro j
  exact measurable_list_append.comp ((wholeAtoms_measurable active reserve cuts t eta hreserve hcuts ht heta j).prodMk
    (getD_measurable _ ((measurable_list_getElem j.val).comp hc) []))

end EnvyFreeResearch.Full.UpperCorrectionOutputMeasurable
