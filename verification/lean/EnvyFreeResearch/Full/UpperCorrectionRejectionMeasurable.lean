import EnvyFreeResearch.Full.UpperPreparedEnvelopeFamily
import EnvyFreeResearch.Full.UpperCorrectionOutputMeasurable

/-! The actual rejection Boolean is jointly Borel even when the fixed-label
reserve varies across outer label fibers. This supports a second averaging
step without pretending that a varying analytic reserve is fixed. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EnvyFreeResearch.Full.UpperCorrectionRejectionMeasurable

open UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSetup UpperCircularStage
  UpperStageMeasurable UpperPreparedEnvelopeFamily

variable {n k m : ℕ} [Nonempty (Fin k)] {X : Type*} [MeasurableSpace X]

def rejected (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (approved : Bool)
    (tape : Fin k → UpperCircular.Circle) : Bool :=
  approved && (run policy (tasks active reserve cuts t eta lam)
    (preparedInitial active reserve cuts t eta approved) tape).2.stopped

theorem rejected_iff (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (approved : Bool)
    (tape : Fin k → UpperCircular.Circle) :
    rejected policy active reserve cuts t eta lam approved tape = true ↔
      approved = true ∧ (run policy (tasks active reserve cuts t eta lam)
        (preparedInitial active reserve cuts t eta approved) tape).2.stopped = true := by
  simp only [rejected, Bool.and_eq_true]

theorem rejected_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Fin k → Fin n) (reserve : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (t : X → Fin k → ℝ) (eta lam : ℝ) (approved : X → Bool)
    (tape : X → Fin k → UpperCircular.Circle) (hreserve : Measurable reserve)
    (hcuts : ∀ e, Measurable (fun x => cuts x e)) (ht : ∀ j, Measurable (fun x => t x j))
    (happroved : Measurable approved) (htape : ∀ j, Measurable (fun x => tape x j)) :
    Measurable (fun x => rejected policy active (reserve x) (cuts x) (t x) eta lam (approved x) (tape x)) := by
  have hjobs (j : Fin k) := (measurable_pi_apply j).comp
    (tasks_measurable active reserve cuts t (fun _ => eta) (fun _ => lam) hreserve hcuts ht measurable_const measurable_const)
  have hr := UpperCorrectionOutputMeasurable.run_measurable policy hpolicy
    (fun x => tasks active (reserve x) (cuts x) (t x) eta lam)
    (fun x => preparedInitial active (reserve x) (cuts x) (t x) eta (approved x)) tape hjobs
    (preparedInitial_measurable active reserve cuts t eta approved hreserve hcuts ht happroved) htape
  exact (measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp
    (happroved.prodMk (loop_stopped_measurable.comp (measurable_snd.comp hr)))

theorem measurableSet_rejected (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Fin k → Fin n) (reserve : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (t : X → Fin k → ℝ) (eta lam : ℝ) (approved : X → Bool)
    (tape : X → Fin k → UpperCircular.Circle) (hreserve : Measurable reserve)
    (hcuts : ∀ e, Measurable (fun x => cuts x e)) (ht : ∀ j, Measurable (fun x => t x j))
    (happroved : Measurable approved) (htape : ∀ j, Measurable (fun x => tape x j)) :
    MeasurableSet {x | rejected policy active (reserve x) (cuts x) (t x) eta lam (approved x) (tape x) = true} :=
  measurableSet_eq_fun
    (rejected_measurable policy hpolicy active reserve cuts t eta lam approved tape hreserve hcuts ht happroved htape)
    measurable_const

/-- Outer labels are averaged only after each fixed-label reserve has been
handled. The measurable event is the actual program's rejection Boolean. -/
theorem outer_average {Label Tape : Type*} [MeasurableSpace Label] [MeasurableSpace Tape]
    (labels : Measure Label) [IsProbabilityMeasure labels] (tapes : Measure Tape) [SFinite tapes]
    (failure : Label × Tape → Bool) (hfailure : Measurable failure) (C : ℝ≥0∞)
    (hfiber : ∀ label, tapes {tape | failure (label, tape) = true} ≤ C) :
    (labels.prod tapes) {p | failure p = true} ≤ C := by
  rw [Measure.prod_apply (measurableSet_eq_fun hfailure measurable_const)]
  calc
    _ ≤ ∫⁻ _ : Label, C ∂labels := lintegral_mono hfiber
    _ = _ := by simp

end EnvyFreeResearch.Full.UpperCorrectionRejectionMeasurable
