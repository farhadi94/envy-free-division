import EnvyFreeResearch.Full.UpperRawEnvelope
import EnvyFreeResearch.Full.UpperCorrectionPieces
import EnvyFreeResearch.Full.UpperCorrectionLoop

/-! Measurable nonnegative envelope charge for the actual stopped loop.
The list-sum extension is defined on every coded state and agrees with the
physical foreign mass on every well-formed reached state. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperEnvelopeCharge

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  UpperCircularStage UpperStageMeasurable UpperCorrectionPieces UpperEnvelope

abbrev Circle := UpperCircular.Circle

variable {n : ℕ}

def charge (foreign : Measure ℝ) (policy : Policy n) (job : Job n)
    (state : LoopState n) (start : Circle) : ℝ≥0∞ :=
  if state.stopped then 0 else ENNReal.ofReal (sumValues (mass foreign)
    (take state.current.cells (descriptor policy state.current job.owner job.deficit start)))

theorem charge_stopped (foreign : Measure ℝ) (policy : Policy n) (job : Job n)
    (state : LoopState n) (start : Circle) (hstop : state.stopped = true) :
    charge foreign policy job state start = 0 := by simp [charge, hstop]

theorem charge_eq_mass (foreign : Measure ℝ) [IsFiniteMeasure foreign]
    (policy : Policy n) (job : Job n) (state : LoopState n) (start : Circle)
    (hdis : DisjointComponents state.current.cells) (hopen : state.stopped = false) :
    charge foreign policy job state start = ENNReal.ofReal
      (foreign.real (payment policy state.current job.owner job.deficit start)) := by
  rw [charge, hopen]
  simp only [Bool.false_eq_true, ite_false]
  rw [← domain_mass_sum foreign _ (take_disjoint state.current.cells hdis _), take_domain]
  rfl

theorem charge_measurable (foreign : Measure ℝ) [IsFiniteMeasure foreign] [NullSingletonClass foreign]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (job : Job n) :
    Measurable (Function.uncurry (charge foreign policy job)) := by
  have hstate : Measurable (fun p : LoopState n × Circle => p.1.current) :=
    loop_current_measurable.comp measurable_fst
  have hexec : Measurable (fun p : LoopState n × Circle =>
      execute policy p.1.current job.owner job.deficit p.2) :=
    execute_measurable policy hpolicy _ _ _ _ hstate measurable_const measurable_const measurable_snd
  have hpiece : Measurable (fun p : LoopState n × Circle =>
      take p.1.current.cells (descriptor policy p.1.current job.owner job.deficit p.2)) :=
    take_measurable _ _ (state_cells_measurable.comp hstate) (measurable_fst.comp hexec)
  exact measurable_const.ite
    (measurableSet_eq_fun (loop_stopped_measurable.comp measurable_fst) measurable_const)
    (Measurable.ennreal_ofReal (sumValues_mass_measurable foreign _ hpiece))

/-- The conditional lower-integral bound retains the original raw profile
and allows the state to be the first rejecting proposal. -/
theorem charge_expectation_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (job : Job n) (state : LoopState n)
    (hstate : state.stopped = false → WellFormed μ state.current)
    (eps scale N : ℝ) (heps : 0 ≤ eps) (hscale : 0 < scale) (hNnonneg : 0 ≤ N)
    (hdeficit : job.deficit = eps * scale)
    (hfit : state.stopped = false → eps * scale ≤ (μ job.owner).real (domain state.current.cells))
    (hsupply : state.stopped = false → scale / 2 ≤ (μ job.owner).real (domain state.current.cells))
    (foreign : Measure ℝ) [IsFiniteMeasure foreign]
    (hN : state.stopped = false → foreign.real (domain state.current.cells) ≤ N) :
    (∫⁻ start : Circle, charge foreign policy job state start ∂volume) ≤ ENNReal.ofReal (2 * eps * N) := by
  by_cases hstop : state.stopped = true
  · simp only [charge, hstop, ite_true, lintegral_zero]
    exact zero_le
  · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
    simp_rw [charge_eq_mass foreign policy job state _ (hstate hopen).2.1 hopen, hdeficit]
    have hi := UpperRawEnvelope.payment_integrable μ policy hmeas state.current (hstate hopen)
      job.owner (eps * scale) foreign
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => measureReal_nonneg))]
    exact ENNReal.ofReal_le_ofReal (UpperRawEnvelope.payment_expectation_le μ policy hpolicy hmeas
      state.current (hstate hopen) job.owner eps scale N heps hscale (hfit hopen) (hsupply hopen) foreign (hN hopen))

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

instance envelope_nullSingleton (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, NullSingletonClass (rho e)] (j : Agent) : NullSingletonClass (envelope a rho j) := by
  constructor
  intro x
  simp [envelope, Measure.finsetSum_apply, Measure.smul_apply]

end EnvyFreeResearch.Full.UpperEnvelopeCharge
