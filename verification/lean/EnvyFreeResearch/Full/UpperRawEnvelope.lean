import EnvyFreeResearch.Full.UpperEnvelopeStage
import EnvyFreeResearch.Full.UpperCorrectionExecution

/-!
# Envelope bounds in original oracle units

Normalized deficits are multiplied by the recorded reserve mass. Remaining
supply is compared to that same raw scale, so no normalization is imposed on
the actual oracle profile. Empty reserve cells cost no envelope mass.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperRawEnvelope

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperUnionCircular UpperEnvelope UpperPayments Chores

abbrev Circle := UpperCircular.Circle

variable {n : ℕ} {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

theorem envelope_mass_le_support (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsZeroOrProbabilityMeasure (rho e)] (selected : Finset Cell)
    (hzero : ∀ e, e ∉ selected → rho e = 0) (j : Agent) (C : Set ℝ) :
    (envelope a rho j).real C ≤ selected.card := by
  rw [envelope_real]
  have heq : (∑ e, height a j e * (rho e).real C) = ∑ e ∈ selected, height a j e * (rho e).real C := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    simp [hzero e he]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ selected, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact (mul_le_mul (height_le_one a j e) measureReal_le_one measureReal_nonneg (by norm_num)).trans_eq
        (one_mul 1)
    _ = _ := by simp

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (hmeas : MeasurablePolicy policy) (state : State n) (hstate : WellFormed μ state) (cutter : Fin n)

include hstate hmeas in
/-- Integrability of the actual physical executor's foreign mass. -/
theorem payment_integrable (eps : ℝ) (foreign : Measure ℝ) [IsFiniteMeasure foreign] :
    Integrable (fun start : Circle => foreign.real (payment policy state cutter eps start)) volume := by
  change Integrable (fun start => foreign.real (piece policy state.history cutter (values state cutter)
    (total state cutter) state.cells (amount eps (total state cutter)) start)) volume
  rw [total_correct μ state hstate]
  exact UpperCorrectionStage.foreign_integrable μ policy state.history cutter (values state cutter)
    state.cells hmeas _ foreign

include hpolicy hmeas hstate in
/-- The normalized deficit is the only deficit in the expectation bound;
the implemented request remains the raw product `eps * scale`. -/
theorem payment_expectation_le (eps scale N : ℝ) (heps : 0 ≤ eps) (hscale : 0 < scale)
    (hfit : eps * scale ≤ (μ cutter).real (domain state.cells))
    (hsupply : scale / 2 ≤ (μ cutter).real (domain state.cells))
    (foreign : Measure ℝ) [IsFiniteMeasure foreign] (hN : foreign.real (domain state.cells) ≤ N) :
    (∫ start : Circle, foreign.real (payment policy state cutter (eps * scale) start) ∂volume) ≤ 2 * eps * N := by
  have hpositive : 0 < (μ cutter).real (domain state.cells) := (half_pos hscale).trans_le hsupply
  change (∫ start : Circle, foreign.real (piece policy state.history cutter (values state cutter)
    (total state cutter) state.cells (amount (eps * scale) (total state cutter)) start) ∂volume) ≤ _
  rw [total_correct μ state hstate, amount_eq_fraction _ _ (mul_nonneg heps hscale.le) hfit hpositive,
    UpperCorrectionStage.foreign_real_expectation μ policy hpolicy state.history cutter (values state cutter)
      state.cells hstate.1 hstate.2.1 (values_correct μ state hstate cutter) hpositive hmeas]
  have hf : eps * scale / (μ cutter).real (domain state.cells) ≤ 2 * eps := by
    apply (div_le_iff₀ hpositive).mpr
    nlinarith
  exact mul_le_mul hf hN measureReal_nonneg (by positivity)

include hpolicy hmeas hstate in
theorem payment_exceed_probability (eps scale N lam : ℝ) (heps : 0 ≤ eps) (hscale : 0 < scale)
    (hfit : eps * scale ≤ (μ cutter).real (domain state.cells))
    (hsupply : scale / 2 ≤ (μ cutter).real (domain state.cells)) (hlam : 0 < lam)
    (foreign : Measure ℝ) [IsFiniteMeasure foreign] (hN : foreign.real (domain state.cells) ≤ N) :
    (volume : Measure Circle) {start | lam / 4 < foreign.real (payment policy state cutter (eps * scale) start)} ≤
      ENNReal.ofReal (8 * eps * N / lam) := by
  let f (start : Circle) := foreign.real (payment policy state cutter (eps * scale) start)
  have hi : Integrable f volume := payment_integrable μ policy hmeas state hstate cutter (eps * scale) foreign
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (volume : Measure Circle) (fun start => (show 0 ≤ f start from measureReal_nonneg))) hi (lam / 4)
  have hmean := payment_expectation_le μ policy hpolicy hmeas state hstate cutter eps scale N heps hscale hfit hsupply foreign hN
  have hbound : (volume : Measure Circle).real {start | lam / 4 ≤ f start} ≤ 8 * eps * N / lam := by
    apply (le_div_iff₀ hlam).mpr
    change lam / 4 * (volume : Measure Circle).real {start | lam / 4 ≤ f start} ≤ _ at hm
    change (∫ start, f start ∂volume) ≤ _ at hmean
    nlinarith
  calc
    _ ≤ (volume : Measure Circle) {start | lam / 4 ≤ f start} := by
      apply measure_mono
      intro start h
      change lam / 4 < f start at h
      exact h.le
    _ = ENNReal.ofReal ((volume : Measure Circle).real {start | lam / 4 ≤ f start}) :=
      (ofReal_measureReal (by finiteness)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

include hpolicy hmeas hstate in
/-- One maximum envelope controls all active observers, with the actual
selected reserve-cell cap rather than the full fixed grid index count. -/
theorem estimated_failure_probability (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsZeroOrProbabilityMeasure (rho e)] (selected : Finset Cell)
    (hzero : ∀ e, e ∉ selected → rho e = 0) (j : Agent)
    (eps scale N lam : ℝ) (heps : 0 ≤ eps) (hscale : 0 < scale)
    (hfit : eps * scale ≤ (μ cutter).real (domain state.cells))
    (hsupply : scale / 2 ≤ (μ cutter).real (domain state.cells)) (hlam : 0 < lam)
    (hcount : (selected.card : ℝ) ≤ N) :
    (volume : Measure Circle) {start | ∃ i,
      lam * cellGap a i j / 4 < |estimate a rho i j (payment policy state cutter (eps * scale) start)|} ≤
        ENNReal.ofReal (8 * eps * N / lam) := by
  calc
    _ ≤ (volume : Measure Circle) {start | lam / 4 <
        (envelope a rho j).real (payment policy state cutter (eps * scale) start)} := by
      apply measure_mono
      intro start hbad
      exact estimated_exceed_implies_envelope a rho j _ lam hbad
    _ ≤ _ := payment_exceed_probability μ policy hpolicy hmeas state hstate cutter eps scale N lam
      heps hscale hfit hsupply hlam (envelope a rho j)
      ((envelope_mass_le_support a rho selected hzero j _).trans hcount)

end EnvyFreeResearch.Full.UpperRawEnvelope
