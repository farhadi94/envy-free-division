import EnvyFreeResearch.Full.UpperEnvelopeCharge
import EnvyFreeResearch.Full.UpperAggregateInterpolationLoop

/-!
# Unconditioned envelope failure for the actual stopped correction loop

The original product tape is integrated by the proved fresh-coordinate
induction. A single maximum envelope covers all observers at a job; a single
Markov bound on the sum covers every reached job, including rejection.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperEnvelopeLoop

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  UpperCircularStage UpperStageMeasurable UpperEnvelope UpperEnvelopeCharge UpperPayments
  UpperAggregateInterpolation

abbrev Circle := UpperCircular.Circle

variable {n r : ℕ} {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

theorem reached_invariant {State Draw : Type*} {r : ℕ} (transition : Fin r → State → Draw → State)
    (Safe : Fin (r + 1) → State → Prop)
    (hpreserve : ∀ i state draw, Safe i.castSucc state → Safe i.succ (transition i state draw))
    (state : State) (tape : Fin r → Draw) (hstate : Safe 0 state) (i : Fin r) :
    Safe i.castSucc (reached transition state tape i) := by
  induction r generalizing state with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [reached, Fin.cons_zero, Fin.castSucc_zero] using hstate
    · simpa only [reached, Fin.cons_succ, Fin.castSucc_succ] using
        ih (fun i => transition i.succ) (fun i => Safe i.succ)
          (fun i state draw hs => hpreserve i.succ state draw hs)
          (transition 0 state (tape 0)) (fun i => tape i.succ) (hpreserve 0 state (tape 0) hstate) j

def bad (policy : Policy n) (jobs : Fin r → Job n) (a : Agent → Cell → ℝ)
    (rho : Cell → Measure ℝ) (recipient : Fin r → Agent) (lam : ℝ) (initial : LoopState n) :
    Set (Fin r → Circle) := {tape | ∃ j,
      (reached (loopTransition policy jobs) initial tape j).stopped = false ∧ ∃ i,
        lam * cellGap a i (recipient j) / 4 < |estimate a rho i (recipient j)
          (payment policy (reached (loopTransition policy jobs) initial tape j).current
            (jobs j).owner (jobs j).deficit (tape j))|}

/-- A complete original-tape bound derived from actual transition mechanics
and per-reached-state raw supply; no conditional-success law is assumed. -/
theorem probability_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (jobs : Fin r → Job n)
    (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsZeroOrProbabilityMeasure (rho e)] [∀ e, NullSingletonClass (rho e)]
    (selected : Finset Cell) (hzero : ∀ e, e ∉ selected → rho e = 0) (recipient : Fin r → Agent)
    (eps scale : Fin r → ℝ) (heps : ∀ j, 0 ≤ eps j) (hscale : ∀ j, 0 < scale j)
    (hdeficit : ∀ j, (jobs j).deficit = eps j * scale j)
    (Safe : Fin (r + 1) → LoopState n → Prop)
    (hpreserve : ∀ j state start, Safe j.castSucc state → Safe j.succ (loopTransition policy jobs j state start))
    (hready : ∀ j state, Safe j.castSucc state → state.stopped = false →
      WellFormed μ state.current ∧
      eps j * scale j ≤ (μ (jobs j).owner).real (domain state.current.cells) ∧
      scale j / 2 ≤ (μ (jobs j).owner).real (domain state.current.cells))
    (initial : LoopState n) (hinitial : Safe 0 initial)
    (N lam budget : ℝ) (hN : 0 ≤ N) (hcount : (selected.card : ℝ) ≤ N)
    (hlam : 0 < lam) (hbudget : (∑ j, eps j) ≤ budget) :
    (Measure.pi (fun _ : Fin r => (volume : Measure Circle)))
      (bad policy jobs a rho recipient lam initial) ≤ ENNReal.ofReal (8 * budget * N / lam) := by
  let cost (j : Fin r) := charge (envelope a rho (recipient j)) policy (jobs j)
  let totalCharge (tape : Fin r → Circle) := tapeTotal (loopTransition policy jobs) cost initial tape
  let tapeLaw := Measure.pi (fun _ : Fin r => (volume : Measure Circle))
  have hcost (j : Fin r) : Measurable (Function.uncurry (cost j)) :=
    charge_measurable _ policy hmeas (jobs j)
  have htotal : Measurable totalCharge :=
    (tapeTotal_measurable (loopTransition policy jobs) cost
      (loopTransition_measurable policy hmeas jobs) hcost).comp (measurable_const.prodMk measurable_id)
  have hfresh (j : Fin r) (state : LoopState n) (hs : Safe j.castSucc state) :
      (∫⁻ start, cost j state start ∂(volume : Measure Circle)) ≤ ENNReal.ofReal (2 * eps j * N) :=
    charge_expectation_le μ policy hpolicy hmeas (jobs j) state
      (fun hopen => (hready j state hs hopen).1) (eps j) (scale j) N (heps j) (hscale j) hN (hdeficit j)
      (fun hopen => (hready j state hs hopen).2.1) (fun hopen => (hready j state hs hopen).2.2)
      (envelope a rho (recipient j))
      (fun _ => (UpperRawEnvelope.envelope_mass_le_support a rho selected hzero (recipient j) _).trans hcount)
  have hmean0 := expected_tapeTotal_le_invariant (fun _ : Fin r => (volume : Measure Circle))
    (loopTransition policy jobs) cost (fun j _ => ENNReal.ofReal (2 * eps j * N))
    (loopTransition_measurable policy hmeas jobs) hcost (fun _ => measurable_const)
    Safe hpreserve hfresh initial hinitial
  have hmean : (∫⁻ tape, totalCharge tape ∂tapeLaw) ≤ ENNReal.ofReal (2 * budget * N) := by
    calc
      _ ≤ ∫⁻ tape, tapeTotal (loopTransition policy jobs)
          (fun j (_ : LoopState n) (_ : Circle) => ENNReal.ofReal (2 * eps j * N)) initial tape ∂tapeLaw := hmean0
      _ = ∑ j, ENNReal.ofReal (2 * eps j * N) := by simp [tapeTotal_eq_sum, tapeLaw]
      _ = ENNReal.ofReal (∑ j, 2 * eps j * N) :=
        (ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg (by norm_num) (heps j)) hN)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        gcongr
  have hbad : bad policy jobs a rho recipient lam initial ⊆
      {tape | ENNReal.ofReal (lam / 4) ≤ totalCharge tape} := by
    intro tape htape
    obtain ⟨j, hopen, hbad⟩ := htape
    have hs := reached_invariant (loopTransition policy jobs) Safe hpreserve initial tape hinitial j
    have hwf := (hready j _ hs hopen).1
    have henv := estimated_exceed_implies_envelope a rho (recipient j) _ lam hbad
    have hsingle : ENNReal.ofReal (lam / 4) ≤ cost j (reached (loopTransition policy jobs) initial tape j) (tape j) := by
      dsimp only [cost]
      rw [charge_eq_mass _ policy (jobs j) _ _ hwf.2.1 hopen]
      exact ENNReal.ofReal_le_ofReal henv.le
    change ENNReal.ofReal (lam / 4) ≤ totalCharge tape
    dsimp only [totalCharge]
    rw [tapeTotal_eq_sum]
    exact hsingle.trans (Finset.single_le_sum
      (f := fun i : Fin r => cost i (reached (loopTransition policy jobs) initial tape i) (tape i))
      (fun i _ => zero_le) (Finset.mem_univ j))
  have hthreshold : 0 < lam / 4 := div_pos hlam (by norm_num)
  calc
    _ ≤ tapeLaw {tape | ENNReal.ofReal (lam / 4) ≤ totalCharge tape} := measure_mono hbad
    _ ≤ (∫⁻ tape, totalCharge tape ∂tapeLaw) / ENNReal.ofReal (lam / 4) :=
      meas_ge_le_lintegral_div htotal.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * budget * N) / ENNReal.ofReal (lam / 4) := by gcongr
    _ = ENNReal.ofReal ((2 * budget * N) / (lam / 4)) := (ENNReal.ofReal_div_of_pos hthreshold).symm
    _ = _ := by congr 1; field_simp; ring

end EnvyFreeResearch.Full.UpperEnvelopeLoop
