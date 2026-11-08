import EnvyFreeResearch.Full.UpperEnvelopeMeasurable
import EnvyFreeResearch.Full.UpperAggregateInterpolationLoopMeasurable

/-! Joint actual-loop envelope charging with the complete preparation
parameter retained. No sample-success conditioning is used. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperEnvelopeFamily

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  UpperCircularStage UpperStageMeasurable UpperEnvelope UpperEnvelopeCharge UpperPayments
  UpperAggregateInterpolation UpperCorrectionPieces

abbrev Circle := UpperCircular.Circle

variable {n r : ℕ} {X : Type*} [MeasurableSpace X]

/-- The foreign measure may vary with the entire preparation history. Its
joint component-mass formula supplies the only measure-family input. -/
theorem charge_family_measurable (foreign : X → Measure ℝ)
    (hmass : Measurable (fun p : X × Component => mass (foreign p.1) p.2))
    (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (jobs : X → Fin r → Job n) (hjobs : ∀ i, Measurable (fun x => jobs x i)) (i : Fin r) :
    Measurable (fun p : (X × LoopState n) × Circle =>
      charge (foreign p.1.1) policy (jobs p.1.1 i) p.1.2 p.2) := by
  have hstate : Measurable (fun p : (X × LoopState n) × Circle => p.1.2) := measurable_snd.comp measurable_fst
  have hparam : Measurable (fun p : (X × LoopState n) × Circle => p.1.1) := measurable_fst.comp measurable_fst
  have hjob := (hjobs i).comp hparam
  have hr := descriptor_measurable policy hpolicy
    (fun p : (X × LoopState n) × Circle => p.1.2.current)
    (fun p => (jobs p.1.1 i).owner) (fun p => (jobs p.1.1 i).deficit) (fun p => p.2)
    (loop_current_measurable.comp hstate) (job_owner_measurable.comp hjob)
    (job_deficit_measurable.comp hjob) measurable_snd
  have hp := take_measurable _ _ (state_cells_measurable.comp (loop_current_measurable.comp hstate)) hr
  have hv : Measurable (fun p : ((X × LoopState n) × Circle) × Component =>
      mass (foreign p.1.1.1) p.2) :=
    hmass.comp ((hparam.comp measurable_fst).prodMk measurable_snd)
  have hs := UpperDynamicRouting.sumValues_measurable
    (fun p : (X × LoopState n) × Circle => mass (foreign p.1.1)) hv _ hp
  exact measurable_const.ite
    (measurableSet_eq_fun (loop_stopped_measurable.comp hstate) measurable_const)
    hs.ennreal_ofReal

def totalCharge (policy : Policy n) (jobs : Fin r → Job n) (foreign : Fin r → Measure ℝ)
    (initial : LoopState n) (tape : Fin r → Circle) : ℝ≥0∞ :=
  tapeTotal (loopTransition policy jobs) (fun j => charge (foreign j) policy (jobs j)) initial tape

theorem totalCharge_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (jobs : X → Fin r → Job n) (hjobs : ∀ i, Measurable (fun x => jobs x i))
    (foreign : X → Fin r → Measure ℝ)
    (hmass : ∀ i, Measurable (fun p : X × Component => mass (foreign p.1 i) p.2))
    (initial : X → LoopState n) (hinitial : Measurable initial) :
    Measurable (fun p : X × (Fin r → Circle) => totalCharge policy (jobs p.1) (foreign p.1) (initial p.1) p.2) :=
  parameterized_tapeTotal_measurable (fun x => loopTransition policy (jobs x))
    (fun x j => charge (foreign x j) policy (jobs x j))
    (loopTransition_family_measurable policy hpolicy jobs hjobs)
    (fun j => charge_family_measurable (fun x => foreign x j) (hmass j) policy hpolicy jobs hjobs j)
    initial hinitial

theorem totalCharge_stopped (policy : Policy n) (jobs : Fin r → Job n) (foreign : Fin r → Measure ℝ)
    (initial : LoopState n) (tape : Fin r → Circle) (hstop : initial.stopped = true) :
    totalCharge policy jobs foreign initial tape = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change charge (foreign 0) policy (jobs 0) initial (tape 0) +
      tapeTotal (fun j => loopTransition policy jobs j.succ)
        (fun j => charge (foreign j.succ) policy (jobs j.succ))
        (loopTransition policy jobs 0 initial (tape 0)) (fun j => tape j.succ) = 0
    rw [charge_stopped _ _ _ _ _ hstop]
    have hstep : loopTransition policy jobs 0 initial (tape 0) = initial := by
      simp [loopTransition, step_stopped policy initial _ hstop]
    rw [hstep, zero_add]
    exact ih (fun j => jobs j.succ) (fun j => foreign j.succ) (fun j => tape j.succ)

/-- This is the mean bound before Markov. It counts every actually reached
proposal, including the rejecting one, by fresh-coordinate integration. -/
theorem mean_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (jobs : Fin r → Job n)
    (foreign : Fin r → Measure ℝ) [∀ j, IsFiniteMeasure (foreign j)] [∀ j, NullSingletonClass (foreign j)]
    (eps scale : Fin r → ℝ) (heps : ∀ j, 0 ≤ eps j) (hscale : ∀ j, 0 < scale j)
    (hdeficit : ∀ j, (jobs j).deficit = eps j * scale j)
    (Safe : Fin (r + 1) → LoopState n → Prop)
    (hpreserve : ∀ j state start, Safe j.castSucc state → Safe j.succ (loopTransition policy jobs j state start))
    (N : ℝ) (hN : 0 ≤ N)
    (hready : ∀ j state, Safe j.castSucc state → state.stopped = false →
      WellFormed μ state.current ∧
      eps j * scale j ≤ (μ (jobs j).owner).real (domain state.current.cells) ∧
      scale j / 2 ≤ (μ (jobs j).owner).real (domain state.current.cells) ∧
      (foreign j).real (domain state.current.cells) ≤ N)
    (initial : LoopState n) (hinitial : Safe 0 initial)
    (budget : ℝ) (hbudget : (∑ j, eps j) ≤ budget) :
    (∫⁻ tape, totalCharge policy jobs foreign initial tape
      ∂Measure.pi (fun _ : Fin r => (volume : Measure Circle))) ≤ ENNReal.ofReal (2 * budget * N) := by
  let cost (j : Fin r) := charge (foreign j) policy (jobs j)
  have hcost (j : Fin r) : Measurable (Function.uncurry (cost j)) :=
    charge_measurable _ policy hmeas (jobs j)
  have hfresh (j : Fin r) (state : LoopState n) (hs : Safe j.castSucc state) :
      (∫⁻ start, cost j state start ∂(volume : Measure Circle)) ≤ ENNReal.ofReal (2 * eps j * N) :=
    charge_expectation_le μ policy hpolicy hmeas (jobs j) state
      (fun hopen => (hready j state hs hopen).1) (eps j) (scale j) N (heps j) (hscale j) hN (hdeficit j)
      (fun hopen => (hready j state hs hopen).2.1) (fun hopen => (hready j state hs hopen).2.2.1)
      (foreign j) (fun hopen => (hready j state hs hopen).2.2.2)
  have hmean := expected_tapeTotal_le_invariant (fun _ : Fin r => (volume : Measure Circle))
    (loopTransition policy jobs) cost (fun j _ => ENNReal.ofReal (2 * eps j * N))
    (loopTransition_measurable policy hmeas jobs) hcost (fun _ => measurable_const)
    Safe hpreserve hfresh initial hinitial
  calc
    _ ≤ ∫⁻ tape, tapeTotal (loopTransition policy jobs)
        (fun j (_ : LoopState n) (_ : Circle) => ENNReal.ofReal (2 * eps j * N)) initial tape
          ∂Measure.pi (fun _ : Fin r => (volume : Measure Circle)) := hmean
    _ = ∑ j, ENNReal.ofReal (2 * eps j * N) := by simp [tapeTotal_eq_sum]
    _ = ENNReal.ofReal (∑ j, 2 * eps j * N) :=
      (ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg (by norm_num) (heps j)) hN)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      gcongr

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

theorem bad_subset_charge (policy : Policy n) (jobs : Fin r → Job n)
    (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ) [∀ e, IsFiniteMeasure (rho e)]
    (recipient : Fin r → Agent) (initial : LoopState n) (lam : ℝ)
    (hdis : ∀ tape j, (reached (loopTransition policy jobs) initial tape j).stopped = false →
      DisjointComponents (reached (loopTransition policy jobs) initial tape j).current.cells) :
    UpperEnvelopeLoop.bad policy jobs a rho recipient lam initial ⊆
      {tape | ENNReal.ofReal (lam / 4) ≤
        totalCharge policy jobs (fun j => envelope a rho (recipient j)) initial tape} := by
  intro tape htape
  obtain ⟨j, hopen, hbad⟩ := htape
  have henv := estimated_exceed_implies_envelope a rho (recipient j) _ lam hbad
  have hsingle : ENNReal.ofReal (lam / 4) ≤
      charge (envelope a rho (recipient j)) policy (jobs j)
        (reached (loopTransition policy jobs) initial tape j) (tape j) := by
    rw [charge_eq_mass _ policy (jobs j) _ _ (hdis tape j hopen) hopen]
    exact ENNReal.ofReal_le_ofReal henv.le
  change ENNReal.ofReal (lam / 4) ≤ totalCharge policy jobs _ initial tape
  rw [totalCharge, tapeTotal_eq_sum]
  exact hsingle.trans (Finset.single_le_sum
    (f := fun i : Fin r => charge (envelope a rho (recipient i)) policy (jobs i)
      (reached (loopTransition policy jobs) initial tape i) (tape i))
    (fun i _ => zero_le) (Finset.mem_univ j))

end EnvyFreeResearch.Full.UpperEnvelopeFamily
