import EnvyFreeResearch.Full.UpperEnvelopeLoop
import EnvyFreeResearch.Full.UpperCorrectionReady

/-! The maximum-cell envelope probability for the concrete recorded reserve,
actual floating/rounding deficits, and actual stopped correction loop. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperPreparedEnvelope

open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop UpperCorrectionSetup UpperRawPayments UpperCorrectionSupply
  UpperEnvelope UpperCircularStage UpperStageMeasurable

variable {n k m : ℕ} [Nonempty (Fin k)]

instance uniformCells_nullSingleton {Cell : Type*} (cells : Cell → Set ℝ) (e : Cell) :
    NullSingletonClass (uniformCells cells e) := by
  refine ⟨fun x => ?_⟩
  rw [uniformCells, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_singleton x)]
  have hz : volume ({x} ∩ cells e) = 0 := measure_mono_null inter_subset_left (measure_singleton x)
  simp [hz]

/-- No per-reached-state supply or successful rounding output is a premise.
Those facts are derived from the concrete normalized cache and scalar checks.
The event is measured on the original independent circle tape. -/
theorem probability_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (reserve : State n) (hreserve : WellFormed μ reserve)
    (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
    (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain reserve.cells))
    (t : Fin k → ℝ) (eta lam : ℝ) (heta : 0 ≤ eta) (hlam : 0 < lam)
    (hsmall : ∀ i e, table active reserve cuts i e ≤ eta)
    (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j < 1 / 16) (hsize : (k : ℝ)^2 ≤ lam)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16)
    (selected : Finset (Fin (m + 1)))
    (hempty : ∀ e, e ∉ selected → cell (domain reserve.cells) cuts e = ∅)
    (N : ℝ) (hN : 0 ≤ N) (hcount : (selected.card : ℝ) ≤ N) :
    (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle)))
      (UpperEnvelopeLoop.bad policy (tasks active reserve cuts t eta lam) (table active reserve cuts)
        (uniformCells (cell (domain reserve.cells) cuts)) id lam (startState active reserve cuts t eta)) ≤
          ENNReal.ofReal (8 * ((k : ℝ) * eta) * N / lam) := by
  let a := table active reserve cuts
  let job := tasks active reserve cuts t eta lam
  let eps := UpperPayments.deficit a t eta
  let scale (j : Fin k) := total reserve (active j)
  let Safe := UpperCorrectionSupply.Safe μ (activeSet active) (domain reserve.cells)
    (fun i => 7 / 8 * (μ i).real (domain reserve.cells)) job
  have ha := table_nonneg μ active reserve hreserve cuts hzero hmono hsep hpositive
  have hnormal := table_normalized μ active reserve hreserve cuts hzero hone hmono hsep hpositive
  have hround := UpperPayments.allocation_spec a t eta heta ha hsmall hnormal ht (by linarith)
  have heps (j : Fin k) : 0 ≤ eps j := (hround.2.1 j).1
  have hscale (j : Fin k) : 0 < scale j := by
    dsimp only [scale]
    rw [total_correct μ reserve hreserve]
    exact hpositive j
  have hpreserve (j : Fin k) (state : LoopState n) (start : UpperCircular.Circle)
      (hs : Safe j.castSucc state) : Safe j.succ (UpperAggregateInterpolation.loopTransition policy job j state start) :=
    tasks_safe_step μ active reserve hreserve cuts hzero hone hmono hsep hpositive policy hpolicy
      (domain reserve.cells) t eta lam heta hsmall ht hsum hsize j state start hs
  have hready (j : Fin k) (state : LoopState n) (hs : Safe j.castSucc state) (_ : state.stopped = false) :
      WellFormed μ state.current ∧ eps j * scale j ≤ (μ (job j).owner).real (domain state.current.cells) ∧
        scale j / 2 ≤ (μ (job j).owner).real (domain state.current.cells) := by
    have hfit := UpperCorrectionReady.deficit_fits μ active reserve hreserve cuts hzero hone hmono hsep hpositive
      t eta lam heta hsmall ht hsum hsize (domain reserve.cells) j state hs
    have hsupply := safe_mass μ (activeSet active) (domain reserve.cells) _ job j.castSucc state hs
      (fun j i _ => tasks_budget_nonneg μ active reserve hreserve cuts hzero hone hmono hsep hpositive
        t eta lam heta hsmall ht hsum hsize j i)
      (active j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    refine ⟨hs.1, hfit.2.le, ?_⟩
    change total reserve (active j) / 2 ≤ (μ (active j)).real (domain state.current.cells)
    rw [total_correct μ reserve hreserve]
    nlinarith [hpositive j]
  have hinit : Safe 0 (startState active reserve cuts t eta) :=
    start_safe μ active reserve hreserve cuts hzero hmono hsep hpositive hinj (domain reserve.cells)
      Subset.rfl t eta lam heta hlam.le hsmall hsum hmargin
  have hrhozero (e : Fin (m + 1)) (he : e ∉ selected) :
      uniformCells (cell (domain reserve.cells) cuts) e = 0 := by
    simp [uniformCells, hempty e he, ProbabilityTheory.cond]
  have hb : (∑ j, eps j) ≤ (k : ℝ) * eta := by simpa only [Fintype.card_fin] using hround.2.2.1
  exact UpperEnvelopeLoop.probability_le μ policy hpolicy hmeas job a _ selected hrhozero id
    eps scale heps hscale (fun _ => rfl) Safe hpreserve hready (startState active reserve cuts t eta) hinit
    N lam ((k : ℝ) * eta) hN hcount hlam hb

end EnvyFreeResearch.Full.UpperPreparedEnvelope
