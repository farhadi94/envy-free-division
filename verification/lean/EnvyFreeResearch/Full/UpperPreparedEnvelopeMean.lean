import EnvyFreeResearch.Full.UpperEnvelopeFamily

/-! The concrete preparation checks derive both the actual correction-charge
mean and the physical estimated-failure inclusion, before averaging over
the full original preparation tape. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperPreparedEnvelopeMean

open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop UpperCorrectionSetup UpperRawPayments UpperCorrectionSupply
  UpperEnvelope UpperCircularStage UpperStageMeasurable UpperEnvelopeFamily

variable {n k m : ℕ} [Nonempty (Fin k)]

/-- Explicit physical/cache and finite arithmetic checks. There is no
success-probability or reached-state invariant in this contract. -/
structure Checks (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (active : Fin k → Fin n)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta : ℝ)
    (selected : Finset (Fin (m + 1))) (N : ℝ) : Prop where
  wellFormed : WellFormed μ reserve
  zero : cuts 0 = 0
  one : cuts (Fin.last (m + 1)) = 1
  monotone : Monotone cuts
  separated : ∀ e, SeparatedAt (cuts e) reserve.cells
  positive : ∀ i, 0 < (μ (active i)).real (domain reserve.cells)
  small : ∀ i e, table active reserve cuts i e ≤ eta
  targets : ∀ j, 0 ≤ t j
  sum : ∑ j, t j < 1 / 16
  empty : ∀ e, e ∉ selected → cell (domain reserve.cells) cuts e = ∅
  count : (selected.card : ℝ) ≤ N

theorem mean_and_bad (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N : ℝ) (heta : 0 ≤ eta) (hlam : 0 < lam) (hN : 0 ≤ N)
    (hsize : (k : ℝ)^2 ≤ lam) (hmargin : (k : ℝ) * lam * eta < 1 / 16)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N) :
    let a := table active reserve cuts
    let jobs := tasks active reserve cuts t eta lam
    let rho := uniformCells (cell (domain reserve.cells) cuts)
    let initial := startState active reserve cuts t eta
    (∫⁻ tape, totalCharge policy jobs (fun j => envelope a rho j) initial tape
      ∂Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle))) ≤
        ENNReal.ofReal (2 * ((k : ℝ) * eta) * N) ∧
    UpperEnvelopeLoop.bad policy jobs a rho id lam initial ⊆
      {tape | ENNReal.ofReal (lam / 4) ≤ totalCharge policy jobs (fun j => envelope a rho j) initial tape} := by
  let a := table active reserve cuts
  let job := tasks active reserve cuts t eta lam
  let rho := uniformCells (cell (domain reserve.cells) cuts)
  let eps := UpperPayments.deficit a t eta
  let scale (j : Fin k) := total reserve (active j)
  let Safe := UpperCorrectionSupply.Safe μ (activeSet active) (domain reserve.cells)
    (fun i => 7 / 8 * (μ i).real (domain reserve.cells)) job
  have ha := table_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated hc.positive
  have hnormal := table_normalized μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive
  have hround := UpperPayments.allocation_spec a t eta heta ha hc.small hnormal hc.targets (by linarith [hc.sum])
  have heps (j : Fin k) : 0 ≤ eps j := (hround.2.1 j).1
  have hscale (j : Fin k) : 0 < scale j := by
    dsimp only [scale]
    rw [total_correct μ reserve hc.wellFormed]
    exact hc.positive j
  have hpreserve (j : Fin k) (state : LoopState n) (start : UpperCircular.Circle)
      (hs : Safe j.castSucc state) : Safe j.succ (UpperAggregateInterpolation.loopTransition policy job j state start) :=
    tasks_safe_step μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive policy hpolicy
      (domain reserve.cells) t eta lam heta hc.small hc.targets hc.sum hsize j state start hs
  have hrhozero (e : Fin (m + 1)) (he : e ∉ selected) : rho e = 0 := by
    simp [rho, uniformCells, hc.empty e he, ProbabilityTheory.cond]
  have hready (j : Fin k) (state : LoopState n) (hs : Safe j.castSucc state) (_ : state.stopped = false) :
      WellFormed μ state.current ∧ eps j * scale j ≤ (μ (job j).owner).real (domain state.current.cells) ∧
        scale j / 2 ≤ (μ (job j).owner).real (domain state.current.cells) ∧
        (envelope a rho j).real (domain state.current.cells) ≤ N := by
    have hfit := UpperCorrectionReady.deficit_fits μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone
      hc.separated hc.positive t eta lam heta hc.small hc.targets hc.sum hsize (domain reserve.cells) j state hs
    have hsupply := safe_mass μ (activeSet active) (domain reserve.cells) _ job j.castSucc state hs
      (fun j i _ => tasks_budget_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive
        t eta lam heta hc.small hc.targets hc.sum hsize j i)
      (active j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    refine ⟨hs.1, hfit.2.le, ?_, ?_⟩
    · change total reserve (active j) / 2 ≤ (μ (active j)).real (domain state.current.cells)
      rw [total_correct μ reserve hc.wellFormed]
      nlinarith [hc.positive j]
    · exact (UpperRawEnvelope.envelope_mass_le_support a rho selected hrhozero j _).trans hc.count
  have hinit : Safe 0 (startState active reserve cuts t eta) :=
    start_safe μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated hc.positive hinj
      (domain reserve.cells) Subset.rfl t eta lam heta hlam.le hc.small hc.sum hmargin
  have hb : (∑ j, eps j) ≤ (k : ℝ) * eta := by simpa only [Fintype.card_fin] using hround.2.2.1
  refine ⟨UpperEnvelopeFamily.mean_le μ policy hpolicy hmeas job (fun j => envelope a rho j)
    eps scale heps hscale (fun _ => rfl) Safe hpreserve N hN hready
    (startState active reserve cuts t eta) hinit ((k : ℝ) * eta) hb, ?_⟩
  apply bad_subset_charge policy job a rho id (startState active reserve cuts t eta) lam
  intro tape j _
  exact (UpperEnvelopeLoop.reached_invariant _ Safe hpreserve _ tape hinit j).1.2.1

end EnvyFreeResearch.Full.UpperPreparedEnvelopeMean
