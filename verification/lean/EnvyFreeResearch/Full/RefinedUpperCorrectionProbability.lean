import EnvyFreeResearch.Full.RefinedUpperCorrectionConditional

/-! Fresh-attempt probabilities derived from the actual physical supply
invariant and queried payment table. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperCorrectionProbability
open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop RefinedUpperCorrectionSetup UpperCorrectionSupply RefinedUpperRawPayments
  UpperEnvelope RefinedUpperPayments UpperCircularStage UpperPreparedEnvelopeMean
  RefinedUpperCorrectionChance UpperEnvelopeCharge UpperStageMeasurable
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem envelope_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (active : Fin k → Fin n)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N : ℝ) (heta : 0 ≤ eta) (hlam : 0 < lam) (hN : 0 ≤ N)
    (hsize : 4 * (k : ℝ) ≤ lam)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
    (buffer : Set ℝ) (j : Fin k) (s : LoopState n)
    (hs : Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) j.castSucc s) :
    (volume : Measure UpperCircular.Circle) {start | ENNReal.ofReal (lam / 4) ≤
      charge (envelope (table active reserve cuts)
        (uniformCells (cell (domain reserve.cells) cuts)) j)
        policy (tasks active reserve cuts t eta lam j) s start} ≤
      ENNReal.ofReal (8 * eta * N / lam) := by
  let a := table active reserve cuts
  let rho := uniformCells (cell (domain reserve.cells) cuts)
  let eps := deficit a t eta j
  let scale := (μ (active j)).real (domain reserve.cells)
  have hround := allocation_spec a t eta heta
    (table_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated hc.positive)
    hc.small (table_normalized μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive)
    hc.targets (by linarith [hc.sum])
  have heps : 0 ≤ eps := (hround.2.1 j).1
  have hepsle : eps ≤ eta := (hround.2.1 j).2.trans (min_le_right _ _)
  have howner : (tasks active reserve cuts t eta lam j).owner = active j := rfl
  have hdeficit : (tasks active reserve cuts t eta lam j).deficit = eps * scale := by
    simp only [tasks, recordedJobs, jobs, total_correct μ reserve hc.wellFormed]
    rfl
  have hfit := RefinedUpperCorrectionReady.deficit_fits μ active reserve hc.wellFormed cuts
    hc.zero hc.one hc.monotone hc.separated hc.positive t eta lam heta hc.small hc.targets hc.sum
    hsize buffer j s hs
  have hmass := safe_mass μ (activeSet active) buffer _ (tasks active reserve cuts t eta lam)
    j.castSucc s hs
    (fun j i _ => tasks_budget_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone
      hc.separated hc.positive t eta lam heta hc.small hc.targets hc.sum hsize j i)
    (active j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hrhozero (e : Fin (m + 1)) (he : e ∉ selected) : rho e = 0 := by
    simp [rho, uniformCells, hc.empty e he, ProbabilityTheory.cond]
  have hprob := RefinedUpperCorrectionChance.envelope_probability μ policy hp hm
    (tasks active reserve cuts t eta lam j) s (fun _ => hs.1)
    eps scale N lam heps (hc.positive j) hN hlam hdeficit
    (fun _ => by rw [howner]; simpa only [hdeficit] using hfit.2.le)
    (fun _ => by rw [howner]; dsimp only [scale]; nlinarith [hc.positive j])
    (envelope a rho j)
    (fun _ => (UpperRawEnvelope.envelope_mass_le_support a rho selected hrhozero j _).trans hc.count)
  apply hprob.trans
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hepsle (by norm_num)) hN) hlam.le

/-- Endpoint domination uses the actual retained domain. Its complement and
finite grid coordinates may therefore be added to the bad set at zero cost. -/
theorem endpoint_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (active : Fin k → Fin n)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N : ℝ) (heta : 0 ≤ eta) (hsize : 4 * (k : ℝ) ≤ lam)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
    (j : Fin k) (s : LoopState n)
    (hs : Safe μ (activeSet active) (domain reserve.cells)
      (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) j.castSucc s)
    (bad : Set ℝ) (hb : MeasurableSet bad) (originalMass : ℝ) (hpos : 0 < originalMass)
    (hhalf : originalMass / 2 ≤ (μ (active j)).real (domain reserve.cells))
    (δ : ℝ≥0∞)
    (hbadmass : ((μ (active j)).restrict (domain reserve.cells)) bad ≤
      ENNReal.ofReal (originalMass * (k : ℝ)) * δ) :
    (volume : Measure UpperCircular.Circle)
      {start | endpointBad policy (tasks active reserve cuts t eta lam j) bad s start = true} ≤
      ENNReal.ofReal (32 * (k : ℝ) / 7) * δ := by
  have howner : (tasks active reserve cuts t eta lam j).owner = active j := rfl
  have hmass := safe_mass μ (activeSet active) (domain reserve.cells) _
    (tasks active reserve cuts t eta lam) j.castSucc s hs
    (fun j i _ => tasks_budget_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone
      hc.separated hc.positive t eta lam heta hc.small hc.targets hc.sum hsize j i)
    (active j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hp0 := RefinedUpperCorrectionChance.endpointBad_probability μ policy hp hm
    (tasks active reserve cuts t eta lam j) bad hb s hs.1 (domain reserve.cells) hs.2.1
    (7 / 16 * originalMass) (by positivity)
    (by rw [howner]; linarith)
  rw [howner] at hp0
  apply hp0.trans
  calc
    _ ≤ (2 * ENNReal.ofReal (1 / (7 / 16 * originalMass))) *
        (ENNReal.ofReal (originalMass * (k : ℝ)) * δ) := by gcongr
    _ = ENNReal.ofReal (32 * (k : ℝ) / 7) * δ := by
      rw [← mul_assoc]
      congr 1
      rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      field_simp
      <;> ring

end EnvyFreeResearch.Full.RefinedUpperCorrectionProbability
