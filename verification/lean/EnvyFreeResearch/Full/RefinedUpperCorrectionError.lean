import EnvyFreeResearch.Full.UpperCorrectionError
import EnvyFreeResearch.Full.RefinedUpperCorrectionReady

/-! The concrete acceptance test follows from linear whole-payment and
inherited-boundary bounds, plus the maximum-cell envelope estimate. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperCorrectionError
open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop RefinedUpperCorrectionSetup UpperCorrectionSupply RefinedUpperRawPayments
  UpperEnvelope RefinedUpperPayments UpperCircularStage UpperPreparedEnvelopeMean
open UpperPayments (cellGap cellGap_nonneg)
open UpperCorrectionError (three_errors)
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem accepts_of_errors (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N : ℝ) (heta : 0 ≤ eta) (hlam : 0 ≤ lam)
    (hsize : 16 * (k : ℝ) ≤ lam)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
    (buffer : Set ℝ) (j : Fin k) (state : LoopState n)
    (hsafe : Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) j.castSucc state)
    (start : UpperCircular.Circle)
    (hestimate : ∀ i, |estimate (table active reserve cuts)
      (uniformCells (cell (domain reserve.cells) cuts)) i j
      (payment policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start)| ≤
      lam * cellGap (table active reserve cuts) i j / 4)
    (hinterpolation : ∀ i,
      |(μ (active i)).real (payment policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start) /
          (μ (active i)).real (domain reserve.cells) -
        (μ (active j)).real (payment policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start) /
          (μ (active j)).real (domain reserve.cells) -
        estimate (table active reserve cuts) (uniformCells (cell (domain reserve.cells) cuts)) i j
          (payment policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start)| ≤
          4 * (k : ℝ) * cellGap (table active reserve cuts) i j) :
    accepts (tasks active reserve cuts t eta lam j) state.current
      (execute policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start).2 = true := by
  let a := table active reserve cuts
  let C := payment policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start
  let scale (i : Fin k) := (μ (active i)).real (domain reserve.cells)
  have hfullsize : 4 * (k : ℝ) ≤ lam := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hf := RefinedUpperCorrectionReady.deficit_fits μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone
    hc.separated hc.positive t eta lam heta hc.small hc.targets hc.sum hfullsize buffer j state hsafe
  have hpos : 0 < (μ (active j)).real (domain state.current.cells) := hf.1.trans_lt hf.2
  have hown : (μ (active j)).real C = deficit a t eta j * scale j := by
    rw [payment_exact μ policy hpolicy state.current hsafe.1 (active j) hpos _ hf.1 hf.2.le]
    simp only [tasks, recordedJobs, jobs, scale, total_correct μ reserve hc.wellFormed]
    rfl
  have hownn : value a t eta j j + (μ (active j)).real C / scale j = t j := by
    rw [hown, mul_div_cancel_right₀ _ (hc.positive j).ne']
    simp only [deficit]
    ring
  have hround := allocation_spec a t eta heta
    (table_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated hc.positive)
    hc.small (table_normalized μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive)
    hc.targets (by linarith [hc.sum])
  have herr (i : Fin k) : |value a t eta i j + (μ (active i)).real C / scale i - t j| ≤ lam * cellGap a i j := by
    apply three_errors _ _ _ _ _ _ _ _ hownn
    · have h := hround.2.2.2 i j
      simp only [Fintype.card_fin] at h
      exact h.trans (by nlinarith [cellGap_nonneg a i j])
    · exact hestimate i
    · exact (hinterpolation i).trans (by nlinarith [cellGap_nonneg a i j])
  apply (accepts_physical_iff μ policy hpolicy state.current hsafe.1
    (tasks active reserve cuts t eta lam j) hpos start).mpr
  intro observer hchecked
  have hin : observer ∈ activeSet active := by
    simpa only [tasks, recordedJobs, jobs, decide_eq_true_eq] using hchecked
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hin
  have hinverse : Function.invFun active (active i) = i := Function.leftInverse_invFun hinj i
  have hprev : (tasks active reserve cuts t eta lam j).previous (active i) = value a t eta i j * scale i := by
    simp only [tasks, recordedJobs, jobs, hinverse, scale, total_correct μ reserve hc.wellFormed]
    rfl
  have hdesired : (tasks active reserve cuts t eta lam j).desired (active i) = t j * scale i := by
    simp only [tasks, recordedJobs, jobs, scale, total_correct μ reserve hc.wellFormed]
  have htolerance : (tasks active reserve cuts t eta lam j).tolerance (active i) = lam * cellGap a i j * scale i := by
    simp only [tasks, recordedJobs, jobs, hinverse, scale, total_correct μ reserve hc.wellFormed]
    rfl
  rw [hprev, hdesired, htolerance]
  change |value a t eta i j * scale i + (μ (active i)).real C - t j * scale i| ≤ _
  have heq : value a t eta i j * scale i + (μ (active i)).real C - t j * scale i =
      (value a t eta i j + (μ (active i)).real C / scale i - t j) * scale i := by
    rw [sub_mul, add_mul, div_mul_cancel₀ _ (show scale i ≠ 0 from (hc.positive i).ne')]
  rw [heq, abs_mul, abs_of_pos (hc.positive i)]
  exact mul_le_mul_of_nonneg_right (herr i) (hc.positive i).le

end EnvyFreeResearch.Full.RefinedUpperCorrectionError
