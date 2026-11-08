import EnvyFreeResearch.Full.UpperPreparedEnvelopeMean

/-! The actual cached acceptance test follows from the whole-cell,
estimated-correction and interpolation bounds. All physical measures retain
their original units; normalization is explicit real division. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperCorrectionError

open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop UpperCorrectionSetup UpperCorrectionSupply UpperRawPayments
  UpperEnvelope UpperPayments UpperCircularStage UpperPreparedEnvelopeMean UpperGridSensitivity

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

theorem distance_le_support (a : Agent → Cell → ℝ) (selected : Finset Cell)
    (hzero : ∀ i e, e ∉ selected → a i e = 0) (i j : Agent) :
    distance a i j ≤ (selected.card : ℝ) * cellGap a i j := by
  calc
    _ = ∑ e ∈ selected, |a i e - a j e| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ selected)
      intro e _ he
      simp [hzero i e he, hzero j e he]
    _ ≤ ∑ _e ∈ selected, cellGap a i j :=
      Finset.sum_le_sum (fun e _ => difference_le_cellGap a i j e)
    _ = _ := by simp

theorem three_errors (yi yj ci cj target lam A est : ℝ)
    (hown : yj + cj = target)
    (hwhole : |yi - yj| ≤ lam * A / 2)
    (hestimate : |est| ≤ lam * A / 4)
    (herror : |ci - cj - est| ≤ lam * A / 4) :
    |yi + ci - target| ≤ lam * A := by
  have hid : yi + ci - target = (yi - yj) + (est + (ci - cj - est)) := by linarith
  rw [hid]
  calc
    _ ≤ |yi - yj| + |est + (ci - cj - est)| := abs_add_le _ _
    _ ≤ |yi - yj| + (|est| + |ci - cj - est|) := add_le_add le_rfl (abs_add_le _ _)
    _ ≤ _ := by linarith

variable {n k m : ℕ} [Nonempty (Fin k)]

theorem accepts_of_errors (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N b : ℝ) (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hb : 0 ≤ b)
    (hsize : (k : ℝ)^2 ≤ lam / 2) (hquarter : b * N ≤ lam / 4)
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
          b * distance (table active reserve cuts) i j) :
    accepts (tasks active reserve cuts t eta lam j) state.current
      (execute policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start).2 = true := by
  let a := table active reserve cuts
  let C := payment policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start
  let scale (i : Fin k) := (μ (active i)).real (domain reserve.cells)
  have hfullsize : (k : ℝ)^2 ≤ lam := by linarith
  have hf := UpperCorrectionReady.deficit_fits μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone
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
  have hazero (i : Fin k) (e : Fin (m + 1)) (he : e ∉ selected) : a i e = 0 := by
    dsimp only [a]
    rw [table_correct μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated, hc.empty e he]
    simp
  have herr (i : Fin k) : |value a t eta i j + (μ (active i)).real C / scale i - t j| ≤ lam * cellGap a i j := by
    apply three_errors _ _ _ _ _ _ _ _ hownn
    · have h := hround.2.2.2 i j
      simp only [Fintype.card_fin] at h
      exact h.trans (by nlinarith [cellGap_nonneg a i j])
    · exact hestimate i
    · apply (hinterpolation i).trans
      have hd := (distance_le_support a selected hazero i j).trans
        (mul_le_mul_of_nonneg_right hc.count (cellGap_nonneg a i j))
      have hmul := mul_le_mul_of_nonneg_left hd hb
      have hquarter' := mul_le_mul_of_nonneg_right hquarter (cellGap_nonneg a i j)
      nlinarith
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

end EnvyFreeResearch.Full.UpperCorrectionError
