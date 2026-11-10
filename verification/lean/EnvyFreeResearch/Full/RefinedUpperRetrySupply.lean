import EnvyFreeResearch.Full.RefinedUpperCorrectionRetries
import EnvyFreeResearch.Full.UpperCorrectionSupply

/-! The physical reserve invariant survives a whole batch of retries.
Rejected attempts retain the current job's budget; acceptance advances the
budget exactly once. No rejected cut is subtracted from the reserve. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperRetrySupply
open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSupply
  UpperRecordedDomain RefinedUpperCorrectionRetries
abbrev Circle := UpperCircular.Circle
variable {n m : ℕ}

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

/-- Supply does not depend on the stop flag or the list of accepted descriptors. -/
theorem safe_reopen (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (jobs : Fin m → Job n) (time : Fin (m + 1)) (s : LoopState n) :
    Safe μ active buffer floor jobs time (reopen s) ↔ Safe μ active buffer floor jobs time s := Iff.rfl

def RetrySafe (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (jobs : Fin m → Job n) (time : Fin m) (s : RetryState n) : Prop :=
  Safe μ active buffer floor jobs (if s.1 then time.succ else time.castSucc) s.2

theorem rejected_safe (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (jobs : Fin m → Job n) (time : Fin (m + 1)) (s : RetryState n) (draw : Job n × Circle)
    (hs : Safe μ active buffer floor jobs time s.2)
    (hpositive : s.2.stopped = false → 0 < (μ draw.1.owner).real (domain s.2.current.cells))
    (hr : (attempt policy s draw).1 = true) :
    Safe μ active buffer floor jobs time (attempt policy s draw).2.2 := by
  have hrestore := rejected_restores policy s draw hr
  refine ⟨attempt_wellFormed μ policy hpolicy s hs.1 draw hpositive, ?_, ?_⟩
  · simpa only [hrestore.1] using hs.2.1
  · simpa only [hrestore.1] using hs.2.2

theorem attempt_safe (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (hfloor : ∀ i ∈ active, 0 < floor i) (jobs : Fin m → Job n)
    (howner : ∀ j, (jobs j).owner ∈ active)
    (hchecked : ∀ j i, i ∈ active → (jobs j).checked i = true)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (time : Fin m) (s : RetryState n) (draw : Circle)
    (hs : RetrySafe μ active buffer floor jobs time s) :
    RetrySafe μ active buffer floor jobs time (attempt policy s (jobs time, draw)).2 := by
  by_cases hd : s.1 = true
  · simpa [attempt, hd] using hs
  · have hf : s.1 = false := Bool.eq_false_iff.mpr hd
    by_cases hstop : s.2.stopped = true
    · simpa [attempt, hstop] using hs
    · have ho : s.2.stopped = false := Bool.eq_false_iff.mpr hstop
      have hs0 : Safe μ active buffer floor jobs time.castSucc s.2 := by
        simpa [RetrySafe, hf] using hs
      have hp : 0 < (μ (jobs time).owner).real (domain s.2.current.cells) :=
        (hfloor _ (howner time)).trans
          (safe_mass μ active buffer floor jobs time.castSucc s.2 hs0 hbudget _ (howner time))
      by_cases hr : (step policy s.2 (jobs time, draw)).1 = true
      · have har : (attempt policy s (jobs time, draw)).1 = true := by
          simpa [attempt, hf, ho, update] using hr
        have hpreserve := rejected_safe μ policy hpolicy active buffer floor jobs time.castSucc
          s (jobs time, draw) hs0 (fun _ => hp) har
        simpa [RetrySafe, attempt, hf, ho, update, hr] using hpreserve
      · have hr0 : (step policy s.2 (jobs time, draw)).1 = false := Bool.eq_false_iff.mpr hr
        have hpreserve := safe_step μ policy hpolicy active buffer floor hfloor jobs howner
          hchecked hbudget time s.2 draw hs0
        simpa [RetrySafe, attempt, hf, ho, update, hr0, safe_reopen] using hpreserve

theorem retry_safe (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (hfloor : ∀ i ∈ active, 0 < floor i) (jobs : Fin m → Job n)
    (howner : ∀ j, (jobs j).owner ∈ active)
    (hchecked : ∀ j i, i ∈ active → (jobs j).checked i = true)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (time : Fin m) (s : LoopState n)
    (hs : Safe μ active buffer floor jobs time.castSucc s)
    (r : ℕ) (tape : Fin r → Circle) :
    RetrySafe μ active buffer floor jobs time (retry policy (jobs time) s tape).2 := by
  have hrun (r : ℕ) (s : RetryState n) (hs : RetrySafe μ active buffer floor jobs time s)
      (tape : Fin r → Circle) :
      RetrySafe μ active buffer floor jobs time
        (UpperFreshSamples.run (attempt policy) r s (fun i => (jobs time, tape i))).2 := by
    induction r generalizing s with
    | zero => exact hs
    | succ r ih =>
      exact ih _ (attempt_safe μ policy hpolicy active buffer floor hfloor jobs howner
        hchecked hbudget time s (tape 0) hs) (fun i => tape i.succ)
  exact hrun r (false, s) hs tape

/-- Even an exhausted batch may advance the job index: its unspent budget
is nonnegative, and exhaustion causes no further physical allocation. -/
theorem finish_safe (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (jobs : Fin m → Job n) (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (time : Fin m) (s : RetryState n) (hs : RetrySafe μ active buffer floor jobs time s) :
    Safe μ active buffer floor jobs time.succ (finish s) := by
  by_cases hd : s.1 = true
  · simpa [RetrySafe, hd, Safe, finish] using hs
  · have hf : s.1 = false := Bool.eq_false_iff.mpr hd
    have hs0 : Safe μ active buffer floor jobs time.castSucc s.2 := by
      simpa [RetrySafe, hf] using hs
    refine ⟨hs0.1, hs0.2.1, ?_⟩
    intro i hi
    have hb := hbudget time i hi
    have hmass := hs0.2.2 i hi
    change floor i + tailBudget jobs time.val i < _ at hmass
    rw [tailBudget_succ jobs time i] at hmass
    change floor i + tailBudget jobs (time.val + 1) i < (μ i).real (domain s.2.current.cells)
    linarith

theorem batch_safe (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (hfloor : ∀ i ∈ active, 0 < floor i) (jobs : Fin m → Job n)
    (howner : ∀ j, (jobs j).owner ∈ active)
    (hchecked : ∀ j i, i ∈ active → (jobs j).checked i = true)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (time : Fin m) (s : LoopState n) (hs : Safe μ active buffer floor jobs time.castSucc s)
    (r : ℕ) (tape : Fin r → Circle) :
    Safe μ active buffer floor jobs time.succ (batch policy (jobs time) s tape) :=
  finish_safe μ active buffer floor jobs hbudget time _
    (retry_safe μ policy hpolicy active buffer floor hfloor jobs howner hchecked hbudget time s hs r tape)

end EnvyFreeResearch.Full.RefinedUpperRetrySupply
