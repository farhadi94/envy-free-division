import EnvyFreeResearch.Full.RefinedUpperCorrectionChance
import EnvyFreeResearch.Full.RefinedUpperRetryFailure
import EnvyFreeResearch.Full.RefinedUpperRetryTrace
import EnvyFreeResearch.Full.RefinedUpperRetrySupply

/-! The actual accepted endpoint history remains good until the first bad
proposal. A rejected attempt preserves both the physical geometry and index. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperCorrectionGood
open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionTrace
  UpperRecordedDomain RefinedUpperCorrectionRetries RefinedUpperCorrectionChance
  RefinedUpperRetryFailure UpperCorrectionSupply
variable {n k : ℕ}

def HistoryGood (origin : List Component) (bad : Set ℝ) (time : ℕ) (s : LoopState n) : Prop :=
  Consistent origin s ∧ s.accepted.length = time ∧
    ∀ rec ∈ s.accepted, rec.first ∉ bad ∧ rec.last ∉ bad

theorem initial_good (s : State n) (bad : Set ℝ) : HistoryGood s.cells bad 0 (initial s) := by
  exact ⟨rfl, rfl, by simp [initial]⟩

theorem next_rejected (policy : Policy n) (job : Job n) (origin : List Component)
    (bad : Set ℝ) (time : ℕ) (s : LoopState n) (d : UpperCircular.Circle)
    (hs : HistoryGood origin bad time s) (ho : s.stopped = false)
    (hr : (step policy s (job, d)).1 = true) :
    HistoryGood origin bad time (next policy job s d) := by
  have ha : accepts job s.current (execute policy s.current job.owner job.deficit d).2 = false := by
    by_contra hn
    have ht : accepts job s.current (execute policy s.current job.owner job.deficit d).2 = true :=
      Bool.eq_true_of_not_eq_false hn
    simp [step, ho, ht] at hr
  refine ⟨step_consistent policy origin s (job, d) hs.1, ?_, ?_⟩
  · simpa [next, step, ho, ha, reopen] using hs.2.1
  · simpa [next, step, ho, ha, reopen] using hs.2.2

theorem next_accepted (policy : Policy n) (job : Job n) (origin : List Component)
    (bad : Set ℝ) (time : ℕ) (s : LoopState n) (d : UpperCircular.Circle)
    (hs : HistoryGood origin bad time s) (ho : s.stopped = false)
    (hb : endpointBad policy job bad s d = false)
    (hr : (step policy s (job, d)).1 = false) :
    HistoryGood origin bad (time + 1) (next policy job s d) := by
  have ha : accepts job s.current (execute policy s.current job.owner job.deficit d).2 = true := by
    by_contra hn
    have hf : accepts job s.current (execute policy s.current job.owner job.deficit d).2 = false :=
      Bool.eq_false_iff.mpr hn
    simp [step, ho, hf] at hr
  have he : (descriptor policy s.current job.owner job.deficit d).first ∉ bad ∧
      (descriptor policy s.current job.owner job.deficit d).last ∉ bad := by
    simpa [endpointBad, ho] using hb
  refine ⟨step_consistent policy origin s (job, d) hs.1, ?_, ?_⟩
  · simp [next, step, ho, ha, reopen, hs.2.1]
  · intro rec hrec
    have hdesc : (execute policy s.current job.owner job.deficit d).1 =
        descriptor policy s.current job.owner job.deficit d := rfl
    have hm : rec ∈ s.accepted ∨ rec = descriptor policy s.current job.owner job.deficit d := by
      simpa [next, step, ho, ha, reopen, hdesc] using hrec
    rcases hm with hm | rfl
    · exact hs.2.2 rec hm
    · exact he

theorem supply_next (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (hfloor : ∀ i ∈ active, 0 < floor i) (jobs : Fin k → Job n)
    (howner : ∀ j, (jobs j).owner ∈ active)
    (hchecked : ∀ j i, i ∈ active → (jobs j).checked i = true)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (time : Fin k) (s : LoopState n) (d : UpperCircular.Circle)
    (hs : Safe μ active buffer floor jobs time.castSucc s) (ho : s.stopped = false) :
    Safe μ active buffer floor jobs
      (if (step policy s (jobs time, d)).1 then time.castSucc else time.succ)
      (next policy (jobs time) s d) := by
  have h := RefinedUpperRetrySupply.attempt_safe μ policy hp active buffer floor hfloor jobs
    howner hchecked hbudget time (false, s) d hs
  cases hr : (step policy s (jobs time, d)).1 <;>
    simpa [RefinedUpperRetrySupply.RetrySafe, attempt, ho, update, next, hr] using h

end EnvyFreeResearch.Full.RefinedUpperCorrectionGood
