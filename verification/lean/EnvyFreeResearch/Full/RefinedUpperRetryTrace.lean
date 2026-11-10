import EnvyFreeResearch.Full.RefinedUpperCorrectionRetries
import EnvyFreeResearch.Full.UpperCorrectionTrace

/-! Accepted-descriptor accounting for the concrete retry implementation. -/
noncomputable section
open Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperRetryTrace
open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionTrace
  UpperRecordedDomain RefinedUpperCorrectionRetries
abbrev Circle := UpperCircular.Circle
variable {n : ℕ}

theorem attempt_consistent (policy : Policy n) (origin : List Component) (s : RetryState n)
    (draw : Job n × Circle) (hs : Consistent origin s.2) :
    Consistent origin (attempt policy s draw).2.2 := by
  unfold attempt
  split_ifs
  · exact hs
  · exact step_consistent policy origin s.2 draw hs

/-- Each recipient appends exactly one record if and only if it succeeds.
Failed attempts never enter the physical descriptor list. -/
theorem attempt_length (policy : Policy n) (s : RetryState n) (draw : Job n × Circle)
    (base : ℕ) (hs : s.2.accepted.length = base + if s.1 then 1 else 0) :
    (attempt policy s draw).2.2.accepted.length =
      base + if (attempt policy s draw).2.1 then 1 else 0 := by
  by_cases hd : s.1 = true
  · simpa [attempt, hd] using hs
  · have hf : s.1 = false := Bool.eq_false_iff.mpr hd
    by_cases hstop : s.2.stopped = true
    · simpa [attempt, hstop] using hs
    · have ho : s.2.stopped = false := Bool.eq_false_iff.mpr hstop
      simp only [hf, Bool.false_eq_true, ite_false, Nat.add_zero] at hs
      simp only [attempt, hf, ho, Bool.false_or, Bool.false_eq_true, ite_false,
        update, reopen, step]
      by_cases ha : accepts draw.1 s.2.current
        (execute policy s.2.current draw.1.owner draw.1.deficit draw.2).2 = true <;> simp [ha, hs]

theorem retry_consistent_length {r : ℕ} (policy : Policy n) (origin : List Component)
    (job : Job n) (s : LoopState n) (tape : Fin r → Circle)
    (hs : Consistent origin s) :
    Consistent origin (retry policy job s tape).2.2 ∧
      (retry policy job s tape).2.2.accepted.length =
        s.accepted.length + if (retry policy job s tape).2.1 then 1 else 0 := by
  have hrun (r : ℕ) (state : RetryState n) (tape : Fin r → Circle)
      (hc : Consistent origin state.2)
      (hl : state.2.accepted.length = s.accepted.length + if state.1 then 1 else 0) :
      Consistent origin (UpperFreshSamples.run (attempt policy) r state (fun i => (job, tape i))).2.2 ∧
      (UpperFreshSamples.run (attempt policy) r state (fun i => (job, tape i))).2.2.accepted.length =
        s.accepted.length + if (UpperFreshSamples.run (attempt policy) r state (fun i => (job, tape i))).2.1 then 1 else 0 := by
    induction r generalizing state with
    | zero => exact ⟨hc, hl⟩
    | succ r ih =>
      exact ih _ (fun i => tape i.succ)
        (attempt_consistent policy origin state (job, tape 0) hc)
        (attempt_length policy state (job, tape 0) s.accepted.length hl)
  exact hrun r (false, s) tape hs (by simp)

theorem batch_consistent {r : ℕ} (policy : Policy n) (origin : List Component)
    (job : Job n) (s : LoopState n) (tape : Fin r → Circle)
    (hs : Consistent origin s) : Consistent origin (batch policy job s tape) :=
  (retry_consistent_length policy origin job s tape hs).1

theorem batch_accepted_length {r : ℕ} (policy : Policy n) (job : Job n)
    (s : LoopState n) (tape : Fin r → Circle)
    (hr : (batch policy job s tape).stopped = false) :
    (batch policy job s tape).accepted.length = s.accepted.length + 1 := by
  have hd : (retry policy job s tape).2.1 = true := by
    by_contra h
    have hf : (retry policy job s tape).2.1 = false := Bool.eq_false_iff.mpr h
    simp [batch, finish, hf] at hr
  have hrun (r : ℕ) (state : RetryState n) (tape : Fin r → Circle)
      (hl : state.2.accepted.length = s.accepted.length + if state.1 then 1 else 0) :
      (UpperFreshSamples.run (attempt policy) r state (fun i => (job, tape i))).2.2.accepted.length =
        s.accepted.length + if (UpperFreshSamples.run (attempt policy) r state (fun i => (job, tape i))).2.1 then 1 else 0 := by
    induction r generalizing state with
    | zero => exact hl
    | succ r ih =>
      exact ih _ (fun i => tape i.succ)
        (attempt_length policy state (job, tape 0) s.accepted.length hl)
  have h := hrun r (false, s) tape (by simp)
  change (retry policy job s tape).2.2.accepted.length =
    s.accepted.length + if (retry policy job s tape).2.1 then 1 else 0 at h
  simpa [batch, finish, hd] using h

theorem attempt_domain_subset (policy : Policy n) (s : RetryState n) (draw : Job n × Circle) :
    domain (attempt policy s draw).2.2.current.cells ⊆ domain s.2.current.cells := by
  unfold attempt
  split_ifs
  · exact Subset.rfl
  · exact step_domain_subset policy s.2 draw

theorem batch_domain_subset {r : ℕ} (policy : Policy n) (job : Job n)
    (s : LoopState n) (tape : Fin r → Circle) :
    domain (batch policy job s tape).current.cells ⊆ domain s.current.cells := by
  have hrun (r : ℕ) (state : RetryState n) (tape : Fin r → Circle) :
      domain (UpperFreshSamples.run (attempt policy) r state (fun i => (job, tape i))).2.2.current.cells ⊆
        domain state.2.current.cells := by
    induction r generalizing state with
    | zero => exact Subset.rfl
    | succ r ih =>
      exact (ih _ (fun i => tape i.succ)).trans (attempt_domain_subset policy state (job, tape 0))
  exact hrun r (false, s) tape

end EnvyFreeResearch.Full.RefinedUpperRetryTrace
