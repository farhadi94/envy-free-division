import EnvyFreeResearch.Full.UpperCorrectionLoopProgram

/-!
# Retrying a physical circular correction

An unsuccessful attempt restores the pre-attempt cells, retains every oracle
answer, and permits another fresh attempt. A successful attempt ends this
recipient's batch. Exhausting the batch stops the encompassing Repair trial.
This is an ordinary-query implementation, not an acceptance-oracle interface.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.RefinedUpperCorrectionRetries

open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop
  UpperQueryPrograms UpperProgramIteration Chores.QueryProgram ProtocolMeasurable UpperStageMeasurable

abbrev Circle := UpperCircular.Circle

abbrev RetryState (n : ℕ) := Bool × LoopState n

/-- Reopen a rejected attempt without changing either cells or query history. -/
def reopen {n : ℕ} (s : LoopState n) : LoopState n :=
  ⟨s.current, false, s.accepted⟩

def update {n : ℕ} (r : Bool × LoopState n) : Bool × RetryState n :=
  (r.1, !r.1, reopen r.2)

def attempt {n : ℕ} (policy : Policy n) (s : RetryState n)
    (draw : Job n × Circle) : Bool × RetryState n :=
  if s.1 || s.2.stopped then (false, s)
  else update (step policy s.2 draw)

def retry {n m : ℕ} (policy : Policy n) (job : Job n) (s : LoopState n)
    (tape : Fin m → Circle) : (Fin m → Bool) × RetryState n :=
  UpperFreshSamples.run (attempt policy) m (false, s) (fun i => (job, tape i))

def finish {n : ℕ} (s : RetryState n) : LoopState n :=
  ⟨s.2.current, s.2.stopped || !s.1, s.2.accepted⟩

def batch {n m : ℕ} (policy : Policy n) (job : Job n) (s : LoopState n)
    (tape : Fin m → Circle) : LoopState n := finish (retry policy job s tape).2

variable {n : ℕ}

theorem attempt_query_bound (policy : Policy n) (s : RetryState n) (draw : Job n × Circle) :
    (attempt policy s draw).2.2.current.history.length ≤
      s.2.current.history.length + 2 * (n + 1) := by
  unfold attempt
  split_ifs
  · simp only
    omega
  · exact step_query_bound policy s.2 draw

theorem attempt_cut_bound (policy : Policy n) (s : RetryState n) (draw : Job n × Circle) :
    ((attempt policy s draw).2.2.current.history.map Prod.fst).countP isCut ≤
      (s.2.current.history.map Prod.fst).countP isCut + 2 := by
  unfold attempt
  split_ifs
  · simp only
    omega
  · exact step_cut_bound policy s.2 draw

theorem batch_query_bound {m : ℕ} (policy : Policy n) (job : Job n) (s : LoopState n)
    (tape : Fin m → Circle) :
    (batch policy job s tape).current.history.length ≤
      s.current.history.length + m * (2 * (n + 1)) :=
  UpperFreshSamples.cost_bound (attempt policy) (fun s => s.2.current.history.length)
    (2 * (n + 1)) (attempt_query_bound policy) m (false, s) _

theorem batch_cut_bound {m : ℕ} (policy : Policy n) (job : Job n) (s : LoopState n)
    (tape : Fin m → Circle) :
    ((batch policy job s tape).current.history.map Prod.fst).countP isCut ≤
      (s.current.history.map Prod.fst).countP isCut + m * 2 :=
  UpperFreshSamples.cost_bound (attempt policy)
    (fun s => (s.2.current.history.map Prod.fst).countP isCut)
    2 (attempt_cut_bound policy) m (false, s) _

/-- Rejected attempts cannot create physical holes or accepted boundaries. -/
theorem rejected_restores (policy : Policy n) (s : RetryState n) (draw : Job n × Circle)
    (h : (attempt policy s draw).1 = true) :
    (attempt policy s draw).2.2.current.cells = s.2.current.cells ∧
    (attempt policy s draw).2.2.accepted = s.2.accepted ∧
    (attempt policy s draw).2.1 = false ∧
    (attempt policy s draw).2.2.stopped = false := by
  unfold attempt at h ⊢
  split_ifs at h ⊢ <;> simp_all [update, reopen, step]
  split_ifs at h ⊢ <;> simp_all

/-- The physical invariant survives failed attempts as well as successful ones. -/
theorem attempt_wellFormed (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (s : RetryState n) (hs : WellFormed μ s.2.current) (draw : Job n × Circle)
    (hpositive : s.2.stopped = false →
      0 < (μ draw.1.owner).real (UpperRecordedDomain.domain s.2.current.cells)) :
    WellFormed μ (attempt policy s draw).2.2.current := by
  unfold attempt
  split_ifs
  · exact hs
  · exact step_wellFormed μ policy hpolicy s.2 hs draw hpositive

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem reopen_measurable : Measurable (reopen (n := n)) :=
  loop_mk_measurable _ _ _ loop_current_measurable measurable_const loop_accepted_measurable

theorem update_measurable : Measurable (update (n := n)) :=
  measurable_fst.prodMk (((measurable_of_countable Bool.not).comp measurable_fst).prodMk (reopen_measurable.comp measurable_snd))

theorem attempt_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy) :
    Measurable (Function.uncurry (attempt policy)) := by
  have hs : Measurable (fun p : RetryState n × (Job n × Circle) => p.1.1 || p.1.2.stopped) :=
    (measurable_of_countable (fun b : Bool × Bool => b.1 || b.2)).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (loop_stopped_measurable.comp (measurable_snd.comp measurable_fst)))
  have ht : Measurable (fun p : RetryState n × (Job n × Circle) =>
      update (step policy p.1.2 p.2)) := update_measurable.comp ((step_measurable policy hpolicy).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact (measurable_const.prodMk measurable_fst).ite
    (measurableSet_eq_fun hs measurable_const) ht

theorem retry_measurable {m : ℕ} (policy : Policy n) (hpolicy : MeasurablePolicy policy) :
    Measurable (fun p : (Job n × LoopState n) × (Fin m → Circle) =>
      retry policy p.1.1 p.1.2 p.2) := by
  have ht : Measurable (fun p : (Job n × LoopState n) × (Fin m → Circle) =>
      fun i => (p.1.1, p.2 i)) := Measurable.of_eval (fun i =>
    (measurable_fst.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact (UpperFreshSamples.run_measurable (attempt policy)
    (attempt_measurable policy hpolicy) m).comp
    ((measurable_const.prodMk (measurable_snd.comp measurable_fst)).prodMk ht)

theorem finish_measurable : Measurable (finish (n := n)) :=
  loop_mk_measurable _ _ _ (loop_current_measurable.comp measurable_snd)
    ((measurable_of_countable (fun b : Bool × Bool => b.1 || !b.2)).comp
      ((loop_stopped_measurable.comp measurable_snd).prodMk measurable_fst))
    (loop_accepted_measurable.comp measurable_snd)

theorem batch_measurable {m : ℕ} (policy : Policy n) (hpolicy : MeasurablePolicy policy) :
    Measurable (fun p : (Job n × LoopState n) × (Fin m → Circle) =>
      batch policy p.1.1 p.1.2 p.2) :=
  finish_measurable.comp (measurable_snd.comp (retry_measurable policy hpolicy))

end Measurability

/-- Literal ordinary-query program for one attempt. -/
def attemptProgram (s : RetryState n) (draw : Job n × Circle) :
    QProgram n (Bool × RetryState n) :=
  if s.1 || s.2.stopped then .returned (false, s)
  else (UpperCorrectionLoopProgram.stepProgram s.2 draw).bind
    (fun r => .returned (update r))

def retryProgram {m : ℕ} (job : Job n) (s : LoopState n) (tape : Fin m → Circle) :
    QProgram n ((Fin m → Bool) × RetryState n) :=
  runProgram attemptProgram m (false, s) (fun i => (job, tape i))

theorem attemptProgram_executes (policy : Policy n) (s : RetryState n) (draw : Job n × Circle) :
    ∃ trace, Executes (totalPolicy policy) (attemptProgram s draw) s.2.current.history
      (attempt policy s draw) trace ∧
      (attempt policy s draw).2.2.current.history = s.2.current.history ++ trace := by
  by_cases hs : (s.1 || s.2.stopped) = true
  · refine ⟨[], ?_, ?_⟩
    · simpa only [attemptProgram, attempt, hs, ite_true] using
        (Executes.returned (oracle := totalPolicy policy) (false, s) s.2.current.history)
    · simp [attempt, hs]
  · obtain ⟨trace, hr, he⟩ := UpperCorrectionLoopProgram.stepProgram_executes policy s.2 draw
    refine ⟨trace, ?_, ?_⟩
    · have ht := hr.bind (fun r => Program.returned (update r))
        (Executes.returned (oracle := totalPolicy policy) (update (step policy s.2 draw))
          (s.2.current.history ++ trace))
      simpa only [attemptProgram, attempt, hs, Bool.false_eq_true, ite_false, List.append_nil] using ht
    · simpa only [attempt, hs, Bool.false_eq_true, ite_false, update, reopen] using he

theorem retryProgram_executes {m : ℕ} (policy : Policy n) (job : Job n)
    (s : LoopState n) (tape : Fin m → Circle) :
    ∃ trace, Executes (totalPolicy policy) (retryProgram job s tape) s.current.history
      (retry policy job s tape) trace ∧
      (retry policy job s tape).2.2.current.history = s.current.history ++ trace :=
  runProgram_executes policy (fun s : RetryState n => s.2.current.history)
    attemptProgram (attempt policy) (attemptProgram_executes policy) m (false, s) _

/-- The cap counts rejected attempts, including their observer evaluations. -/
theorem retryProgram_executes_bounded {m : ℕ} (policy : Policy n) (job : Job n)
    (s : LoopState n) (tape : Fin m → Circle) :
    ∃ trace, Executes (totalPolicy policy) (retryProgram job s tape) s.current.history
      (retry policy job s tape) trace ∧
      (retry policy job s tape).2.2.current.history = s.current.history ++ trace ∧
      trace.length ≤ m * (2 * (n + 1)) ∧ (trace.map Prod.fst).countP isCut ≤ m * 2 := by
  obtain ⟨trace, hr, he⟩ := retryProgram_executes policy job s tape
  have hq := batch_query_bound policy job s tape
  have hc := batch_cut_bound policy job s tape
  change (retry policy job s tape).2.2.current.history.length ≤ _ at hq
  change ((retry policy job s tape).2.2.current.history.map Prod.fst).countP isCut ≤ _ at hc
  rw [he, List.length_append] at hq
  rw [he, List.map_append, List.countP_append] at hc
  exact ⟨trace, hr, he, by omega, by omega⟩

end EnvyFreeResearch.Full.RefinedUpperCorrectionRetries
