import EnvyFreeResearch.Full.RefinedUpperRetryTrace
import EnvyFreeResearch.Full.RefinedUpperRetrySupply

/-! Ordinary-query execution and all-outcome accounting for a finite sequence
of recipient batches. Each batch may retry; only accepted descriptors persist. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperBatchLoop
open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionTrace
  UpperQueryPrograms UpperProgramIteration Chores.QueryProgram UpperStageMeasurable
  UpperRecordedDomain UpperDomainDifference UpperCorrectionPieces RefinedUpperCorrectionRetries RefinedUpperRetryTrace
abbrev Circle := UpperCircular.Circle
variable {n r k : ℕ}

abbrev Draw (n r : ℕ) := Job n × (Fin r → Circle)

def transition (policy : Policy n) (s : LoopState n) (d : Draw n r) : Unit × LoopState n :=
  ((), batch policy d.1 s d.2)

def run (policy : Policy n) (jobs : Fin k → Job n) (s : LoopState n)
    (tape : Fin k → Fin r → Circle) : (Fin k → Unit) × LoopState n :=
  UpperFreshSamples.run (transition policy) k s (fun i => (jobs i, tape i))

def transitionProgram (s : LoopState n) (d : Draw n r) : QProgram n (Unit × LoopState n) :=
  (retryProgram d.1 s d.2).bind (fun result => .returned ((), finish result.2))

def program (jobs : Fin k → Job n) (s : LoopState n) (tape : Fin k → Fin r → Circle) :
    QProgram n ((Fin k → Unit) × LoopState n) :=
  runProgram transitionProgram k s (fun i => (jobs i, tape i))

theorem transitionProgram_executes (policy : Policy n) (s : LoopState n) (d : Draw n r) :
    ∃ trace, Executes (totalPolicy policy) (transitionProgram s d) s.current.history
      (transition policy s d) trace ∧
      (transition policy s d).2.current.history = s.current.history ++ trace := by
  obtain ⟨trace, hr, he⟩ := retryProgram_executes policy d.1 s d.2
  refine ⟨trace, ?_, he⟩
  have h := hr.bind (fun result => Program.returned ((), finish result.2))
    (Executes.returned (oracle := totalPolicy policy)
      ((), finish (retry policy d.1 s d.2).2) (s.current.history ++ trace))
  simpa only [transitionProgram, transition, batch, List.append_nil] using h

theorem program_executes (policy : Policy n) (jobs : Fin k → Job n)
    (s : LoopState n) (tape : Fin k → Fin r → Circle) :
    ∃ trace, Executes (totalPolicy policy) (program jobs s tape) s.current.history
      (run policy jobs s tape) trace ∧
      (run policy jobs s tape).2.current.history = s.current.history ++ trace :=
  runProgram_executes policy (fun s : LoopState n => s.current.history)
    transitionProgram (transition policy) (transitionProgram_executes policy) k s _

theorem query_bound (policy : Policy n) (jobs : Fin k → Job n)
    (s : LoopState n) (tape : Fin k → Fin r → Circle) :
    (run policy jobs s tape).2.current.history.length ≤ s.current.history.length + k * (r * (2 * (n + 1))) :=
  UpperFreshSamples.cost_bound (transition policy) (fun s => s.current.history.length)
    (r * (2 * (n + 1))) (fun state d => batch_query_bound policy d.1 state d.2) k s _

theorem cut_bound (policy : Policy n) (jobs : Fin k → Job n)
    (s : LoopState n) (tape : Fin k → Fin r → Circle) :
    ((run policy jobs s tape).2.current.history.map Prod.fst).countP isCut ≤
      (s.current.history.map Prod.fst).countP isCut + k * (r * 2) :=
  UpperFreshSamples.cost_bound (transition policy)
    (fun s => (s.current.history.map Prod.fst).countP isCut)
    (r * 2) (fun state d => batch_cut_bound policy d.1 state d.2) k s _

theorem program_executes_bounded (policy : Policy n) (jobs : Fin k → Job n)
    (s : LoopState n) (tape : Fin k → Fin r → Circle) :
    ∃ trace, Executes (totalPolicy policy) (program jobs s tape) s.current.history
      (run policy jobs s tape) trace ∧
      (run policy jobs s tape).2.current.history = s.current.history ++ trace ∧
      trace.length ≤ k * (r * (2 * (n + 1))) ∧ (trace.map Prod.fst).countP isCut ≤ k * (r * 2) := by
  obtain ⟨trace, hr, he⟩ := program_executes policy jobs s tape
  have hq := query_bound policy jobs s tape
  have hc := cut_bound policy jobs s tape
  rw [he, List.length_append] at hq
  rw [he, List.map_append, List.countP_append] at hc
  exact ⟨trace, hr, he, by omega, by omega⟩

theorem transition_measurable (policy : Policy n) (hp : MeasurablePolicy policy) :
    Measurable (Function.uncurry (transition (r := r) policy)) :=
  measurable_const.prodMk ((batch_measurable policy hp).comp
    (((measurable_fst.comp measurable_snd).prodMk measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)))

theorem run_measurable (policy : Policy n) (hp : MeasurablePolicy policy) :
    Measurable (fun p : ((Fin k → Job n) × LoopState n) × (Fin k → Fin r → Circle) =>
      run policy p.1.1 p.1.2 p.2) := by
  have ht : Measurable (fun p : ((Fin k → Job n) × LoopState n) × (Fin k → Fin r → Circle) =>
      fun i => (p.1.1 i, p.2 i)) := Measurable.of_eval (fun i =>
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  exact (UpperFreshSamples.run_measurable (transition policy)
    (transition_measurable policy hp) k).comp ((measurable_snd.comp measurable_fst).prodMk ht)

theorem run_consistent (policy : Policy n) (jobs : Fin k → Job n) (origin : List Component)
    (s : LoopState n) (tape : Fin k → Fin r → Circle) (hs : Consistent origin s) :
    Consistent origin (run policy jobs s tape).2 := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih _ _ _ (batch_consistent policy origin (jobs 0) s (tape 0) hs)

theorem batch_stopped (policy : Policy n) (job : Job n) (s : LoopState n)
    (tape : Fin r → Circle) (hs : s.stopped = true) : batch policy job s tape = s := by
  have hrun (r : ℕ) (tape : Fin r → Circle) :
      (UpperFreshSamples.run (attempt policy) r (false, s) (fun i => (job, tape i))).2 = (false, s) := by
    induction r with
    | zero => rfl
    | succ r ih => simpa [UpperFreshSamples.run, attempt, hs] using ih (fun i => tape i.succ)
  unfold batch retry
  rw [hrun]
  cases s
  simp_all [finish]

theorem run_stopped (policy : Policy n) (jobs : Fin k → Job n) (s : LoopState n)
    (tape : Fin k → Fin r → Circle) (hs : s.stopped = true) : (run policy jobs s tape).2 = s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    change (run policy (fun i => jobs i.succ) (batch policy (jobs 0) s (tape 0)) (fun i => tape i.succ)).2 = s
    rw [batch_stopped policy (jobs 0) s (tape 0) hs]
    exact ih _ _ _ hs

theorem run_running_origin (policy : Policy n) (jobs : Fin k → Job n) (s : LoopState n)
    (tape : Fin k → Fin r → Circle) (hs : (run policy jobs s tape).2.stopped = false) :
    s.stopped = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rw [run_stopped policy jobs s tape h, h] at hs
  contradiction

theorem run_accepted_length (policy : Policy n) (jobs : Fin k → Job n) (s : LoopState n)
    (tape : Fin k → Fin r → Circle) (hs : (run policy jobs s tape).2.stopped = false) :
    (run policy jobs s tape).2.accepted.length = s.accepted.length + k := by
  induction k generalizing s with
  | zero => simp [run, UpperFreshSamples.run]
  | succ k ih =>
    change (run policy (fun i => jobs i.succ) (batch policy (jobs 0) s (tape 0))
      (fun i => tape i.succ)).2.stopped = false at hs
    have hb := run_running_origin policy (fun i => jobs i.succ) _ (fun i => tape i.succ) hs
    have hc := batch_accepted_length policy (jobs 0) s (tape 0) hb
    change (run policy (fun i => jobs i.succ) (batch policy (jobs 0) s (tape 0))
      (fun i => tape i.succ)).2.accepted.length = _
    rw [ih _ _ _ hs, hc]
    omega

/-- Literal finite physical outputs of every successful complete batch run. -/
theorem successful_outputs (policy : Policy n) (jobs : Fin k → Job n) (origin : State n)
    (tape : Fin k → Fin r → Circle) (hrun : (run policy jobs (initial origin) tape).2.stopped = false) :
    let final := (run policy jobs (initial origin) tape).2
    (payments origin.cells final.accepted).length = k ∧
      (payments origin.cells final.accepted).Pairwise (fun a b => Disjoint (domain a) (domain b)) ∧
      domain final.current.cells = domain origin.cells \ domain (payments origin.cells final.accepted).flatten := by
  dsimp only
  have hc := run_consistent policy jobs origin.cells (initial origin) tape (initial_consistent origin)
  have hl := run_accepted_length policy jobs (initial origin) tape hrun
  refine ⟨?_, payments_disjoint _ _, ?_⟩
  · rw [payments_length]
    simpa only [initial, List.length_nil, Nat.zero_add] using hl
  · rw [hc, remaining_domain, payments_flatten_domain]

end EnvyFreeResearch.Full.RefinedUpperBatchLoop
