import EnvyFreeResearch.Full.UpperCorrectionRecording
import EnvyFreeResearch.Full.RefinedUpperBatchLoop

/-! Every accepted endpoint and every rejected attempt's answers survive in
the final history of the concrete retry executor. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperRepairFinalCache
open UpperRecordedDomain UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSupply
  UpperCorrectionRecording UpperCircularStage RefinedUpperCorrectionRetries RefinedUpperRetrySupply
variable {n k r : ℕ}

theorem batch_recorded (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (hfloor : ∀ i ∈ active, 0 < floor i) (jobs : Fin k → Job n)
    (howner : ∀ j, (jobs j).owner ∈ active)
    (hchecked : ∀ j i, i ∈ active → (jobs j).checked i = true)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (time : Fin k) (s : LoopState n) (tape : Fin r → UpperCircular.Circle)
    (hs : Safe μ active buffer floor jobs time.castSucc s)
    (hrecords : RecordedEndpoints s.accepted s.current.history) :
    Safe μ active buffer floor jobs time.succ (batch policy (jobs time) s tape) ∧
      s.current.history ⊆ (batch policy (jobs time) s tape).current.history ∧
      RecordedEndpoints (batch policy (jobs time) s tape).accepted
        (batch policy (jobs time) s tape).current.history := by
  let Inv (state : RetryState n) := RetrySafe μ active buffer floor jobs time state ∧
    s.current.history ⊆ state.2.current.history ∧
      RecordedEndpoints state.2.accepted state.2.current.history
  have hstep (state : RetryState n) (d : UpperCircular.Circle) (hi : Inv state) :
      Inv (attempt policy state (jobs time, d)).2 := by
    refine ⟨attempt_safe μ policy hp active buffer floor hfloor jobs howner hchecked hbudget
      time state d hi.1, ?_⟩
    by_cases hskip : (state.1 || state.2.stopped) = true
    · simpa only [attempt, hskip, ite_true] using hi.2
    · have ho : state.2.stopped = false := by
        cases h1 : state.1 <;> cases h2 : state.2.stopped <;> simp_all
      have hsafe : Safe μ active buffer floor jobs
          (if state.1 then time.succ else time.castSucc) state.2 := hi.1
      have hmass := safe_mass μ active buffer floor jobs _ state.2 hsafe hbudget
        (jobs time).owner (howner time)
      have hr := step_recorded μ policy hp state.2 hsafe.1 (jobs time, d)
        (fun _ => (hfloor _ (howner time)).trans hmass) hi.2.2
      have hext : s.current.history ⊆ (step policy state.2 (jobs time, d)).2.current.history :=
        fun _ hx => hr.1 (hi.2.1 hx)
      simpa only [attempt, hskip, Bool.false_eq_true, ite_false, update, reopen] using
        And.intro hext hr.2
  have hrun (r : ℕ) (state : RetryState n) (hi : Inv state)
      (draw : Fin r → UpperCircular.Circle) :
      Inv (UpperFreshSamples.run (attempt policy) r state (fun i => (jobs time, draw i))).2 := by
    induction r generalizing state with
    | zero => exact hi
    | succ r ih => exact ih _ (hstep state (draw 0) hi) (fun i => draw i.succ)
  have h := hrun r (false, s) ⟨hs, Subset.rfl, hrecords⟩ tape
  exact ⟨finish_safe μ active buffer floor jobs hbudget time _ h.1, h.2⟩

theorem batch_run_invariant (policy : Policy n) (jobs : Fin k → Job n)
    (Inv : Fin (k + 1) → LoopState n → Prop)
    (hstep : ∀ i state (draw : Fin r → UpperCircular.Circle), Inv i.castSucc state →
      Inv i.succ (batch policy (jobs i) state draw))
    (s : LoopState n) (tape : Fin k → Fin r → UpperCircular.Circle) (hs : Inv 0 s) :
    Inv (Fin.last k) (RefinedUpperBatchLoop.run policy jobs s tape).2 := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih =>
    exact ih (fun i => jobs i.succ) (fun i => Inv i.succ)
      (fun i state draw h => hstep i.succ state draw h)
      (batch policy (jobs 0) s (tape 0)) (fun i => tape i.succ) (hstep 0 s (tape 0) hs)

theorem run_recorded (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (hfloor : ∀ i ∈ active, 0 < floor i) (jobs : Fin k → Job n)
    (howner : ∀ j, (jobs j).owner ∈ active)
    (hchecked : ∀ j i, i ∈ active → (jobs j).checked i = true)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (s : LoopState n) (tape : Fin k → Fin r → UpperCircular.Circle)
    (hs : Safe μ active buffer floor jobs 0 s)
    (hrecords : RecordedEndpoints s.accepted s.current.history) :
    Safe μ active buffer floor jobs (Fin.last k) (RefinedUpperBatchLoop.run policy jobs s tape).2 ∧
      s.current.history ⊆ (RefinedUpperBatchLoop.run policy jobs s tape).2.current.history ∧
      RecordedEndpoints (RefinedUpperBatchLoop.run policy jobs s tape).2.accepted
        (RefinedUpperBatchLoop.run policy jobs s tape).2.current.history := by
  apply batch_run_invariant policy jobs
    (fun time state => Safe μ active buffer floor jobs time state ∧
      s.current.history ⊆ state.current.history ∧ RecordedEndpoints state.accepted state.current.history)
    _ s tape ⟨hs, Subset.rfl, hrecords⟩
  intro time state draw hi
  have hr := batch_recorded μ policy hp active buffer floor hfloor jobs howner hchecked hbudget
    time state draw hi.1 hi.2.2
  exact ⟨hr.1, (fun _ hx => hr.2.1 (hi.2.1 hx)), hr.2.2⟩

end EnvyFreeResearch.Full.RefinedUpperRepairFinalCache
