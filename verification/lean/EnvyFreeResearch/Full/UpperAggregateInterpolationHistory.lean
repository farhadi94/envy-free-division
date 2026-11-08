import EnvyFreeResearch.Full.UpperAggregateInterpolationStream

/-! Both charged descriptor endpoints are present in the actual next oracle
history, whether that proposal is accepted or rejected. -/

noncomputable section

open MeasureTheory

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperCorrectionExecution UpperCorrectionLoop UpperCircularStage UpperDomainDifference
  UpperRecordedDomain UpperUnionCircular UpperEndpointCache Chores

variable {n : ℕ}

theorem open_step_history (policy : Policy n) (state : LoopState n) (job : Job n) (start : Start)
    (hopen : state.stopped = false) :
    (UpperCorrectionLoop.step policy state (job, start)).2.current.history =
      (execute policy state.current job.owner job.deficit start).2.history := by
  simp only [UpperCorrectionLoop.step, hopen, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> rfl

/-- The charged points are actual recorded endpoints, including boundary
reuse. No new recording query is assumed for a reused endpoint. -/
theorem charged_endpoints_recorded (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (state : LoopState n) (hstate : WellFormed μ state.current) (job : Job n)
    (hpositive : 0 < (μ job.owner).real (domain state.current.cells))
    (start : Start) (hopen : state.stopped = false) :
    (∀ i, ∃ answer, (IntervalOracle.Query.eval i 0
      (descriptor policy state.current job.owner job.deficit start).first, answer) ∈
        (UpperCorrectionLoop.step policy state (job, start)).2.current.history) ∧
    (∀ i, ∃ answer, (IntervalOracle.Query.eval i 0
      (descriptor policy state.current job.owner job.deficit start).last, answer) ∈
        (UpperCorrectionLoop.step policy state (job, start)).2.current.history) := by
  rw [open_step_history policy state job start hopen]
  have h := circular_history μ policy hpolicy state.current.history job.owner (values state.current job.owner)
    state.current.cells hstate.2.1 hstate.2.2.1 hstate.2.2.2
    (values_correct μ state.current hstate job.owner) hpositive
    (amount job.deficit ((μ job.owner).real (domain state.current.cells))) start
  simpa only [descriptor, execute, recordedCorrection, total_correct μ state.current hstate job.owner]
    using And.intro h.2.2.1 h.2.2.2

/-- The first rejecting proposal advances the actual oracle history exactly
as a successful proposal does; only its physical domain update is rolled back. -/
theorem charged_history_extends (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (state : LoopState n) (hstate : WellFormed μ state.current) (job : Job n)
    (hpositive : 0 < (μ job.owner).real (domain state.current.cells))
    (start : Start) (hopen : state.stopped = false) :
    state.current.history ⊆ (UpperCorrectionLoop.step policy state (job, start)).2.current.history := by
  rw [open_step_history policy state job start hopen]
  exact (execute_history μ policy hpolicy state.current hstate job.owner hpositive job.deficit start).2

end EnvyFreeResearch.Full.UpperAggregateInterpolation
