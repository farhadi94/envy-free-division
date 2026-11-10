import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolActual
import EnvyFreeResearch.Full.UpperSnapshotProtocolZeroMeasurable

/-! The last candidate check uses only caches. On well-formed recorded
states it proves exactly the preconditions needed by the following Repair. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperDomainDifference UpperRepairPreparationChecks
variable {n k : ℕ} {X : Type} [MeasurableSpace X]

theorem candidateSafe_iff (chores : Bool) (active : Fin k → Fin n)
    (old : Fin k → State n) (buffer : State n) :
    candidateSafe chores active old buffer = true ↔
    (∀ i, 0 < total buffer (active i)) ∧ ∀ i j,
      if chores then total (old i) (active i) - total (old j) (active i) ≤
        RefinedUpperRepair.nearError n * total buffer (active i)
      else total (old j) (active i) - total (old i) (active i) ≤
        RefinedUpperRepair.nearError n * total buffer (active i) := decide_eq_true_iff

theorem candidateSafe_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (chores : Bool) (active : Fin k → Fin n)
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (buffer : State n) (hbuffer : WellFormed μ buffer) :
    candidateSafe chores active old buffer = true ↔
      (∀ i, 0 < (μ (active i)).real (domain buffer.cells)) ∧
      Near chores μ active buffer old (RefinedUpperRepair.nearError n) := by
  rw [candidateSafe_iff]
  simp only [total_correct μ _ hbuffer,total_correct μ _ (hold _)]
  cases chores <;> rfl

theorem candidateSafe_measurable (chores : Bool) (active : Fin k → Fin n)
    (old : X → Fin k → State n) (buffer : X → State n)
    (ho : Measurable old) (hb : Measurable buffer) :
    Measurable (fun x => candidateSafe chores active (old x) (buffer x)) := by
  apply decide_measurable
  have hv (i j : Fin k) : Measurable (fun x => total (old x j) (active i)) :=
    total_measurable _ _ ((measurable_pi_apply j).comp ho) measurable_const
  have hr (i : Fin k) : Measurable (fun x => total (buffer x) (active i)) :=
    total_measurable _ _ hb measurable_const
  simp only [setOf_and,setOf_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const (hr i))
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    cases chores
    · exact measurableSet_le ((hv i j).sub (hv i i)) (measurable_const.mul (hr i))
    · exact measurableSet_le ((hv i i).sub (hv i j)) (measurable_const.mul (hr i))

theorem restoreRejected_history (origin : State n) (out : PhysicalResult n k) :
    (restoreRejected origin out).2.1.history = out.2.1.history := by
  unfold restoreRejected
  split <;> rfl

theorem restoreRejected_success (origin : State n) (out : PhysicalResult n k) :
    (restoreRejected origin out).2.2 = false ↔ out.2.2 = false := by
  unfold restoreRejected
  split <;> simp_all [rejectWhole]
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
