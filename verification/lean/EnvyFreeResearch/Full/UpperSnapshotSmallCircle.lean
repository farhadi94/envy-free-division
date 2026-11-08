import EnvyFreeResearch.Full.UpperSnapshotSmallMeasurable
import EnvyFreeResearch.Full.UpperSnapshotSmallTargets

/-! Auditable shared-circle partition façade for the Snapshot zero and small
branches. The first positive-cell choice and candidate repetition are separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperCircularStage UpperStageMeasurable Chores
variable {n J : ℕ}

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
include hpolicy hgood hpositive

/-- One actual shared-circle run returns a complete literal partition, exact
cutter increments, cached states, and a full history charging every endpoint. -/
theorem shared_circle_partition (hJ : 0 < J) (q : Fin (J + 1) → I)
    (hq : StrictMono q) (hq0 : q 0 = 0) (hq1 : q (Fin.last J) = 1) (start : Circle) :
    WellFormed μ (partitionRun policy origin cutter q start).2 ∧
    (∀ j, WellFormed μ (partState hJ policy origin cutter q start j)) ∧
    (⋃ j, domain (partState hJ policy origin cutter q start j).cells) = domain origin.cells ∧
    Pairwise (fun i j => Disjoint (domain (partState hJ policy origin cutter q start i).cells)
      (domain (partState hJ policy origin cutter q start j).cells)) ∧
    (∀ j, total (partState hJ policy origin cutter q start j) cutter =
      ((q j.succ : ℝ) - q j.castSucc) * (μ cutter).real (domain origin.cells)) ∧
    origin.history ⊆ (partitionRun policy origin cutter q start).2.history ∧
    (∀ j, HasEndpoint (partitionRun policy origin cutter q start).2.history
      ((partitionRun policy origin cutter q start).1 j)) ∧
    (partitionRun policy origin cutter q start).2.history.length ≤ origin.history.length + J * (n + 1) ∧
    ((partitionRun policy origin cutter q start).2.history.map Prod.fst).countP isCut ≤
      (origin.history.map Prod.fst).countP isCut + J := by
  have hp := actual_partition μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1 hq start
  have hr := execute_records μ policy hpolicy origin hgood cutter hpositive (shifts q) start
  refine ⟨execute_wellFormed μ policy hpolicy origin hgood cutter hpositive _ _,
    partState_wellFormed μ hJ policy hpolicy origin hgood cutter hpositive q start, ?_, ?_, ?_,
    hr.1, fun j => (hr.2 j).2, execute_query_bound _ _ _ _ _, execute_cut_bound _ _ _ _ _⟩
  · simpa only [partState_domain] using hp.1
  · simpa only [partState_domain] using hp.2
  · intro j
    rw [partState_cached μ hJ policy hpolicy origin hgood cutter hpositive,
      actual_part_mass μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1 hq]

theorem equal_partition_value (hJ : 0 < J) (start : Circle) (j : Fin J) :
    total (partState hJ policy origin cutter (equalTargets J) start j) cutter =
      (μ cutter).real (domain origin.cells) / J := by
  rw [partState_cached μ hJ policy hpolicy origin hgood cutter hpositive,
    actual_part_mass μ policy hpolicy origin hgood cutter hpositive hJ _
      (equalTargets_zero hJ) (equalTargets_last hJ) (equalTargets_strict hJ), equalTargets_increment hJ]
  ring

theorem remainder_partition_value (hJ : 0 < J) (t : ℝ) (ht : 0 < t) (hfit : (J : ℝ) * t < 1)
    (start : Circle) (j : Fin J) (hj : j.val + 1 < J) :
    total (partState hJ policy origin cutter (remainderTargets J t) start j) cutter =
      t / (1 - t) * (μ cutter).real (domain origin.cells) := by
  rw [partState_cached μ hJ policy hpolicy origin hgood cutter hpositive,
    actual_part_mass μ policy hpolicy origin hgood cutter hpositive hJ _
      (remainderTargets_zero hJ t ht hfit) (remainderTargets_last t) (remainderTargets_strict hJ t ht hfit),
    remainderTargets_increment hJ t ht hfit j hj]

theorem remainder_buffer_value (hJ : 0 < J) (t : ℝ) (ht : 0 < t) (hfit : (J : ℝ) * t < 1)
    (start : Circle) (j : Fin J) (hj : j.val + 1 = J) :
    total (partState hJ policy origin cutter (remainderTargets J t) start j) cutter =
      (1 - J * t) / (1 - t) * (μ cutter).real (domain origin.cells) := by
  rw [partState_cached μ hJ policy hpolicy origin hgood cutter hpositive,
    actual_part_mass μ policy hpolicy origin hgood cutter hpositive hJ _
      (remainderTargets_zero hJ t ht hfit) (remainderTargets_last t) (remainderTargets_strict hJ t ht hfit),
    remainderTargets_final_increment hJ t ht hfit j hj]

/-- The second group's first endowment has the required signed conditional
mean for every fixed complete preceding history and recorded remainder. -/
theorem remainder_first_signed_expectation (hmeas : MeasurablePolicy policy) (hJ : 2 ≤ J)
    (t : ℝ) (ht : 0 < t) (hfit : (J : ℝ) * t < 1) (signed : SignedMeasure ℝ) :
    (∫ start, signed (domain (partState (by omega) policy origin cutter
      (remainderTargets J t) start ⟨0, by omega⟩).cells) ∂(volume : Measure Circle)) =
      t / (1 - t) * signed (domain origin.cells) := by
  simp only [partState_domain]
  rw [actual_part_signed_expectation μ policy hpolicy hmeas origin hgood cutter hpositive (by omega) _
    (remainderTargets_zero (by omega) t ht hfit) (remainderTargets_last t)
    (remainderTargets_strict (by omega) t ht hfit),
    remainderTargets_increment (by omega) t ht hfit _ (by change 0 + 1 < J; omega)]

end EnvyFreeResearch.Full.UpperSnapshotSmall
