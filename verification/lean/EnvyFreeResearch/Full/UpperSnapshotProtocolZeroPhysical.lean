import EnvyFreeResearch.Full.UpperSnapshotProtocolZero
import EnvyFreeResearch.Full.UpperSnapshotSmallCircle
import EnvyFreeResearch.Full.UpperComponentGroups

/-! Accepted zero-disagreement outputs have no residue and satisfy literal
complete physical envy-freeness. The check uses only returned endpoint caches. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall UpperDomainDifference
variable {n k : ℕ}

 theorem equalPieces_actual (policy : Policy n) (hk : 0 < k) (origin : State n)
    (cutter : Fin n) (start : UpperSnapshotSmall.Circle) :
    equalPieces hk start (partitionRun policy origin cutter (equalTargets k) start) =
      partState hk policy origin cutter (equalTargets k) start := rfl

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin k)
  (hpositive : 0 < (μ (active cutter)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem zero_success_complete (start : UpperSnapshotSmall.Circle)
    (hs : (zeroExecute policy hk chores active origin cutter start).2.2 = false) :
    (∀ j, WellFormed μ ((zeroExecute policy hk chores active origin cutter start).1 j)) ∧
    WellFormed μ (zeroExecute policy hk chores active origin cutter start).2.1 ∧
    domain (zeroExecute policy hk chores active origin cutter start).2.1.cells = ∅ ∧
    (⋃ j, domain ((zeroExecute policy hk chores active origin cutter start).1 j).cells) = domain origin.cells ∧
    Pairwise (fun i j => Disjoint
      (domain ((zeroExecute policy hk chores active origin cutter start).1 i).cells)
      (domain ((zeroExecute policy hk chores active origin cutter start).1 j).cells)) ∧
    (∀ i j, if chores then
      (μ (active i)).real (domain ((zeroExecute policy hk chores active origin cutter start).1 i).cells) ≤
        (μ (active i)).real (domain ((zeroExecute policy hk chores active origin cutter start).1 j).cells)
      else (μ (active i)).real (domain ((zeroExecute policy hk chores active origin cutter start).1 j).cells) ≤
        (μ (active i)).real (domain ((zeroExecute policy hk chores active origin cutter start).1 i).cells)) := by
  have hp := (zeroFinish_success hk chores active start _).mp hs
  have he : zeroExecute policy hk chores active origin cutter start =
      (partState hk policy origin (active cutter) (equalTargets k) start,
        ⟨[],(partitionRun policy origin (active cutter) (equalTargets k) start).2.history⟩,false) := by
    unfold zeroExecute
    rw [zeroFinish, if_pos hp]
    rfl
  rw [he]
  have hpart := shared_circle_partition μ policy hpolicy origin hgood (active cutter) hpositive hk
    (equalTargets k) (equalTargets_strict hk) (equalTargets_zero hk) (equalTargets_last hk) start
  refine ⟨hpart.2.1,UpperComponentAssembly.empty_wellFormed μ _ hpart.1.2.2.1,
    by simp [domain],hpart.2.2.1,hpart.2.2.2.1,?_⟩
  have hc := (completeCheck_iff chores active _).mp hp
  rw [equalPieces_actual] at hc
  intro i j
  have hij := hc i j
  rw [total_correct μ _ (hpart.2.1 i), total_correct μ _ (hpart.2.1 j)] at hij
  exact hij

end EnvyFreeResearch.Full.UpperSnapshotProtocol
