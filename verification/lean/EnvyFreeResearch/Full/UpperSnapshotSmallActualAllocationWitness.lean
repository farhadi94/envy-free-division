import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationValues
import EnvyFreeResearch.Full.UpperSnapshotSmallChance

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
variable {n m J : ℕ}

/-- The contrast in the probability theorem is exactly the contrast of the
first two shares in the returned full-history allocation packet. -/
theorem actual_witness_pair (hJ : 2 ≤ J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle)
    (signed : SignedMeasure ℝ) :
    candidateContrast hJ policy origin cutter cuts selected t signed (first,second) =
      signed (domain ((actualAllocation (J:=J) (by omega) policy origin cutter cuts selected t first second).1 ⟨0,by omega⟩).cells) -
      signed (domain ((actualAllocation (J:=J) (by omega) policy origin cutter cuts selected t first second).1 ⟨1,by omega⟩).cells) := by
  rw [actual_share_zero,firstAllocationFrom_actual,
    actual_share_nonzero (by omega) policy origin cutter cuts selected t first second ⟨1,by omega⟩ (by change (1 : ℕ) ≠ 0; omega)]
  rfl

end EnvyFreeResearch.Full.UpperSnapshotSmall
