import EnvyFreeResearch.Full.UpperSnapshotSmallSecondRestored

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperRecordedDomain UpperCorrectionExecution UpperGridRecords UpperDomainDifference UpperCircularStage
variable {n m J : ℕ}

theorem secondRestored_separated (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (first second : Circle) (x : ℝ) (hx : SeparatedAt x origin.cells) :
    SeparatedAt x (secondRestored (J := J) policy origin cutter cuts selected t first second).cells := by
  apply UpperGridCells.refineEndpoints_preserves_separated
  exact UpperGridCells.refineEndpoints_preserves_separated _ _ x hx

/-- Every immutable logical cell remains the same literal set after either
accepting or rejecting the candidate. Refinement does not resample the grid. -/
theorem secondRestored_cell (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (first second : Circle) (e : Fin (m+1)) :
    UpperLogicalCells.cell (domain (secondRestored (J := J) policy origin cutter cuts selected t first second).cells) cuts e =
      UpperLogicalCells.cell (domain origin.cells) cuts e := by
  rw [secondRestored_domain]

end EnvyFreeResearch.Full.UpperSnapshotSmall
