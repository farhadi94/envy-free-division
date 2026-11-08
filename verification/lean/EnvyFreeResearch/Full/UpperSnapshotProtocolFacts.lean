import EnvyFreeResearch.Full.UpperSnapshotProtocolActualRun
import EnvyFreeResearch.Full.UpperSnapshotIntegrationPhysical

/-! Physical interface for an accepted Snapshot call. This is an output
specification; concrete branch proofs establish it from the executed program. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperRepairProgram UpperSnapshotContrast
variable {n k : ℕ}
structure SnapshotSuccessFacts (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (result : PhysicalResult n k) : Prop where
  allocation_wellFormed : ∀ j, WellFormed μ (result.1 j)
  residue_wellFormed : WellFormed μ result.2.1
  allocation_disjoint : Pairwise (fun i j => Disjoint (domain (result.1 i).cells) (domain (result.1 j).cells))
  residue_disjoint : ∀ j, Disjoint (domain (result.1 j).cells) (domain result.2.1.cells)
  material_preserved : (⋃ j, domain (result.1 j).cells) ∪ domain result.2.1.cells = domain origin.cells
  envyFree : ∀ i j, if chores then
      (μ (active i)).real (domain (result.1 i).cells) ≤ (μ (active i)).real (domain (result.1 j).cells)
    else (μ (active i)).real (domain (result.1 j).cells) ≤ (μ (active i)).real (domain (result.1 i).cells)
  common_history : ∀ j, (result.1 j).history = result.2.1.history
  terminal_or_margin : result.2.1.cells = [] ∨
    ((∀ i, 0 < (μ (active i)).real (domain result.2.1.cells)) ∧
      ∃ a b : Fin k, a ≠ b ∧
        0 < physicalGap chores (fun i => μ (active i)) (fun j => domain (result.1 j).cells) a b ∧
        margin n * (μ (active a)).real (domain result.2.1.cells) ≤
          physicalGap chores (fun i => μ (active i)) (fun j => domain (result.1 j).cells) a b)
end EnvyFreeResearch.Full.UpperSnapshotProtocol
