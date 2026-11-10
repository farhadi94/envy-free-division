import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepairPartition
import EnvyFreeResearch.Full.UpperRepairSuccess

/-! Exact all-original-observer conservation and quarter spending derived
from the actual Repair success facts and whole-old-label geometry. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
open UpperRecordedDomain UpperCorrectionExecution
variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old addition : Fin k → State n)
  (result : UpperRepairProgram.PhysicalResult n k)
  (facts : RefinedUpperRepairProgram.SuccessFacts μ chores active origin old result)
  (f : Equiv.Perm (Fin k))
  (hlabel : ∀ j, domain (result.1 (f j)).cells = domain (old j).cells ∪ domain (addition j).cells)
  (hold : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
  (hadd : ∀ j, domain (addition j).cells ⊆ domain origin.cells)

include facts hlabel hold hadd in
theorem success_additions_balance (i : Fin n) :
    (∑ j, (μ i).real (domain (addition j).cells)) + (μ i).real (domain result.2.1.cells) =
      (μ i).real (domain origin.cells) := by
  have hp := additions_partition (fun j => domain (old j).cells) (fun j => domain (addition j).cells)
    (fun j => domain (result.1 j).cells) f (domain origin.cells) (domain result.2.1.cells)
    hlabel facts.material_preserved hold hadd facts.residue_subset
  have hpair := additions_pairwise (fun j => domain (old j).cells) (fun j => domain (addition j).cells)
    (fun j => domain (result.1 j).cells) f hlabel facts.allocation_disjoint
  have hsep := additions_separate (fun j => domain (old j).cells) (fun j => domain (addition j).cells)
    (fun j => domain (result.1 j).cells) f (domain result.2.1.cells) hlabel facts.residue_disjoint
  rw [← measureReal_iUnion_fintype hpair (fun j => domain_measurable (addition j).cells),
    ← measureReal_union (disjoint_iUnion_left.mpr hsep) (domain_measurable result.2.1.cells),hp]

include facts hlabel hold hadd in
theorem success_additions_quarter (i : Fin k) :
    (∑ j, (μ (active i)).real (domain (addition j).cells)) <
      (μ (active i)).real (domain origin.cells) / 4 := by
  have hb := success_additions_balance μ chores active origin old addition result facts f hlabel hold hadd (active i)
  have hr := (facts.residue_mass i).1
  linarith

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
