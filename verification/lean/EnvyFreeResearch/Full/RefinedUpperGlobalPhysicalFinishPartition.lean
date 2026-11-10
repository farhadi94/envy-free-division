import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinishExtension
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepairPartition

/-! The final original-residue partition combines the already allocated
Snapshot/Shrink pieces with the literal additions from the accepted Repair. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
  (localAdded : Fin p.anchor.active.card → State n) (remaining : State n)

 theorem extended_subset (hsub : ∀ j, domain (localAdded j).cells ⊆ domain p.buffer.cells)
    (j : Fin n) : domain (extendPieces p.anchor.active localAdded remaining.history j).cells ⊆
      domain p.buffer.cells := by
  by_cases hj : j ∈ p.anchor.active
  · obtain ⟨i,rfl⟩ := enumerate_preimage _ j hj
    rw [extendPieces_apply]
    exact hsub i
  · rw [extendPieces_frozen _ _ _ _ hj]
    exact empty_subset _

include hp
 theorem added_pairwise
    (hsub : ∀ j, domain (localAdded j).cells ⊆ domain p.buffer.cells)
    (hpair : Pairwise (fun i j => Disjoint (domain (localAdded i).cells) (domain (localAdded j).cells))) :
    Pairwise (fun i j => Disjoint (domain (added p localAdded remaining.history i).cells)
      (domain (added p localAdded remaining.history j).cells)) := by
  have hcross (i j : Fin n) := (pending_additions_separate μ whole p hp i).mono_right
    (extended_subset p localAdded remaining hsub j)
  intro i j hij
  simp only [added_domain,disjoint_union_left,disjoint_union_right]
  exact ⟨⟨pending_additions_pair μ whole p hp hij,(hcross j i).symm⟩,
    ⟨hcross i j,extendPieces_pairwise _ _ _ hpair hij⟩⟩

 theorem added_separate
    (hrem : domain remaining.cells ⊆ domain p.buffer.cells)
    (hsep : ∀ j, Disjoint (domain (localAdded j).cells) (domain remaining.cells)) :
    ∀ j, Disjoint (domain (added p localAdded remaining.history j).cells) (domain remaining.cells) := by
  intro j
  rw [added_domain]
  refine disjoint_union_left.mpr ⟨(pending_additions_separate μ whole p hp j).mono_right hrem,?_⟩
  by_cases hj : j ∈ p.anchor.active
  · obtain ⟨i,rfl⟩ := enumerate_preimage _ j hj
    rw [extendPieces_apply]
    exact hsep i
  · rw [extendPieces_frozen _ _ _ _ hj]
    exact empty_disjoint _

 theorem added_cover
    (hc : (⋃ i, domain (localAdded i).cells) ∪ domain remaining.cells = domain p.buffer.cells) :
    (⋃ j, domain (added p localAdded remaining.history j).cells) ∪ domain remaining.cells =
      domain p.anchor.residue.cells := by
  simp only [added_domain,iUnion_union_distrib]
  rw [extendPieces_domain,union_assoc,hc]
  exact pending_additions_cover μ whole p hp

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
