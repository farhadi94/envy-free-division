import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationSupportedFirst
import EnvyFreeResearch.Full.UpperSnapshotSmallVirtual

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperCorrectionPieces
variable {n m : ℕ}

theorem remainderVirtual_domain (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) :
    domain (remainderVirtual policy origin cutter cuts selected t first) =
      Icc 0 1 \ domain (firstVirtual policy origin cutter cuts selected t first) := by
  have hp := physicalPiece_restrict (Icc (0:ℝ) 1) (domain (positiveVirtual cuts selected))
    (domain_subset_unit _) (firstAmount origin cutter cuts selected t) first
    ((firstRun policy origin cutter cuts selected t first).1 0)
    ((firstRun policy origin cutter cuts selected t first).1 1)
  have hn := physicalPiece_restrict (Icc (0:ℝ) 1) (domain (negativeVirtual cuts selected))
    (domain_subset_unit _) (firstAmount origin cutter cuts selected t) first
    ((firstRun policy origin cutter cuts selected t first).1 0)
    ((firstRun policy origin cutter cuts selected t first).1 1)
  have hps := domain_subset_unit (positiveVirtual cuts selected)
  have has := physicalPiece_subset (Icc (0:ℝ) 1) (firstAmount origin cutter cuts selected t) first
    ((firstRun policy origin cutter cuts selected t first).1 0)
    ((firstRun policy origin cutter cuts selected t first).1 1)
  unfold remainderVirtual firstVirtual
  split_ifs
  · rw [applyCorrection,removeCorrection_domain,domain_append,take_domain]
    simp only [firstRecord,correctionPiece,UpperVirtualGrid.atoms_domain]
    rw [hn,negativeVirtual_domain]
    ext x
    have hpx := @hps x
    have hax := @has x
    simp only [mem_sdiff,mem_inter_iff,mem_union] at *
    tauto
  · rw [domain_append,applyCorrection,removeCorrection_domain,take_domain]
    simp only [firstRecord,correctionPiece]
    rw [hp,negativeVirtual_domain]
    ext x
    have hpx := @hps x
    simp only [mem_sdiff,mem_inter_iff,mem_union] at *
    tauto

theorem firstRemainder_complement (policy : Policy n) (origin : State n)
    (hdis : DisjointComponents origin.cells) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) :
    domain (firstRemainder policy origin cutter cuts selected t first).cells =
      domain origin.cells \ domain (firstEndowment policy origin cutter cuts selected t first).cells := by
  change domain ((firstRestored policy origin cutter cuts selected t first).cells.filter _) = _
  have hd : DisjointComponents (firstRestored policy origin cutter cuts selected t first).cells :=
    refineEndpoints_disjoint _ _ hdis
  rw [whole_filter_domain _ hd,firstRestored_domain]
  rfl

theorem remainderVirtual_inter (policy : Policy n) (origin : State n)
    (hdis : DisjointComponents origin.cells) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (hzero : cuts 0=0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) :
    domain (firstRemainder policy origin cutter cuts selected t first).cells =
      domain origin.cells ∩ domain (remainderVirtual policy origin cutter cuts selected t first) := by
  rw [firstRemainder_complement policy origin hdis,
    firstVirtual_inter policy origin hdis cutter cuts hzero hmono hsep,remainderVirtual_domain]
  have hs := domain_subset_unit origin.cells
  ext x
  have hx := @hs x
  simp only [mem_sdiff,mem_inter_iff] at *
  tauto

end EnvyFreeResearch.Full.UpperSnapshotSmall
