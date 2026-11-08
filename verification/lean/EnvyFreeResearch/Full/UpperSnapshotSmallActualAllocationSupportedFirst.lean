import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationPhysical
import EnvyFreeResearch.Full.UpperVirtualGrid
import EnvyFreeResearch.Full.UpperCorrectionPieces

/-! Virtual first shares and remainders use only immutable grid boundaries
and the first two new roots, even when the original domain has many joins. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperCorrectionPieces
variable {n m : ℕ}

def positiveVirtual (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) : List Component :=
  (UpperVirtualGrid.atoms cuts).filter (positiveFlag cuts selected)

def negativeVirtual (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) : List Component :=
  (UpperVirtualGrid.atoms cuts).filter (fun c => !positiveFlag cuts selected c)

theorem positiveVirtual_domain (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (selected : Finset (Fin (m+1))) :
    domain (positiveVirtual cuts selected) = selectedUnion (cell (Icc 0 1) cuts) selected := by
  change domain (retain (⟨UpperVirtualGrid.atoms cuts,[]⟩ : State 0) cuts selected).cells = _
  rw [retain_domain _ cuts hzero hmono (UpperVirtualGrid.atoms_separated cuts),UpperVirtualGrid.atoms_domain]

theorem negativeVirtual_domain (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) :
    domain (negativeVirtual cuts selected) = Icc 0 1 \ domain (positiveVirtual cuts selected) := by
  rw [negativeVirtual,whole_filter_domain _ (UpperVirtualGrid.atoms_disjoint cuts),UpperVirtualGrid.atoms_domain]
  rfl

theorem positiveVirtual_inter (origin : State n) (cuts : Fin (m+2) → ℝ)
    (hzero : cuts 0=0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) :
    domain (retain origin cuts selected).cells = domain origin.cells ∩ domain (positiveVirtual cuts selected) := by
  rw [retain_domain origin cuts hzero hmono hsep,positiveVirtual_domain cuts hzero hmono]
  ext x
  simp only [mem_selectedUnion,mem_inter_iff]
  constructor
  · rintro ⟨e,he,hx⟩
    rw [UpperVirtualGrid.logicalCell_unit_inter _ (domain_subset_unit _) cuts e] at hx
    exact ⟨hx.1,e,he,hx.2⟩
  · rintro ⟨hU,e,he,hx⟩
    refine ⟨e,he,?_⟩
    rw [UpperVirtualGrid.logicalCell_unit_inter _ (domain_subset_unit _) cuts e]
    exact ⟨hU,hx⟩

def firstRecord (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) : Correction :=
  ⟨firstAmount origin cutter cuts selected t,first,
    (firstRun policy origin cutter cuts selected t first).1 0,
    (firstRun policy origin cutter cuts selected t first).1 1⟩

def firstVirtual (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) : List Component :=
  let r := firstRecord policy origin cutter cuts selected t first
  if firstFill origin cutter cuts selected t then positiveVirtual cuts selected ++ take (UpperVirtualGrid.atoms cuts) r
  else take (positiveVirtual cuts selected) r

def remainderVirtual (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) : List Component :=
  let r := firstRecord policy origin cutter cuts selected t first
  if firstFill origin cutter cuts selected t then applyCorrection (negativeVirtual cuts selected) r
  else negativeVirtual cuts selected ++ applyCorrection (positiveVirtual cuts selected) r

theorem firstVirtual_inter (policy : Policy n) (origin : State n) (hdis : DisjointComponents origin.cells)
    (cutter : Fin n) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) :
    domain (firstEndowment policy origin cutter cuts selected t first).cells =
      domain origin.cells ∩ domain (firstVirtual policy origin cutter cuts selected t first) := by
  have hp := positiveVirtual_inter origin cuts hzero hmono hsep selected
  have ha : firstArc policy origin cutter cuts selected t first =
      domain origin.cells ∩ correctionPiece (UpperVirtualGrid.atoms cuts)
        (firstRecord policy origin cutter cuts selected t first) := by
    unfold firstArc correctionPiece firstRecord
    rw [UpperVirtualGrid.atoms_domain]
    exact physicalPiece_restrict _ _ (domain_subset_unit _) _ _ _ _
  rw [firstEndowment_arc_domain policy origin hdis cutter cuts hzero hmono hsep]
  unfold firstVirtual
  split_ifs
  · rw [domain_append,take_domain, hp,ha]
    ext x
    simp only [mem_inter_iff,mem_union]
    tauto
  · rw [take_domain,hp,ha]
    have hr := physicalPiece_restrict (Icc (0:ℝ) 1) (domain (positiveVirtual cuts selected))
      (domain_subset_unit _) (firstAmount origin cutter cuts selected t) first
      ((firstRun policy origin cutter cuts selected t first).1 0)
      ((firstRun policy origin cutter cuts selected t first).1 1)
    simp only [firstRecord,correctionPiece,UpperVirtualGrid.atoms_domain]
    rw [hr]
    ext x
    simp only [mem_inter_iff]
    tauto

end EnvyFreeResearch.Full.UpperSnapshotSmall
