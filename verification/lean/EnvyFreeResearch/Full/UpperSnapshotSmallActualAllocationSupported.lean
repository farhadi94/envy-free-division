import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationSupportedRemainder
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationSupportedRecorded
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationValues

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperCorrectionPieces
variable {n m J : ℕ} {Generated : Type*}

variable (policy : Policy n) (origin : State n) (hdis : DisjointComponents origin.cells)
    (cutter : Fin n) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle)
    (points : Generated → ℝ)
    (hfirst : ∀ j, ∃ e, points e=(firstRun policy origin cutter cuts selected t first).1 j)
    (hsecond : ∀ j, ∃ e, points e=(secondRun (J:=J) policy origin cutter cuts selected t first second).1 j)
include hdis hzero hone hmono hsep hfirst

theorem firstEndowment_supported :
    ∃ virtual, RecordedEndpoints cuts points virtual ∧
      domain (firstEndowment policy origin cutter cuts selected t first).cells =
        domain origin.cells ∩ domain virtual := by
  exact ⟨firstVirtual policy origin cutter cuts selected t first,
    (firstVirtual_recorded policy origin cutter cuts hzero hone selected t first points hfirst).1,
    firstVirtual_inter policy origin hdis cutter cuts hzero hmono hsep selected t first⟩

include hsecond in
 theorem secondPiece_supported (hJ : 0 < J) (j : Fin J) :
    ∃ virtual, RecordedEndpoints cuts points virtual ∧
      domain (secondPiece hJ policy origin cutter cuts selected t first second j).cells =
        domain origin.cells ∩ domain virtual := by
  let rv := remainderVirtual policy origin cutter cuts selected t first
  let roots := (secondRun (J:=J) policy origin cutter cuts selected t first second).1
  refine ⟨virtualPart hJ rv (remainderTargets J t) second roots j,?_,?_⟩
  · exact virtualPart_recorded_of_supported hJ cuts points rv
      (firstVirtual_recorded policy origin cutter cuts hzero hone selected t first points hfirst).2
      (remainderTargets J t) second roots hsecond j
  · rw [virtualPart_domain,secondPiece,partState_domain]
    unfold actualPart
    rw [remainderVirtual_inter policy origin hdis cutter cuts hzero hmono hsep,part_inter]
    rfl

include hsecond in
 theorem actualAllocation_supported (hJ : 0 < J) :
    (∀ j, ∃ virtual, RecordedEndpoints cuts points virtual ∧
      domain ((actualAllocation hJ policy origin cutter cuts selected t first second).1 j).cells =
        domain origin.cells ∩ domain virtual) ∧
    (∃ virtual, RecordedEndpoints cuts points virtual ∧
      domain (actualAllocation hJ policy origin cutter cuts selected t first second).2.1.cells =
        domain origin.cells ∩ domain virtual) := by
  constructor
  · intro j
    by_cases hj : j.val=0
    · have hz : j=⟨0,hJ⟩ := Fin.ext hj
      rw [hz,actual_share_zero,firstAllocationFrom_actual]
      exact firstEndowment_supported policy origin hdis cutter cuts hzero hone hmono hsep selected t first points hfirst
    · rw [actual_share_nonzero hJ policy origin cutter cuts selected t first second j hj]
      exact secondPiece_supported policy origin hdis cutter cuts hzero hone hmono hsep selected t first second points hfirst hsecond hJ _
  · rw [actual_buffer]
    exact secondPiece_supported policy origin hdis cutter cuts hzero hone hmono hsep selected t first second points hfirst hsecond hJ _

end EnvyFreeResearch.Full.UpperSnapshotSmall
