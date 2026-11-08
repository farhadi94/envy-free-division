import EnvyFreeResearch.Full.ChoresTerminalPool
import EnvyFreeResearch.Full.ChoresTerminalProgram

/-! Every actual affine donor appears in the full terminal pool. Its
recipient and original baseline are preserved, including zero-credit donors. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory ChoreComposition IntervalOracle InitialPartition OrderedUnion ComponentDonors
open scoped Classical

variable {n : ℕ} {RootId : Type*}
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (p : Fin n) (A : Finset (Fin n))
  (out : ComponentClosed.Result (Root := Fin data.size) A)
  (hmany : Fintype.card A < Fintype.card (Fin data.size))
  (hlabel : ∀ j ∈ A, data.pending.partition.representative j=p)

def actualDonor (j : A) : ChoreComposition.Allocation (Fin n) RootId :=
  (affine data.pending data.visited data.frames Subtype.val (Outer.originalGaps data original) out j).output

include hlabel

theorem actual_donation_mem (j : A) :
    (⟨data.packages (out.allocation.assigned j),
      affine data.pending data.visited data.frames Subtype.val (Outer.originalGaps data original) out j⟩ :
        Donation (Fin n) RootId) ∈
      ComponentClosed.donations data.pending data.visited A p data.packages data.frames
        (Outer.originalGaps data original) out := by
  unfold ComponentClosed.donations ComponentAffine.tasks
  apply List.mem_map.mpr
  refine ⟨j,Finset.mem_toList.mpr j.property,?_⟩
  simp only [Function.comp_apply,ComponentClosed.donorRoot,ComponentClosed.utilities,
    ComponentClosed.owners,dite_eq_left j.property,affine,hlabel j j.property]

theorem actual_donor_member (j : A) :
    actualDonor data original A out j ∈
      (ComponentClosed.outputPackage data.pending data.visited A p data.packages data.frames
        (Outer.originalGaps data original) out hmany).allocations := by
  unfold ComponentClosed.outputPackage mergeClosed Package.allocations
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨⟨data.packages (out.allocation.assigned j),
    affine data.pending data.visited data.frames Subtype.val (Outer.originalGaps data original) out j⟩,
    actual_donation_mem data original p A out hlabel j,?_⟩
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem actual_donor_full_pool_member (j : A) :
    actualDonor data original A out j ∈
      (finalPool data (ComponentClosed.outputPackage data.pending data.visited A p data.packages data.frames
        (Outer.originalGaps data original) out hmany)).flatMap Package.allocations := by
  apply List.mem_flatMap.mpr
  refine ⟨_,List.mem_append_right _ (List.mem_singleton.mpr rfl),?_⟩
  exact actual_donor_member data original p A out hmany hlabel j

theorem actual_donor_owner (j : A) : (actualDonor data original A out j).owner p=j := by
  have h := owner_recipient data.pending data.visited Subtype.val out j
  simpa only [actualDonor,affine,affineProposal,Proposal.output,ite_true,hlabel j j.property] using h

omit hlabel in
theorem actual_donor_baseline (j : A) (i : Fin n) :
    (actualDonor data original A out j).baseline i=(data.frames (out.allocation.assigned j)).baseline i := by
  simp only [actualDonor,affine,affineProposal,Proposal.output,ite_true]

end EnvyFreeResearch.Full.Chores.Terminal
