import EnvyFreeResearch.Full.ChoresComponentUpdate
import EnvyFreeResearch.Full.ChoresComponentDispatch

/-! Every allocation produced by the concrete open group is either an
unchanged frozen ancestor or the actual updated live root. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentBatch
open Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ) (out : Result state hall cycle)

theorem donation_member (d : Donation (Fin n) RootId)
    (hd : d ∈ donations state hall cycle visited packages frames gap out) :
    ∃ j : Task state hall cycle,
      d = ⟨packages (out.allocation.assigned j),
        ComponentDonors.ordinary state visited frames Subtype.val gap out j⟩ := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
  have hj' := Finset.mem_toList.mp hj
  refine ⟨⟨j, hj'⟩, ?_⟩
  simp only [Function.comp_apply, donorRoot, utilities, owners, dite_eq_left hj',
    ComponentDonors.ordinary]

def nextAllocation (s : Root) : Allocation (Fin n) RootId :=
  ComponentAssignment.dispatch out.allocation
    (fun s => (ComponentFrames.advance state hall cycle visited frames s).allocation)
    (fun j => (ComponentDonors.ordinary state visited frames Subtype.val gap out j).output) s

theorem next_allocation_assigned (j : Task state hall cycle) :
    nextAllocation state hall cycle visited frames gap out (out.allocation.assigned j) =
      (ComponentDonors.ordinary state visited frames Subtype.val gap out j).output :=
  ComponentAssignment.dispatch_assigned _ _ _ _

theorem next_allocation_unused
    (hmany : Fintype.card (Task state hall cycle) < Fintype.card Root) :
    nextAllocation state hall cycle visited frames gap out (ComponentAssignment.unused out.allocation hmany) =
      (ComponentFrames.advance state hall cycle visited frames
        (ComponentAssignment.unused out.allocation hmany)).allocation :=
  ComponentAssignment.dispatch_unassigned _ _ _ _ (ComponentAssignment.unused_spec _ _)

theorem next_allocation_root (s : Root) :
    (nextAllocation state hall cycle visited frames gap out s).root = (frames s).root := by
  unfold nextAllocation
  apply ComponentAssignment.dispatch_property out.allocation _ _
    (fun s (a : Allocation (Fin n) RootId) => a.root = (frames s).root)
  · intro s
    rfl
  · intro j
    exact proposal_root _

theorem output_allocation_member
    (hmany : Fintype.card (Task state hall cycle) < Fintype.card Root)
    (a : Allocation (Fin n) RootId)
    (ha : a ∈ (outputPackage state hall cycle visited packages frames gap hmany out).allocations) :
    (∃ s, a ∈ (packages s).frozen) ∨
      ∃ s, a = nextAllocation state hall cycle visited frames gap out s := by
  simp only [outputPackage, mergeOpen, Package.allocations, Option.toList_some,
    List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | ha) | ha
  · exact Or.inl ⟨_, ha⟩
  · obtain ⟨d, hd, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨j, rfl⟩ := donation_member state hall cycle visited packages frames gap out d hd
    rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl ⟨_, ha⟩
    · right
      refine ⟨out.allocation.assigned j, ?_⟩
      rw [next_allocation_assigned]
      simpa only [List.mem_singleton] using ha
  · right
    refine ⟨ComponentAssignment.unused out.allocation hmany, ?_⟩
    rw [next_allocation_unused]
    exact ha

end EnvyFreeResearch.Full.Chores.ComponentBatch
