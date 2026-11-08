import EnvyFreeResearch.Full.ChoresComponentClosedProgram
import EnvyFreeResearch.Full.ChoresComponentDispatch

/-! Root ownership and unchanged frozen ancestry in a closed affine group. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentClosed
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (visited : Visited state)
  (participants : Finset (Fin n)) (label : Fin n)
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) participants)
  (hmany : Fintype.card participants < Fintype.card Root)

def rootList : List Root := ComponentAssignment.unused out.allocation hmany ::
  participants.toList.map (donorRoot participants out)

def inputGroup : List (Package (Fin n) RootId) := (rootList participants out hmany).map packages

theorem root_list_nodup : (rootList participants out hmany).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hmem
    have hj' := Finset.mem_toList.mp hj
    exact ComponentAssignment.unused_spec out.allocation hmany (⟨j, hj'⟩ : participants)
      (by simpa only [donorRoot, dite_eq_left hj'] using heq)
  · apply (List.nodup_map_iff_inj_on (Finset.nodup_toList _)).mpr
    intro i hi j hj heq
    have hi' := Finset.mem_toList.mp hi
    have hj' := Finset.mem_toList.mp hj
    have h : out.allocation.assigned ⟨i, hi'⟩ = out.allocation.assigned ⟨j, hj'⟩ := by
      simpa only [donorRoot, dite_eq_left hi', dite_eq_left hj'] using heq
    exact congrArg Subtype.val (out.allocation.assigned.injective h)

theorem root_list_complete (hcard : Fintype.card Root = Fintype.card participants + 1) :
    (rootList participants out hmany).Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup (root_list_nodup participants out hmany) (Finset.nodup_toList _)).mpr
  intro s
  constructor
  · intro _
    simp
  · intro _
    rcases ComponentAssignment.every_root out.allocation hcard s with hs | ⟨j, hj⟩
    · exact List.mem_cons.mpr (Or.inl hs)
    · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr
        ⟨j, Finset.mem_toList.mpr j.property, (donorRoot_task participants out j).trans hj⟩))

theorem input_group_eq : inputGroup participants packages out hmany =
    packages (ComponentAssignment.unused out.allocation hmany) ::
      (donations state visited participants label packages frames gap out).map Donation.package := by
  simp only [inputGroup, rootList, List.map_cons, List.map_map, donations,
    ComponentAffine.tasks, Function.comp_def]

variable (hlabel : ∀ j ∈ participants, state.partition.representative j = label)

include hlabel in
theorem donation_member (d : Donation (Fin n) RootId)
    (hd : d ∈ donations state visited participants label packages frames gap out) :
    ∃ j : participants,
      d = ⟨packages (out.allocation.assigned j),
        ComponentDonors.affine state visited frames Subtype.val gap out j⟩ := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
  have hj' := Finset.mem_toList.mp hj
  refine ⟨⟨j, hj'⟩, ?_⟩
  simp only [Function.comp_apply, donorRoot, utilities, owners, dite_eq_left hj',
    ComponentDonors.affine, hlabel j hj']

def nextAllocation (s : Root) : Allocation (Fin n) RootId :=
  ComponentAssignment.dispatch out.allocation (fun s => (frames s).allocation)
    (fun j => (ComponentDonors.affine state visited frames Subtype.val gap out j).output) s

theorem next_allocation_assigned (j : participants) :
    nextAllocation state visited participants frames gap out (out.allocation.assigned j) =
      (ComponentDonors.affine state visited frames Subtype.val gap out j).output :=
  ComponentAssignment.dispatch_assigned _ _ _ _

theorem next_allocation_unused :
    nextAllocation state visited participants frames gap out (ComponentAssignment.unused out.allocation hmany) =
      (frames (ComponentAssignment.unused out.allocation hmany)).allocation :=
  ComponentAssignment.dispatch_unassigned _ _ _ _ (ComponentAssignment.unused_spec _ _)

theorem next_allocation_root (s : Root) :
    (nextAllocation state visited participants frames gap out s).root = (frames s).root := by
  unfold nextAllocation
  apply ComponentAssignment.dispatch_property out.allocation _ _
    (fun s (a : Allocation (Fin n) RootId) => a.root = (frames s).root)
  · intro s
    rfl
  · intro j
    exact proposal_root _

include hlabel in
theorem output_allocation_member (hlive : ∀ s, (packages s).live = some (frames s))
    (a : Allocation (Fin n) RootId)
    (ha : a ∈ (outputPackage state visited participants label packages frames gap out hmany).allocations) :
    (∃ s, a ∈ (packages s).frozen) ∨
      ∃ s, a = nextAllocation state visited participants frames gap out s := by
  simp only [outputPackage, mergeClosed, Package.allocations, Package.close, hlive,
    Option.toList_none, List.map_nil, List.append_nil, Option.toList_some, List.map_cons,
    List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | ha) | ha
  · exact Or.inl ⟨_, ha⟩
  · right
    refine ⟨ComponentAssignment.unused out.allocation hmany, ?_⟩
    rw [next_allocation_unused]
    exact ha
  · obtain ⟨d, hd, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨j, rfl⟩ := donation_member state visited participants label packages frames gap out hlabel d hd
    rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl ⟨_, ha⟩
    · right
      refine ⟨out.allocation.assigned j, ?_⟩
      rw [next_allocation_assigned]
      simpa only [List.mem_singleton] using ha

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks : Root → Fin n → Set ℝ)
  (hparts : PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out)
  (hcorrect : PhysicalCorrect
    (affineUtility cost (domains blocks state.partition.representative)
      (offsets gap state.partition.representative)) Subtype.val out.allocation)
  (hlive : ∀ s, (packages s).live = some (frames s)) (hvalid : ∀ s, (packages s).Valid)
  (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
  (hprotect : ∀ i ∉ participants, ∀ s, (cost i).real (blocks s label) ≤ gap s label i)
include hlabel hparts hcorrect hlive hvalid hallowed hprotect

theorem output_group_update : GroupUpdate (inputGroup participants packages out hmany)
    (outputPackage state visited participants label packages frames gap out hmany) := by
  rw [input_group_eq state visited participants label packages frames gap out hmany]
  have hframes : ∀ s, (frames s).Good := fun s => (hvalid s).live_good _ (hlive s)
  apply GroupUpdate.affine _ _
    (donations_wellFormed state visited participants label packages frames gap out hlabel cost
      blocks hparts hcorrect hlive hframes hallowed)
  · intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    rfl
  · intro i j p hij
    exact payment_coverage state visited participants label packages frames gap out hlabel cost
      blocks hparts hcorrect hprotect i j p

theorem output_ids (hcard : Fintype.card Root = Fintype.card participants + 1) :
    (outputPackage state visited participants label packages frames gap out hmany).ids.Perm
      (Finset.univ.toList.flatMap (fun s => (packages s).ids)) := by
  have h := group_update_ids (output_group_update state visited participants label packages frames
    gap out hmany hlabel cost blocks hparts hcorrect hlive hvalid hallowed hprotect)
  have hp := (root_list_complete participants out hmany hcard).map packages
  exact h.trans (by simpa only [inputGroup, List.flatMap_map] using hp.flatMap_right Package.ids)

end EnvyFreeResearch.Full.Chores.ComponentClosed
