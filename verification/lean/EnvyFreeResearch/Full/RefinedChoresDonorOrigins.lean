import EnvyFreeResearch.Full.RefinedChoresDonorCachesNext

/-! Closed batches retain exactly all input root IDs and frozen ancestors,
while installing every actual affine donor output. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresDonorOrigins
open Set MeasureTheory IntervalOracle
open ChoreComposition Chores Chores.ComponentPayments Chores.ComponentRecording
open RefinedChoresPhysicalPayment RefinedChoresDonorCaches
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (A : Finset (Fin n)) (p : Fin n)
    (frames : Root → Frame (Fin n) RootId)
    (hpath : ∀ s j, j ∈ A → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)
    (packages : Root → Package (Fin n) RootId)
    (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) A)

theorem donation_member (d : Donation (Fin n) RootId)
    (hd : d ∈ donations A p frames hpath packages gap out) :
    ∃ j : A, d = ⟨packages (out.allocation.assigned j),donorProposal A p frames hpath gap out j⟩ := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
  have hj' := Finset.mem_toList.mp hj
  refine ⟨⟨j,hj'⟩,?_⟩
  simp only [Function.comp_apply,donorRoot,donorProposal,dite_eq_left hj']

theorem output_allocation_member (target : Root → Fin n)
    (hmany : Fintype.card A < Fintype.card Root)
    (hlive : ∀ s, (packages s).live = some (frames s))
    (a : ChoreComposition.Allocation (Fin n) RootId)
    (ha : a ∈ (outputPackage A p frames hpath packages gap out target hmany).allocations) :
    (∃ s, a ∈ (packages s).frozen) ∨
      ∃ s, a = nextAllocation A p frames hpath gap out s := by
  simp only [outputPackage,mergeOpen,Package.allocations,Option.toList_some,List.map_cons,
    List.map_nil,List.mem_append,List.mem_singleton] at ha
  rcases ha with (ha | ha) | ha
  · exact Or.inl ⟨_,ha⟩
  · obtain ⟨d,hd,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨j,rfl⟩ := donation_member A p frames hpath packages gap out d hd
    rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl ⟨_,ha⟩
    · right
      refine ⟨out.allocation.assigned j,?_⟩
      rw [next_allocation_assigned]
      simpa only [List.mem_singleton] using ha
  · right
    refine ⟨ComponentAssignment.unused out.allocation hmany,?_⟩
    rw [next_allocation_unused]
    exact ha

end EnvyFreeResearch.Full.RefinedChoresDonorOrigins
#print axioms EnvyFreeResearch.Full.RefinedChoresDonorOrigins.output_allocation_member
