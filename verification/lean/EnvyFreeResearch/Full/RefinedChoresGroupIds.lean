import EnvyFreeResearch.Full.RefinedChoresPhysicalPayment

/-! A deferred-payment batch consumes every nominal donor exactly once,
including zero-credit donors. Its output preserves every original root ID. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresGroupIds
open ChoreComposition Chores Chores.ComponentRecording RefinedChoresPhysicalPayment
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (C : Finset (Fin n)) (p : Fin n)
    (frames : Root → Frame (Fin n) RootId)
    (hpath : ∀ s j, j ∈ C → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)
    (packages : Root → Package (Fin n) RootId)
    (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) C)
    (target : Root → Fin n) (hmany : Fintype.card C < Fintype.card Root)

def rootList : List Root :=
  ComponentAssignment.unused out.allocation hmany :: C.toList.map (donorRoot C out)

def inputGroup : List (Package (Fin n) RootId) := (rootList C out hmany).map packages

theorem root_list_nodup : (rootList C out hmany).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    obtain ⟨j,hj,heq⟩ := List.mem_map.mp hmem
    have hj' := Finset.mem_toList.mp hj
    have h := ComponentAssignment.unused_spec out.allocation hmany (⟨j,hj'⟩ : C)
    exact h (by simpa only [donorRoot,dite_eq_left hj'] using heq)
  · apply (List.nodup_map_iff_inj_on (Finset.nodup_toList _)).mpr
    intro i hi j hj heq
    have hi' := Finset.mem_toList.mp hi
    have hj' := Finset.mem_toList.mp hj
    have h : out.allocation.assigned ⟨i,hi'⟩ = out.allocation.assigned ⟨j,hj'⟩ := by
      simpa only [donorRoot,dite_eq_left hi',dite_eq_left hj'] using heq
    exact congrArg Subtype.val (out.allocation.assigned.injective h)

theorem root_list_complete (hcard : Fintype.card Root = Fintype.card C+1) :
    (rootList C out hmany).Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup (root_list_nodup C out hmany) (Finset.nodup_toList _)).mpr
  intro s
  constructor
  · intro _; simp
  · intro _
    rcases ComponentAssignment.every_root out.allocation hcard s with hs | ⟨j,hj⟩
    · exact List.mem_cons.mpr (Or.inl hs)
    · apply List.mem_cons.mpr
      right
      apply List.mem_map.mpr
      refine ⟨j,Finset.mem_toList.mpr j.property,?_⟩
      simpa only [donorRoot,dite_eq_left j.property] using hj

theorem input_group_eq : inputGroup C packages out hmany =
    packages (ComponentAssignment.unused out.allocation hmany) ::
      (donations C p frames hpath packages gap out).map Donation.package := by
  simp only [inputGroup,rootList,List.map_cons,List.map_map,donations,ordinaryTasks,Function.comp_def]

theorem input_group_complete (hcard : Fintype.card Root = Fintype.card C+1) :
    (inputGroup C packages out hmany).Perm (Finset.univ.toList.map packages) :=
  (root_list_complete C out hmany hcard).map packages

theorem output_ids
    (hcard : Fintype.card Root = Fintype.card C+1)
    (hlive : ∀ s, (packages s).live = some (frames s))
    (hvalid : ∀ s, (packages s).Valid)
    (hreflexive : ∀ s a, a ∈ (frames s).allowed a) :
    (outputPackage C p frames hpath packages gap out target hmany).ids.Perm
      (Finset.univ.toList.flatMap (fun s => (packages s).ids)) := by
  let s := ComponentAssignment.unused out.allocation hmany
  have h := merge_open_ids (packages s) (donations C p frames hpath packages gap out)
    (frames s) (RefinedChoresDeferredPayment.pay (frames s) C p (target s)) (hlive s) rfl
    (donors_wellFormed C p frames hpath packages gap out hlive hvalid hreflexive)
  have hin : (outputPackage C p frames hpath packages gap out target hmany).ids.Perm
      ((inputGroup C packages out hmany).flatMap Package.ids) := by
    rw [input_group_eq C p frames hpath packages gap out hmany]
    simpa only [outputPackage,s,List.flatMap_cons,List.flatMap_map] using h
  exact hin.trans (by simpa only [List.flatMap_map] using
    (input_group_complete C packages out hmany hcard).flatMap_right Package.ids)

/-- The weight used in the capacity/no-stall argument is the actual number
of original roots in the returned physical package. -/
theorem output_mass
    (hcard : Fintype.card Root = Fintype.card C+1)
    (hlive : ∀ s, (packages s).live = some (frames s))
    (hvalid : ∀ s, (packages s).Valid)
    (hreflexive : ∀ s a, a ∈ (frames s).allowed a) :
    (outputPackage C p frames hpath packages gap out target hmany).ids.length =
      ∑ s : Root, (packages s).ids.length := by
  have h := (output_ids C p frames hpath packages gap out target hmany
    hcard hlive hvalid hreflexive).length_eq
  simpa only [List.length_flatMap,Finset.sum_map_toList] using h

end EnvyFreeResearch.Full.RefinedChoresGroupIds
#print axioms EnvyFreeResearch.Full.RefinedChoresGroupIds.output_mass
