import EnvyFreeResearch.Full.RefinedChoresData

/-! Exact finite-pool partition for replacing one cohort, shared by open
payments and terminal closed batches. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId Root : Type*} [Fintype Root]
    (data : Data n RootId) (roots : Root ↪ Fin data.size)

def selectedRoots : List (Fin data.size) := Finset.univ.toList.map roots
def remainingRoots : List (Fin data.size) :=
  (Finset.univ.filter (fun s => s ∉ Set.range roots)).toList

theorem selected_nodup : (selectedRoots data roots).Nodup :=
  (Finset.nodup_toList _).map roots.injective

theorem remaining_nodup : (remainingRoots data roots).Nodup := Finset.nodup_toList _

theorem selected_remaining_disjoint : List.Disjoint (selectedRoots data roots) (remainingRoots data roots) := by
  apply List.disjoint_left.mpr
  intro s hs ht
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hs
  have hn := (Finset.mem_filter.mp (Finset.mem_toList.mp ht)).2
  exact hn ⟨j,rfl⟩

theorem root_partition :
    (selectedRoots data roots ++ remainingRoots data roots).Perm (List.finRange data.size) := by
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_append.mpr ⟨selected_nodup data roots,remaining_nodup data roots,
      (fun a ha b hb hab => List.disjoint_left.mp (selected_remaining_disjoint data roots)
        ha (hab.symm ▸ hb))⟩) (List.nodup_finRange _)).mpr
  intro s
  constructor
  · intro _; exact List.mem_finRange s
  · intro _
    by_cases h : s ∈ Set.range roots
    · obtain ⟨j,rfl⟩ := h
      exact List.mem_append_left _ (List.mem_map.mpr ⟨j,by simp,rfl⟩)
    · exact List.mem_append_right _ (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨by simp,h⟩))

theorem remaining_count : (remainingRoots data roots).length + Fintype.card Root = data.size := by
  have h := (root_partition data roots).length_eq
  simpa only [List.length_append,selectedRoots,List.length_map,Finset.length_toList,
    Finset.card_univ,List.length_finRange,Nat.add_comm] using h

theorem remaining_not_selected (s : Fin (remainingRoots data roots).length) :
    (remainingRoots data roots).get s ∉ Set.range roots := by
  unfold remainingRoots at s ⊢
  exact (Finset.mem_filter.mp (Finset.mem_toList.mp (List.get_mem _ s))).2

/-- Replacing all selected packages by their one actual output preserves
exactly the multiset of original root IDs. -/
theorem replacement_ids (output : Package (Fin n) RootId)
    (houtput : output.ids.Perm (Finset.univ.toList.flatMap (fun s => (data.packages (roots s)).ids))) :
    ((output :: (remainingRoots data roots).map data.packages).flatMap Package.ids).Perm
      ((List.ofFn data.packages).flatMap Package.ids) := by
  have hpart := (root_partition data roots).flatMap_right (fun s => (data.packages s).ids)
  have hout := houtput.append (List.Perm.refl
    ((remainingRoots data roots).flatMap (fun s => (data.packages s).ids)))
  refine List.Perm.trans (l₂ := Finset.univ.toList.flatMap (fun s => (data.packages (roots s)).ids) ++
    (remainingRoots data roots).flatMap (fun s => (data.packages s).ids)) ?_ ?_
  · simpa only [List.flatMap_cons,List.flatMap_map] using hout
  · simpa only [List.flatMap_append,selectedRoots,List.flatMap_map,List.ofFn_eq_map] using hpart

/-- Closing the unused packages changes neither their original root IDs
nor the replacement identity. -/
theorem closed_replacement_ids (output : Package (Fin n) RootId)
    (houtput : output.ids.Perm (Finset.univ.toList.flatMap (fun s => (data.packages (roots s)).ids))) :
    ((output :: (remainingRoots data roots).map (fun s => (data.packages s).close)).flatMap Package.ids).Perm
      ((List.ofFn data.packages).flatMap Package.ids) := by
  simpa only [List.flatMap_cons,List.flatMap_map,package_close_ids] using replacement_ids data roots output houtput

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.replacement_ids
