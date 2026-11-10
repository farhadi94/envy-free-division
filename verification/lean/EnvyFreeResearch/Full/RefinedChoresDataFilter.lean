import EnvyFreeResearch.Full.RefinedChoresDataMass
import EnvyFreeResearch.Full.ChoresOuterFiltering

/-! Initial finite selection retains every unselected original root as a
closed package. Its physical fragments remain in the full pool. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open ChoreComposition
open scoped Classical BigOperators
variable {n k : ℕ} {RootId : Type*} (data : Data n RootId) (roots : Fin k ↪ Fin data.size)

def filterData : Data n RootId where
  size := k
  source := data.source ∘ roots
  packages := data.packages ∘ roots
  frames := data.frames ∘ roots
  tracked := fun s => data.tracked (roots s)
  protectedLabel := data.protectedLabel
  protected_fixed := fun s => data.protected_fixed (roots s)
  frontier := data.frontier ∘ roots
  cache := data.cache
  closed := data.closed ++ (remainingRoots data roots).map (fun s => (data.packages s).close)

theorem filter_ids : ((filterData data roots).allPackages.flatMap Package.ids).Perm
    (data.allPackages.flatMap Package.ids) := by
  have hp := (root_partition data roots).flatMap_right (fun s => (data.packages s).ids)
  have hfin : (List.finRange k).Perm (Finset.univ : Finset (Fin k)).toList := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_finRange k) (Finset.nodup_toList _)).mpr
    intro i
    simp
  have hsel : ((List.ofFn (data.packages ∘ roots)).flatMap Package.ids).Perm
      ((selectedRoots data roots).flatMap (fun s => (data.packages s).ids)) := by
    simpa only [selectedRoots,List.flatMap_map,List.ofFn_eq_map,Function.comp_def] using
      hfin.flatMap_right (fun s => (data.packages (roots s)).ids)
  have he : ((filterData data roots).allPackages.flatMap Package.ids).Perm
      (data.closed.flatMap Package.ids ++
        (remainingRoots data roots).flatMap (fun s => (data.packages s).ids) ++
        (selectedRoots data roots).flatMap (fun s => (data.packages s).ids)) := by
    simpa only [Data.allPackages,filterData,List.flatMap_append,List.flatMap_map,package_close_ids] using
      hsel.append_left (data.closed.flatMap Package.ids ++
        (remainingRoots data roots).flatMap (fun s => (data.packages s).ids))
  apply he.trans
  have hc := List.perm_append_comm
    (l₁ := (remainingRoots data roots).flatMap (fun s => (data.packages s).ids))
    (l₂ := (selectedRoots data roots).flatMap (fun s => (data.packages s).ids))
  have h := hc.trans (by simpa only [List.flatMap_append] using hp)
  simpa only [Data.allPackages,List.flatMap_append,List.ofFn_eq_map,List.flatMap_map,List.append_assoc] using
    h.append_left (data.closed.flatMap Package.ids)

variable [Fintype RootId] (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
include good

theorem filter_good : (filterData data roots).Good original cost r H := by
  refine { good with
    package_valid := ?_
    all_ids := (filter_ids data roots).trans good.all_ids
    closed := ?_
    live := fun s => good.live (roots s)
    source := fun s => good.source (roots s)
    original_frame := fun s => good.original_frame (roots s)
    realized := ?_
    live_cache := fun s => good.live_cache (roots s)
    frontier := fun s => good.frontier (roots s)
    frontier_value := fun s => good.frontier_value (roots s)
    weight_bounded := fun s => good.weight_bounded (roots s) }
  · intro package hp
    simp only [Data.allPackages,filterData,List.mem_append,List.mem_map,List.mem_ofFn] at hp
    rcases hp with (hp | ⟨s,_,rfl⟩) | ⟨s,rfl⟩
    · exact good.package_valid package (List.mem_append_left _ hp)
    · exact package_close_valid _ (active_package_valid data original cost r H good s)
    · exact active_package_valid data original cost r H good (roots s)
  · intro package hp
    rcases List.mem_append.mp hp with hp | hp
    · exact good.closed package hp
    · obtain ⟨s,_,rfl⟩ := List.mem_map.mp hp
      exact package_close_live _
  · intro a ha i p
    obtain ⟨package,hpackage,ha⟩ := List.mem_flatMap.mp ha
    simp only [Data.allPackages,filterData,List.mem_append,List.mem_map,List.mem_ofFn] at hpackage
    rcases hpackage with (hp | ⟨s,_,rfl⟩) | ⟨s,rfl⟩
    · exact good.realized a (List.mem_flatMap.mpr ⟨package,List.mem_append_left _ hp,ha⟩) i p
    · rw [Outer.package_close_allocations] at ha
      exact good.realized a (List.mem_flatMap.mpr ⟨_,List.mem_append_right _ (List.mem_ofFn.mpr ⟨s,rfl⟩),ha⟩) i p
    · exact good.realized a (List.mem_flatMap.mpr ⟨_,List.mem_append_right _ (List.mem_ofFn.mpr ⟨roots s,rfl⟩),ha⟩) i p

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.filter_good
