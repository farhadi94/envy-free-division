import EnvyFreeResearch.Full.RefinedChoresDataFacts
import EnvyFreeResearch.Full.ChoresComponentRealization

/-! Generic physical cache patch for either an ordinary or terminal cohort.
Only the cohort's original live source IDs are updated. Frozen ancestry and
all untouched packages retain their actual physical caches. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId Root : Type*} [Fintype RootId] [Fintype Root]
    (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
    (roots : Root ↪ Fin data.size) (next : Root → Fin n → List (Parent n))

def patchedCache : RootId → Fin n → List (Parent n) :=
  ComponentPhysical.patchCache (data.frames ∘ roots) data.cache next

include good

theorem patch_on (s : Root) (p : Fin n) :
    patchedCache data roots next (data.source (roots s)) p = next s p := by
  rw [← good.source (roots s)]
  exact ComponentPhysical.patch_live (data.frames ∘ roots) data.cache next
    (fun a b h => roots.injective ((active_roots_injective data original cost r H good) h)) s p

theorem source_mem_package_ids (s t : Fin data.size)
    (hm : data.source t ∈ (data.packages s).ids) : t = s := by
  by_contra hne
  have hd := ComponentPhysical.package_ids_disjoint data.packages data.frames good.live
    (active_ids_distinct data original cost r H good) s t (Ne.symm hne)
  have ht := ComponentPhysical.live_mem_ids data.packages data.frames good.live t
  rw [good.source t] at ht
  exact List.disjoint_left.mp hd hm ht

theorem patch_unused (s : Fin data.size) (hs : s ∉ Set.range roots)
    (root : RootId) (hm : root ∈ (data.packages s).ids) (p : Fin n) :
    patchedCache data roots next root p = data.cache root p := by
  apply ComponentPhysical.patch_other
  intro j he
  change (data.frames (roots j)).root = root at he
  have hm' : data.source (roots j) ∈ (data.packages s).ids := by
    rwa [← good.source (roots j),he]
  exact hs ⟨j,source_mem_package_ids data original cost r H good s (roots j) hm'⟩

theorem patch_frozen (s : Fin data.size) (a : Allocation (Fin n) RootId)
    (ha : a ∈ (data.packages s).frozen) (p : Fin n) :
    patchedCache data roots next a.root p = data.cache a.root p := by
  apply ComponentPhysical.patch_other
  intro j he
  exact ComponentPhysical.frozen_root_not_live data.packages data.frames good.live
    (active_ids_distinct data original cost r H good) s (roots j) a ha he.symm

theorem patch_closed (root : RootId) (hm : root ∈ data.closed.flatMap Package.ids) (p : Fin n) :
    patchedCache data roots next root p = data.cache root p := by
  have hnd := good.all_ids.nodup_iff.mpr (Finset.nodup_toList _)
  rw [Data.allPackages,List.flatMap_append] at hnd
  have hd := hnd.disjoint
  apply ComponentPhysical.patch_other
  intro j he
  change (data.frames (roots j)).root = root at he
  have hs := ComponentPhysical.live_mem_ids data.packages data.frames good.live (roots j)
  rw [he] at hs
  exact List.disjoint_left.mp hd hm
    (List.mem_flatMap.mpr ⟨data.packages (roots j),List.mem_ofFn.mpr ⟨roots j,rfl⟩,hs⟩)

theorem patched_valid
    (hnext : ∀ s p, Valid (measureProfile cost) (next s p) ∧ Ordered (next s p))
    (root : RootId) (p : Fin n) :
    Valid (measureProfile cost) (patchedCache data roots next root p) ∧
      Ordered (patchedCache data roots next root p) :=
  ComponentPhysical.patch_valid (data.frames ∘ roots) (measureProfile cost) data.cache next
    good.cache hnext root p

theorem patched_subset
    (hnext : ∀ s p, material (next s p) ⊆ (original (data.source (roots s))).piece p)
    (root : RootId) (p : Fin n) :
    material (patchedCache data roots next root p) ⊆ (original root).piece p := by
  unfold patchedCache ComponentPhysical.patchCache
  split
  next h =>
    have he := h.choose_spec
    have hsource : data.source (roots h.choose) = root := (good.source _).symm.trans he
    simpa only [hsource] using hnext h.choose p
  next h => exact good.cache_subset root p

/-- A physical origin certificate names exactly the ways an allocation
can occur after replacing a cohort. -/
def AllocationOrigin (nextAllocation : Root → Allocation (Fin n) RootId)
    (a : Allocation (Fin n) RootId) : Prop :=
  a ∈ data.closed.flatMap Package.allocations ∨
  (∃ s, a ∈ (data.packages s).frozen) ∨
  (∃ s, s ∉ Set.range roots ∧ a = (data.frames s).allocation) ∨
  ∃ s, a = nextAllocation s

theorem patched_realizes (nextAllocation : Root → Allocation (Fin n) RootId)
    (hroot : ∀ s, (nextAllocation s).root = data.source (roots s))
    (hcost : ∀ s i p, (nextAllocation s).cost i p = (cost i).real (material (next s p)))
    (allocations : List (Allocation (Fin n) RootId))
    (horigin : ∀ a ∈ allocations, AllocationOrigin data roots nextAllocation a) :
    ∀ a ∈ allocations, ∀ i p,
      a.cost i p = (cost i).real (material (patchedCache data roots next a.root p)) := by
  intro a ha i p
  rcases horigin a ha with hclosed | ⟨s,hfrozen⟩ | ⟨s,houtside,rfl⟩ | ⟨s,rfl⟩
  · have hid : a.root ∈ data.closed.flatMap Package.ids := by
      rw [← PackageGeometry.pool_allocation_roots]
      exact List.mem_map.mpr ⟨a,hclosed,rfl⟩
    rw [patch_closed data original cost r H good roots next a.root hid p]
    apply good.realized a _ i p
    rw [Data.allPackages,List.flatMap_append]
    exact List.mem_append_left _ hclosed
  · rw [patch_frozen data original cost r H good roots next s a hfrozen p]
    exact active_frozen_cost data original cost r H good s a hfrozen i p
  · have hid := ComponentPhysical.live_mem_ids data.packages data.frames good.live s
    change (data.frames s).allocation.cost i p =
      (cost i).real (material (patchedCache data roots next (data.frames s).root p))
    rw [patch_unused data original cost r H good roots next s houtside _ hid p]
    apply good.realized _ _ i p
    apply List.mem_flatMap.mpr
    refine ⟨data.packages s,List.mem_append_right _ (List.mem_ofFn.mpr ⟨s,rfl⟩),?_⟩
    simp only [Package.allocations,good.live s,Option.toList_some,List.map_cons,List.map_nil]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · rw [hroot s,patch_on data original cost r H good roots next s p]
    exact hcost s i p

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.patched_realizes
