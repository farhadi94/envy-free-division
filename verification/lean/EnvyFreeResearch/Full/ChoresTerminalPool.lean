import EnvyFreeResearch.Full.ChoresOuterPackageFacts
import EnvyFreeResearch.Full.ChoresOuterPool

/-! Replacing the terminal active cohort retains all already closed
packages. Their physical pieces cannot be overwritten by a live-root patch. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) (original : RootId → Snapshot.Output n)
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)

include good

theorem closed_root_not_live (a : Allocation (Fin n) RootId)
    (ha : a ∈ data.closed.flatMap Package.allocations) (s : Fin data.size) :
    (data.frames s).root ≠ a.root := by
  have hd := good.all_ids.nodup_iff.mpr (Finset.nodup_toList _)
  rw [Outer.Data.allPackages,List.flatMap_append,List.nodup_append] at hd
  have har : a.root ∈ data.closed.flatMap Package.ids := by
    rw [← PackageGeometry.pool_allocation_roots]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  have hsr : (data.frames s).root ∈ (List.ofFn data.packages).flatMap Package.ids := by
    apply List.mem_flatMap.mpr
    refine ⟨data.packages s,List.mem_ofFn.mpr ⟨s,rfl⟩,?_⟩
    exact ComponentPhysical.live_mem_ids data.packages data.frames good.live s
  exact fun heq => hd.2.2 _ har _ hsr heq.symm

theorem closed_cost_after_patch (next : Fin data.size → Fin n → List (Parent n))
    (a : Allocation (Fin n) RootId) (ha : a ∈ data.closed.flatMap Package.allocations)
    (i p : Fin n) :
    a.cost i p=(cost i).real (material (ComponentPhysical.patchCache data.frames data.cache next a.root p)) := by
  rw [ComponentPhysical.patch_other data.frames data.cache next a.root
    (closed_root_not_live data original cost r H good a ha)]
  apply good.realized a _ i p
  rw [Outer.Data.allPackages,List.flatMap_append]
  exact List.mem_append_left _ ha

def finalPool (package : Package (Fin n) RootId) := data.closed++[package]

theorem final_pool_valid (package : Package (Fin n) RootId) (hp : package.Valid) :
    PoolValid (finalPool data package) := by
  intro pkg hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact good.package_valid pkg (List.mem_append_left _ hmem)
  · have heq := List.mem_singleton.mp hmem
    exact heq.symm ▸ hp

theorem final_pool_ids (package : Package (Fin n) RootId)
    (hids : package.ids.Perm ((List.ofFn data.packages).flatMap Package.ids)) :
    ((finalPool data package).flatMap Package.ids).Perm Finset.univ.toList := by
  have hp := hids.append_left (data.closed.flatMap Package.ids)
  apply List.Perm.trans _ good.all_ids
  simpa only [finalPool,Outer.Data.allPackages,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil] using hp

end EnvyFreeResearch.Full.Chores.Terminal
