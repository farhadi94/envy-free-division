import EnvyFreeResearch.Full.ChoresOuterOffers

/-! Global committed-root accounting supplies the local group's distinct
root and frozen-ancestor hypotheses. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) (original : RootId → Snapshot.Output n)
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)

include good

theorem active_package_valid (s : Fin data.size) : (data.packages s).Valid := by
  apply good.package_valid
  apply List.mem_append_right
  exact List.mem_ofFn.mpr ⟨s,rfl⟩

theorem active_frozen_cost (s : Fin data.size) (a : Allocation (Fin n) RootId)
    (ha : a ∈ (data.packages s).frozen) (i p : Fin n) :
    a.cost i p=(cost i).real (material (data.cache a.root p)) := by
  apply good.realized a _ i p
  apply List.mem_flatMap.mpr
  refine ⟨data.packages s,List.mem_append_right _ (List.mem_ofFn.mpr ⟨s,rfl⟩),?_⟩
  exact List.mem_append_left _ ha

theorem active_ids_distinct :
    (Finset.univ.toList.flatMap (fun s => (data.packages s).ids)).Nodup := by
  have hnd := good.all_ids.nodup_iff.mpr (Finset.nodup_toList _)
  have htail : ((List.ofFn data.packages).flatMap Package.ids).Nodup := by
    rw [Data.allPackages,List.flatMap_append,List.nodup_append] at hnd
    exact hnd.2.1
  have hperm : (Finset.univ.toList : List (Fin data.size)).Perm (List.finRange data.size) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange _)).mpr
    intro s
    simp
  have hp := hperm.flatMap_right (fun s => (data.packages s).ids)
  apply hp.nodup_iff.mpr
  simpa only [List.ofFn_eq_map,List.flatMap_map] using htail

theorem active_roots_injective : Function.Injective (fun s => (data.frames s).root) :=
  ComponentPhysical.live_roots_injective data.packages data.frames good.live
    (active_ids_distinct data original cost r H good)

theorem source_injective : Function.Injective data.source := by
  intro s t h
  apply active_roots_injective data original cost r H good
  simpa only [good.source] using h

end EnvyFreeResearch.Full.Chores.Outer
