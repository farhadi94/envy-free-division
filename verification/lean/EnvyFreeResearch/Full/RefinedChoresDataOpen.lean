import EnvyFreeResearch.Full.RefinedChoresDataPatch
import EnvyFreeResearch.Full.RefinedChoresCohort

/-! Generic commit of a physical ordinary cohort into the root-local pool.
The local output is supplied with its ledger/graph facts; cache semantics
are obtained through the concrete source-root patch, including unchanged
frozen ancestors and untouched active packages. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Frontier ChoreComposition RefinedChoresRootState RefinedChoresStateCapacity
open scoped Classical
variable {n : ℕ} {RootId Root : Type*} [Fintype Root]

structure LiveOutput (data : Data n RootId) where
  source : RootId
  frame : Frame (Fin n) RootId
  package : Package (Fin n) RootId
  tracked : Tracked frame
  protected_fixed : tracked.state.partition.representative data.protectedLabel = data.protectedLabel
  frontier : Fin n → Fin n

variable (data : Data n RootId) (roots : Root ↪ Fin data.size) (out : LiveOutput data)
    (next : Root → Fin n → List (Parent n))

def commitOpen : Data n RootId where
  size := (remainingRoots data roots).length+1
  source := Fin.cons out.source (fun i => data.source ((remainingRoots data roots).get i))
  packages := Fin.cons out.package (fun i => data.packages ((remainingRoots data roots).get i))
  frames := Fin.cons out.frame (fun i => data.frames ((remainingRoots data roots).get i))
  tracked := Fin.cases out.tracked (fun i => data.tracked ((remainingRoots data roots).get i))
  protectedLabel := data.protectedLabel
  protected_fixed := Fin.cases out.protected_fixed (fun i => data.protected_fixed ((remainingRoots data roots).get i))
  frontier := Fin.cons out.frontier (fun i => data.frontier ((remainingRoots data roots).get i))
  cache := patchedCache data roots next
  closed := data.closed

theorem commit_packages : (commitOpen data roots out next).allPackages =
    data.closed ++ out.package :: (remainingRoots data roots).map data.packages := by
  simp only [Data.allPackages,commitOpen,List.ofFn_cons]
  congr 2
  exact List.ofFn_getElem_eq_map (remainingRoots data roots) data.packages

theorem commit_decreases (htwo : 2 ≤ Fintype.card Root) :
    (commitOpen data roots out next).size < data.size := by
  have h := remaining_count data roots
  change (remainingRoots data roots).length+1 < data.size
  omega

variable [Fintype RootId] (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)

structure LiveOutput.Good : Prop where
  valid : out.package.Valid
  live : out.package.live = some out.frame
  source : out.frame.root = out.source
  original_frame : Outer.OriginalFrame out.frame (original out.source)
  frontier : ∀ p, RefinedChoresPendingFrontier.Pending
    (weight (original out.source).equalizers p) (rankOf (original out.source).equalizers p) r H
    (eligible (weight (original out.source).equalizers p) (rankOf (original out.source).equalizers p) r H)
    (componentSet out.tracked.state (out.tracked.state.component p))
    (out.frame.allowed p) (out.frame.forbidden p) (out.frontier p)
  frontier_value : ∀ i p, out.frame.frontierGap i p = out.frame.gap i (out.frontier p) p
  weight_bounded : out.package.ids.length ≤ capacity out.tracked.state

include good

theorem commit_good
    (hout : LiveOutput.Good data out original r H)
    (hids : out.package.ids.Perm (Finset.univ.toList.flatMap (fun s => (data.packages (roots s)).ids)))
    (hnextvalid : ∀ s p, Valid (measureProfile cost) (next s p) ∧ Ordered (next s p))
    (hnextsub : ∀ s p, material (next s p) ⊆ (original (data.source (roots s))).piece p)
    (hnextsmall : ∀ s p i, (cost i).real ((original (data.source (roots s))).piece p \ material (next s p)) ≤ (n:ℝ)*r i/H)
    (hnewcache : ∀ p, patchedCache data roots next out.source p =
      ((original out.source).equalizers (p,p)).parts.prefixParts)
    (nextAllocation : Root → Allocation (Fin n) RootId)
    (hroot : ∀ s, (nextAllocation s).root = data.source (roots s))
    (hcost : ∀ s i p, (nextAllocation s).cost i p = (cost i).real (material (next s p)))
    (horigin : ∀ a ∈ out.package.allocations, AllocationOrigin data roots nextAllocation a) :
    (commitOpen data roots out next).Good original cost r H := by
  have hreal : ∀ a ∈ (commitOpen data roots out next).allPackages.flatMap Package.allocations,
      ∀ i p, a.cost i p = (cost i).real (material (patchedCache data roots next a.root p)) := by
    apply patched_realizes data original cost r H good roots next nextAllocation hroot hcost
    intro a ha
    rw [commit_packages,List.flatMap_append,List.flatMap_cons] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact horigin a ha
      · obtain ⟨package,hpackage,ha⟩ := List.mem_flatMap.mp ha
        obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hpackage
        simp only [Package.allocations,good.live s,Option.toList_some,List.map_cons,List.map_nil] at ha
        rcases List.mem_append.mp ha with hfrozen | hlive
        · exact Or.inr (Or.inl ⟨s,hfrozen⟩)
        · refine Or.inr (Or.inr (Or.inl ⟨s,?_,List.mem_singleton.mp hlive⟩))
          exact (Finset.mem_filter.mp (Finset.mem_toList.mp hs)).2
  refine {
    package_valid := ?_
    all_ids := ?_
    closed := good.closed
    live := ?_
    source := ?_
    original_frame := ?_
    cache := patched_valid data original cost r H good roots next hnextvalid
    cache_subset := patched_subset data original cost r H good roots next hnextsub
    realized := hreal
    live_cache := ?_
    frontier := ?_
    frontier_value := ?_
    weight_bounded := ?_
    complement_small := ?_ }
  · intro package hp
    rw [commit_packages] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact good.package_valid package (List.mem_append_left _ hp)
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact hout.valid
      · obtain ⟨s,_,rfl⟩ := List.mem_map.mp hp
        exact active_package_valid data original cost r H good s
  · rw [commit_packages,List.flatMap_append]
    have h := (replacement_ids data roots out.package hids).append_left
      (data.closed.flatMap Package.ids)
    exact h.trans (by simpa only [Data.allPackages,List.flatMap_append] using good.all_ids)
  · intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · exact hout.live
    · exact good.live _
  · intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · exact hout.source
    · exact good.source _
  · intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · exact hout.original_frame
    · exact good.original_frame _
  · intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · exact hnewcache
    · intro p
      let t := (remainingRoots data roots).get i
      have hid := ComponentPhysical.live_mem_ids data.packages data.frames good.live t
      rw [good.source t] at hid
      exact (patch_unused data original cost r H good roots next t (remaining_not_selected data roots i)
        (data.source t) hid p).trans (good.live_cache t p)
  · intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · exact hout.frontier
    · exact good.frontier _
  · intro s
    refine Fin.cases ?_ (fun j => ?_) s
    · exact hout.frontier_value
    · exact good.frontier_value _
  · intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · exact hout.weight_bounded
    · exact good.weight_bounded _
  · intro root p i
    change (cost i).real ((original root).piece p \ material (patchedCache data roots next root p)) ≤ _
    unfold patchedCache ComponentPhysical.patchCache
    split
    next h =>
      have he : data.source (roots h.choose) = root := (good.source _).symm.trans h.choose_spec
      simpa only [he] using hnextsmall h.choose p i
    next h => exact good.complement_small root p i

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.commit_good
