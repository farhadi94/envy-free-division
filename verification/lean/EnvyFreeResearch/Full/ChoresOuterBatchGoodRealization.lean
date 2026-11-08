import EnvyFreeResearch.Full.ChoresOuterBatchRealizationClosed
import EnvyFreeResearch.Full.ChoresOuterBatchGoodPackages
import EnvyFreeResearch.Full.ChoresOuterBatchCacheFacts

/-! Physical costs of each actual cohort output agree with the retained cache. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (r : Fin n → ℝ) (H : ℝ)
  (good : data.Good (fun root => xs.get (index root)) cost r H)
include hsound good

theorem group_cost_realized (out : GroupResult data hall cycle)
    (hout : out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (a : Allocation (Fin n) RootId)
    (ha : a ∈ (out.package data hall cycle (fun root => xs.get (index root))).allocations)
    (i p : Fin n) :
    a.cost i p=(cost i).real (material
      (out.localCache data (fun root => xs.get (index root)) hall cycle a.root p)) := by
  let state := out.group.state data hall cycle
  let original := fun root => xs.get (index root)
  have hg := filter_good data original cost r H good out.group.roots out.group.nodup
  apply ComponentBatch.output_cost_realized state.pending (out.group.all_pending data hall cycle)
    (out.group.recordedCycle data hall cycle) state.visited state.packages state.frames
    (originalGaps state original) out.result state.cache (equalizerCache state original)
    (offeredFrontier state original) cost (fun t q => (original (state.source t)).piece q)
    (offeredBlocks state original)
  · intro t q
    obtain ⟨U,hs⟩ := hsound (state.source t)
    exact valid_material_unit cost _ (hs.parent_cache q).1
  · exact offered_frontier_valid cost xs index c hsound state
  · exact offered_equalizer_valid cost xs index c hsound state
  · intro t q
    exact offered_equalizer_subset cost xs index c hsound state t q _
  · exact offered_blocks_complement cost xs index c hsound state
  · exact hout.2.2.1
  · intro t i p j
    obtain ⟨U,hs⟩ := hsound (state.source t)
    exact original_equalizer_value cost hs (state.frames t) (hg.original_frame t) i p j
  · intro t p i
    obtain ⟨U,hs⟩ := hsound (state.source t)
    exact original_gap cost hs (state.frames t) (hg.original_frame t) p i
  · exact hg.live
  · exact active_ids_distinct state original cost r H hg
  · exact active_frozen_cost state original cost r H hg
  · exact ha

omit hsound good in
theorem allocation_root_mem_ids (pkg : Package (Fin n) RootId) (a : Allocation (Fin n) RootId)
    (ha : a ∈ pkg.allocations) : a.root ∈ pkg.ids := by
  rw [← PackageGeometry.allocation_roots]
  exact List.mem_map.mpr ⟨a,ha,rfl⟩

variable (R : Set ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (goodR : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
include hsound hsep hr hH hscale goodR
omit good

theorem commit_batch_realized (outputs : List (GroupResult data hall cycle))
    (hout : ∀ out ∈ outputs, out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (hgroups : outputs.map GroupResult.group=cohorts data hall cycle)
    (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
    (a : Allocation (Fin n) RootId)
    (ha : a ∈ (commitBatch data hall cycle (fun root => xs.get (index root)) outputs keep hk).allPackages.flatMap Package.allocations)
    (i p : Fin n) :
    a.cost i p=(cost i).real (material
      (batchCache data hall cycle (fun root => xs.get (index root)) outputs a.root p)) := by
  let original := fun root => xs.get (index root)
  obtain ⟨pkg,hpkg,ha⟩ := List.mem_flatMap.mp ha
  rcases List.mem_append.mp hpkg with hc | hg
  · rcases List.mem_append.mp hc with hc | hl
    · have hid : a.root ∈ data.closed.flatMap Package.ids :=
        List.mem_flatMap.mpr ⟨pkg,hc,allocation_root_mem_ids pkg a ha⟩
      rw [batch_cache_closed data original cost _ H goodR hall cycle outputs a.root hid p]
      exact goodR.realized a (List.mem_flatMap.mpr ⟨pkg,List.mem_append_left _ hc,ha⟩) i p
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hl
      rw [package_close_allocations] at ha
      have hid := allocation_root_mem_ids (data.packages s) a ha
      have hmap := congrArg (List.map Cohort.roots) hgroups
      rw [List.map_map,cohorts_roots] at hmap
      have hflat := congrArg List.flatten hmap
      simp only [Function.comp_def] at hflat
      have hsnot : s ∉ outputs.flatMap (fun out => out.group.roots) := by
        intro hm
        have hm' : s ∈ (Scheduler.groups (List.finRange data.size)
          (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1)).flatten := hflat ▸ hm
        exact List.disjoint_left.mp (Scheduler.groups_leftovers_disjoint (List.finRange data.size)
          _ (List.nodup_finRange _)) hm' hs
      rw [batch_cache_unused data original cost _ H goodR hall cycle outputs s hsnot a.root hid p]
      exact goodR.realized a (List.mem_flatMap.mpr ⟨data.packages s,
        List.mem_append_right _ (List.mem_ofFn.mpr ⟨s,rfl⟩),ha⟩) i p
  · obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hg
    have hc := hout (outputs.get g) (List.get_mem _ _)
    have hid := allocation_root_mem_ids ((outputs.get g).package data hall cycle original) a ha
    have hold := (group_result_ids data hall cycle cost xs index c hsound R H hsep hr hH hscale
      goodR (outputs.get g) hc).mem_iff.mp hid
    rw [batch_cache_group data original cost _ H goodR hall cycle outputs
      (actual_slots_distinct data hall cycle outputs hgroups) g a.root hold p]
    exact group_cost_realized data hall cycle cost xs index c hsound _ H goodR (outputs.get g) hc a ha i p

end EnvyFreeResearch.Full.Chores.Outer
