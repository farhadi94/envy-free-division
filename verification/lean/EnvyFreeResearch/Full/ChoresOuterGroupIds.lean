import EnvyFreeResearch.Full.ChoresOuterBatchSlots

/-! Every completed cohort retains exactly the original roots of its input
packages, including every frozen ancestor. The local arithmetic hypotheses
are derived from the actual committed state and recorded scan. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open Components ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : Components.ProposalCycle (data.pending.outgoing hall))
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)

include hsound hsep hr hH hscale good

theorem group_result_ids (out : GroupResult data hall cycle)
    (hout : out.Correct data hall cycle cost (fun root => xs.get (index root))) :
    (out.package data hall cycle (fun root => xs.get (index root))).ids.Perm
      (out.group.roots.flatMap (fun s => (data.packages s).ids)) := by
  let state := out.group.state data hall cycle
  let all := out.group.all_pending data hall cycle
  let cc := out.group.recordedCycle data hall cycle
  let original := fun root => xs.get (index root)
  have hg : state.Good original cost (fun i => (cost i).real R) H :=
    filter_good data original cost (fun i => (cost i).real R) H good out.group.roots out.group.nodup
  have hequalized (s : Fin state.size) (p i : Fin n) :
      (state.frames s).equalizerCost i p i=(state.frames s).baseline i := by
    obtain ⟨U,hs⟩ := hsound (state.source s)
    exact original_equalized cost hs (state.frames s) (hg.original_frame s) p i
  have hforbidden (s : Fin state.size) (p : Fin n) (hp : p ∈ state.pending.selected all cc) :
      (state.frames s).forbidden p ⊆ state.pending.partition.component p := by
    have h := (hg.frontier s p).forbidden_internal
    change _ ⊆ state.pending.partition.component (state.pending.partition.representative p) at h
    simpa only [(state.pending.partition.mem_labels p).mp (state.pending.selected_subset all cc hp)] using h
  have hids := ComponentBatch.output_ids state.pending all cc state.visited state.packages state.frames
    (originalGaps state original) (out.group.more_roots data hall cycle) out.result cost
    (offeredBlocks state original) hout.2.2.1 hout.2.1 hout.2.2.2 hg.live
    (active_package_valid state original cost _ H hg) hg.allowed hequalized hforbidden
    (fun s p _ i => offered_frontier_value cost xs index c hsound R H state hg s p i)
    (fun p hp s i hi => offered_protection cost xs index c hsound R H hsep hr hH hscale state hg all
      p (state.pending.selected_subset all cc hp) s i hi)
    (fun s p hp i j hj => offered_containment cost xs index c hsound R H hr hH state hg all
      p (state.pending.selected_subset all cc hp) s i j hj)
    (by
      rw [Fintype.card_fin]
      change out.group.roots.length=Fintype.card (ComponentBatch.Task data.pending hall cycle)+1
      exact out.group.length)
  have hperm : (Finset.univ.toList : List (Fin out.group.roots.length)).Perm
      (List.finRange out.group.roots.length) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange _)).mpr
    intro s
    simp
  have hget : (List.finRange out.group.roots.length).map out.group.roots.get=out.group.roots := by
    simpa only [List.ofFn_eq_map] using (List.ofFn_get out.group.roots)
  have hmap := hperm.map out.group.roots.get
  rw [hget] at hmap
  have hflat := hmap.flatMap_right (fun s => (data.packages s).ids)
  apply hids.trans
  simp only [List.flatMap_map] at hflat
  exact hflat

end EnvyFreeResearch.Full.Chores.Outer
