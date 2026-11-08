import EnvyFreeResearch.Full.ChoresOuterBatchCache

/-! A simultaneous batch cache agrees with each local group cache on every
root belonging to that group, including its frozen ancestors. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) (original : RootId → Snapshot.Output n)
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)

include good

theorem source_mem_package_ids (s t : Fin data.size)
    (hm : data.source t ∈ (data.packages s).ids) : t=s := by
  by_contra hne
  have hd := ComponentPhysical.package_ids_disjoint data.packages data.frames good.live
    (active_ids_distinct data original cost r H good) s t (Ne.symm hne)
  have ht := ComponentPhysical.live_mem_ids data.packages data.frames good.live t
  rw [good.source t] at ht
  exact List.disjoint_left.mp hd hm ht

theorem source_mem_group_ids (roots : List (Fin data.size)) (t : Fin data.size)
    (hm : data.source t ∈ roots.flatMap (fun s => (data.packages s).ids)) : t ∈ roots := by
  obtain ⟨s,hs,hid⟩ := List.mem_flatMap.mp hm
  exact (source_mem_package_ids data original cost r H good s t hid).symm ▸ hs

variable (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))

def GroupResult.localCache (out : GroupResult data hall cycle) : RootId → Fin n → List (Parent n) :=
  ComponentPhysical.patchCache (out.group.state data hall cycle).frames data.cache
    (out.nextCache data hall cycle original)

theorem batch_cache_group (outputs : List (GroupResult data hall cycle))
    (hnodup : (outputs.flatMap (fun out => out.group.roots)).Nodup)
    (g : Fin outputs.length) (root : RootId)
    (hroot : root ∈ (outputs.get g).group.roots.flatMap (fun s => (data.packages s).ids))
    (p : Fin n) :
    batchCache data hall cycle original outputs root p=
      (outputs.get g).localCache data original hall cycle root p := by
  let out := outputs.get g
  let state := out.group.state data hall cycle
  have hs (j : Fin out.group.roots.length) :
      (state.frames j).root=data.source (out.group.roots.get j) := good.source _
  by_cases hex : ∃ j : Fin out.group.roots.length, (state.frames j).root=root
  · obtain ⟨j,hj⟩ := hex
    have hglobal := batch_cache_slot data hall cycle original outputs hnodup
      (source_injective data original cost r H good) ⟨g,j⟩ p
    have hlocal := ComponentPhysical.patch_live state.frames data.cache
      (out.nextCache data hall cycle original)
      (fun i j he => out.group.nodup.injective_get
        ((source_injective data original cost r H good) ((hs i).symm.trans (he.trans (hs j))))) j p
    rw [hj] at hlocal
    change _=out.localCache data original hall cycle root p
    change _=ComponentPhysical.patchCache state.frames data.cache
      (out.nextCache data hall cycle original) root p
    rw [hlocal]
    change batchCache data hall cycle original outputs (data.source (out.group.roots.get j)) p=
      out.nextCache data hall cycle original j p at hglobal
    rw [← hs j,hj] at hglobal
    exact hglobal
  · have hav : ∀ slot : BatchSlot data hall cycle outputs,
        data.source (slotOld data hall cycle outputs slot) ≠ root := by
      intro slot heq
      have hm : data.source (slotOld data hall cycle outputs slot) ∈
          out.group.roots.flatMap (fun s => (data.packages s).ids) := heq ▸ hroot
      have ht := source_mem_group_ids data original cost r H good out.group.roots _ hm
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp ht
      apply hex
      refine ⟨j,?_⟩
      exact (hs j).trans ((congrArg data.source hj).trans heq)
    rw [batch_cache_other data hall cycle original outputs root hav p]
    exact (ComponentPhysical.patch_other state.frames data.cache
      (out.nextCache data hall cycle original) root (fun j hj => hex ⟨j,hj⟩) p).symm

end EnvyFreeResearch.Full.Chores.Outer
