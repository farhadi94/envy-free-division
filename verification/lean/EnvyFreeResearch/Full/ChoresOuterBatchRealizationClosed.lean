import EnvyFreeResearch.Full.ChoresOuterBatchRealization

/-! A simultaneous batch leaves old closed packages and unused live
packages physically unchanged. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) (original : RootId → Snapshot.Output n)
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))

include good

theorem batch_cache_closed (outputs : List (GroupResult data hall cycle)) (root : RootId)
    (hm : root ∈ data.closed.flatMap Package.ids) (p : Fin n) :
    batchCache data hall cycle original outputs root p=data.cache root p := by
  have hnd := good.all_ids.nodup_iff.mpr (Finset.nodup_toList _)
  rw [Data.allPackages,List.flatMap_append] at hnd
  have hd := hnd.disjoint
  apply batch_cache_other data hall cycle original outputs root
  intro slot heq
  let s := slotOld data hall cycle outputs slot
  have hs := ComponentPhysical.live_mem_ids data.packages data.frames good.live s
  rw [good.source s,heq] at hs
  exact List.disjoint_left.mp hd hm
    (List.mem_flatMap.mpr ⟨data.packages s,List.mem_ofFn.mpr ⟨s,rfl⟩,hs⟩)

theorem batch_cache_unused (outputs : List (GroupResult data hall cycle))
    (s : Fin data.size) (hs : s ∉ outputs.flatMap (fun out => out.group.roots))
    (root : RootId) (hm : root ∈ (data.packages s).ids) (p : Fin n) :
    batchCache data hall cycle original outputs root p=data.cache root p := by
  apply batch_cache_other data hall cycle original outputs root
  intro slot heq
  have he := source_mem_package_ids data original cost r H good s
    (slotOld data hall cycle outputs slot) (heq ▸ hm)
  apply hs
  rw [← he]
  exact List.mem_flatMap.mpr ⟨outputs.get slot.1,List.get_mem _ _,List.get_mem _ _⟩

end EnvyFreeResearch.Full.Chores.Outer
