import EnvyFreeResearch.Full.ChoresOuterBatchCommit

/-! The committed live cache is precisely the advanced original equalizer. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
  (original : RootId → Snapshot.Output n)

theorem group_survivor_cache (out : GroupResult data hall cycle) (p : Fin n) :
    out.nextCache data hall cycle original
      (ComponentAssignment.unused out.result.allocation (out.group.more_roots data hall cycle)) p=
      ((original (data.source (out.survivor data hall cycle))).equalizers
        (p,(ComponentFrames.advance data.pending hall cycle data.visited data.frames
          (out.survivor data hall cycle)).owner p)).parts.prefixParts := by
  unfold GroupResult.nextCache ComponentBatch.nextCache ComponentAssignment.dispatch
  split
  next h =>
    exact False.elim (ComponentAssignment.unused_spec out.result.allocation
      (out.group.more_roots data hall cycle) h.choose h.choose_spec)
  next _ =>
    have hf := data.pending.restrict_advance out.group.roots.get hall cycle data.visited data.frames
      (ComponentAssignment.unused out.result.allocation (out.group.more_roots data hall cycle))
    have ho := congrArg (fun f : Frame (Fin n) RootId => f.owner p) hf
    exact congrArg (fun j => ((original (data.source (out.survivor data hall cycle))).equalizers
      (p,j)).parts.prefixParts) ho

theorem commit_batch_live_cache (outputs : List (GroupResult data hall cycle))
    (hnodup : (outputs.flatMap (fun out => out.group.roots)).Nodup)
    (hsource : Function.Injective data.source)
    (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
    (s : Fin outputs.length) (p : Fin n) :
    (commitBatch data hall cycle original outputs keep hk).cache
      ((commitBatch data hall cycle original outputs keep hk).source s) p=
      ((original ((commitBatch data hall cycle original outputs keep hk).source s)).equalizers
        (p,((commitBatch data hall cycle original outputs keep hk).frames s).owner p)).parts.prefixParts := by
  let slot : BatchSlot data hall cycle outputs := ⟨s,ComponentAssignment.unused (outputs.get s).result.allocation
    ((outputs.get s).group.more_roots data hall cycle)⟩
  change batchCache data hall cycle original outputs (data.source (slotOld data hall cycle outputs slot)) p=_
  rw [batch_cache_slot data hall cycle original outputs hnodup hsource slot p]
  exact group_survivor_cache data hall cycle original (outputs.get s) p

end EnvyFreeResearch.Full.Chores.Outer
