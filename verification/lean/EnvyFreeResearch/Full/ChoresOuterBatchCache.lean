import EnvyFreeResearch.Full.ChoresOuterGroupIds

/-! Simultaneous physical cache updates over disjoint old-state cohorts. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))

def GroupResult.nextCache (original : RootId → Snapshot.Output n)
    (out : GroupResult data hall cycle) : Fin out.group.roots.length → Fin n → List (Parent n) :=
  ComponentBatch.nextCache (out.group.state data hall cycle).pending
    (out.group.all_pending data hall cycle) (out.group.recordedCycle data hall cycle)
    (out.group.state data hall cycle).visited (out.group.state data hall cycle).frames
    (originalGaps (out.group.state data hall cycle) original) out.result
    (equalizerCache (out.group.state data hall cycle) original)
    (offeredFrontier (out.group.state data hall cycle) original)

def batchCache (original : RootId → Snapshot.Output n)
    (outputs : List (GroupResult data hall cycle)) (root : RootId) (p : Fin n) : List (Parent n) :=
  if h : ∃ slot : BatchSlot data hall cycle outputs, data.source (slotOld data hall cycle outputs slot)=root
  then (outputs.get h.choose.1).nextCache data hall cycle original h.choose.2 p
  else data.cache root p

theorem batch_cache_slot (original : RootId → Snapshot.Output n)
    (outputs : List (GroupResult data hall cycle))
    (hnodup : (outputs.flatMap (fun out => out.group.roots)).Nodup)
    (hsource : Function.Injective data.source)
    (slot : BatchSlot data hall cycle outputs) (p : Fin n) :
    batchCache data hall cycle original outputs (data.source (slotOld data hall cycle outputs slot)) p=
      (outputs.get slot.1).nextCache data hall cycle original slot.2 p := by
  have h : ∃ t : BatchSlot data hall cycle outputs,
      data.source (slotOld data hall cycle outputs t)=data.source (slotOld data hall cycle outputs slot) := ⟨slot,rfl⟩
  have heq : h.choose=slot := slot_old_injective data hall cycle outputs hnodup (hsource h.choose_spec)
  rw [batchCache, dif_pos h]
  exact congrArg (fun t : BatchSlot data hall cycle outputs =>
    (outputs.get t.1).nextCache data hall cycle original t.2 p) heq

theorem batch_cache_other (original : RootId → Snapshot.Output n)
    (outputs : List (GroupResult data hall cycle)) (root : RootId)
    (hother : ∀ slot : BatchSlot data hall cycle outputs,
      data.source (slotOld data hall cycle outputs slot) ≠ root) (p : Fin n) :
    batchCache data hall cycle original outputs root p=data.cache root p := by
  unfold batchCache
  rw [dif_neg (show ¬ ∃ slot : BatchSlot data hall cycle outputs,
    data.source (slotOld data hall cycle outputs slot)=root from fun ⟨s,hs⟩ => hother s hs)]

theorem batch_cache_valid (original : RootId → Snapshot.Output n)
    (outputs : List (GroupResult data hall cycle)) (P : Profile (Fin n))
    (hold : ∀ root p, Valid P (data.cache root p) ∧ Ordered (data.cache root p))
    (hnext : ∀ slot : BatchSlot data hall cycle outputs, ∀ p,
      Valid P ((outputs.get slot.1).nextCache data hall cycle original slot.2 p) ∧
      Ordered ((outputs.get slot.1).nextCache data hall cycle original slot.2 p)) (root : RootId) (p : Fin n) :
    Valid P (batchCache data hall cycle original outputs root p) ∧
      Ordered (batchCache data hall cycle original outputs root p) := by
  unfold batchCache
  split
  · exact hnext _ p
  · exact hold root p

end EnvyFreeResearch.Full.Chores.Outer
