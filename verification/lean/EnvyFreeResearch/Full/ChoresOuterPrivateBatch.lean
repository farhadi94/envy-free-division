import EnvyFreeResearch.Full.ChoresOuterPrivateNext
import EnvyFreeResearch.Full.ChoresOuterBatchCache
import EnvyFreeResearch.Full.ChoresOuterNextCache

/-! Original suffix caches and the simultaneous batch complement update. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))

def equalizerSuffixCache (original : RootId → Snapshot.Output n)
    (s : Fin data.size) (p j : Fin n) : List (Parent n) :=
  ((original (data.source s)).equalizers (p,j)).parts.suffixParts

def GroupResult.nextPrivate (original : RootId → Snapshot.Output n)
    (out : GroupResult data hall cycle) : Fin out.group.roots.length → Fin n → List (Parent n) :=
  nextPrivateCache (out.group.state data hall cycle).pending
    (out.group.all_pending data hall cycle) (out.group.recordedCycle data hall cycle)
    (out.group.state data hall cycle).visited (out.group.state data hall cycle).frames
    (originalGaps (out.group.state data hall cycle) original) out.result
    (equalizerSuffixCache (out.group.state data hall cycle) original)

def batchPrivateCache (original : RootId → Snapshot.Output n)
    (oldPrivate : RootId → Fin n → List (Parent n))
    (outputs : List (GroupResult data hall cycle)) (root : RootId) (p : Fin n) : List (Parent n) :=
  if h : ∃ slot : BatchSlot data hall cycle outputs, data.source (slotOld data hall cycle outputs slot)=root
  then (outputs.get h.choose.1).nextPrivate data hall cycle original h.choose.2 p
  else oldPrivate root p

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
include hsound

theorem group_private_correct (out : GroupResult data hall cycle)
    (hout : out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (s : Fin out.group.roots.length) (p : Fin n) :
    CacheValid (measureProfile cost)
      ((xs.get (index (data.source (out.group.roots.get s)))).piece p \
        material (out.nextCache data hall cycle (fun root => xs.get (index root)) s p))
      (out.nextPrivate data hall cycle (fun root => xs.get (index root)) s p) := by
  let state := out.group.state data hall cycle
  let original := fun root => xs.get (index root)
  apply next_private_correct state.pending (out.group.all_pending data hall cycle)
    (out.group.recordedCycle data hall cycle) state.visited state.frames
    (originalGaps state original) out.result (equalizerCache state original)
    (equalizerSuffixCache state original) (offeredFrontier state original)
    cost (fun s => (original (state.source s)).piece) (offeredBlocks state original)
  · intro t q
    obtain ⟨U,hs⟩ := hsound (state.source t)
    exact valid_material_unit cost _ (hs.parent_cache q).1
  · exact offered_frontier_valid cost xs index c hsound state
  · exact offered_equalizer_valid cost xs index c hsound state
  · intro t q
    exact offered_equalizer_subset cost xs index c hsound state t q _
  · exact offered_blocks_complement cost xs index c hsound state
  · exact hout.2.2.1
  · intro t q j
    obtain ⟨U,hs⟩ := hsound (state.source t)
    exact private_equalizer cost _ c U hs q j

theorem batch_private_correct (oldPrivate : RootId → Fin n → List (Parent n))
    (outputs : List (GroupResult data hall cycle))
    (hold : PrivateCorrect (measureProfile cost) (fun r => (xs.get (index r)).piece) data.cache oldPrivate)
    (hout : ∀ out ∈ outputs, out.Correct data hall cycle cost (fun root => xs.get (index root))) :
    PrivateCorrect (measureProfile cost) (fun r => (xs.get (index r)).piece)
      (batchCache data hall cycle (fun root => xs.get (index root)) outputs)
      (batchPrivateCache data hall cycle (fun root => xs.get (index root)) oldPrivate outputs) := by
  intro r p
  unfold batchCache batchPrivateCache
  split
  next h =>
    have hh := group_private_correct data hall cycle cost xs index c hsound
      (outputs.get h.choose.1) (hout _ (List.get_mem _ _)) h.choose.2 p
    change CacheValid _ ((xs.get (index (data.source (slotOld data hall cycle outputs h.choose)))).piece p \ _) _ at hh
    simpa only [h.choose_spec] using hh
  next _ => exact hold r p
end EnvyFreeResearch.Full.Chores.Outer
