import EnvyFreeResearch.Full.ChoresOuterBatchProgram
import EnvyFreeResearch.Full.ChoresOuterGroupFrames

/-! Every physical group slot and survivor refers to a distinct old root.
The actual group live frame agrees with the common component merger. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))

def GroupResult.survivor (out : GroupResult data hall cycle) : Fin data.size :=
  out.group.roots.get (ComponentAssignment.unused out.result.allocation (out.group.more_roots data hall cycle))

theorem GroupResult.survivor_mem (out : GroupResult data hall cycle) :
    out.survivor data hall cycle ∈ out.group.roots := List.get_mem _ _

theorem GroupResult.live_frame (original : RootId → Snapshot.Output n) (out : GroupResult data hall cycle) :
    (out.package data hall cycle original).live=some
      (ComponentFrames.advance data.pending hall cycle data.visited data.frames (out.survivor data hall cycle)) := by
  change some (ComponentFrames.advance (out.group.state data hall cycle).pending
    (out.group.all_pending data hall cycle) (out.group.recordedCycle data hall cycle)
    (out.group.state data hall cycle).visited (out.group.state data hall cycle).frames
    (ComponentAssignment.unused out.result.allocation (out.group.more_roots data hall cycle)))=some _
  apply congrArg some
  exact data.pending.restrict_advance out.group.roots.get hall cycle data.visited data.frames _

def BatchSlot (outputs : List (GroupResult data hall cycle)) :=
  (g : Fin outputs.length) × Fin (outputs.get g).group.roots.length

def slotOld (outputs : List (GroupResult data hall cycle)) (slot : BatchSlot data hall cycle outputs) : Fin data.size :=
  (outputs.get slot.1).group.roots.get slot.2

theorem slot_old_injective (outputs : List (GroupResult data hall cycle))
    (hnodup : (outputs.flatMap (fun out => out.group.roots)).Nodup) :
    Function.Injective (slotOld data hall cycle outputs) := by
  have hpair : outputs.Pairwise (fun a b => List.Disjoint a.group.roots b.group.roots) := by
    have hp := (List.nodup_flatten.mp hnodup).2
    simpa only [List.pairwise_map] using hp
  rintro ⟨g,i⟩ ⟨k,j⟩ heq
  change (outputs.get g).group.roots.get i=(outputs.get k).group.roots.get j at heq
  by_cases hgk : g=k
  · subst k
    have hij : i=j := (outputs.get g).group.nodup.injective_get heq
    subst j
    rfl
  · exfalso
    rcases lt_or_gt_of_ne hgk with hlt | hgt
    · have hd := hpair.rel_get_of_lt hlt
      exact List.disjoint_left.mp hd (List.get_mem _ i) (heq.symm ▸ List.get_mem _ j)
    · have hd := hpair.rel_get_of_lt hgt
      exact List.disjoint_left.mp hd (List.get_mem _ j) (heq ▸ List.get_mem _ i)

theorem actual_slots_distinct (outputs : List (GroupResult data hall cycle))
    (hgroups : outputs.map GroupResult.group=cohorts data hall cycle) :
    (outputs.flatMap (fun out => out.group.roots)).Nodup := by
  have hg := congrArg (List.map Cohort.roots) hgroups
  rw [List.map_map,cohorts_roots] at hg
  have hf := congrArg List.flatten hg
  have h := Scheduler.groups_nodup (List.finRange data.size)
    (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1) (List.nodup_finRange _)
  rw [← hf] at h
  simpa only [List.flatMap,Function.comp_def] using h

theorem batch_survivors_distinct (outputs : List (GroupResult data hall cycle))
    (hnodup : (outputs.flatMap (fun out => out.group.roots)).Nodup) :
    (outputs.map (GroupResult.survivor data hall cycle)).Nodup := by
  induction outputs with
  | nil => simp
  | cons out rest ih =>
    have hsplit := List.nodup_append.mp hnodup
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hsplit.2.1⟩
    intro hm
    obtain ⟨other,ho,heq⟩ := List.mem_map.mp hm
    have hr : out.survivor data hall cycle ∈ rest.flatMap (fun out => out.group.roots) :=
      List.mem_flatMap.mpr ⟨other,ho,heq ▸ other.survivor_mem data hall cycle⟩
    exact hsplit.2.2 _ (out.survivor_mem data hall cycle) _ hr rfl

end EnvyFreeResearch.Full.Chores.Outer
