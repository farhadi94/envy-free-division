import EnvyFreeResearch.Full.ChoresOuterGroupRestriction
import EnvyFreeResearch.Full.ChoresSchedulerPool

/-! Concrete disjoint old-pool cohorts, each with one more root than the
actual component-cycle task set. Each cohort restricts the same old state
and uses the same cycle, before any group output is committed. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Scheduler Components
open scoped Classical

variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))

structure Cohort where
  roots : List (Fin data.size)
  nodup : roots.Nodup
  length : roots.length=Fintype.card (ComponentBatch.Task data.pending hall cycle)+1

instance (group : Cohort data hall cycle) : Nonempty (Fin group.roots.length) :=
  ⟨⟨0,by rw [group.length]; omega⟩⟩

def Cohort.ofBatch (roots : List (Fin data.size))
    (h : roots ∈ Scheduler.groups (List.finRange data.size)
      (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1)) : Cohort data hall cycle where
  roots := roots
  nodup := (Scheduler.groups_nodup (List.finRange data.size) _ (List.nodup_finRange _)).sublist
    (List.sublist_flatten_of_mem h)
  length := Scheduler.group_length _ _ h

def cohorts : List (Cohort data hall cycle) :=
  (Scheduler.groups (List.finRange data.size)
    (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1)).attach.map
    (fun roots => Cohort.ofBatch data hall cycle roots.val roots.property)

theorem cohorts_roots :
    (cohorts data hall cycle).map Cohort.roots=Scheduler.groups (List.finRange data.size)
      (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1) := by
  simp only [cohorts,List.map_map,Cohort.ofBatch,Function.comp_def,List.attach_map_subtype_val]

theorem cohorts_length : (cohorts data hall cycle).length=
    data.size/(Fintype.card (ComponentBatch.Task data.pending hall cycle)+1) := by
  simp [cohorts]

theorem cohorts_disjoint : ((cohorts data hall cycle).map Cohort.roots).Pairwise List.Disjoint := by
  rw [cohorts_roots]
  exact (List.nodup_flatten.mp (Scheduler.groups_nodup (List.finRange data.size) _
    (List.nodup_finRange _))).2

def Cohort.state (group : Cohort data hall cycle) : Data n RootId := data.filter group.roots

theorem Cohort.all_pending (group : Cohort data hall cycle) :
    (group.state data hall cycle).pending.partition.labels ⊆ (group.state data hall cycle).pending.pending :=
  data.pending.restrict_all_pending group.roots.get hall

def Cohort.recordedCycle (group : Cohort data hall cycle) :
    ProposalCycle ((group.state data hall cycle).pending.outgoing (group.all_pending data hall cycle)) :=
  data.pending.restrictCycle group.roots.get hall cycle

theorem Cohort.selected (group : Cohort data hall cycle) :
    (group.state data hall cycle).pending.selected (group.all_pending data hall cycle)
      (group.recordedCycle data hall cycle)=data.pending.selected hall cycle := rfl

theorem Cohort.task_card (group : Cohort data hall cycle) :
    Fintype.card (ComponentBatch.Task (group.state data hall cycle).pending (group.all_pending data hall cycle)
      (group.recordedCycle data hall cycle))=Fintype.card (ComponentBatch.Task data.pending hall cycle) := rfl

theorem Cohort.more_roots (group : Cohort data hall cycle) :
    Fintype.card (ComponentBatch.Task (group.state data hall cycle).pending (group.all_pending data hall cycle)
      (group.recordedCycle data hall cycle)) < Fintype.card (Fin (group.state data hall cycle).size) := by
  rw [Fintype.card_fin,group.task_card]
  change _ < group.roots.length
  rw [group.length]
  omega

end EnvyFreeResearch.Full.Chores.Outer
