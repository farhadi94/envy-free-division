import EnvyFreeResearch.Full.ChoresOuterBatchCommit

/-! The actual old-pool partition retains all root IDs exactly once. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
  (original : RootId → Snapshot.Output n) (outputs : List (GroupResult data hall cycle))
  (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)

theorem commit_batch_ids_perm
    (hgroups : outputs.map GroupResult.group=cohorts data hall cycle)
    (hids : ∀ out ∈ outputs, (out.package data hall cycle original).ids.Perm
      (out.group.roots.flatMap (fun s => (data.packages s).ids))) :
    ((commitBatch data hall cycle original outputs keep hk).allPackages.flatMap Package.ids).Perm
      (data.allPackages.flatMap Package.ids) := by
  let leftover := Scheduler.leftovers (List.finRange data.size)
    (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1)
  have hg := congrArg (List.map Cohort.roots) hgroups
  rw [List.map_map,cohorts_roots] at hg
  have hflatten := congrArg List.flatten hg
  simp only [Function.comp_def] at hflatten
  have hpartition : outputs.flatMap (fun out => out.group.roots) ++ leftover=List.finRange data.size := by
    change (outputs.map (fun out => out.group.roots)).flatten ++ leftover=_
    rw [hflatten]
    exact Scheduler.batches_partition _ _
  have hp := List.Perm.flatMap_left outputs hids
  have hperm : (leftover ++ outputs.flatMap (fun out => out.group.roots)).Perm (List.finRange data.size) := by
    rw [← hpartition]
    exact List.perm_append_comm
  have hrest := (hperm.flatMap_right (fun s => (data.packages s).ids))
  have hjoin := (hp.append_left (leftover.flatMap (fun s => (data.packages s).ids))).trans (by
    simpa only [List.flatMap_append,List.flatMap_assoc] using hrest)
  have h := hjoin.append_left (data.closed.flatMap Package.ids)
  have hof : List.ofFn (fun s : Fin outputs.length =>
      (outputs.get s).package data hall cycle original)=outputs.map (fun out => out.package data hall cycle original) :=
    List.ofFn_getElem_eq_map outputs _
  simpa only [Data.allPackages,commitBatch,List.flatMap_append,List.flatMap_map,
    hof,Function.comp_def,package_close_ids,List.append_assoc,List.ofFn_eq_map] using h

end EnvyFreeResearch.Full.Chores.Outer
