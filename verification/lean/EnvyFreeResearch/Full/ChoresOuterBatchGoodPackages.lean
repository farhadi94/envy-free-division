import EnvyFreeResearch.Full.ChoresOuterBatchCommitIds

/-! Validity and root accounting of the full committed package pool. -/
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
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (outputs : List (GroupResult data hall cycle))
  (hout : ∀ out ∈ outputs, out.Correct data hall cycle cost (fun root => xs.get (index root)))
  (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
include good hout

theorem commit_batch_package_valid :
    PoolValid (commitBatch data hall cycle (fun root => xs.get (index root)) outputs keep hk).allPackages := by
  intro package hp
  rcases List.mem_append.mp hp with hc | ha
  · rcases List.mem_append.mp hc with hold | hleft
    · exact good.package_valid package (List.mem_append_left _ hold)
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hleft
      exact package_close_valid _ (active_package_valid data _ cost _ H good s)
  · obtain ⟨s,rfl⟩ := List.mem_ofFn.mp ha
    exact (hout (outputs.get s) (List.get_mem _ _)).1

include hsound hsep hr hH hscale

theorem commit_batch_all_ids
    (hgroups : outputs.map GroupResult.group=cohorts data hall cycle) :
    ((commitBatch data hall cycle (fun root => xs.get (index root)) outputs keep hk).allPackages.flatMap Package.ids).Perm
      Finset.univ.toList := by
  apply (commit_batch_ids_perm data hall cycle _ outputs keep hk hgroups ?_).trans good.all_ids
  intro out ho
  exact group_result_ids data hall cycle cost xs index c hsound R H hsep hr hH hscale good out (hout out ho)

end EnvyFreeResearch.Full.Chores.Outer
