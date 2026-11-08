import EnvyFreeResearch.Full.ChoresOuterData

/-! Full semantic preservation for the concrete filtering and pending
revelation updates. Rejected packages close without changing any physical
piece; retained source indices are literal old indices. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) (original : RootId → Snapshot.Output n)
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)

include good

theorem filter_good (kept : List (Fin data.size)) (hk : kept.Nodup) :
    (data.filter kept).Good original cost r H := by
  have hp : ∀ s, (data.packages s).Valid := by
    intro s
    apply good.package_valid
    apply List.mem_append.mpr
    right
    exact List.mem_ofFn.mpr ⟨s,rfl⟩
  have hc : PoolValid data.closed := fun package hpackage =>
    good.package_valid package (List.mem_append.mpr (Or.inl hpackage))
  constructor
  · rw [filter_package_list]
    exact filtered_valid (List.finRange data.size) kept (fun s _ => List.mem_finRange s)
      data.packages data.closed hc (fun s _ => hp s)
  · exact (filter_ids_perm data kept hk).trans good.all_ids
  · intro package hpackage
    obtain hpackage | hpackage := List.mem_append.mp hpackage
    · exact good.closed package hpackage
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hpackage
      exact package_close_live _
  · exact fun s => good.live (kept.get s)
  · exact fun s => good.source (kept.get s)
  · exact fun s => good.original_frame (kept.get s)
  · exact good.cache
  · exact good.cache_subset
  · intro a ha i p
    exact good.realized a ((filter_allocations_perm data kept hk).mem_iff.mp ha) i p
  · exact fun s p => good.live_cache (kept.get s) p
  · exact fun s p i => good.allowed (kept.get s) p i
  · exact fun s p => good.frontier (kept.get s) p
  · exact fun s i p => good.frontier_value (kept.get s) i p
  · intro p proposed hproposed s
    obtain ⟨old,hold,rfl⟩ := Option.map_eq_some_iff.mp hproposed
    exact good.pending_scan p old hold (kept.get s)
  · exact good.complement_small

theorem reveal_good (p : Fin n) (hp : p ∈ data.pending.partition.labels)
    (proposed : Scheduler.Proposal (Fin data.size) (Fin n))
    (hvalid : proposed.Valid data.pending.partition p)
    (hscan : ∀ s, Frontier.scan (original (data.source s)).equalizers p r H
      (data.pending.partition.component p)=Frontier.Outcome.outside (proposed.nextAgent s)) :
    (data.reveal p hp proposed hvalid).Good original cost r H := by
  constructor
  · exact good.package_valid
  · exact good.all_ids
  · exact good.closed
  · exact good.live
  · exact good.source
  · exact good.original_frame
  · exact good.cache
  · exact good.cache_subset
  · exact good.realized
  · exact good.live_cache
  · exact good.allowed
  · exact good.frontier
  · exact good.frontier_value
  · intro q prop hprop s
    change Function.update data.pending.proposals p (some proposed) q=some prop at hprop
    by_cases hq : q=p
    · subst q
      rw [Function.update_self] at hprop
      have heq : proposed=prop := Option.some.inj hprop
      subst prop
      exact hscan s
    · rw [Function.update_of_ne hq] at hprop
      exact good.pending_scan q prop hprop s
  · exact good.complement_small

end EnvyFreeResearch.Full.Chores.Outer
