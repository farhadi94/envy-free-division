import EnvyFreeResearch.Full.ChoresOuterOutside

/-! The actual component merger preserves old components and every
unselected proposal. Selected frontiers advance to their recorded
outside marks; all other frontiers retain their old atom certificates. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open scoped Classical

namespace Scheduler.Partition
variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

theorem component_merge_mono (P : Partition Agent) (selected : Finset Agent)
    (keep : Agent) (hsub : selected ⊆ P.labels) (hk : keep ∈ selected) (p : Agent) :
    P.component (P.representative p) ⊆
      (P.merge selected keep hsub hk).component ((P.merge selected keep hsub hk).representative p) := by
  intro i hi
  apply (mem_component _ _ _).mpr
  exact (P.merge_relation selected keep hsub hk i p).mpr (Or.inl ((mem_component _ _ _).mp hi))

theorem component_merge_off (P : Partition Agent) (selected : Finset Agent)
    (keep : Agent) (hsub : selected ⊆ P.labels) (hk : keep ∈ selected) (p : Agent)
    (hp : p ∈ P.labels) (hnot : p ∉ selected) :
    (P.merge selected keep hsub hk).component p=P.component p := by
  have hpfix := (P.mem_labels p).mp hp
  have hpnew : (P.merge selected keep hsub hk).representative p=p := by
    simp only [merge_representative,collapse,hpfix,ite_eq_right hnot]
  ext i
  rw [mem_component,mem_component,← hpnew]
  rw [P.merge_relation selected keep hsub hk i p,hpfix,hpnew]
  simp [hnot]

end Scheduler.Partition

namespace Frontier
variable {n : ℕ}

theorem Invariant.mono_component {w : Fin n → Fin n → ℝ} {rank : Fin n → ℕ}
    {r : Fin n → ℝ} {H : ℝ} {E C C' A F : Finset (Fin n)} {z : Fin n}
    (h : Invariant w rank r H E C A F z) (hC : C ⊆ C') :
    Invariant w rank r H E C' A F z :=
  ⟨h.allowed_eligible,fun _ hi => hC (h.allowed_internal hi),
    fun _ hi => hC (h.forbidden_internal hi),h.allowed_forbidden,h.frontier_eligible,
    hC h.frontier_internal,fun i hi hrank => hC (h.higher_internal i hi hrank),
    h.allowed_above,h.passed_small⟩

end Frontier

namespace Outer
variable {n : ℕ} {RootId : Type*}

def advancedFrontier (data : Data n RootId)
    (hall : data.pending.partition.labels ⊆ data.pending.pending)
    (cycle : Components.ProposalCycle (data.pending.outgoing hall)) (s : Fin data.size) (p : Fin n) : Fin n :=
  if p ∈ data.pending.selected hall cycle then ComponentFrames.nextAgent data.pending s p
  else data.frontier s p

variable [Fintype RootId] (data : Data n RootId) (original : RootId → Snapshot.Output n)
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : Components.ProposalCycle (data.pending.outgoing hall))
  (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)

include good

theorem advanced_pending_scan (p : Fin n) (proposed : Proposal (Fin data.size) (Fin n))
    (hp : (data.pending.merge (data.pending.selected hall cycle) keep
      (data.pending.selected_subset hall cycle) hk).proposals p=some proposed) (s : Fin data.size) :
    Frontier.scan (original (data.source s)).equalizers p r H
      ((data.pending.partition.merge (data.pending.selected hall cycle) keep
        (data.pending.selected_subset hall cycle) hk).component p)=.outside (proposed.nextAgent s) := by
  change (if p ∈ data.pending.selected hall cycle then none else data.pending.proposals p)=some proposed at hp
  by_cases hps : p ∈ data.pending.selected hall cycle
  · simp only [ite_eq_left hps] at hp
    cases hp
  · rw [ite_eq_right hps] at hp
    rw [data.pending.partition.component_merge_off _ keep _ hk p (data.pending.sound p proposed hp).1 hps]
    exact good.pending_scan p proposed hp s

theorem advanced_frontier (hr : ∀ i, 0 ≤ r i) (hH : 0 < H) (s : Fin data.size) (p : Fin n) :
    Frontier.Invariant (Frontier.weight (original (data.source s)).equalizers p)
      (Frontier.rankOf (original (data.source s)).equalizers p) r H
      (Frontier.eligible (Frontier.weight (original (data.source s)).equalizers p)
        (Frontier.rankOf (original (data.source s)).equalizers p) r H)
      ((data.pending.partition.merge (data.pending.selected hall cycle) keep
        (data.pending.selected_subset hall cycle) hk).component
        ((data.pending.partition.merge (data.pending.selected hall cycle) keep
          (data.pending.selected_subset hall cycle) hk).representative p))
      ((ComponentFrames.advance data.pending hall cycle data.visited data.frames s).allowed p)
      ((ComponentFrames.advance data.pending hall cycle data.visited data.frames s).forbidden p)
      (advancedFrontier data hall cycle s p) := by
  have hmono := data.pending.partition.component_merge_mono (data.pending.selected hall cycle)
    keep (data.pending.selected_subset hall cycle) hk p
  by_cases hp : p ∈ data.pending.selected hall cycle
  · have hpfix := (data.pending.partition.mem_labels p).mp (data.pending.selected_subset hall cycle hp)
    let cp : data.pending.Component := ⟨p,data.pending.selected_subset hall cycle hp⟩
    have hscan := good.pending_scan p (data.pending.proposalAt hall cp) (data.pending.proposalAt_spec hall cp) s
    rw [← ComponentFrames.nextAgent_proposalAt data.pending hall s cp] at hscan
    obtain ⟨hstop,hsmall⟩ := Reveal.scan_outside_stop _ p r H _ _ hscan (hr p) hH
    have hnext : ComponentFrames.nextAgent data.pending s p ∈
        (data.pending.partition.merge (data.pending.selected hall cycle) keep
          (data.pending.selected_subset hall cycle) hk).component
          ((data.pending.partition.merge (data.pending.selected hall cycle) keep
            (data.pending.selected_subset hall cycle) hk).representative p) := by
      apply (Partition.mem_component _ _ _).mpr
      apply (data.pending.partition.merge_relation _ keep _ hk _ p).mpr
      right
      constructor
      · apply (data.pending.component_mem_selected hall cycle _).mp
        obtain ⟨q,hq,hqp⟩ := (ComponentFrames.selected_iff_cycle data.pending hall cycle p).mp hp
        have hqc : q=cp := Subtype.ext hqp
        subst q
        rw [ComponentFrames.nextAgent_proposalAt data.pending hall s cp]
        have hc := data.pending.cycleRecipient_component hall cycle s cp
        rw [PendingState.cycleRecipient,ite_eq_left hq] at hc
        rw [hc]
        exact List.formPerm_mem_iff_mem.mpr hq
      · simpa only [hpfix] using hp
    have hinv := good.frontier s p
    change Frontier.Invariant _ _ _ _ _ (data.pending.partition.component (data.pending.partition.representative p)) _ _ _ at hinv
    rw [hpfix] at hinv hmono
    simpa only [ComponentFrames.advance,advancedFrontier,ite_eq_left hp] using
      Frontier.outside_update _ _ r H _ _ _ _ _ _ _ hinv hstop hsmall hmono hnext
  · simpa only [ComponentFrames.advance,advancedFrontier,ite_eq_right hp] using
      (good.frontier s p).mono_component hmono

theorem advanced_frontier_value (s : Fin data.size) (i p : Fin n) :
    (ComponentFrames.advance data.pending hall cycle data.visited data.frames s).frontierGap i p=
      (ComponentFrames.advance data.pending hall cycle data.visited data.frames s).gap i
        (advancedFrontier data hall cycle s p) p := by
  by_cases hp : p ∈ data.pending.selected hall cycle
  · simp only [ComponentFrames.advance,advancedFrontier,ite_eq_left hp,ChoreComposition.Frame.gap]
  · simpa only [ComponentFrames.advance,advancedFrontier,ite_eq_right hp,ChoreComposition.Frame.gap] using
      good.frontier_value s i p

end Outer
end EnvyFreeResearch.Full.Chores
