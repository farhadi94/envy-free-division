import EnvyFreeResearch.Full.ChoresSchedulerGraphRound
import EnvyFreeResearch.Full.ChoresSchedulerAccounting

/-! A total fuel discipline for the concrete scheduler. Valid pending
proposals forbid a terminal one-component state from having a self-loop;
therefore every nonterminal state has rank at least three. The actual
reveal and merger updates consume a unit from the 3n-2 entrance budget. -/

namespace EnvyFreeResearch.Full.Chores.Outer
open Scheduler Components

variable {Root Agent : Type*} [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]

theorem scheduler_rank_min (state : PendingState Root Agent) : 3 ≤ state.rank := by
  have hc : 0 < state.partition.labels.card := Finset.card_pos.mpr state.partition.labels_nonempty
  by_cases hu : state.unrevealed.Nonempty
  · have hu' := Finset.card_pos.mpr hu
    unfold PendingState.rank
    omega
  · have hempty : state.unrevealed=∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    have hall : state.partition.labels ⊆ state.pending := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have htwo := state.selected_two hall (state.cycle hall)
    have hsub := Finset.card_le_card (state.selected_subset hall (state.cycle hall))
    unfold PendingState.rank
    omega

theorem restrict_rank (state : PendingState Root Agent) {Root' : Type*} (includeRoot : Root' → Root) :
    (state.restrict includeRoot).rank=state.rank := by
  unfold PendingState.rank PendingState.unrevealed
  rw [PendingState.restrict_pending]
  rfl

theorem initial_rank : (PendingState.initial : PendingState Root Agent).rank=3*Fintype.card Agent := by
  simp [PendingState.rank,PendingState.unrevealed,PendingState.pending,
    PendingState.initial,Partition.initial_labels]
  omega

theorem initial_fuel :
    (PendingState.initial : PendingState Root Agent).rank ≤ (3*Fintype.card Agent-2)+2 := by
  rw [initial_rank]
  have hn := Fintype.card_pos (α := Agent)
  omega

theorem positive_fuel (state : PendingState Root Agent) (fuel : ℕ) (h : state.rank ≤ fuel+2) : 0 < fuel := by
  have hm := scheduler_rank_min state
  omega

theorem reveal_fuel (state : PendingState Root Agent) (fuel : ℕ) (h : state.rank ≤ (fuel+1)+2)
    (p : Agent) (hp : p ∈ state.partition.labels) (hnew : p ∉ state.pending)
    (q : Proposal Root Agent) (hq : q.Valid state.partition p) :
    (state.reveal p hp q hq).rank ≤ fuel+2 := by
  have hd := state.reveal_rank p hp hnew q hq
  omega

theorem merge_fuel (state : PendingState Root Agent) (fuel : ℕ) (h : state.rank ≤ (fuel+1)+2)
    (selected : Finset Agent) (keep : Agent) (hsub : selected ⊆ state.partition.labels)
    (hk : keep ∈ selected) (hpending : selected ⊆ state.pending) (htwo : 2 ≤ selected.card) :
    (state.merge selected keep hsub hk).rank ≤ fuel+2 := by
  have hd := state.merge_rank selected keep hsub hk hpending htwo
  omega

end EnvyFreeResearch.Full.Chores.Outer
