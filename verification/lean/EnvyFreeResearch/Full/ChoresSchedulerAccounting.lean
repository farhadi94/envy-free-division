import EnvyFreeResearch.Full.ChoresSchedulerCounts

/-! The derived count invariant also transports through actual root-type
restrictions, as required when a filtered or committed pool has a new finite
index type. It is initialized and preserved by every concrete update below. -/

namespace EnvyFreeResearch.Full.Chores.Scheduler

variable {Root Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def Accounting (state : PendingState Root Agent) (F G : ℕ) : Prop :=
  state.unrevealed.card + F = Fintype.card Agent + G ∧
    state.partition.labels.card + G ≤ Fintype.card Agent

namespace Accounting

theorem initial : Accounting (PendingState.initial : PendingState Root Agent) 0 0 :=
  Prefix.initial.invariant

theorem reveal {state : PendingState Root Agent} {F G : ℕ} (h : Accounting state F G)
    (p : Agent) (hp : p ∈ state.partition.labels) (hnew : p ∉ state.pending)
    (q : Proposal Root Agent) (hq : q.Valid state.partition p) :
    Accounting (state.reveal p hp q hq) (F + 1) G := by
  have hu := state.reveal_unrevealed_card p hp hnew q hq
  exact ⟨by have := h.1; omega, h.2⟩

theorem merge {state : PendingState Root Agent} {F G : ℕ} (h : Accounting state F G)
    (selected : Finset Agent) (keep : Agent) (hsub : selected ⊆ state.partition.labels)
    (hk : keep ∈ selected) (hpending : selected ⊆ state.pending) (htwo : 2 ≤ selected.card) :
    Accounting (state.merge selected keep hsub hk) F (G + 1) := by
  have hu := state.merge_unrevealed_card selected keep hsub hk hpending
  have hc := state.partition.merge_decreases selected keep hsub hk htwo
  constructor
  · have := h.1
    omega
  · change (state.partition.merge selected keep hsub hk).labels.card + (G + 1) ≤ _
    have := h.2
    omega

theorem restrict {state : PendingState Root Agent} {F G : ℕ} (h : Accounting state F G)
    {Root' : Type*} (includeRoot : Root' → Root) :
    Accounting (state.restrict includeRoot) F G := by
  constructor
  · change ((state.restrict includeRoot).partition.labels \
      (state.restrict includeRoot).pending).card + F = _
    rw [PendingState.restrict_pending]
    exact h.1
  · exact h.2

theorem counts [Nonempty Agent] {state : PendingState Root Agent} {F G : ℕ}
    (h : Accounting state F G) :
    G ≤ Fintype.card Agent - 1 ∧ F ≤ Fintype.card Agent + G ∧
      F + G ≤ 3 * Fintype.card Agent - 2 := by
  have hn := Fintype.card_pos (α := Agent)
  have hp := Finset.card_pos.mpr state.partition.labels_nonempty
  obtain ⟨hu, hc⟩ := h
  omega

theorem closed_counts [Nonempty Agent] {state : PendingState Root Agent} {F G : ℕ}
    (h : Accounting state F G) (p : Agent) (hp : p ∈ state.unrevealed) :
    G ≤ Fintype.card Agent - 1 ∧ F + 1 ≤ Fintype.card Agent + G ∧
      F + 1 + G ≤ 3 * Fintype.card Agent - 2 := by
  have hn := Fintype.card_pos (α := Agent)
  have hcpos := Finset.card_pos.mpr state.partition.labels_nonempty
  have hup := Finset.card_pos.mpr (show state.unrevealed.Nonempty from ⟨p, hp⟩)
  obtain ⟨hu, hc⟩ := h
  omega

end Accounting

end EnvyFreeResearch.Full.Chores.Scheduler
