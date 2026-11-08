import EnvyFreeResearch.Full.ChoresSchedulerPending

/-!
# Prefix counts from the actual component and proposal transitions

A continuing revelation inserts one previously absent proposal.  A merger
removes the proposals of at least two selected components and creates exactly
one unrevealed component.  These statements are proved from the finite update
functions; neither the operation counts nor a decreasing rank are inputs.
-/

namespace EnvyFreeResearch.Full.Chores.Scheduler

variable {Root Agent : Type*} [Fintype Agent] [DecidableEq Agent]

namespace PendingState

theorem unrevealed_add_pending (state : PendingState Root Agent) :
    state.unrevealed.card + state.pending.card = state.partition.labels.card :=
  Finset.card_sdiff_add_card_eq_card state.pending_subset

theorem reveal_unrevealed_card (state : PendingState Root Agent) (p : Agent)
    (hp : p ∈ state.partition.labels) (hnew : p ∉ state.pending)
    (q : Proposal Root Agent) (hq : q.Valid state.partition p) :
    (state.reveal p hp q hq).unrevealed.card + 1 = state.unrevealed.card := by
  have hbefore := state.unrevealed_add_pending
  have hafter := (state.reveal p hp q hq).unrevealed_add_pending
  rw [reveal_pending, Finset.card_insert_of_notMem hnew] at hafter
  change (state.reveal p hp q hq).unrevealed.card + (state.pending.card + 1) =
    state.partition.labels.card at hafter
  omega

theorem merge_unrevealed_card (state : PendingState Root Agent)
    (selected : Finset Agent) (keep : Agent)
    (hsub : selected ⊆ state.partition.labels) (hk : keep ∈ selected)
    (hpending : selected ⊆ state.pending) :
    (state.merge selected keep hsub hk).unrevealed.card = state.unrevealed.card + 1 := by
  have hbefore := state.unrevealed_add_pending
  have hafter := (state.merge selected keep hsub hk).unrevealed_add_pending
  have hparts := state.partition.merge_card selected keep hsub hk
  have hpend := Finset.card_sdiff_add_card_eq_card hpending
  rw [merge_pending] at hafter
  change (state.merge selected keep hsub hk).unrevealed.card +
    (state.pending \ selected).card =
    (state.partition.merge selected keep hsub hk).labels.card at hafter
  omega

def rank (state : PendingState Root Agent) : ℕ :=
  2 * state.partition.labels.card + state.unrevealed.card

theorem reveal_rank (state : PendingState Root Agent) (p : Agent)
    (hp : p ∈ state.partition.labels) (hnew : p ∉ state.pending)
    (q : Proposal Root Agent) (hq : q.Valid state.partition p) :
    (state.reveal p hp q hq).rank < state.rank := by
  have h := state.reveal_unrevealed_card p hp hnew q hq
  unfold rank
  change 2 * state.partition.labels.card + (state.reveal p hp q hq).unrevealed.card < _
  omega

theorem merge_rank (state : PendingState Root Agent)
    (selected : Finset Agent) (keep : Agent)
    (hsub : selected ⊆ state.partition.labels) (hk : keep ∈ selected)
    (hpending : selected ⊆ state.pending) (htwo : 2 ≤ selected.card) :
    (state.merge selected keep hsub hk).rank < state.rank := by
  have h := state.merge_unrevealed_card selected keep hsub hk hpending
  have hc := state.partition.merge_decreases selected keep hsub hk htwo
  unfold rank
  change 2 * (state.partition.merge selected keep hsub hk).labels.card +
    (state.merge selected keep hsub hk).unrevealed.card < _
  omega

end PendingState

/-- A prefix records actual well-formed updates, with their real side conditions. -/
inductive Prefix : PendingState Root Agent → ℕ → ℕ → Prop where
  | initial : Prefix PendingState.initial 0 0
  | reveal {state : PendingState Root Agent} {F G : ℕ}
      (before : Prefix state F G) (p : Agent) (hp : p ∈ state.partition.labels)
      (hnew : p ∉ state.pending) (q : Proposal Root Agent) (hq : q.Valid state.partition p) :
      Prefix (state.reveal p hp q hq) (F + 1) G
  | merge {state : PendingState Root Agent} {F G : ℕ}
      (before : Prefix state F G) (selected : Finset Agent) (keep : Agent)
      (hsub : selected ⊆ state.partition.labels) (hk : keep ∈ selected)
      (hpending : selected ⊆ state.pending) (htwo : 2 ≤ selected.card) :
      Prefix (state.merge selected keep hsub hk) F (G + 1)

namespace Prefix

theorem invariant {state : PendingState Root Agent} {F G : ℕ}
    (h : Prefix state F G) :
    state.unrevealed.card + F = Fintype.card Agent + G ∧
      state.partition.labels.card + G ≤ Fintype.card Agent := by
  induction h with
  | initial =>
      simp [PendingState.unrevealed, PendingState.initial, PendingState.pending,
        Partition.initial_labels]
  | @reveal state F G before p hp hnew q hq ih =>
      have hcard := state.reveal_unrevealed_card p hp hnew q hq
      constructor
      · omega
      · exact ih.2
  | @merge state F G before selected keep hsub hk hpending htwo ih =>
      have hu := state.merge_unrevealed_card selected keep hsub hk hpending
      have hc := state.partition.merge_decreases selected keep hsub hk htwo
      constructor
      · omega
      · change (state.partition.merge selected keep hsub hk).labels.card + (G + 1) ≤ _
        omega

theorem counts [Nonempty Agent] {state : PendingState Root Agent} {F G : ℕ}
    (h : Prefix state F G) :
    G ≤ Fintype.card Agent - 1 ∧ F ≤ Fintype.card Agent + G ∧
      F + G ≤ 3 * Fintype.card Agent - 2 := by
  have hi := h.invariant
  have hn := Fintype.card_pos (α := Agent)
  have hpos := Finset.card_pos.mpr state.partition.labels_nonempty
  omega

/-- The final closed revelation is charged, even though it creates no proposal. -/
theorem closed_counts [Nonempty Agent] {state : PendingState Root Agent} {F G : ℕ}
    (h : Prefix state F G) (p : Agent) (hp : p ∈ state.unrevealed) :
    G ≤ Fintype.card Agent - 1 ∧ F + 1 ≤ Fintype.card Agent + G ∧
      (F + 1) + G ≤ 3 * Fintype.card Agent - 2 := by
  have hi := h.invariant
  have hn := Fintype.card_pos (α := Agent)
  have hpos := Finset.card_pos.mpr state.partition.labels_nonempty
  have hu := Finset.card_pos.mpr (show state.unrevealed.Nonempty from ⟨p, hp⟩)
  omega

end Prefix

end EnvyFreeResearch.Full.Chores.Scheduler
