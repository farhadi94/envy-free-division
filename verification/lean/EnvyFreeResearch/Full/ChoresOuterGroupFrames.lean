import EnvyFreeResearch.Full.ChoresOuterGroupRestriction

/-! A group's actual survivor matching and advanced frame are the
restriction of the common old-state computation. This identifies the
physical group output with the single partition committed after the batch. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Scheduler.PendingState
open Components ChoreComposition
open scoped Classical

variable {Root Root' RootId Agent : Type*} [Fintype Agent] [DecidableEq Agent]
  (state : PendingState Root Agent) (includeRoot : Root' → Root)
  (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)

theorem restrict_cycleRecipient (s : Root') (p : state.Component) :
    (state.restrict includeRoot).cycleRecipient (restrict_all_pending state includeRoot hall)
      (restrictCycle state includeRoot hall cycle) s p=state.cycleRecipient hall cycle (includeRoot s) p := by
  by_cases hp : p ∈ cycle.vertices
  · change (if p ∈ cycle.vertices then _ else _)=_
    rw [ite_eq_left hp]
    change ((state.restrict includeRoot).proposalAt (restrict_all_pending state includeRoot hall) p).nextAgent s=_
    have h := congrArg (fun q : Proposal Root' Agent => q.nextAgent s)
      (restrict_proposalAt state includeRoot hall p)
    exact h.trans (by simp only [cycleRecipient,ite_eq_left hp,Proposal.restrict,Function.comp_apply])
  · change (if p ∈ cycle.vertices then _ else (p : Agent))=
      (if p ∈ cycle.vertices then _ else (p : Agent))
    simp only [ite_eq_right hp]

theorem restrict_survivor (s : Root') :
    (state.restrict includeRoot).survivor (restrict_all_pending state includeRoot hall)
      (restrictCycle state includeRoot hall cycle) (visited.restrict includeRoot) s=
        state.survivor hall cycle visited (includeRoot s) := by
  have hr : (state.restrict includeRoot).cycleRecipient (restrict_all_pending state includeRoot hall)
      (restrictCycle state includeRoot hall cycle) s=state.cycleRecipient hall cycle (includeRoot s) :=
    funext (restrict_cycleRecipient state includeRoot hall cycle s)
  unfold survivor
  simp only [restrictCycle,Visited.restrict]
  congr 1

theorem restrict_advance (frames : Root → Frame Agent RootId) (s : Root') :
    ComponentFrames.advance (state.restrict includeRoot) (restrict_all_pending state includeRoot hall)
      (restrictCycle state includeRoot hall cycle) (visited.restrict includeRoot) (frames ∘ includeRoot) s=
        ComponentFrames.advance state hall cycle visited frames (includeRoot s) := by
  simp only [ComponentFrames.advance,restrict_selected,restrict_nextAgent,Function.comp_apply,
    restrict_survivor]
  rfl

end EnvyFreeResearch.Full.Chores.Scheduler.PendingState
