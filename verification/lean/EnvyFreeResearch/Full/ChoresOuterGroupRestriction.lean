import EnvyFreeResearch.Full.ChoresOuterOpenGroup

/-! Every disjoint group of an old pool uses the same recorded component
cycle. Restricting the root array changes next-agent records but preserves
their target components, the selected source labels, and the task set. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Scheduler.PendingState
open Components
open scoped Classical

variable {Root Root' Agent : Type*} [Fintype Agent] [DecidableEq Agent]
  (state : PendingState Root Agent) (includeRoot : Root' → Root)
  (hall : state.partition.labels ⊆ state.pending)

include hall

theorem restrict_all_pending : (state.restrict includeRoot).partition.labels ⊆
    (state.restrict includeRoot).pending := by
  rw [restrict_pending]
  exact hall

theorem restrict_proposalAt (p : state.Component) :
    (state.restrict includeRoot).proposalAt (restrict_all_pending state includeRoot hall) p=
      (state.proposalAt hall p).restrict includeRoot := by
  have hnew := (state.restrict includeRoot).proposalAt_spec (restrict_all_pending state includeRoot hall) p
  change (state.proposals p).map (fun q => q.restrict includeRoot)=some _ at hnew
  rw [state.proposalAt_spec hall p,Option.map_some] at hnew
  exact (Option.some.inj hnew).symm

theorem restrict_outgoing :
    (state.restrict includeRoot).outgoing (restrict_all_pending state includeRoot hall)=state.outgoing hall := by
  funext p
  apply Subtype.ext
  change state.partition.representative
      ((state.restrict includeRoot).proposalAt (restrict_all_pending state includeRoot hall) p).targetAnchor=
    state.partition.representative (state.proposalAt hall p).targetAnchor
  exact congrArg state.partition.representative
    (congrArg (fun q : Proposal Root' Agent => q.targetAnchor)
      (restrict_proposalAt state includeRoot hall p))

def restrictCycle (cycle : ProposalCycle (state.outgoing hall)) :
    ProposalCycle ((state.restrict includeRoot).outgoing (restrict_all_pending state includeRoot hall)) :=
  { vertices := cycle.vertices
    two_le := cycle.two_le
    nodup := cycle.nodup
    follows := by
      intro a ha
      exact (cycle.follows a ha).trans (congrFun (restrict_outgoing state includeRoot hall) a).symm }

theorem restrict_selected (cycle : ProposalCycle (state.outgoing hall)) :
    (state.restrict includeRoot).selected (restrict_all_pending state includeRoot hall)
      (restrictCycle state includeRoot hall cycle)=state.selected hall cycle := rfl

omit hall in
theorem restrict_nextAgent (s : Root') (p : Agent) :
    ComponentFrames.nextAgent (state.restrict includeRoot) s p=
      ComponentFrames.nextAgent state (includeRoot s) p := by
  cases h : state.proposals p <;>
    simp only [ComponentFrames.nextAgent,restrict,h,Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,Proposal.restrict,Function.comp_apply]

end EnvyFreeResearch.Full.Chores.Scheduler.PendingState
