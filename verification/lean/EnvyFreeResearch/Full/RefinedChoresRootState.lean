import EnvyFreeResearch.Full.RefinedChoresNormalize
import EnvyFreeResearch.Full.RefinedChoresDeferredPayment

/-! Concrete root-local bookkeeping with immutable live owner permutations.
The paid permission graph is tied exactly to the frame used by the physical
ledger, rather than interpreted as a record of executed allocations. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresRootState
open ChoreComposition Chores.Components Chores.Scheduler
open RefinedChoresPartialGraph RefinedChoresNormalize RefinedChoresDeferredPayment
open scoped Classical
variable {Agent Root : Type*} [Fintype Agent] [DecidableEq Agent]

structure Tracked (frame : Frame Agent Root) where
  state : State Agent
  graph : Visited state
  exact : ∀ a b, b ∈ frame.allowed a ↔ Allowed state graph a b
  owner_identity : frame.owner = 1

/-- Original identity packages have the initial singleton permission graph. -/
def initial (frame : Frame Agent Root) (ho : frame.owner = 1)
    (ha : ∀ a, frame.allowed a = {a}) : Tracked frame where
  state := PendingState.initial
  graph := Visited.initial
  exact a b := by
    simp [ha,Allowed,Visited.initial,PendingState.initial,Edge,eq_comm]
  owner_identity := ho

def componentSet (state : State Agent) (c : state.Component) : Finset Agent :=
  Finset.univ.filter (fun a => state.partition.representative a = c)

@[simp] theorem mem_componentSet (state : State Agent) (c : state.Component) (a : Agent) :
    a ∈ componentSet state c ↔ state.partition.representative a = c := by
  simp [componentSet]

theorem component_self (state : State Agent) (c : state.Component) :
    (c : Agent) ∈ componentSet state c := by
  rw [mem_componentSet]
  exact (state.partition.mem_labels c).mp c.property

/-- The hypotheses of the deferred physical payment's internal/external
case split follow from the chosen sink in the tracked graph. -/
theorem sink_allowed (frame : Frame Agent Root) (tracked : Tracked frame)
    (c : tracked.state.Component) (hc : (c : Agent) ∉ tracked.state.pending) :
    frame.allowed c ⊆ componentSet tracked.state c := by
  intro b hb
  rw [mem_componentSet]
  exact sink_closed tracked.state tracked.graph c hc c b
    ((tracked.state.partition.mem_labels c).mp c.property)
    ((tracked.exact c b).mp hb)

/-- Every donor recipient in the source set has the actual allowed return
path needed for constructing its donor permutation. -/
theorem donor_path (frame : Frame Agent Root) (tracked : Tracked frame)
    (c : tracked.state.Component) (j : Agent) (hj : j ∈ componentSet tracked.state c) :
    Relation.ReflTransGen (fun a b => b ∈ frame.allowed a) j c := by
  have h := internal_path tracked.state tracked.graph j c
    ((mem_componentSet _ _ _).mp hj |>.trans
      ((tracked.state.partition.mem_labels c).mp c.property).symm)
  exact Relation.ReflTransGen.mono (fun a b he => (tracked.exact a b).mpr he) _ _ h

/-- Normalize all paid cycles while keeping the frame, including its physical
allocation and reserve, literally unchanged. -/
theorem normalize (frame : Frame Agent Root) (tracked : Tracked frame) :
    ∃ result : Tracked frame, ¬ Nonempty (Cycle result.state) := by
  obtain ⟨state,graph,hn,_,he⟩ := normalization_exists tracked.state tracked.graph
  exact ⟨⟨state,graph,fun a b => (tracked.exact a b).trans (he a b).symm,
    tracked.owner_identity⟩,hn⟩

def proposal (q : Agent) : Chores.Scheduler.Proposal Unit Agent := ⟨q,fun _ => q⟩

theorem proposal_valid (state : State Agent) (c : state.Component) (q : Agent)
    (hq : q ∉ componentSet state c) : (proposal q).Valid state.partition c := by
  constructor
  · exact fun h => hq ((mem_componentSet _ _ _).mpr h)
  · intro s; rfl

/-- Add the paid proposal both to the exact graph record and to the actual
frame. This is the graph bridge for `RefinedChoresPhysicalPayment.program`. -/
def payTracked (frame : Frame Agent Root) (tracked : Tracked frame)
    (c : tracked.state.Component) (hc : (c : Agent) ∉ tracked.state.pending)
    (q : Agent) (hq : q ∉ componentSet tracked.state c) :
    Tracked (pay frame (componentSet tracked.state c) c q) where
  state := tracked.state.reveal c c.property (proposal q) (proposal_valid _ c q hq)
  graph := tracked.graph.reveal c c.property (proposal q) (proposal_valid _ c q hq)
  exact a b := by
    have hnone : tracked.state.proposals c = none := by
      cases h : tracked.state.proposals c with
      | none => rfl
      | some prop => exact (hc ((tracked.state.mem_pending c).mpr ⟨prop,h⟩)).elim
    rw [allowed_reveal _ _ _ _ _ _ hnone]
    by_cases ha : a = c
    · subst a
      simp [pay,proposal,tracked.exact,eq_comm,or_comm]
    · simp [pay,ha,tracked.exact]
  owner_identity := tracked.owner_identity

theorem proposalAt_valid (state : State Agent) (p q : Agent)
    (hq : state.partition.representative q ≠ p) : (proposal q).Valid state.partition p := by
  exact ⟨hq,fun _ => rfl⟩

/-- Label-indexed version for a common source set across different roots. -/
def payAt (frame : Frame Agent Root) (tracked : Tracked frame)
    (C : Finset Agent) (p : Agent) (hp : p ∈ tracked.state.partition.labels)
    (hn : p ∉ tracked.state.pending) (q : Agent)
    (hq : tracked.state.partition.representative q ≠ p) : Tracked (pay frame C p q) where
  state := tracked.state.reveal p hp (proposal q) (proposalAt_valid tracked.state p q hq)
  graph := tracked.graph.reveal p hp (proposal q) (proposalAt_valid tracked.state p q hq)
  exact a b := by
    have hnone : tracked.state.proposals p = none := by
      cases h : tracked.state.proposals p with
      | none => rfl
      | some prop => exact (hn ((tracked.state.mem_pending p).mpr ⟨prop,h⟩)).elim
    rw [allowed_reveal _ _ _ _ _ _ hnone]
    by_cases ha : a = p
    · subst a
      simp [pay,proposal,tracked.exact,eq_comm,or_comm]
    · simp [pay,ha,tracked.exact]
  owner_identity := tracked.owner_identity

@[simp] theorem payTracked_allocation (frame : Frame Agent Root) (tracked : Tracked frame)
    (c : tracked.state.Component) (q : Agent) :
    (pay frame (componentSet tracked.state c) c q).allocation = frame.allocation := rfl

end EnvyFreeResearch.Full.RefinedChoresRootState
#print axioms EnvyFreeResearch.Full.RefinedChoresRootState.payTracked
#print axioms EnvyFreeResearch.Full.RefinedChoresRootState.normalize
