import EnvyFreeResearch.Full.ChoresSchedulerCounts

/-!
# Root-local graph execution at a common component merger

The state has one visited graph per live original root.  The constructor below
executes each survivor's own matching from its own old simple paths and recorded
next agents, and proves that all these different graphs have the same new SCC
partition.  The root restriction is separate and literal, so a group output
cannot enter another group before the pool commit.
-/

namespace EnvyFreeResearch.Full.Chores.Scheduler

open Components

variable {Root Agent : Type*} [Fintype Agent] [DecidableEq Agent]

structure Visited (state : PendingState Root Agent) where
  graph : Root → Graph Agent
  identity : ∀ s, (1 : Equiv.Perm Agent) ∈ graph s
  exact : ∀ s a b, SameComponent (graph s) a b ↔
    state.partition.representative a = state.partition.representative b

namespace Visited

def initial : Visited (PendingState.initial : PendingState Root Agent) where
  graph _ := [1]
  identity _ := List.mem_singleton_self _
  exact _ a b := initial_component a b

def reveal {state : PendingState Root Agent} (visited : Visited state)
    (p : Agent) (hp : p ∈ state.partition.labels) (q : Proposal Root Agent)
    (hq : q.Valid state.partition p) : Visited (state.reveal p hp q hq) where
  graph := visited.graph
  identity := visited.identity
  exact := visited.exact

def restrict {state : PendingState Root Agent} (visited : Visited state)
    {Root' : Type*} (includeRoot : Root' → Root) : Visited (state.restrict includeRoot) where
  graph := visited.graph ∘ includeRoot
  identity s := visited.identity (includeRoot s)
  exact s := visited.exact (includeRoot s)

end Visited

namespace PendingState

abbrev Component (state : PendingState Root Agent) := state.partition.labels

def component (state : PendingState Root Agent) (a : Agent) : state.Component :=
  ⟨state.partition.representative a, state.partition.representative_mem a⟩

@[simp] theorem component_label (state : PendingState Root Agent) (c : state.Component) :
    state.component c = c := by
  apply Subtype.ext
  exact (state.partition.mem_labels c).mp c.property

theorem graph_component {state : PendingState Root Agent} (visited : Visited state)
    (s : Root) (a b : Agent) :
    SameComponent (visited.graph s) a b ↔ state.component a = state.component b := by
  rw [visited.exact s a b]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

variable (state : PendingState Root Agent)
  (hall : state.partition.labels ⊆ state.pending)
  (cycle : Components.ProposalCycle (state.outgoing hall))

def selected : Finset Agent := (cycle.vertices.map Subtype.val).toFinset

theorem selected_subset : state.selected hall cycle ⊆ state.partition.labels := by
  intro p hp
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  exact c.property

theorem selected_card : (state.selected hall cycle).card = cycle.vertices.length := by
  apply (List.toFinset_card_of_nodup ?_).trans (List.length_map _)
  exact cycle.nodup.map Subtype.val_injective

theorem selected_two : 2 ≤ (state.selected hall cycle).card := by
  rw [selected_card]
  exact cycle.two_le

theorem component_mem_selected (a : Agent) :
    state.component a ∈ cycle.vertices ↔ state.partition.representative a ∈
      state.selected hall cycle := by
  change _ ↔ _ ∈ (cycle.vertices.map Subtype.val).toFinset
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · exact fun h => ⟨state.component a, h, rfl⟩
  · rintro ⟨c, hc, he⟩
    have h : c = state.component a := Subtype.ext he
    exact h ▸ hc

noncomputable def cycleRecipient (s : Root) (c : state.Component) : Agent :=
  if c ∈ cycle.vertices then (state.proposalAt hall c).nextAgent s else c

theorem cycleRecipient_component (s : Root) (c : state.Component) :
    state.component (state.cycleRecipient hall cycle s c) = cycle.vertices.formPerm c := by
  by_cases hc : c ∈ cycle.vertices
  · rw [cycleRecipient, ite_eq_left hc, cycle.follows c hc]
    apply Subtype.ext
    exact (state.sound c (state.proposalAt hall c) (state.proposalAt_spec hall c)).2.2 s
  · rw [cycleRecipient, ite_eq_right hc, state.component_label,
      List.formPerm_apply_of_notMem hc]

theorem cycleRecipient_off (s : Root) (c : state.Component) (hc : c ∉ cycle.vertices) :
    state.cycleRecipient hall cycle s c = c := by simp [cycleRecipient, hc]

noncomputable def survivor (visited : Visited state) (s : Root) : Equiv.Perm Agent :=
  survivorMatching (visited.graph s) state.component (state.graph_component visited s)
    Subtype.val state.component_label cycle.vertices (state.cycleRecipient hall cycle s)
    (state.cycleRecipient_component hall cycle s)

theorem survivor_recipient (visited : Visited state) (s : Root) (c : state.Component)
    (hc : c ∈ cycle.vertices) :
    state.survivor hall cycle visited s c = (state.proposalAt hall c).nextAgent s := by
  rw [survivor, survivorMatching_recipient, cycleRecipient, ite_eq_left hc]

theorem survivor_other (visited : Visited state) (s : Root) (x : Agent)
    (hx : x ∉ state.partition.labels) :
    state.survivor hall cycle visited s x = x ∨
      Edge (visited.graph s) x (state.survivor hall cycle visited s x) := by
  apply survivorMatching_other
  rintro ⟨c, rfl⟩
  exact hx c.property

theorem survivor_untouched (visited : Visited state) (s : Root) (x : Agent)
    (hx : state.partition.representative x ∉ state.selected hall cycle) :
    state.survivor hall cycle visited s x = x := by
  apply survivorMatching_untouched
  · exact state.cycleRecipient_off hall cycle s
  · exact fun h => hx ((state.component_mem_selected hall cycle x).mp h)

/-- The only newly permitted graph edges are the recorded selected proposals. -/
theorem survivor_edges (visited : Visited state) (s : Root) (x y : Agent) :
    Edge (state.survivor hall cycle visited s :: visited.graph s) x y ↔
      Edge (visited.graph s) x y ∨
        ∃ c : state.Component, c ∈ cycle.vertices ∧ x = c ∧
          y = (state.proposalAt hall c).nextAgent s := by
  rw [Components.edge_cons]
  constructor
  · rintro (hnew | hold)
    · by_cases hx : x ∈ state.partition.labels
      · let c : state.Component := ⟨x, hx⟩
        by_cases hc : c ∈ cycle.vertices
        · right
          refine ⟨c, hc, rfl, ?_⟩
          exact hnew.symm.trans (state.survivor_recipient hall cycle visited s c hc)
        · have hnot : state.partition.representative x ∉ state.selected hall cycle := by
            intro h
            have hxcomp : state.component x = c := state.component_label c
            exact hc (hxcomp ▸ (state.component_mem_selected hall cycle x).mpr h)
          have hself := state.survivor_untouched hall cycle visited s x hnot
          left
          refine ⟨1, visited.identity s, ?_⟩
          simpa only [Equiv.Perm.one_apply, hself] using hnew
      · rcases state.survivor_other hall cycle visited s x hx with hself | hold
        · left
          exact ⟨1, visited.identity s, by simpa only [Equiv.Perm.one_apply, hself] using hnew⟩
        · exact Or.inl (hnew ▸ hold)
    · exact Or.inl hold
  · rintro (hold | ⟨c, hc, rfl, rfl⟩)
    · exact Or.inr hold
    · exact Or.inl (state.survivor_recipient hall cycle visited s c hc)

theorem survivor_graph_exact (visited : Visited state) (s : Root)
    (keep : Agent) (hk : keep ∈ state.selected hall cycle) (a b : Agent) :
    SameComponent (state.survivor hall cycle visited s :: visited.graph s) a b ↔
      (state.partition.merge (state.selected hall cycle) keep
        (state.selected_subset hall cycle) hk).representative a =
      (state.partition.merge (state.selected hall cycle) keep
        (state.selected_subset hall cycle) hk).representative b := by
  rw [survivor, survivor_component_exact _ _ _ _ _ _ _ _ cycle.nodup
    (state.cycleRecipient_off hall cycle s), Partition.merge_relation]
  unfold Coarsened
  rw [state.component_mem_selected hall cycle a, state.component_mem_selected hall cycle b]
  exact or_congr Subtype.ext_iff Iff.rfl

/-- All old roots can be processed before any survivor is selected for the new pool. -/
noncomputable def commitGraphs (visited : Visited state)
    (keep : Agent) (hk : keep ∈ state.selected hall cycle) :
    Visited (state.merge (state.selected hall cycle) keep (state.selected_subset hall cycle) hk) where
  graph s := state.survivor hall cycle visited s :: visited.graph s
  identity s := List.mem_cons_of_mem _ (visited.identity s)
  exact s a b := state.survivor_graph_exact hall cycle visited s keep hk a b

end PendingState

end EnvyFreeResearch.Full.Chores.Scheduler
