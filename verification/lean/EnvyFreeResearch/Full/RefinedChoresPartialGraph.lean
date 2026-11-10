import EnvyFreeResearch.Full.ChoresSchedulerGraphRound

/-!
Root-local partial proposal cycles. A pending edge is already paid; absorbing
a cycle into the internal permission graph is a query-free bookkeeping step.
It does not execute or change the physical owner permutation.
-/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresPartialGraph
open Chores.Components Chores.Scheduler
open scoped Classical
variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

abbrev State (Agent : Type*) [Fintype Agent] [DecidableEq Agent] := PendingState Unit Agent

def target (state : State Agent) (c : state.Component) : Agent :=
  ((state.proposals c).map (fun q => q.nextAgent ())).getD c

def outgoing (state : State Agent) (c : state.Component) : state.Component :=
  state.component (target state c)

theorem target_pending (state : State Agent) (c : state.Component)
    (hc : (c : Agent) ∈ state.pending) : outgoing state c ≠ c := by
  obtain ⟨q,hq⟩ := (state.mem_pending c).mp hc
  have hv := (state.sound c q hq).2
  intro h
  have h' := congrArg Subtype.val h
  change state.partition.representative (target state c) = c at h'
  simp only [target,hq,Option.map_some,Option.getD_some] at h'
  exact hv.1 ((hv.2 ()).symm.trans h')

theorem target_absent (state : State Agent) (c : state.Component)
    (hc : (c : Agent) ∉ state.pending) : target state c = c := by
  have hn : state.proposals c = none := by
    cases h : state.proposals c with
    | none => rfl
    | some q => exact (hc ((state.mem_pending c).mpr ⟨q,h⟩)).elim
  simp [target,hn]

theorem outgoing_absent (state : State Agent) (c : state.Component)
    (hc : (c : Agent) ∉ state.pending) : outgoing state c = c := by
  rw [outgoing,target_absent state c hc,state.component_label c]

theorem pending_of_outgoing_ne (state : State Agent) (c : state.Component)
    (hc : outgoing state c ≠ c) : (c : Agent) ∈ state.pending := by
  by_contra hn
  exact hc (outgoing_absent state c hn)

abbrev Cycle (state : State Agent) := ProposalCycle (outgoing state)

def selected (state : State Agent) (cycle : Cycle state) : Finset Agent :=
  (cycle.vertices.map Subtype.val).toFinset

theorem selected_subset (state : State Agent) (cycle : Cycle state) :
    selected state cycle ⊆ state.partition.labels := by
  intro p hp
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  exact c.property

theorem selected_pending (state : State Agent) (cycle : Cycle state) :
    selected state cycle ⊆ state.pending := by
  intro p hp
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  exact pending_of_outgoing_ne state c (cycle.next_ne hc)

theorem selected_card (state : State Agent) (cycle : Cycle state) :
    (selected state cycle).card = cycle.vertices.length := by
  apply (List.toFinset_card_of_nodup ?_).trans (List.length_map _)
  exact cycle.nodup.map Subtype.val_injective

theorem selected_two (state : State Agent) (cycle : Cycle state) :
    2 ≤ (selected state cycle).card := by rw [selected_card]; exact cycle.two_le

theorem component_selected (state : State Agent) (cycle : Cycle state) (a : Agent) :
    state.component a ∈ cycle.vertices ↔ state.partition.representative a ∈ selected state cycle := by
  change _ ↔ _ ∈ (cycle.vertices.map Subtype.val).toFinset
  rw [List.mem_toFinset,List.mem_map]
  constructor
  · exact fun h => ⟨state.component a,h,rfl⟩
  · rintro ⟨c,hc,he⟩
    have h : c = state.component a := Subtype.ext he
    exact h ▸ hc

def cycleTarget (state : State Agent) (cycle : Cycle state) (c : state.Component) : Agent :=
  if c ∈ cycle.vertices then target state c else c

theorem cycleTarget_component (state : State Agent) (cycle : Cycle state) (c : state.Component) :
    state.component (cycleTarget state cycle c) = cycle.vertices.formPerm c := by
  by_cases hc : c ∈ cycle.vertices
  · rw [cycleTarget,ite_eq_left hc,cycle.follows c hc]
    rfl
  · rw [cycleTarget,ite_eq_right hc,state.component_label c,List.formPerm_apply_of_notMem hc]

theorem cycleTarget_off (state : State Agent) (cycle : Cycle state) (c : state.Component)
    (hc : c ∉ cycle.vertices) : cycleTarget state cycle c = c := by simp [cycleTarget,hc]

def permissionMatching (state : State Agent) (visited : Visited state) (cycle : Cycle state) :
    Equiv.Perm Agent :=
  survivorMatching (visited.graph ()) state.component (state.graph_component visited ())
    Subtype.val state.component_label cycle.vertices (cycleTarget state cycle)
    (cycleTarget_component state cycle)

theorem matching_recipient (state : State Agent) (visited : Visited state) (cycle : Cycle state)
    (c : state.Component) (hc : c ∈ cycle.vertices) :
    permissionMatching state visited cycle c = target state c := by
  rw [permissionMatching,survivorMatching_recipient,cycleTarget,ite_eq_left hc]

theorem matching_other (state : State Agent) (visited : Visited state) (cycle : Cycle state)
    (x : Agent) (hx : x ∉ state.partition.labels) :
    permissionMatching state visited cycle x = x ∨
      Edge (visited.graph ()) x (permissionMatching state visited cycle x) := by
  apply survivorMatching_other
  rintro ⟨c,rfl⟩
  exact hx c.property

theorem matching_untouched (state : State Agent) (visited : Visited state) (cycle : Cycle state)
    (x : Agent) (hx : state.partition.representative x ∉ selected state cycle) :
    permissionMatching state visited cycle x = x := by
  apply survivorMatching_untouched
  · exact cycleTarget_off state cycle
  · exact fun h => hx ((component_selected state cycle x).mp h)

theorem matching_edges (state : State Agent) (visited : Visited state) (cycle : Cycle state)
    (x y : Agent) :
    Edge (permissionMatching state visited cycle :: visited.graph ()) x y ↔
      Edge (visited.graph ()) x y ∨
        ∃ c : state.Component, c ∈ cycle.vertices ∧ x = c ∧ y = target state c := by
  rw [Chores.Components.edge_cons]
  constructor
  · rintro (hnew | hold)
    · by_cases hx : x ∈ state.partition.labels
      · let c : state.Component := ⟨x,hx⟩
        by_cases hc : c ∈ cycle.vertices
        · right
          exact ⟨c,hc,rfl,hnew.symm.trans (matching_recipient state visited cycle c hc)⟩
        · have hnot : state.partition.representative x ∉ selected state cycle := by
            intro h
            have hcomp : state.component x = c := state.component_label c
            exact hc (hcomp ▸ (component_selected state cycle x).mpr h)
          have hself := matching_untouched state visited cycle x hnot
          left
          exact ⟨1,visited.identity (),by simpa only [Equiv.Perm.one_apply,hself] using hnew⟩
      · rcases matching_other state visited cycle x hx with hself | hold
        · left
          exact ⟨1,visited.identity (),by simpa only [Equiv.Perm.one_apply,hself] using hnew⟩
        · exact Or.inl (hnew ▸ hold)
    · exact Or.inl hold
  · rintro (hold | ⟨c,hc,rfl,rfl⟩)
    · exact Or.inr hold
    · exact Or.inl (matching_recipient state visited cycle c hc)

theorem merged_graph_exact (state : State Agent) (visited : Visited state) (cycle : Cycle state)
    (keep : Agent) (hk : keep ∈ selected state cycle) (a b : Agent) :
    SameComponent (permissionMatching state visited cycle :: visited.graph ()) a b ↔
      (state.partition.merge (selected state cycle) keep (selected_subset state cycle) hk).representative a =
      (state.partition.merge (selected state cycle) keep (selected_subset state cycle) hk).representative b := by
  rw [permissionMatching,survivor_component_exact _ _ _ _ _ _ _ _ cycle.nodup
    (cycleTarget_off state cycle),Partition.merge_relation]
  unfold Coarsened
  rw [component_selected state cycle a,component_selected state cycle b]
  exact or_congr Subtype.ext_iff Iff.rfl

/-- Absorb already-paid cycle edges without executing a physical matching. -/
def absorb (state : State Agent) (visited : Visited state) (cycle : Cycle state)
    (keep : Agent) (hk : keep ∈ selected state cycle) :
    Visited (state.merge (selected state cycle) keep (selected_subset state cycle) hk) where
  graph _ := permissionMatching state visited cycle :: visited.graph ()
  identity _ := List.mem_cons_of_mem _ (visited.identity ())
  exact _ a b := merged_graph_exact state visited cycle keep hk a b

/-- The live reserve permission relation includes both internal edges and
external already-paid proposals. -/
def Allowed (state : State Agent) (visited : Visited state) (a b : Agent) : Prop :=
  Edge (visited.graph ()) a b ∨ ∃ q, state.proposals a = some q ∧ q.nextAgent () = b

theorem allowed_refl (state : State Agent) (visited : Visited state) (a : Agent) :
    Allowed state visited a a := Or.inl ⟨1,visited.identity (),rfl⟩

theorem target_of_proposal (state : State Agent) (c : state.Component)
    (q : Proposal Unit Agent) (hq : state.proposals c = some q) :
    target state c = q.nextAgent () := by simp [target,hq]

theorem allowed_absorb (state : State Agent) (visited : Visited state) (cycle : Cycle state)
    (keep : Agent) (hk : keep ∈ selected state cycle) (a b : Agent) :
    Allowed (state.merge (selected state cycle) keep (selected_subset state cycle) hk)
      (absorb state visited cycle keep hk) a b ↔ Allowed state visited a b := by
  change (Edge (permissionMatching state visited cycle :: visited.graph ()) a b ∨
    ∃ q, (if a ∈ selected state cycle then none else state.proposals a) = some q ∧ q.nextAgent () = b) ↔ _
  rw [matching_edges]
  constructor
  · rintro ((hold | ⟨c,hc,rfl,hb⟩) | ⟨q,hq,hb⟩)
    · exact Or.inl hold
    · obtain ⟨q,hq⟩ := (state.mem_pending c).mp
        (pending_of_outgoing_ne state c (cycle.next_ne hc))
      exact Or.inr ⟨q,hq,(target_of_proposal state c q hq).symm.trans hb.symm⟩
    · by_cases ha : a ∈ selected state cycle
      · simp [ha] at hq
      · exact Or.inr ⟨q,by simpa only [ite_eq_right ha] using hq,hb⟩
  · rintro (hold | ⟨q,hq,hb⟩)
    · exact Or.inl (Or.inl hold)
    · by_cases ha : a ∈ selected state cycle
      · obtain ⟨c,hc,he⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
        have hac : a = c := he.symm
        subst a
        exact Or.inl (Or.inr ⟨c,hc,rfl,hb.symm.trans (target_of_proposal state c q hq).symm⟩)
      · exact Or.inr ⟨q,by simpa only [ite_eq_right ha] using hq,hb⟩

/-- Paying a proposal adds exactly one permission edge and changes no others. -/
theorem allowed_reveal (state : State Agent) (visited : Visited state)
    (p : Agent) (hp : p ∈ state.partition.labels) (q : Proposal Unit Agent)
    (hq : q.Valid state.partition p) (hnone : state.proposals p = none) (a b : Agent) :
    Allowed (state.reveal p hp q hq) (visited.reveal p hp q hq) a b ↔
      Allowed state visited a b ∨ (a = p ∧ b = q.nextAgent ()) := by
  by_cases ha : a = p
  · subst a
    simp [Allowed,Visited.reveal,PendingState.reveal,hnone,eq_comm]
  · simp only [Allowed,Visited.reveal,PendingState.reveal,Function.update_of_ne ha,ha,false_and,or_false]

end EnvyFreeResearch.Full.RefinedChoresPartialGraph

#print axioms EnvyFreeResearch.Full.RefinedChoresPartialGraph.absorb
#print axioms EnvyFreeResearch.Full.RefinedChoresPartialGraph.allowed_absorb
