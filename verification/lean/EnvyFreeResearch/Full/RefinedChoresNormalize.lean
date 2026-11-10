import EnvyFreeResearch.Full.RefinedChoresPartialGraph

/-! Query-free normalization of a root's paid permission graph. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresNormalize
open Chores.Components Chores.Scheduler RefinedChoresPartialGraph
open scoped Classical
variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

/-- Every orbit in a finite set reaches a periodic point. -/
theorem eventually_periodic {α : Type*} [Finite α] (f : α → α) (a : α) :
    ∃ k, f^[k] a ∈ Function.periodicPts f := by
  obtain ⟨m,n,hne,heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => f^[k] a)
  have hperiod : ∀ {i j : ℕ}, i < j → f^[i] a = f^[j] a →
      f^[i] a ∈ Function.periodicPts f := by
    intro i j hij h
    apply Function.mk_mem_periodicPts (n := j-i) (by omega)
    change f^[j-i] (f^[i] a) = f^[i] a
    rw [← Function.iterate_add_apply,Nat.sub_add_cancel hij.le]
    exact h.symm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨m,hperiod hlt heq⟩
  · exact ⟨n,hperiod hlt heq.symm⟩

/-- With no nontrivial proposal cycle, an arbitrary component reaches an
unpaid component. The conclusion is specific to the requested start. -/
theorem reaches_sink (state : State Agent) (hn : ¬ Nonempty (Cycle state))
    (start : state.Component) :
    ∃ k, ((outgoing state)^[k] start : Agent) ∉ state.pending := by
  obtain ⟨k,hk⟩ := eventually_periodic (outgoing state) start
  refine ⟨k,?_⟩
  intro hp
  have hne := target_pending state ((outgoing state)^[k] start) hp
  apply hn
  exact ⟨{ vertices := orbitList (outgoing state) ((outgoing state)^[k] start)
           nodup := orbitList_nodup _ _
           two_le := orbitList_two _ _ hk hne
           follows := fun _ hx => orbitList_follows _ _ hx }⟩

/-- All already-paid cycles can be absorbed. This changes neither the full
allowed relation nor any physical owner; component count strictly decreases
at every absorption. -/
theorem normalization_exists (state : State Agent) (visited : Visited state) :
    ∃ (result : State Agent) (graph : Visited result),
      ¬ Nonempty (Cycle result) ∧
      result.partition.labels.card ≤ state.partition.labels.card ∧
      ∀ a b, Allowed result graph a b ↔ Allowed state visited a b := by
  generalize hcount : state.partition.labels.card = count
  induction count using Nat.strong_induction_on generalizing state with
  | h count ih =>
      by_cases hc : Nonempty (Cycle state)
      · let cycle := hc.some
        have hnonempty : (selected state cycle).Nonempty :=
          Finset.card_pos.mp (by have := selected_two state cycle; omega)
        let keep := hnonempty.choose
        have hkeep : keep ∈ selected state cycle := hnonempty.choose_spec
        let next := state.merge (selected state cycle) keep (selected_subset state cycle) hkeep
        let nextGraph := absorb state visited cycle keep hkeep
        have hlt : next.partition.labels.card < count := by
          rw [← hcount]
          exact state.partition.merge_decreases (selected state cycle) keep (selected_subset state cycle) hkeep (selected_two state cycle)
        obtain ⟨result,graph,hn,hsize,hallow⟩ := ih _ hlt next nextGraph rfl
        refine ⟨result,graph,hn,hsize.trans (by omega),?_⟩
        intro a b
        exact (hallow a b).trans (allowed_absorb state visited cycle keep hkeep a b)
      · exact ⟨state,visited,hc,hcount.le,fun _ _ => Iff.rfl⟩

/-- The normalization can retain the designated protectedLabel representative. -/
theorem normalization_protected_exists (state : State Agent) (visited : Visited state)
    (protectedLabel : Agent) (hp : state.partition.representative protectedLabel = protectedLabel) :
    ∃ (result : State Agent) (graph : Visited result),
      ¬ Nonempty (Cycle result) ∧
      result.partition.labels.card ≤ state.partition.labels.card ∧
      result.partition.representative protectedLabel = protectedLabel ∧
      ∀ a b, Allowed result graph a b ↔ Allowed state visited a b := by
  generalize hcount : state.partition.labels.card = count
  induction count using Nat.strong_induction_on generalizing state with
  | h count ih =>
      by_cases hc : Nonempty (Cycle state)
      · let cycle := hc.some
        have hnonempty : (selected state cycle).Nonempty :=
          Finset.card_pos.mp (by have := selected_two state cycle; omega)
        let keep := Partition.keepLabel protectedLabel (selected state cycle) hnonempty
        have hkeep : keep ∈ selected state cycle := Partition.keepLabel_mem _ _ _
        let next := state.merge (selected state cycle) keep (selected_subset state cycle) hkeep
        let nextGraph := absorb state visited cycle keep hkeep
        have hlt : next.partition.labels.card < count := by
          rw [← hcount]
          exact state.partition.merge_decreases (selected state cycle) keep
            (selected_subset state cycle) hkeep (selected_two state cycle)
        have hpnext : next.partition.representative protectedLabel = protectedLabel :=
          state.partition.merge_protected _ (selected_subset state cycle) hnonempty protectedLabel hp
        obtain ⟨result,graph,hn,hsize,hprotected,hallow⟩ :=
          ih _ hlt next nextGraph hpnext rfl
        refine ⟨result,graph,hn,hsize.trans (by omega),hprotected,?_⟩
        intro a b
        exact (hallow a b).trans (allowed_absorb state visited cycle keep hkeep a b)
      · exact ⟨state,visited,hc,hcount.le,hp,fun _ _ => Iff.rfl⟩

/-- An internal permission path is also a path in the full paid graph. -/
theorem internal_path (state : State Agent) (visited : Visited state) (a b : Agent)
    (hab : state.partition.representative a = state.partition.representative b) :
    Relation.ReflTransGen (Allowed state visited) a b := by
  have h := component_iff_reach.mp ((visited.exact () a b).mpr hab)
  exact Relation.ReflTransGen.mono (fun _ _ he => Or.inl he) _ _ h

/-- A proposal-map step is realized by an already-paid edge followed by an
internal permission path to the target component's representative. -/
theorem outgoing_path (state : State Agent) (visited : Visited state)
    (c : state.Component) :
    Relation.ReflTransGen (Allowed state visited) (c : Agent) (outgoing state c : Agent) := by
  by_cases hc : (c : Agent) ∈ state.pending
  · obtain ⟨q,hq⟩ := (state.mem_pending c).mp hc
    have hedge : Allowed state visited c (target state c) :=
      Or.inr ⟨q,hq,(target_of_proposal state c q hq).symm⟩
    apply (Relation.ReflTransGen.single hedge).trans
    apply internal_path
    exact (state.partition.fixed (target state c)).symm
  · rw [outgoing_absent state c hc]

/-- Sink choice preserves the directed reachability from the requested agent. -/
theorem reachable_sink (state : State Agent) (visited : Visited state)
    (hn : ¬ Nonempty (Cycle state)) (a : Agent) :
    ∃ c : state.Component, (c : Agent) ∉ state.pending ∧
      Relation.ReflTransGen (Allowed state visited) a c := by
  obtain ⟨k,hk⟩ := reaches_sink state hn (state.component a)
  refine ⟨(outgoing state)^[k] (state.component a),hk,?_⟩
  have hstart : Relation.ReflTransGen (Allowed state visited) a (state.component a) := by
    apply internal_path
    exact (state.partition.fixed a).symm
  apply hstart.trans
  have hiter : ∀ k, Relation.ReflTransGen (Allowed state visited)
      (state.component a : Agent) ((outgoing state)^[k] (state.component a) : Agent) := by
    intro k
    induction k with
    | zero => exact .refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (outgoing_path state visited _)
  exact hiter k

/-- No permission edge leaves an unpaid component. -/
theorem sink_closed (state : State Agent) (visited : Visited state)
    (c : state.Component) (hc : (c : Agent) ∉ state.pending) (a b : Agent)
    (ha : state.partition.representative a = c) (hab : Allowed state visited a b) :
    state.partition.representative b = c := by
  rcases hab with hi | ⟨q,hq,hb⟩
  · exact ((visited.exact () a b).mp (.rel _ _ hi)).symm.trans ha
  · have hfixed := (state.partition.mem_labels a).mp (state.sound a q hq).1
    have hac : a = c := hfixed.symm.trans ha
    exact (hc (hac ▸ (state.mem_pending a).mpr ⟨q,hq⟩)).elim

end EnvyFreeResearch.Full.RefinedChoresNormalize
#print axioms EnvyFreeResearch.Full.RefinedChoresNormalize.normalization_exists
#print axioms EnvyFreeResearch.Full.RefinedChoresNormalize.reaches_sink
