import EnvyFreeResearch.Full.RefinedChoresStateCapacity
import EnvyFreeResearch.Full.RefinedChoresNormalize

/-! The factorial package invariant is preserved by the actual root-local
reveal and cycle-absorption transitions. This is a combinatorial execution
lemma; the physical pool implementation is a separate obligation. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresCapacityRun
open Chores.Components Chores.Scheduler RefinedChoresPartialGraph RefinedChoresNormalize
open RefinedChoresBucketCapacity RefinedChoresStateCapacity
open scoped Classical BigOperators
variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

@[simp] theorem initial_size (p : Agent) : size (PendingState.initial : State Agent) p = 1 := by
  change (Finset.univ.filter (fun a : Agent => a = p)).card = 1
  apply Finset.card_eq_one.mpr
  refine ⟨p,?_⟩
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,Finset.mem_singleton,true_and]

@[simp] theorem initial_capacity : capacity (PendingState.initial : State Agent) = 1 := by
  simp only [capacity,factor,PendingState.initial_pending,Finset.notMem_empty,ite_false,
    initial_size,unpaid]
  norm_num

/-- A weighted survivor lineage contains the actual paid proposal states.
Each payment consumes one bucket-compatible group, and each absorption is
an actual paid proposal cycle in that state. -/
inductive Weighted : State Agent → ℕ → Prop
  | initial : Weighted PendingState.initial 1
  | pay {state : State Agent} {weight : ℕ} (old : Weighted state weight)
      (p : Agent) (hp : p ∈ state.partition.labels) (q : Proposal Unit Agent)
      (hq : q.Valid state.partition p) (hn : p ∉ state.pending)
      (bucket : ℕ) (weights : List ℕ)
      (hlen : weights.length = size state p+1)
      (hlower : 2^bucket ≤ weight)
      (hupper : ∀ w ∈ weights, w < 2^(bucket+1)) :
      Weighted (state.reveal p hp q hq) weights.sum
  | absorb {state : State Agent} {weight : ℕ} (old : Weighted state weight)
      (cycle : Cycle state) (keep : Agent) (hk : keep ∈ selected state cycle) :
      Weighted (state.merge (selected state cycle) keep (selected_subset state cycle) hk) weight

/-- Unlike a stand-alone factorial estimate, this induction covers the
computed weight of every admitted survivor transition. -/
theorem Weighted.capacity_le {state : State Agent} {weight : ℕ}
    (run : Weighted state weight) : weight ≤ capacity state := by
  induction run with
  | initial => rw [initial_capacity]
  | @pay state weight old p hp q hq hn bucket weights hlen hlower hupper ih =>
    rw [capacity_reveal state p hp q hq hn]
    exact (group_sum_le weights hlen hlower hupper).trans (Nat.mul_le_mul_left _ ih)
  | @absorb state weight old cycle keep hk ih =>
    exact ih.trans (capacity_merge state (selected state cycle) keep
      (selected_subset state cycle) hk (selected_pending state cycle) (selected_two state cycle))

theorem Weighted.factorial_bound [Nonempty Agent] {state : State Agent} {weight : ℕ}
    (run : Weighted state weight) : weight ≤ unpaid (Fintype.card Agent) :=
  run.capacity_le.trans (capacity_bound state)

/-- Query-free cycle normalization preserves all weights admitted by the
actual state capacity, and preserves the protected representative. -/
theorem normalization_with_capacity (state : State Agent) (visited : Visited state)
    (protectedLabel : Agent)
    (hp : state.partition.representative protectedLabel = protectedLabel) :
    ∃ (result : State Agent) (graph : Visited result),
      ¬ Nonempty (Cycle result) ∧ capacity state ≤ capacity result ∧
      result.partition.representative protectedLabel = protectedLabel ∧
      (∀ a b, state.partition.representative a = state.partition.representative b →
        result.partition.representative a = result.partition.representative b) ∧
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
      obtain ⟨result,graph,hn,hcap,hprotected,hrefine,hallow⟩ :=
        ih _ hlt next nextGraph hpnext rfl
      refine ⟨result,graph,hn,?_,hprotected,?_,?_⟩
      · exact (capacity_merge state (selected state cycle) keep (selected_subset state cycle)
          hkeep (selected_pending state cycle) (selected_two state cycle)).trans hcap
      · intro a b hab
        apply hrefine a b
        exact (state.partition.merge_relation (selected state cycle) keep
          (selected_subset state cycle) hkeep a b).mpr (Or.inl hab)
      · intro a b
        exact (hallow a b).trans (allowed_absorb state visited cycle keep hkeep a b)
    · exact ⟨state,visited,hc,le_rfl,hp,fun _ _ h => h,fun _ _ => Iff.rfl⟩

end EnvyFreeResearch.Full.RefinedChoresCapacityRun
#print axioms EnvyFreeResearch.Full.RefinedChoresCapacityRun.Weighted.factorial_bound
#print axioms EnvyFreeResearch.Full.RefinedChoresCapacityRun.normalization_with_capacity
