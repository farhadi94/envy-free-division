import EnvyFreeResearch.Full.RefinedChoresPartialGraph
import EnvyFreeResearch.Full.RefinedChoresBucketCapacity

/-! Factorial capacities for the actual root-local pending-state partition. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresStateCapacity
open Chores.Components Chores.Scheduler RefinedChoresPartialGraph RefinedChoresBucketCapacity
open scoped Classical BigOperators
variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def size (state : State Agent) (p : Agent) : ℕ :=
  (Finset.univ.filter (fun a => state.partition.representative a = p)).card

def factor (state : State Agent) (p : Agent) : ℕ :=
  if p ∈ state.pending then paid (size state p) else unpaid (size state p)

def capacity (state : State Agent) : ℕ := ∏ p ∈ state.partition.labels, factor state p

theorem size_positive (state : State Agent) (p : Agent) (hp : p ∈ state.partition.labels) :
    1 ≤ size state p := by
  apply Finset.card_pos.mpr
  refine ⟨p,?_⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact (state.partition.mem_labels p).mp hp

theorem sizes_sum (state : State Agent) :
    ∑ p ∈ state.partition.labels, size state p = Fintype.card Agent := by
  unfold size
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp only [state.partition.representative_mem,Finset.filter_true,Finset.card_univ]

theorem factor_le_paid (state : State Agent) (p : Agent) :
    factor state p ≤ paid (size state p) := by
  unfold factor
  split_ifs
  · exact le_rfl
  · exact unpaid_le_paid _

theorem sole_unpaid (state : State Agent) (p : Agent)
    (hone : state.partition.labels = {p}) : p ∉ state.pending := by
  intro hp
  obtain ⟨q,hq⟩ := (state.mem_pending p).mp hp
  have hv := (state.sound p q hq).2
  apply hv.1
  have hm := state.partition.representative_mem q.targetAnchor
  rw [hone,Finset.mem_singleton] at hm
  exact hm

theorem paid_selected_bound (state : State Agent) (selected : Finset Agent)
    (hsub : selected ⊆ state.partition.labels) (htwo : 2 ≤ selected.card) :
    (∏ p ∈ selected, paid (size state p)) ≤ unpaid (∑ p ∈ selected, size state p) := by
  have h := paid_list_le_unpaid (selected.toList.map (size state))
    (by intro m hm; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
        exact size_positive state p (hsub (Finset.mem_toList.mp hp)))
    (by simpa using htwo)
  simpa only [List.map_map,Function.comp_def,Finset.prod_map_toList,Finset.sum_map_toList] using h

/-- Every actual pending-state partition has capacity at most 8^(n-1)n!.
A sole component cannot carry an external proposal, which removes the
otherwise spurious final paid factor. -/
theorem capacity_bound [Nonempty Agent] (state : State Agent) :
    capacity state ≤ unpaid (Fintype.card Agent) := by
  have hpos : 0 < state.partition.labels.card :=
    Finset.card_pos.mpr state.partition.labels_nonempty
  by_cases hone : state.partition.labels.card = 1
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hone
    have hsize := sizes_sum state
    rw [hp,Finset.sum_singleton] at hsize
    simp only [capacity,hp,Finset.prod_singleton,factor,
      ite_eq_right (sole_unpaid state p hp),hsize,le_refl]
  · have htwo : 2 ≤ state.partition.labels.card := by omega
    calc
      capacity state ≤ ∏ p ∈ state.partition.labels, paid (size state p) :=
        Finset.prod_le_prod (fun p _ => factor_le_paid state p)
      _ ≤ unpaid (∑ p ∈ state.partition.labels, size state p) :=
        paid_selected_bound state _ (fun _ h => h) htwo
      _ = unpaid (Fintype.card Agent) := by rw [sizes_sum]

@[simp] theorem size_reveal (state : State Agent) (p : Agent)
    (hp : p ∈ state.partition.labels) (q : Proposal Unit Agent)
    (hq : q.Valid state.partition p) (a : Agent) :
    size (state.reveal p hp q hq) a = size state a := rfl

theorem capacity_reveal (state : State Agent) (p : Agent)
    (hp : p ∈ state.partition.labels) (q : Proposal Unit Agent)
    (hq : q.Valid state.partition p) (hn : p ∉ state.pending) :
    capacity (state.reveal p hp q hq) = 2*(size state p+1)*capacity state := by
  have hself : factor (state.reveal p hp q hq) p = paid (size state p) := by
    simp [factor,state.reveal_pending,size_reveal]
  have hother : ∀ a ∈ state.partition.labels.erase p,
      factor (state.reveal p hp q hq) a = factor state a := by
    intro a ha
    have hap := (Finset.mem_erase.mp ha).1
    simp [factor,state.reveal_pending,hap]
  change (∏ a ∈ state.partition.labels, factor (state.reveal p hp q hq) a) = _
  rw [← Finset.mul_prod_erase _ _ hp,hself,Finset.prod_congr rfl hother]
  rw [capacity,← Finset.mul_prod_erase _ _ hp]
  have holdp : factor state p = unpaid (size state p) := by simp [factor,hn]
  rw [holdp,paid]
  ring

variable (state : State Agent) (selected : Finset Agent) (keep : Agent)
    (hsub : selected ⊆ state.partition.labels) (hk : keep ∈ selected)

theorem size_merge_other (a : Agent) (ha : a ∉ selected) :
    size (state.merge selected keep hsub hk) a = size state a := by
  unfold size
  apply congrArg Finset.card
  apply Finset.ext
  intro b
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change (if state.partition.representative b ∈ selected then keep else
    state.partition.representative b) = a ↔ state.partition.representative b = a
  by_cases hb : state.partition.representative b ∈ selected
  · simp only [ite_eq_left hb]
    constructor
    · intro h; exact (ha (h ▸ hk)).elim
    · intro h; exact (ha (h ▸ hb)).elim
  · simp [hb]

theorem size_merge_keep :
    size (state.merge selected keep hsub hk) keep = ∑ a ∈ selected, size state a := by
  unfold size
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  apply Finset.ext
  intro b
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change (if state.partition.representative b ∈ selected then keep else
    state.partition.representative b) = keep ↔ state.partition.representative b ∈ selected
  by_cases hb : state.partition.representative b ∈ selected
  · simp [hb]
  · simp only [hb,ite_false,iff_false]
    intro h
    exact hb (h ▸ hk)

theorem factor_merge_other (a : Agent) (ha : a ∉ selected) :
    factor (state.merge selected keep hsub hk) a = factor state a := by
  unfold factor
  rw [state.merge_pending,size_merge_other state selected keep hsub hk a ha]
  simp [ha]

/-- Absorbing any two or more already-paid components can only increase the
capacity of the surviving physical package. -/
theorem capacity_merge (hpaid : selected ⊆ state.pending) (htwo : 2 ≤ selected.card) :
    capacity state ≤ capacity (state.merge selected keep hsub hk) := by
  have hold : capacity state =
      (∏ a ∈ state.partition.labels \ selected, factor state a) *
      (∏ a ∈ selected, paid (size state a)) := by
    rw [capacity,← Finset.prod_sdiff hsub]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    simp only [factor,ite_eq_left (hpaid ha)]
  have hnew : capacity (state.merge selected keep hsub hk) =
      unpaid (∑ a ∈ selected, size state a) *
      (∏ a ∈ state.partition.labels \ selected, factor state a) := by
    unfold capacity
    change (∏ a ∈ (state.partition.merge selected keep hsub hk).labels,
      factor (state.merge selected keep hsub hk) a) = _
    rw [Partition.merge_labels,Finset.prod_insert (by simp [hk])]
    have hf : factor (state.merge selected keep hsub hk) keep =
        unpaid (∑ a ∈ selected, size state a) := by
      rw [factor,state.merge_pending]
      simp only [Finset.mem_sdiff,not_true_eq_false,hk,and_false,ite_false]
      rw [size_merge_keep]
    rw [hf]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    exact factor_merge_other state selected keep hsub hk a (Finset.mem_sdiff.mp ha).2
  rw [hold,hnew,mul_comm]
  exact Nat.mul_le_mul_right _ (paid_selected_bound state selected hsub htwo)

end EnvyFreeResearch.Full.RefinedChoresStateCapacity
#print axioms EnvyFreeResearch.Full.RefinedChoresStateCapacity.capacity_bound

#print axioms EnvyFreeResearch.Full.RefinedChoresStateCapacity.capacity_merge
#print axioms EnvyFreeResearch.Full.RefinedChoresStateCapacity.capacity_reveal
