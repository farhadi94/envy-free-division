import EnvyFreeResearch.R3ChoreAncestry
import EnvyFreeResearch.R5ChoreSchedule

/-!
# Round 7 finite clipped-utility and skip/forbid certificates

The module proves finite utility-table, recipient-reserve and accounting facts.
It does not implement transformed SubCore, construct physical suffixes, or
assert the complete component-batch protocol.
-/

noncomputable section

namespace EnvyFreeResearch.R7Chores

open scoped BigOperators

def clipped (u : ℝ) : ℝ := max 0 u

theorem clipped_nonnegative (u : ℝ) : 0 ≤ clipped u := le_max_left _ _

/-- The offset is essential: the actual new prefix deficit is the clipped affine suffix utility. -/
theorem complementary_deficit_identity (whole baseline removed : ℝ) :
    max 0 (baseline-(whole-removed))=clipped (removed-(whole-baseline)) := by
  unfold clipped
  congr 1
  ring

theorem complementary_own_reduction (whole baseline removed : ℝ) :
    baseline-(whole-removed)=removed-(whole-baseline) := by ring

theorem positive_clipped_exact (u : ℝ) (hu : 0 < clipped u) : clipped u=u := by
  unfold clipped at *
  rcases max_cases (0 : ℝ) u with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h] at hu
    linarith
  · exact h

theorem clipped_zero_of_nonpositive (u : ℝ) (hu : u ≤ 0) : clipped u=0 := max_eq_left hu

theorem clipped_offset_monotone (gap : ℝ) : Monotone (fun cost : ℝ => clipped (cost-gap)) := by
  intro a b hab
  exact max_le_max_left 0 (sub_le_sub_right hab gap)

/-- A positive clipped target is exactly one original-cost target with the parent offset added. -/
theorem positive_clipped_target_iff (cost gap target : ℝ) (htarget : 0 < target) :
    clipped (cost-gap)=target ↔ cost=gap+target := by
  constructor
  · intro h
    have hp : 0 < clipped (cost-gap) := by simpa only [h] using htarget
    have heq := positive_clipped_exact (cost-gap) hp
    linarith
  · intro h
    have heq : cost-gap=target := by linarith
    rw [heq]
    exact max_eq_right htarget.le

theorem affine_target_iff (cost gap target : ℝ) : cost-gap=target ↔ cost=gap+target := by
  constructor <;> intro h <;> linarith

/-- An affine zero means original suffix cost equals its offset, not generally physical emptiness. -/
theorem affine_zero_target_iff (cost gap : ℝ) : cost-gap=0 ↔ cost=gap := by
  constructor <;> intro h <;> linarith

/-- Zero clipped value does not license retaining a negative-affine assignment. -/
theorem negative_affine_counterexample :
    clipped ((1 : ℝ)-(3-1))=0 ∧ (1 : ℝ)<3-1 := by norm_num [clipped]

/-- In a closed affine batch, a nonnegative own utility pays the rival's actual positive deficit. -/
theorem affine_closed_payment (own rival : ℝ) (hown : 0 ≤ own) (hEF : rival ≤ own) :
    clipped rival ≤ own := max_le hown hEF

/-- An affine-zero assignment keeps the recipient's own baseline exactly. -/
theorem affine_zero_preserves_baseline (whole baseline removed : ℝ)
    (hzero : removed-(whole-baseline)=0) : whole-removed=baseline := by linarith

/-- Nonnegative-affine retention keeps an actual whole assigned parent, including a zero-own one. -/
theorem affine_retention_keeps_whole {Donor : Type*} (assigned : Finset Donor)
    (own : Donor → ℝ) (w : Donor) (hw : w ∈ assigned)
    (hnonnegative : ∀ d ∈ assigned, 0 ≤ own d) :
    w ∈ assigned.filter (fun d => 0 ≤ own d) := by
  exact Finset.mem_filter.mpr ⟨hw, hnonnegative w hw⟩

section Stripping

variable {Agent : Type*}

def retainedCredit (u : Agent → Agent → ℝ) (i : Agent) : ℝ :=
  if 0 < u i i then u i i else 0

def retainedDeficit (u : Agent → Agent → ℝ) (i j : Agent) : ℝ :=
  if 0 < u j j then clipped (u i j) else 0

/-- Stripping a zero-own assignment keeps precisely the nonnegative own credit. -/
theorem retained_credit_exact (u : Agent → Agent → ℝ) (i : Agent) :
    retainedCredit u i=clipped (u i i) := by
  unfold retainedCredit clipped
  by_cases h : 0 < u i i
  · simp only [h, ite_true, max_eq_right h.le]
  · simp only [h, ite_false, max_eq_left (le_of_not_gt h)]

theorem retained_credit_nonnegative (u : Agent → Agent → ℝ) (i : Agent) :
    0 ≤ retainedCredit u i := by
  rw [retained_credit_exact]
  exact clipped_nonnegative _

theorem stripping_reduces_deficits (u : Agent → Agent → ℝ) (i j : Agent) :
    retainedDeficit u i j ≤ clipped (u i j) := by
  unfold retainedDeficit
  split
  · exact le_rfl
  · exact clipped_nonnegative _

/-- A zero-own row of a clipped EF table values every proposed donor at zero. -/
theorem zero_own_all_zero (u : Agent → Agent → ℝ) (i : Agent)
    (hEF : ∀ a b, clipped (u a b) ≤ clipped (u a a)) (hzero : u i i ≤ 0) :
    ∀ j, clipped (u i j)=0 := by
  intro j
  have h := hEF i j
  rw [clipped_zero_of_nonpositive _ hzero] at h
  exact le_antisymm h (clipped_nonnegative _)

/-- A zero-own observer also has zero required survivor payment. -/
theorem zero_own_survivor_zero (u : Agent → Agent → ℝ) (i : Agent) (required : ℝ)
    (hrequired : 0 ≤ required) (hthreshold : required ≤ clipped (u i i))
    (hzero : u i i ≤ 0) : required=0 := by
  rw [clipped_zero_of_nonpositive _ hzero] at hthreshold
  exact le_antisymm hthreshold hrequired

/-- Every actual retained recipient deficit remains covered after all zero-own donors are removed. -/
theorem stripped_comparison_payment (u : Agent → Agent → ℝ) (i j : Agent)
    (hcomparison : clipped (u i j) ≤ clipped (u i i)) :
    retainedDeficit u i j ≤ retainedCredit u i := by
  rw [retained_credit_exact]
  exact (stripping_reduces_deficits u i j).trans hcomparison

theorem stripped_ef_payment (u : Agent → Agent → ℝ)
    (hEF : ∀ a b, clipped (u a b) ≤ clipped (u a a)) (i j : Agent) :
    retainedDeficit u i j ≤ retainedCredit u i := by
  exact stripped_comparison_payment u i j (hEF i j)

theorem stripping_preserves_survivor_threshold (u : Agent → Agent → ℝ) (i : Agent)
    (required : ℝ) (hthreshold : required ≤ clipped (u i i)) :
    required ≤ retainedCredit u i := by simpa only [retained_credit_exact] using hthreshold

end Stripping

section RecipientSeparation

variable {Agent : Type*} [DecidableEq Agent]

def recipientReserve (allowed forbidden : Finset Agent) (pair : Agent → ℝ)
    (frontier : ℝ) (j : Agent) : ℝ :=
  if j ∈ allowed then clipped (pair j) else if j ∈ forbidden then 0 else clipped frontier

theorem recipient_reserve_nonnegative (allowed forbidden : Finset Agent)
    (pair : Agent → ℝ) (frontier : ℝ) (j : Agent) :
    0 ≤ recipientReserve allowed forbidden pair frontier j := by
  unfold recipientReserve
  split
  · exact clipped_nonnegative _
  · split
    · exact le_rfl
    · exact clipped_nonnegative _

/-- Forbidding every unallowed old component member makes its live reserve nonincreasing. -/
theorem internal_skip_forbid_no_growth (C allowed forbidden : Finset Agent)
    (pair : Agent → ℝ) (oldFrontier newFrontier : ℝ) (q j : Agent)
    (hq : q ∉ C) (hj : j ∈ C) :
    recipientReserve (insert q allowed) (forbidden ∪ (C\allowed)) pair newFrontier j ≤
      recipientReserve allowed forbidden pair oldFrontier j := by
  have hjq : j ≠ q := by intro h; subst j; exact hq hj
  by_cases ha : j ∈ allowed
  · simp [recipientReserve, ha]
  · have hf : j ∈ forbidden ∪ (C\allowed) :=
      Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hj, ha⟩)
    simpa [recipientReserve, ha, hjq, hf] using
      recipient_reserve_nonnegative allowed forbidden pair oldFrontier j

/-- Every outside recipient has exactly the new frontier reserve, including the actual new owner. -/
theorem external_skip_forbid_reserve (C allowed forbidden : Finset Agent)
    (pair : Agent → ℝ) (newFrontier : ℝ) (q j : Agent)
    (hallowed : allowed ⊆ C) (hforbidden : forbidden ⊆ C) (hj : j ∉ C)
    (hnewowner : pair q=newFrontier) :
    recipientReserve (insert q allowed) (forbidden ∪ (C\allowed)) pair newFrontier j =
      clipped newFrontier := by
  have ha : j ∉ allowed := fun h => hj (hallowed h)
  have hf : j ∉ forbidden ∪ (C\allowed) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hj (hforbidden h)
    · exact hj (Finset.mem_sdiff.mp h).1
  by_cases heq : j=q
  · subst j
    simp [recipientReserve, hnewowner]
  · simp [recipientReserve, ha, hf, heq]

def batchLoss (C : Finset Agent) (u : Agent → Agent → ℝ) (i j : Agent) : ℝ :=
  if j ∈ C then retainedDeficit u i j else 0

theorem outside_batch_loss_zero (C : Finset Agent) (u : Agent → Agent → ℝ)
    (i j : Agent) (hj : j ∉ C) : batchLoss C u i j=0 := by simp [batchLoss, hj]

/-- The actual loss-plus-growth inequality follows from recipient membership, not from double charging. -/
theorem skip_forbid_payment (C allowed forbidden : Finset Agent)
    (pair : Agent → ℝ) (oldFrontier newFrontier : ℝ) (q i j : Agent)
    (u : Agent → Agent → ℝ) (hq : q ∉ C)
    (hallowed : allowed ⊆ C) (hforbidden : forbidden ⊆ C)
    (hnewowner : pair q=newFrontier)
    (hEF : ∀ j ∈ C, clipped (u i j) ≤ clipped (u i i))
    (hthreshold : clipped newFrontier ≤ clipped (u i i)) :
    batchLoss C u i j + clipped
      (recipientReserve (insert q allowed) (forbidden ∪ (C\allowed)) pair newFrontier j -
        recipientReserve allowed forbidden pair oldFrontier j) ≤ retainedCredit u i := by
  by_cases hj : j ∈ C
  · have hg := internal_skip_forbid_no_growth C allowed forbidden pair oldFrontier newFrontier q j hq hj
    have hz := clipped_zero_of_nonpositive _ (sub_nonpos.mpr hg)
    simpa [batchLoss, hj, hz] using stripped_comparison_payment u i j (hEF j hj)
  · rw [outside_batch_loss_zero C u i j hj,
      external_skip_forbid_reserve C allowed forbidden pair newFrontier q j
        hallowed hforbidden hj hnewowner, zero_add]
    have hnonneg := recipient_reserve_nonnegative allowed forbidden pair oldFrontier j
    have hg : clipped (clipped newFrontier-
        recipientReserve allowed forbidden pair oldFrontier j) ≤ clipped newFrontier := by
      apply max_le (clipped_nonnegative _)
      linarith
    exact hg.trans (stripping_preserves_survivor_threshold u i _ hthreshold)

/-- An observer protected by the physical geometry needs no fictitious positive credit. -/
theorem protected_observer_zero_payment (C allowed forbidden : Finset Agent)
    (pair : Agent → ℝ) (oldFrontier newFrontier : ℝ) (q i j : Agent)
    (u : Agent → Agent → ℝ) (hq : q ∉ C)
    (hallowed : allowed ⊆ C) (hforbidden : forbidden ⊆ C)
    (hnewowner : pair q=newFrontier) (hown : u i i ≤ 0) (hfrontier : newFrontier ≤ 0)
    (hprotected : ∀ a ∈ C, u i a ≤ 0) :
    batchLoss C u i j + clipped
      (recipientReserve (insert q allowed) (forbidden ∪ (C\allowed)) pair newFrontier j -
        recipientReserve allowed forbidden pair oldFrontier j) ≤ 0 := by
  have h := skip_forbid_payment C allowed forbidden pair oldFrontier newFrontier q i j u
    hq hallowed hforbidden hnewowner
    (by intro a ha; rw [clipped_zero_of_nonpositive _ (hprotected a ha)]; exact clipped_nonnegative _)
    (by rw [clipped_zero_of_nonpositive _ hfrontier]; exact clipped_nonnegative _)
  simpa only [retained_credit_exact, clipped_zero_of_nonpositive _ hown] using h

/-- The separated payment preserves the full old frozen-deficit and live-reserve budget. -/
theorem batch_budget_transition (credit oldDeficit donorReserve oldLive newDeficit newLive
    ownPayment recipientLoss : ℝ)
    (hold : oldDeficit+donorReserve+oldLive ≤ credit)
    (hdeficit : newDeficit ≤ oldDeficit+donorReserve+recipientLoss)
    (hpayment : recipientLoss+clipped (newLive-oldLive) ≤ ownPayment) :
    newDeficit+newLive ≤ credit+ownPayment := by
  have hg : newLive-oldLive ≤ clipped (newLive-oldLive) := le_max_right _ _
  linarith

/-- The discarded old batch rule could charge one unit twice. -/
theorem double_payment_counterexample :
    (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ ¬((1 : ℝ)+1 ≤ 1) := by norm_num

end RecipientSeparation

/-- Calls may be charged to all distinct frozen roots, even when every proposed donor is stripped. -/
theorem frozen_roots_charge {Event Root : Type*} [Fintype Root] [DecidableEq Event]
    [DecidableEq Root] (events : Finset Event) (frozen : Event → Finset Root)
    (calls : Event → ℕ) (hcalls : ∀ e ∈ events, calls e ≤ (frozen e).card)
    (hdisjoint : ∀ e ∈ events, ∀ f ∈ events, e ≠ f → Disjoint (frozen e) (frozen f)) :
    (∑ e ∈ events, calls e) ≤ Fintype.card Root := by
  exact (Finset.sum_le_sum hcalls).trans
    (R5ChoreSchedule.disjoint_charge_total events frozen hdisjoint)

theorem calls_paid_by_square_freeze (d calls : ℕ) (hcalls : calls ≤ d) : calls ≤ d*d := by
  have hd : d ≤ d*d := by nlinarith
  exact hcalls.trans hd

section GraphCycles

variable {Vertex : Type*} [DecidableEq Vertex]

/-- A simple directed cycle plus unchanged self edges is a complete permutation matching. -/
theorem cyclic_list_matching (nodes : List Vertex) (hnodup : nodes.Nodup)
    (edge : Vertex → Vertex → Prop) (hself : ∀ x, edge x x)
    (hcycle : ∀ x (hx : x ∈ nodes), edge x (nodes.next x hx)) :
    ∀ x, edge x (nodes.formPerm x) := by
  intro x
  by_cases hx : x ∈ nodes
  · rw [List.formPerm_apply_mem_eq_next hnodup x hx]
    exact hcycle x hx
  · rw [List.formPerm_apply_of_notMem hx]
    exact hself x

/-- Closing a simple old path with its proposed first edge really installs that edge in a matching. -/
theorem cycle_matching_installs_first (p q : Vertex) (tail : List Vertex)
    (hnodup : (p::q::tail).Nodup) (edge : Vertex → Vertex → Prop)
    (hself : ∀ x, edge x x)
    (hcycle : ∀ x (hx : x ∈ p::q::tail), edge x ((p::q::tail).next x hx)) :
    ∃ matching : Equiv.Perm Vertex, matching p=q ∧ ∀ x, edge x (matching x) := by
  refine ⟨(p::q::tail).formPerm, List.formPerm_apply_head p q tail hnodup, ?_⟩
  exact cyclic_list_matching (p::q::tail) hnodup edge hself hcycle

omit [DecidableEq Vertex] in
/-- Every finite iteration of a matching whose edges are present is an actual graph walk. -/
theorem matching_power_reachable (matching : Equiv.Perm Vertex)
    (edge : Vertex → Vertex → Prop) (hedge : ∀ x, edge x (matching x))
    (x : Vertex) (k : ℕ) : Relation.ReflTransGen edge x ((matching^k) x) := by
  induction k with
  | zero => simpa using (Relation.ReflTransGen.refl : Relation.ReflTransGen edge x x)
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.tail (hedge _)

/-- The vertices on the newly executed simple cycle become mutually reachable. -/
theorem cycle_nodes_reachable [Finite Vertex] (nodes : List Vertex) (hnodup : nodes.Nodup)
    (hlen : 2 ≤ nodes.length) (edge : Vertex → Vertex → Prop) (hself : ∀ x, edge x x)
    (hcycle : ∀ x (hx : x ∈ nodes), edge x (nodes.next x hx))
    (x y : Vertex) (hx : x ∈ nodes) (hy : y ∈ nodes) :
    Relation.ReflTransGen edge x y := by
  have hcyclic := List.isCycle_formPerm hnodup hlen
  have hxn : nodes.formPerm x ≠ x := (List.formPerm_apply_mem_ne_self_iff nodes hnodup x hx).2 hlen
  have hyn : nodes.formPerm y ≠ y := (List.formPerm_apply_mem_ne_self_iff nodes hnodup y hy).2 hlen
  obtain ⟨k, hk⟩ := hcyclic.exists_pow_eq hxn hyn
  rw [← hk]
  exact matching_power_reachable nodes.formPerm edge
    (cyclic_list_matching nodes hnodup edge hself hcycle) x k

omit [DecidableEq Vertex] in
theorem old_walk_remains (old new : Vertex → Vertex → Prop)
    (hsub : ∀ a b, old a b → new a b) {x y : Vertex}
    (hwalk : Relation.ReflTransGen old x y) : Relation.ReflTransGen new x y := by
  induction hwalk with
  | refl => exact .refl
  | tail hwalk hlast ih => exact ih.tail (hsub _ _ hlast)

/-- Old component paths attach every selected vertex to the new cycle, proving the merger. -/
theorem attached_components_merge [Finite Vertex] (vertices : Finset Vertex)
    (nodes : List Vertex) (hnodup : nodes.Nodup) (hlen : 2 ≤ nodes.length)
    (old new : Vertex → Vertex → Prop) (hsub : ∀ a b, old a b → new a b)
    (hself : ∀ x, new x x)
    (hcycle : ∀ x (hx : x ∈ nodes), new x (nodes.next x hx))
    (hattach : ∀ x ∈ vertices, ∃ a ∈ nodes,
      Relation.ReflTransGen old x a ∧ Relation.ReflTransGen old a x) :
    ∀ x ∈ vertices, ∀ y ∈ vertices, Relation.ReflTransGen new x y := by
  intro x hx y hy
  obtain ⟨a, ha, hxa, _⟩ := hattach x hx
  obtain ⟨b, hb, _, hby⟩ := hattach y hy
  exact (old_walk_remains old new hsub hxa).trans
    ((cycle_nodes_reachable nodes hnodup hlen new hself hcycle a b ha hb).trans
      (old_walk_remains old new hsub hby))

omit [DecidableEq Vertex] in
/-- Edge closure of a selected component union rules out a path escaping that union. -/
theorem closed_union_no_escape (vertices : Finset Vertex) (edge : Vertex → Vertex → Prop)
    (hclosed : ∀ x ∈ vertices, ∀ y, edge x y → y ∈ vertices)
    {x y : Vertex} (hx : x ∈ vertices) (hwalk : Relation.ReflTransGen edge x y) :
    y ∈ vertices := by
  induction hwalk with
  | refl => exact hx
  | tail hwalk hlast ih => exact hclosed _ ih _ hlast

end GraphCycles

section ComponentCardinality

variable {Vertex : Type*} [DecidableEq Vertex]

def mergedPartition (blocks selected : Finset (Finset Vertex)) : Finset (Finset Vertex) :=
  insert (selected.biUnion id) (blocks\selected)

/-- A union of nonempty selected disjoint blocks is distinct from every unselected block. -/
theorem merged_block_is_fresh (blocks selected : Finset (Finset Vertex))
    (hsub : selected ⊆ blocks) (hselected : selected.Nonempty)
    (hnonempty : ∀ b ∈ blocks, b.Nonempty)
    (hdisjoint : ∀ a ∈ blocks, ∀ b ∈ blocks, a ≠ b → Disjoint a b) :
    selected.biUnion id ∉ blocks\selected := by
  intro hm
  obtain ⟨a, ha⟩ := hselected
  obtain ⟨x, hx⟩ := hnonempty a (hsub ha)
  have hxunion : x ∈ selected.biUnion id := Finset.mem_biUnion.mpr ⟨a, ha, hx⟩
  have hmem := Finset.mem_sdiff.mp hm
  have hne : a ≠ selected.biUnion id := by
    intro heq
    exact hmem.2 (heq ▸ ha)
  exact (Finset.disjoint_left.mp (hdisjoint a (hsub ha) _ hmem.1 hne)) hx hxunion

/-- This is the cardinality of the actual replacement of selected blocks by their union. -/
theorem component_merge_cardinality (blocks selected : Finset (Finset Vertex))
    (hsub : selected ⊆ blocks) (hselected : selected.Nonempty)
    (hnonempty : ∀ b ∈ blocks, b.Nonempty)
    (hdisjoint : ∀ a ∈ blocks, ∀ b ∈ blocks, a ≠ b → Disjoint a b) :
    (mergedPartition blocks selected).card=blocks.card-selected.card+1 := by
  unfold mergedPartition
  rw [Finset.card_insert_of_notMem (merged_block_is_fresh blocks selected hsub hselected
    hnonempty hdisjoint), Finset.card_sdiff_of_subset hsub]

theorem component_cycle_strictly_reduces_count (blocks selected : Finset (Finset Vertex))
    (hsub : selected ⊆ blocks) (hselected : 2 ≤ selected.card)
    (hnonempty : ∀ b ∈ blocks, b.Nonempty)
    (hdisjoint : ∀ a ∈ blocks, ∀ b ∈ blocks, a ≠ b → Disjoint a b) :
    (mergedPartition blocks selected).card+1 ≤ blocks.card := by
  have hpos : selected.Nonempty := Finset.card_pos.mp (by omega)
  rw [component_merge_cardinality blocks selected hsub hpos hnonempty hdisjoint]
  have hcard := Finset.card_le_card hsub
  omega

end ComponentCardinality

abbrev AtomicMaskClass (n : ℕ) := (Fin n → Bool) × (Fin n → Bool)
abbrev ExhaustedMaskClass (n : ℕ) := Fin n → Bool

theorem atomic_mask_class_count (n : ℕ) : Fintype.card (AtomicMaskClass n)=4^n := by
  simp [AtomicMaskClass, ← mul_pow]

theorem exhausted_mask_class_count (n : ℕ) : Fintype.card (ExhaustedMaskClass n)=2^n := by
  simp [ExhaustedMaskClass]

theorem finite_scarce_fiber_count {Root Class : Type*} [Fintype Root] [Fintype Class]
    [DecidableEq Class]
    (code : Root → Class) (K : ℕ)
    (hfiber : ∀ c, (Finset.univ.filter fun s => code s=c).card ≤ K) :
    Fintype.card Root ≤ Fintype.card Class*K := by
  classical
  by_contra h
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card code (Nat.lt_of_not_ge h)
  exact (not_lt_of_ge (hfiber c)) hc

/-- The actual two mask codings give the additive scarce-population budget. -/
theorem component_scarce_budget {Atomic Exhausted : Type*} [Fintype Atomic] [Fintype Exhausted]
    (n : ℕ) (atomicCode : Atomic → AtomicMaskClass n)
    (exhaustedCode : Exhausted → ExhaustedMaskClass n)
    (ha : ∀ c, (Finset.univ.filter fun s => atomicCode s=c).card ≤ n)
    (he : ∀ c, (Finset.univ.filter fun s => exhaustedCode s=c).card ≤ n) :
    Fintype.card Atomic+Fintype.card Exhausted ≤ n*(4^n+2^n) := by
  have hA := finite_scarce_fiber_count atomicCode n ha
  have hE := finite_scarce_fiber_count exhaustedCode n he
  rw [atomic_mask_class_count] at hA
  rw [exhausted_mask_class_count] at hE
  nlinarith

end EnvyFreeResearch.R7Chores

#print axioms EnvyFreeResearch.R7Chores.complementary_deficit_identity
#print axioms EnvyFreeResearch.R7Chores.positive_clipped_target_iff
#print axioms EnvyFreeResearch.R7Chores.skip_forbid_payment
#print axioms EnvyFreeResearch.R7Chores.protected_observer_zero_payment
#print axioms EnvyFreeResearch.R7Chores.affine_closed_payment
#print axioms EnvyFreeResearch.R7Chores.frozen_roots_charge
#print axioms EnvyFreeResearch.R7Chores.cycle_matching_installs_first
#print axioms EnvyFreeResearch.R7Chores.attached_components_merge
#print axioms EnvyFreeResearch.R7Chores.component_cycle_strictly_reduces_count
#print axioms EnvyFreeResearch.R7Chores.component_scarce_budget
