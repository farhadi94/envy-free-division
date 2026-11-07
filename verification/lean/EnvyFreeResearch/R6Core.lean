import Mathlib

/-!
# Round 6 finite Core state certificates

These proofs concern finite matching cuts, coherent real cost tables, backward
anchor chains, and subset-pair counts. They do not construct hungry measures,
formal prefix records, oracle operations, or the complete Core dynamic program.
-/

namespace EnvyFreeResearch.R6Core

open scoped BigOperators

section Matchings

variable {Agent : Type*} [DecidableEq Agent]

/-- The two sign-class inclusions force equality by finite bijective cardinality. -/
theorem matching_cut_equality (A J : Finset Agent) (π τ : Equiv.Perm Agent)
    (hπ : A.image π ⊆ J) (hτ : J.image τ.symm ⊆ A) :
    A.image π=J ∧ A.image τ=J := by
  have hAJ : A.card ≤ J.card := by
    simpa only [Finset.card_image_of_injective A π.injective] using Finset.card_le_card hπ
  have hJA : J.card ≤ A.card := by
    simpa only [Finset.card_image_of_injective J τ.symm.injective] using Finset.card_le_card hτ
  have hπeq : A.image π=J := Finset.eq_of_subset_of_card_le hπ (by
    simpa only [Finset.card_image_of_injective A π.injective] using hJA)
  have hτsur : J ⊆ A.image τ := by
    intro j hj
    have hpre : τ.symm j ∈ A := hτ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    exact Finset.mem_image.mpr ⟨τ.symm j, hpre, by simp⟩
  have hτeq : J=A.image τ := Finset.eq_of_subset_of_card_le hτsur (by
    simpa only [Finset.card_image_of_injective A τ.injective] using hAJ)
  exact ⟨hπeq, hτeq.symm⟩

theorem matching_cut_membership (A J : Finset Agent) (π : Equiv.Perm Agent)
    (himage : A.image π=J) (i : Agent) : π i ∈ J ↔ i ∈ A := by
  rw [← himage]
  constructor
  · intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    exact (π.injective heq) ▸ hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

def hybridMatching (A : Finset Agent) (π τ : Equiv.Perm Agent) (i : Agent) : Agent :=
  if i ∈ A then τ i else π i

/-- Swapping the two bijections on a common finite image block gives a genuine matching. -/
theorem hybrid_matching_bijective (A J : Finset Agent) (π τ : Equiv.Perm Agent)
    (hπ : A.image π=J) (hτ : A.image τ=J) :
    Function.Bijective (hybridMatching A π τ) := by
  have hπmem := matching_cut_membership A J π hπ
  have hτmem := matching_cut_membership A J τ hτ
  constructor
  · intro i j heq
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
    · simpa only [hybridMatching, hi, hj, ite_true, τ.injective.eq_iff] using heq
    · simp only [hybridMatching, hi, hj, ite_true, ite_false] at heq
      have hm : π j ∈ J := heq ▸ (hτmem i).2 hi
      exact False.elim (hj ((hπmem j).1 hm))
    · simp only [hybridMatching, hi, hj, ite_true, ite_false] at heq
      have hm : π i ∈ J := heq.symm ▸ (hτmem j).2 hj
      exact False.elim (hi ((hπmem i).1 hm))
    · simpa only [hybridMatching, hi, hj, ite_false, π.injective.eq_iff] using heq
  · intro j
    by_cases hj : j ∈ J
    · have hi : τ.symm j ∈ A := (hτmem (τ.symm j)).1 (by simpa using hj)
      exact ⟨τ.symm j, by simp [hybridMatching, hi]⟩
    · have hi : π.symm j ∉ A := by
        intro h
        have hm := (hπmem (π.symm j)).2 h
        exact hj (by simpa using hm)
      exact ⟨π.symm j, by simp [hybridMatching, hi]⟩

end Matchings

section CostTables

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

/-- Coherent strict parent signs and actual EF minima imply the matching sign-class identity. -/
theorem cost_table_sign_matching (x y : Agent → Agent → ℝ) (bx bY : Agent → ℝ)
    (π τ : Equiv.Perm Agent) (J : Finset Agent)
    (hπown : ∀ i, x i (π i)=bx i) (hτown : ∀ i, y i (τ i)=bY i)
    (hEFx : ∀ i p, bx i ≤ x i p) (hEFy : ∀ i p, bY i ≤ y i p)
    (hsign : ∀ i p, x i p < y i p ↔ p ∈ J) :
    (Finset.univ.filter fun i => bx i < bY i).image π=J ∧
      (Finset.univ.filter fun i => bx i < bY i).image τ=J := by
  apply matching_cut_equality
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    have hbi : bx i < bY i := (Finset.mem_filter.mp hi).2
    apply (hsign i (π i)).1
    rw [hπown]
    exact hbi.trans_le (hEFy i (π i))
  · intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hstrict := (hsign (τ.symm p) p).2 hp
    have hown := hτown (τ.symm p)
    simp only [Equiv.apply_symm_apply] at hown
    linarith [hEFx (τ.symm p) p]

/-- The coordinatewise maximum table has an EF bijection with the maximum old own costs. -/
theorem max_table_matching (x y : Agent → Agent → ℝ) (bx bY : Agent → ℝ)
    (π τ : Equiv.Perm Agent) (J : Finset Agent)
    (hπown : ∀ i, x i (π i)=bx i) (hτown : ∀ i, y i (τ i)=bY i)
    (hEFx : ∀ i p, bx i ≤ x i p) (hEFy : ∀ i p, bY i ≤ y i p)
    (hsign : ∀ i p, x i p < y i p ↔ p ∈ J) :
    ∃ σ : Agent → Agent, Function.Bijective σ ∧
      (∀ i, max (x i (σ i)) (y i (σ i))=max (bx i) (bY i)) ∧
      (∀ i p, max (bx i) (bY i) ≤ max (x i p) (y i p)) := by
  let A := Finset.univ.filter fun i => bx i < bY i
  have hcuts := cost_table_sign_matching x y bx bY π τ J hπown hτown hEFx hEFy hsign
  refine ⟨hybridMatching A π τ, hybrid_matching_bijective A J π τ hcuts.1 hcuts.2,
    ?_, fun i p => max_le_max (hEFx i p) (hEFy i p)⟩
  intro i
  by_cases hi : i ∈ A
  · have hb : bx i < bY i := (Finset.mem_filter.mp hi).2
    have hp := (matching_cut_membership A J τ hcuts.2 i).2 hi
    have hs := (hsign i (τ i)).2 hp
    simp only [hybridMatching, hi, ite_true]
    rw [max_eq_right hs.le, hτown, max_eq_right hb.le]
  · have hb : bY i ≤ bx i := by
      have hn : ¬bx i < bY i := by simpa [A] using hi
      exact le_of_not_gt hn
    have hp : π i ∉ J := fun h => hi ((matching_cut_membership A J π hcuts.1 i).1 h)
    have hs : y i (π i) ≤ x i (π i) := le_of_not_gt (fun h => hp ((hsign i (π i)).1 h))
    simp only [hybridMatching, hi, ite_false]
    rw [max_eq_left hs, hπown, max_eq_left hb]

/-- Reversing the same image-block swap realizes the coordinatewise minimum and its own minima. -/
theorem min_table_matching (x y : Agent → Agent → ℝ) (bx bY : Agent → ℝ)
    (π τ : Equiv.Perm Agent) (J : Finset Agent)
    (hπown : ∀ i, x i (π i)=bx i) (hτown : ∀ i, y i (τ i)=bY i)
    (hEFx : ∀ i p, bx i ≤ x i p) (hEFy : ∀ i p, bY i ≤ y i p)
    (hsign : ∀ i p, x i p < y i p ↔ p ∈ J) :
    ∃ σ : Agent → Agent, Function.Bijective σ ∧
      (∀ i, min (x i (σ i)) (y i (σ i))=min (bx i) (bY i)) ∧
      (∀ i p, min (bx i) (bY i) ≤ min (x i p) (y i p)) := by
  let A := Finset.univ.filter fun i => bx i < bY i
  have hcuts := cost_table_sign_matching x y bx bY π τ J hπown hτown hEFx hEFy hsign
  refine ⟨hybridMatching A τ π, hybrid_matching_bijective A J τ π hcuts.2 hcuts.1,
    ?_, fun i p => min_le_min (hEFx i p) (hEFy i p)⟩
  intro i
  by_cases hi : i ∈ A
  · have hb : bx i < bY i := (Finset.mem_filter.mp hi).2
    have hp := (matching_cut_membership A J π hcuts.1 i).2 hi
    have hs := (hsign i (π i)).2 hp
    simp only [hybridMatching, hi, ite_true]
    rw [min_eq_left hs.le, hπown, min_eq_left hb.le]
  · have hb : bY i ≤ bx i := by
      have hn : ¬bx i < bY i := by simpa [A] using hi
      exact le_of_not_gt hn
    have hp : τ i ∉ J := fun h => hi ((matching_cut_membership A J τ hcuts.2 i).1 h)
    have hs : y i (τ i) ≤ x i (τ i) := le_of_not_gt (fun h => hp ((hsign i (τ i)).1 h))
    simp only [hybridMatching, hi, ite_false]
    rw [min_eq_right hs, hτown, min_eq_right hb]

/-- Actual anchor equalities and strictly earlier ranks make an anchored EF table dominate
every coherent comparison table whose whole prefixes cannot grow. -/
theorem anchored_table_dominates (x y : Agent → Agent → ℝ) (bx bY : Agent → ℝ)
    (π τ : Equiv.Perm Agent) (J : Finset Agent) (rank : Agent → ℕ) (whole : Agent → Prop)
    (hπown : ∀ i, x i (π i)=bx i) (hτown : ∀ i, y i (τ i)=bY i)
    (hEFx : ∀ i p, bx i ≤ x i p) (hEFy : ∀ i p, bY i ≤ y i p)
    (hsign : ∀ i p, x i p < y i p ↔ p ∈ J)
    (hanchor : ∀ i, whole i ∨ ∃ j, rank j < rank i ∧ x i (π j)=bx i)
    (hwhole : ∀ i, whole i → y i (π i) ≤ x i (π i)) :
    J=∅ ∧ ∀ i p, y i p ≤ x i p := by
  let A := Finset.univ.filter fun i => bx i < bY i
  have hcuts := cost_table_sign_matching x y bx bY π τ J hπown hτown hEFx hEFy hsign
  have hnogrow : ∀ k, ∀ i, rank i=k → ¬bx i < bY i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro i hki hgrow
        rcases hanchor i with hw | ⟨j, hj, heq⟩
        · have hcost := hwhole i hw
          rw [hπown] at hcost
          linarith [hEFy i (π i)]
        · have hcost : x i (π j) < y i (π j) := by
            rw [heq]
            exact hgrow.trans_le (hEFy i (π j))
          have hp := (hsign i (π j)).1 hcost
          have hjA := (matching_cut_membership A J π hcuts.1 j).1 hp
          have hjgrow : bx j < bY j := (Finset.mem_filter.mp hjA).2
          exact ih (rank j) (by omega) j rfl hjgrow
  have hAempty : A=∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    exact hnogrow (rank i) i rfl (Finset.mem_filter.mp hi).2
  have hJ : J=∅ := by
    rw [← hcuts.1]
    change A.image π=∅
    simp [hAempty]
  refine ⟨hJ, ?_⟩
  intro i p
  apply le_of_not_gt
  intro h
  have hp := (hsign i p).1 h
  simp [hJ] at hp

omit [DecidableEq Agent] in
/-- Strict increase along each parent supplies the common sign class used above. -/
theorem strict_prefix_signs (cost : Agent → Agent → ℝ → ℝ) (x y : Agent → ℝ)
    (hstrict : ∀ i p, StrictMono (cost i p)) :
    ∀ i p, cost i p (x p) < cost i p (y p) ↔
      p ∈ (Finset.univ.filter fun p => x p < y p) := by
  intro i p
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (hstrict i p).lt_iff_lt

/-- For strictly increasing parent cost functions, anchored EF endpoints dominate
the endpoints of every other feasible EF matching. -/
theorem anchored_prefix_maximality (cost : Agent → Agent → ℝ → ℝ)
    (x y cap : Agent → ℝ) (bx bY : Agent → ℝ) (π τ : Equiv.Perm Agent)
    (rank : Agent → ℕ) (whole : Agent → Prop)
    (hstrict : ∀ i p, StrictMono (cost i p))
    (hπown : ∀ i, cost i (π i) (x (π i))=bx i)
    (hτown : ∀ i, cost i (τ i) (y (τ i))=bY i)
    (hEFx : ∀ i p, bx i ≤ cost i p (x p))
    (hEFy : ∀ i p, bY i ≤ cost i p (y p))
    (hanchor : ∀ i, whole i ∨ ∃ j, rank j < rank i ∧ cost i (π j) (x (π j))=bx i)
    (hwhole : ∀ i, whole i → x (π i)=cap (π i))
    (hfeasible : ∀ p, y p ≤ cap p) : ∀ p, y p ≤ x p := by
  have h := anchored_table_dominates (fun i p => cost i p (x p))
    (fun i p => cost i p (y p)) bx bY π τ
    (Finset.univ.filter fun p => x p < y p) rank whole hπown hτown hEFx hEFy
    (strict_prefix_signs cost x y hstrict) hanchor (by
      intro i hi
      apply (hstrict i (π i)).monotone
      rw [hwhole i hi]
      exact hfeasible (π i))
  intro p
  exact (hstrict p p).le_iff_le.mp (h.2 p p)

end CostTables

/-- Any nonempty finite backward-closed growing set must contain a whole anchor. -/
theorem least_growing_whole (G : Finset ℕ) (whole : ℕ → Prop) (hG : G.Nonempty)
    (hanchor : ∀ i ∈ G, whole i ∨ ∃ j ∈ G, j < i) :
    ∃ i ∈ G, whole i := by
  let i := G.min' hG
  have hi : i ∈ G := Finset.min'_mem G hG
  rcases hanchor i hi with hwhole | ⟨j, hj, hji⟩
  · exact ⟨i, hi, hwhole⟩
  · have hmin : i ≤ j := Finset.min'_le G j hj
    omega

/-- Whole prefixes cannot grow, so backward anchor propagation rules out every growing position. -/
theorem backward_anchor_obstruction (G : Finset ℕ) (whole : ℕ → Prop)
    (hanchor : ∀ i ∈ G, whole i ∨ ∃ j ∈ G, j < i)
    (hwhole : ∀ i ∈ G, ¬whole i) : G=∅ := by
  by_contra hne
  have hnonempty : G.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨i, hi, hw⟩ := least_growing_whole G whole hnonempty hanchor
  exact hwhole i hi hw

/-- A directly supplied strictly earlier anchor map gives the same finite contradiction. -/
theorem closed_strict_descent_empty (G : Finset ℕ) (anchor : ℕ → ℕ)
    (hclosed : ∀ i ∈ G, anchor i ∈ G) (hstrict : ∀ i ∈ G, anchor i < i) : G=∅ := by
  apply backward_anchor_obstruction G (fun _ => False)
  · intro i hi
    exact Or.inr ⟨anchor i, hclosed i hi, hstrict i hi⟩
  · simp

/-- The actual number of possible tested last-pair transitions, starting at state size two. -/
def coreTransitionCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n-1), (k+2)^2*(n.choose (k+2))^2

/-- The marked-binomial identity applies before summing over subset pairs. -/
theorem marked_choose_square (n k : ℕ) :
    (k+1)^2*((n+1).choose (k+1))^2=(n+1)^2*(n.choose k)^2 := by
  calc
    (k+1)^2*((n+1).choose (k+1))^2 = (((n+1).choose (k+1))*(k+1))^2 := by ring
    _ = ((n+1)*(n.choose k))^2 := congrArg (fun t : ℕ => t^2)
      (Nat.add_one_mul_choose_eq n k).symm
    _ = (n+1)^2*(n.choose k)^2 := by ring

/-- Vandermonde evaluates the weighted balanced-subset transition sum exactly. -/
theorem weighted_choose_square_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+2), k^2*((n+1).choose k)^2) =
      (n+1)^2*((2*n).choose n) := by
  calc
    (∑ k ∈ Finset.range (n+2), k^2*((n+1).choose k)^2) =
        ∑ k ∈ Finset.range (n+1), (k+1)^2*((n+1).choose (k+1))^2 := by
      rw [Finset.sum_range_succ']
      simp
    _ = ∑ k ∈ Finset.range (n+1), (n+1)^2*(n.choose k)^2 :=
      Finset.sum_congr rfl (fun k _ => marked_choose_square n k)
    _ = (n+1)^2*((2*n).choose n) := by
      rw [← Finset.mul_sum, Nat.sum_range_choose_sq]

/-- Removing the zero and singleton terms gives the precise tested-transition identity. -/
theorem core_transition_balance (n : ℕ) :
    coreTransitionCount (n+1)+(n+1)^2=(n+1)^2*((2*n).choose n) := by
  have h := weighted_choose_square_sum n
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
  simpa [coreTransitionCount, Nat.add_assoc] using h

theorem core_transition_closed (n : ℕ) (hn : 0 < n) :
    coreTransitionCount n=n^2*(((2*(n-1)).choose (n-1))-1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := core_transition_balance m
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
  rw [Nat.mul_sub, mul_one]
  omega

/-- The transition count has a polynomial-times-four-to-n upper bound. -/
theorem core_transition_bound (n : ℕ) (hn : 0 < n) :
    coreTransitionCount n ≤ n^2*4^(n-1) := by
  rw [core_transition_closed n hn]
  apply Nat.mul_le_mul_left
  have h : (2*(n-1)).choose (n-1) ≤ 4^(n-1) :=
    Nat.centralBinom_le_four_pow (n-1)
  exact (Nat.sub_le _ _).trans h

/-- Counting all balanced subset pairs, including the empty pair, gives a central binomial. -/
theorem balanced_subset_state_count (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k)^2)=(2*n).choose n :=
  Nat.sum_range_choose_sq n

def coreStateCount (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (n.choose (k+1))^2

/-- The nonempty states are counted by deleting exactly the empty subset pair. -/
theorem nonempty_core_state_count (n : ℕ) : coreStateCount n+1=(2*n).choose n := by
  have h := Nat.sum_range_choose_sq n
  rw [Finset.sum_range_succ'] at h
  simpa [coreStateCount] using h

/-- Charging every tested candidate, including failed ones, bounds all recorded query costs. -/
theorem core_candidate_query_ledger (n queries cuts : ℕ)
    (hcandidates : queries ≤ n*n+n*coreTransitionCount n)
    (hcuts : cuts ≤ n-1+coreTransitionCount n) (hn : 0 < n) :
    queries ≤ n*n+n^3*4^(n-1) ∧ cuts ≤ n-1+n^2*4^(n-1) := by
  have h := core_transition_bound n hn
  have hm := Nat.mul_le_mul_left n h
  constructor <;> nlinarith

end EnvyFreeResearch.R6Core

#print axioms EnvyFreeResearch.R6Core.matching_cut_equality
#print axioms EnvyFreeResearch.R6Core.hybrid_matching_bijective
#print axioms EnvyFreeResearch.R6Core.max_table_matching
#print axioms EnvyFreeResearch.R6Core.min_table_matching
#print axioms EnvyFreeResearch.R6Core.anchored_table_dominates
#print axioms EnvyFreeResearch.R6Core.anchored_prefix_maximality
#print axioms EnvyFreeResearch.R6Core.backward_anchor_obstruction
#print axioms EnvyFreeResearch.R6Core.core_transition_closed
#print axioms EnvyFreeResearch.R6Core.core_candidate_query_ledger
