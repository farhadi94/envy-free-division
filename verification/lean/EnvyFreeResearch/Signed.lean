import Mathlib

/-!
# Algebraic certificates for envy-free allocation with signed values

These results concern finite utility tables and finite residual atoms. They do
not assert that sign regions of an arbitrary signed measure can be discovered
by Robertson--Webb queries, nor that an arbitrary signed measure has a finite
sign partition. Completeness/geometric disjointness of cell allocations is an
external hypothesis represented by additivity in the utility-table sum.
-/

namespace EnvyFreeResearch.Signed

open scoped BigOperators

/-- Row `i` evaluates the bundle assigned to column `j`. -/
def EnvyFree {Agent : Type*} (u : Agent → Agent → ℝ) : Prop :=
  ∀ i j, u i j ≤ u i i

/-- Envy-free utility tables add, with no assumption on the signs of entries. -/
theorem envyFree_add {Agent : Type*} {u v : Agent → Agent → ℝ}
    (hu : EnvyFree u) (hv : EnvyFree v) :
    EnvyFree (fun i j => u i j + v i j) := by
  intro i j
  exact add_le_add (hu i j) (hv i j)

/-- Disjoint cell allocations compose by additivity, even for signed values. -/
theorem envyFree_sum {Agent Cell : Type*} (s : Finset Cell)
    (u : Cell → Agent → Agent → ℝ)
    (hu : ∀ c ∈ s, EnvyFree (u c)) :
    EnvyFree (fun i j => ∑ c ∈ s, u c i j) := by
  intro i j
  exact Finset.sum_le_sum (fun c hc => hu c hc i j)

/--
Route a cell to a subset of agents who like it. Insiders receive an EF
allocation with nonnegative own values; outsiders receive empty bundles and
value every bundle nonpositively. The conclusion is EF among *all* agents.

The assumptions are about every allocated bundle, not merely the net value of
the whole cell. That distinction matters for signed measures.
-/
theorem sign_cell_routing {Agent : Type*} (P : Set Agent)
    (u : Agent → Agent → ℝ)
    (inside_ef : ∀ i ∈ P, ∀ j ∈ P, u i j ≤ u i i)
    (inside_own_nonneg : ∀ i ∈ P, 0 ≤ u i i)
    (outside_empty : ∀ j ∉ P, ∀ i, u i j = 0)
    (outside_nonpos : ∀ i ∉ P, ∀ j, u i j ≤ 0) :
    EnvyFree u := by
  intro i j
  by_cases hi : i ∈ P
  · by_cases hj : j ∈ P
    · exact inside_ef i hi j hj
    · rw [outside_empty j hj i]
      exact inside_own_nonneg i hi
  · rw [outside_empty i hi i]
    exact outside_nonpos i hi j

/-- A minimum-cost envy-free chore allocation is EF for its negated utilities. -/
theorem chore_to_signed {Agent : Type*} (cost : Agent → Agent → ℝ)
    (h : ∀ i j, cost i i ≤ cost i j) :
    EnvyFree (fun i j => -cost i j) := by
  intro i j
  exact neg_le_neg (h i j)

/--
The entire resource can go to one agent if that agent weakly likes its total
and every other agent weakly dislikes its total. No rank-one assumption is
needed: only one nonempty bundle is allocated.
-/
theorem whole_to_one {Agent : Type*} [DecidableEq Agent]
    (v : Agent → ℝ) (recipient : Agent)
    (hrecipient : 0 ≤ v recipient)
    (hothers : ∀ i, i ≠ recipient → v i ≤ 0) :
    EnvyFree (fun i j => if j = recipient then v i else 0) := by
  intro i j
  by_cases hi : i = recipient
  · subst i
    by_cases hj : j = recipient <;> simp [hj, hrecipient]
  · by_cases hj : j = recipient
    · simpa [hi, hj] using hothers i hi
    · simp [hi, hj]

/-- The all-to-zero-total branch of the mixed-cake construction. -/
theorem whole_to_zero_total {Agent : Type*} [DecidableEq Agent]
    (v : Agent → ℝ) (recipient : Agent)
    (hzero : v recipient = 0) (hnonpos : ∀ i, v i ≤ 0) :
    EnvyFree (fun i j => if j = recipient then v i else 0) := by
  apply whole_to_one v recipient
  · exact le_of_eq hzero.symm
  · intro i hi
    exact hnonpos i

/--
For a common signed base measure, equal-base-value pieces routed to a subset
give this utility table. The proof requires nonnegative total scalar value
for insiders and nonpositive total scalar value for outsiders. Physical
existence/completeness of the equal-base-value pieces remains separate.
-/
theorem rankOne_routed_shares {Agent : Type*} [DecidableEq Agent]
    (P : Finset Agent) (coefficient : Agent → ℝ) (baseTotal : ℝ)
    (hinside : ∀ i ∈ P, 0 ≤ coefficient i * baseTotal)
    (houtside : ∀ i ∉ P, coefficient i * baseTotal ≤ 0) :
    EnvyFree (fun i j =>
      if j ∈ P then coefficient i * baseTotal / (P.card : ℝ) else 0) := by
  apply sign_cell_routing (P : Set Agent)
  · intro i hi j hj
    simp only [Finset.mem_coe] at hi hj
    simp [hi, hj]
  · intro i hi
    simp only [Finset.mem_coe] at hi
    simp only [hi, ite_true]
    exact div_nonneg (hinside i hi) (Nat.cast_nonneg _)
  · intro j hj i
    simp only [Finset.mem_coe] at hj
    simp [hj]
  · intro i hi j
    simp only [Finset.mem_coe] at hi
    by_cases hj : j ∈ P
    · simp only [hj, ite_true]
      exact div_nonpos_of_nonpos_of_nonneg (houtside i hi) (Nat.cast_nonneg _)
    · simp [hj]

/-- Equal values across recipient columns imply EF, whatever their signs. -/
theorem equal_columns_envyFree {Agent : Type*} (v : Agent → ℝ) :
    EnvyFree (fun i _ => v i) := by
  intro i j
  exact le_rfl

/--
Two-agent cut-and-choose only needs an equal-valued partition for the cutter.
Neither agent's values must be nonnegative. `false` is the cutter and `true`
the chooser; the two Boolean columns are the two pieces.

This theorem is conditional on the equal-valued cut. It makes no hidden claim
about a signed cut oracle or its computational implementation.
-/
theorem signed_cut_and_choose (v : Bool → Bool → ℝ)
    (equal_for_cutter : v false false = v false true) :
    ∃ allocation : Bool → Bool,
      Function.Bijective allocation ∧
        EnvyFree (fun i j => v i (allocation j)) := by
  by_cases h : v true false ≤ v true true
  · refine ⟨id, Function.bijective_id, ?_⟩
    intro i j
    cases i <;> cases j <;> simp_all
  · have h' : v true true ≤ v true false := le_of_lt (lt_of_not_ge h)
    refine ⟨Bool.not, ?_, ?_⟩
    · constructor
      · intro a b hab
        cases a <;> cases b <;> simp_all
      · intro b
        exact ⟨!b, by cases b <;> rfl⟩
    · intro i j
      cases i <;> cases j <;> simp_all

section Residue

variable {Atom : Type*} [DecidableEq Atom]

/-- The value of the part of finite residue `R` assigned according to set `S`. -/
def assignedValue (w : Atom → ℝ) (R S : Finset Atom) : ℝ :=
  ∑ a ∈ R, if a ∈ S then w a else 0

/-- The exact finite-atom total variation of a signed valuation. -/
def totalVariation (w : Atom → ℝ) (R : Finset Atom) : ℝ :=
  ∑ a ∈ R, |w a|

/-- Positive and negative Jordan masses in the finite-atom setting. -/
def positiveMass (w : Atom → ℝ) (R : Finset Atom) : ℝ :=
  ∑ a ∈ R, max (w a) 0

def negativeMass (w : Atom → ℝ) (R : Finset Atom) : ℝ :=
  ∑ a ∈ R, max (-w a) 0

omit [DecidableEq Atom] in
theorem totalVariation_nonneg (w : Atom → ℝ) (R : Finset Atom) :
    0 ≤ totalVariation w R := by
  exact Finset.sum_nonneg (fun a _ => abs_nonneg (w a))

omit [DecidableEq Atom] in
/-- Cancellation in the net residual value can never enlarge its absolute value. -/
theorem abs_net_value_le_totalVariation (w : Atom → ℝ) (R : Finset Atom) :
    |∑ a ∈ R, w a| ≤ totalVariation w R := by
  exact Finset.abs_sum_le_sum_abs _ _

theorem assignedValue_le_positiveMass (w : Atom → ℝ) (R S : Finset Atom) :
    assignedValue w R S ≤ positiveMass w R := by
  apply Finset.sum_le_sum
  intro a ha
  by_cases hs : a ∈ S
  · simp [hs]
  · simp [hs]

theorem neg_assignedValue_le_negativeMass (w : Atom → ℝ) (R S : Finset Atom) :
    -assignedValue w R S ≤ negativeMass w R := by
  unfold assignedValue negativeMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hs : a ∈ S
  · simp [hs]
  · simp [hs]

omit [DecidableEq Atom] in
theorem jordan_masses_sum (w : Atom → ℝ) (R : Finset Atom) :
    positiveMass w R + negativeMass w R = totalVariation w R := by
  unfold positiveMass negativeMass totalVariation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : 0 ≤ w a
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
    ring
  · have h' : w a ≤ 0 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right h', max_eq_left (by linarith), abs_of_nonpos h']
    ring

/--
Giving arbitrary parts of `R` to oneself and a competitor changes the envy
gap by at most total variation. Disjointness is not needed for this inequality:
an atom occurring in both sums cancels. Valid allocations are a special case.
-/
theorem residual_loss_le_totalVariation (w : Atom → ℝ) (R S T : Finset Atom) :
    assignedValue w R T - assignedValue w R S ≤ totalVariation w R := by
  unfold assignedValue totalVariation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a ha
  split_ifs <;>
    linarith [le_abs_self (w a), neg_le_abs (w a), abs_nonneg (w a)]

/-- The finite Hahn partition attains the worst possible pairwise loss. -/
theorem hahn_partition_attains (w : Atom → ℝ) (R : Finset Atom) :
    ∃ S T : Finset Atom,
      Disjoint S T ∧ S ∪ T = R ∧
        assignedValue w R T - assignedValue w R S = totalVariation w R := by
  classical
  let S := R.filter (fun a => w a < 0)
  let T := R.filter (fun a => 0 ≤ w a)
  refine ⟨S, T, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro a hs ht
    have hs' : w a < 0 := (Finset.mem_filter.mp hs).2
    have ht' : 0 ≤ w a := (Finset.mem_filter.mp ht).2
    linarith
  · ext a
    simp only [S, T, Finset.mem_union, Finset.mem_filter]
    by_cases h : 0 ≤ w a
    · simp [h, not_lt.mpr h]
    · have h' : w a < 0 := lt_of_not_ge h
      simp [h, h']
  · unfold assignedValue totalVariation
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : 0 ≤ w a
    · simp [S, T, ha, h, not_lt.mpr h, abs_of_nonneg h]
    · have h' : w a < 0 := lt_of_not_ge h
      simp [S, T, ha, h, h', abs_of_neg h']

/--
Total variation is the *least* uniform pairwise residual-risk bound, already
when all residual atoms are allocated between just the two agents.
-/
theorem uniform_residual_bound_iff (w : Atom → ℝ) (R : Finset Atom) (b : ℝ) :
    (∀ S T : Finset Atom, Disjoint S T → S ∪ T = R →
      assignedValue w R T - assignedValue w R S ≤ b) ↔
        totalVariation w R ≤ b := by
  constructor
  · intro h
    obtain ⟨S, T, hd, hu, heq⟩ := hahn_partition_attains w R
    rw [← heq]
    exact h S T hd hu
  · intro h S T hd hu
    exact (residual_loss_le_totalVariation w R S T).trans h

/-- Exact criterion for robustness against *every* complete two-recipient split. -/
theorem robust_completion_iff (w : Atom → ℝ) (R : Finset Atom)
    (own other : ℝ) :
    (∀ S T : Finset Atom, Disjoint S T → S ∪ T = R →
      other + assignedValue w R T ≤ own + assignedValue w R S) ↔
        other + totalVariation w R ≤ own := by
  constructor
  · intro h
    obtain ⟨S, T, hd, hu, heq⟩ := hahn_partition_attains w R
    have hb := h S T hd hu
    linarith
  · intro h S T hd hu
    have hb := residual_loss_le_totalVariation w R S T
    linarith

/-- A sufficient certificate for arbitrary pairwise residual additions. -/
theorem robust_pair_completion (w : Atom → ℝ) (R S T : Finset Atom)
    (own other : ℝ) (hgap : other + totalVariation w R ≤ own) :
    other + assignedValue w R T ≤ own + assignedValue w R S := by
  have hb := residual_loss_le_totalVariation w R S T
  linarith

end Residue

/-- Separate positive and negative risk budgets give a sharper asymmetric test. -/
theorem asymmetric_pair_completion (own other ownAdd otherAdd p q : ℝ)
    (hother : otherAdd ≤ p) (hown : -ownAdd ≤ q)
    (hgap : other + p + q ≤ own) :
    other + otherAdd ≤ own + ownAdd := by
  linarith

/-- If the observing agent is not given any residue, only the positive mass matters. -/
theorem excluded_observer_completion {Atom : Type*} [DecidableEq Atom]
    (w : Atom → ℝ) (R T : Finset Atom) (own other : ℝ)
    (hgap : other + positiveMass w R ≤ own) :
    other + assignedValue w R T ≤ own := by
  have hb := assignedValue_le_positiveMass w R T
  linarith

/-- If the competitor gets no residue, only the observer's negative mass matters. -/
theorem excluded_competitor_completion {Atom : Type*} [DecidableEq Atom]
    (w : Atom → ℝ) (R S : Finset Atom) (own other : ℝ)
    (hgap : other + negativeMass w R ≤ own) :
    other ≤ own + assignedValue w R S := by
  have hb := neg_assignedValue_le_negativeMass w R S
  linarith

/--
A net-zero residue can reverse a positive envy gap: an old own value 1 versus
other value 0 becomes 0 versus 1 after receiving -1 and giving the other +1.
-/
theorem net_zero_residue_counterexample :
    ((-1 : ℝ) + 1 = 0) ∧
    (0 + ((-1 : ℝ) + 1) ≤ 1) ∧
    ¬(0 + (1 : ℝ) ≤ 1 + (-1)) := by
  norm_num

#print axioms envyFree_sum
#print axioms sign_cell_routing
#print axioms whole_to_zero_total
#print axioms rankOne_routed_shares
#print axioms signed_cut_and_choose
#print axioms hahn_partition_attains
#print axioms robust_completion_iff
#print axioms excluded_observer_completion
#print axioms net_zero_residue_counterexample

end EnvyFreeResearch.Signed
