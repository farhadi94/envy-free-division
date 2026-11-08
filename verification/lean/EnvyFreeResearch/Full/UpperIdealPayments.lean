import EnvyFreeResearch.Full.UpperPotentials

/-!
# Actual ideal payment targets for cake and chores

Finite permutation enumeration implements the rejection test. On its
accepting branch the constructed simple-path potentials satisfy every ideal
payment inequality. Row maxima and the actual optimal assignment provide
the quantitative payment budget.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperIdealPayments

open UpperRepresentatives UpperAssignment UpperAssignmentIsolation UpperPotentials

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def rowChoice (V : Agent → Agent → ℝ) (i : Agent) : Agent :=
  ((Finset.univ.toList : List Agent).argmax (V i)).getD i

def rowMaximum (V : Agent → Agent → ℝ) (i : Agent) : ℝ := V i (rowChoice V i)

def regret (V : Agent → Agent → ℝ) (i : Agent) : ℝ :=
  rowMaximum V i - V i (maximize V i)

theorem rowMaximum_spec (V : Agent → Agent → ℝ) (i j : Agent) : V i j ≤ rowMaximum V i := by
  have hne : (Finset.univ.toList : List Agent) ≠ [] := by
    intro h
    have hi : i ∈ (Finset.univ.toList : List Agent) := by simp
    simp [h] at hi
  obtain ⟨best, hbest⟩ := argmax_exists (V i) Finset.univ.toList hne
  have h := List.le_of_mem_argmax (f := V i) (show j ∈ Finset.univ.toList by simp)
    (show best ∈ Finset.univ.toList.argmax (V i) by simp [hbest])
  simpa [rowMaximum, rowChoice, hbest] using h

theorem regret_nonnegative (V : Agent → Agent → ℝ) (i : Agent) : 0 ≤ regret V i :=
  sub_nonneg.mpr (rowMaximum_spec V i _)

/-- Actual assignment optimality bounds total assigned shortfall by the
shortfall of the identity assignment. -/
theorem sum_regret_le_identity (V : Agent → Agent → ℝ) :
    (∑ i, regret V i) ≤ ∑ i, (rowMaximum V i - V i i) := by
  have h := maximize_spec V (Equiv.refl Agent)
  simp only [score, Equiv.refl_apply] at h
  simp only [regret, Finset.sum_sub_distrib]
  linarith

def edge (V A : Agent → Agent → ℝ) (lam : ℝ) (i j : Agent) : ℝ :=
  V i (maximize V j) - V i (maximize V i) + 2 * lam * A i j

def findPositive (V A : Agent → Agent → ℝ) (lam : ℝ) : Option (Equiv.Perm Agent) :=
  assignments.find? (fun transfer => decide (0 < margin V A lam transfer))

theorem findPositive_eq_none (V A : Agent → Agent → ℝ) (lam : ℝ) :
    findPositive V A lam = none ↔ ∀ transfer : Equiv.Perm Agent, margin V A lam transfer ≤ 0 := by
  simp [findPositive, List.find?_eq_none, mem_assignments, not_lt]

theorem findPositive_failure (V A : Agent → Agent → ℝ) (lam : ℝ) :
    findPositive V A lam ≠ none ↔ ∃ transfer : Equiv.Perm Agent, 0 < margin V A lam transfer := by
  rw [ne_eq, findPositive_eq_none]
  push_neg
  rfl

theorem accepted_no_positive_permutation (V A : Agent → Agent → ℝ) (lam : ℝ)
    (haccept : findPositive V A lam = none) : NoPositivePermutation (edge V A lam) :=
  (findPositive_eq_none V A lam).mp haccept

theorem edge_diagonal (V A : Agent → Agent → ℝ) (lam : ℝ) (hdiag : ∀ i, A i i = 0) :
    ∀ i, edge V A lam i i = 0 := by intro i; simp [edge, hdiag]

theorem edge_bound (V A : Agent → Agent → ℝ) (lam eta : ℝ)
    (hlam : 0 ≤ lam) (hA : ∀ i j, A i j ≤ eta) (i j : Agent) :
    edge V A lam i j ≤ regret V i + 2 * lam * eta := by
  have hvalue := rowMaximum_spec V i (maximize V j)
  have hmargin := mul_le_mul_of_nonneg_left (hA i j) (show 0 ≤ 2 * lam by positivity)
  dsimp only [edge, regret]
  linarith

def allowance (V : Agent → Agent → ℝ) (delta : ℝ) : ℝ :=
  (∑ i, regret V i) + (Fintype.card Agent - 1 : ℕ) * delta

def cakeTargets (V A : Agent → Agent → ℝ) (lam : ℝ) : Agent → ℝ :=
  potential (edge V A lam)

/-- For chores a common shift of the negative potential makes every payment
nonnegative while preserving the required reverse difference inequalities. -/
def choreTargets (V A : Agent → Agent → ℝ) (lam eta : ℝ) (i : Agent) : ℝ :=
  allowance (fun r c => -V r c) (2 * lam * eta) -
    potential (edge (fun r c => -V r c) A lam) i

theorem cakeTargets_bound (V A : Agent → Agent → ℝ) (lam eta : ℝ)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (hA : ∀ i j, A i j ≤ eta) (i : Agent) :
    0 ≤ cakeTargets V A lam i ∧ cakeTargets V A lam i ≤ allowance V (2 * lam * eta) := by
  exact ⟨potential_nonnegative _ i,
    potential_bound _ (regret V) (2 * lam * eta) (regret_nonnegative V)
      (by positivity) (edge_bound V A lam eta hlam hA) i⟩

theorem choreTargets_bound (V A : Agent → Agent → ℝ) (lam eta : ℝ)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (hA : ∀ i j, A i j ≤ eta) (i : Agent) :
    0 ≤ choreTargets V A lam eta i ∧
      choreTargets V A lam eta i ≤ allowance (fun r c => -V r c) (2 * lam * eta) := by
  have h := cakeTargets_bound (fun r c => -V r c) A lam eta hlam heta hA i
  change 0 ≤ allowance (fun r c => -V r c) (2 * lam * eta) - cakeTargets (fun r c => -V r c) A lam i ∧ _
  constructor <;> dsimp only [choreTargets, cakeTargets] at * <;> linarith

theorem cake_ideal_inequalities (V A : Agent → Agent → ℝ) (lam : ℝ)
    (hdiag : ∀ i, A i i = 0) (haccept : findPositive V A lam = none) (i j : Agent) :
    2 * lam * A i j ≤
      V i (maximize V i) + cakeTargets V A lam i - V i (maximize V j) - cakeTargets V A lam j := by
  have h := potential_inequality (edge V A lam) (edge_diagonal V A lam hdiag)
    (accepted_no_positive_permutation V A lam haccept) i j
  dsimp only [edge, cakeTargets] at *
  linarith

theorem chore_ideal_inequalities (V A : Agent → Agent → ℝ) (lam eta : ℝ)
    (hdiag : ∀ i, A i i = 0)
    (haccept : findPositive (fun r c => -V r c) A lam = none) (i j : Agent) :
    2 * lam * A i j ≤
      V i (minimize V j) + choreTargets V A lam eta j -
        V i (minimize V i) - choreTargets V A lam eta i := by
  have h := potential_inequality (edge (fun r c => -V r c) A lam)
    (edge_diagonal (fun r c => -V r c) A lam hdiag)
    (accepted_no_positive_permutation (fun r c => -V r c) A lam haccept) i j
  dsimp only [edge, choreTargets, minimize] at *
  linarith

theorem allowance_le_identity (V : Agent → Agent → ℝ) (delta : ℝ) :
    allowance V delta ≤ (∑ i, (rowMaximum V i - V i i)) + (Fintype.card Agent - 1 : ℕ) * delta :=
  add_le_add (sum_regret_le_identity V) le_rfl

theorem allowance_le (V : Agent → Agent → ℝ) (eps delta : ℝ)
    (hnear : ∀ i, rowMaximum V i - V i i ≤ eps) :
    allowance V delta ≤ Fintype.card Agent * eps + (Fintype.card Agent - 1 : ℕ) * delta := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Agent)) => hnear i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  exact (allowance_le_identity V delta).trans (add_le_add hsum le_rfl)

theorem cakeTargets_sum_bound (V A : Agent → Agent → ℝ) (lam eta : ℝ)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (hA : ∀ i j, A i j ≤ eta) :
    (∑ i, cakeTargets V A lam i) ≤ Fintype.card Agent * allowance V (2 * lam * eta) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Agent)) =>
    (cakeTargets_bound V A lam eta hlam heta hA i).2)
  simpa using h

theorem choreTargets_sum_bound (V A : Agent → Agent → ℝ) (lam eta : ℝ)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (hA : ∀ i j, A i j ≤ eta) :
    (∑ i, choreTargets V A lam eta i) ≤
      Fintype.card Agent * allowance (fun r c => -V r c) (2 * lam * eta) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Agent)) =>
    (choreTargets_bound V A lam eta hlam heta hA i).2)
  simpa using h

end EnvyFreeResearch.Full.UpperIdealPayments
