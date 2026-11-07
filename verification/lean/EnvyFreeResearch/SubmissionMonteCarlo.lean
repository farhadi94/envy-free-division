import Mathlib

/-!
# Finite event accounting and the optimized exact Monte Carlo lower bound

These are genuine finite weighted-event and real-algebra certificates. They do
not construct the nearby-bump distribution, replay an adaptive oracle, or
formalize arbitrary random tapes. In particular, the failure-event inclusion
and the quantitative separation/collision estimates used below must be proved
by the separate continuous argument.
-/

namespace EnvyFreeResearch.SubmissionMonteCarlo

open scoped BigOperators

section FiniteEvents

variable {Outcome Agent : Type*} [Fintype Outcome] [Fintype Agent]
  [DecidableEq Outcome] [DecidableEq Agent]

noncomputable def eventMass (weight : Outcome → ℝ) (event : Finset Outcome) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ event then weight ω else 0

theorem eventMass_nonnegative (weight : Outcome → ℝ) (event : Finset Outcome)
    (hweight : ∀ ω, 0 ≤ weight ω) : 0 ≤ eventMass weight event := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hweight ω
  · exact le_rfl

/-- A pointwise decoder, after two exceptional events are removed, gives the
corresponding weighted probability inequality. No independence is needed. -/
theorem failure_mass_after_two_exceptions
    (weight : Outcome → ℝ) (signal badQuery badBoundary failure : Finset Outcome)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hdecoder : ∀ ω ∈ signal, ω ∉ badQuery → ω ∉ badBoundary → ω ∈ failure) :
    eventMass weight signal - eventMass weight badQuery - eventMass weight badBoundary ≤
      eventMass weight failure := by
  classical
  have hpoint (ω : Outcome) :
      (if ω ∈ signal then weight ω else 0) -
        (if ω ∈ badQuery then weight ω else 0) -
        (if ω ∈ badBoundary then weight ω else 0) ≤
          (if ω ∈ failure then weight ω else 0) := by
    by_cases hs : ω ∈ signal
    · by_cases hq : ω ∈ badQuery
      · by_cases hb : ω ∈ badBoundary <;> by_cases hf : ω ∈ failure <;>
          simp only [hs, hq, hb, hf, ite_true, ite_false] <;> linarith [hweight ω]
      · by_cases hb : ω ∈ badBoundary
        · by_cases hf : ω ∈ failure <;>
            simp only [hs, hq, hb, hf, ite_true, ite_false] <;> linarith [hweight ω]
        · have hf := hdecoder ω hs hq hb
          simp [hs, hq, hb, hf]
    · by_cases hq : ω ∈ badQuery <;> by_cases hb : ω ∈ badBoundary <;>
        by_cases hf : ω ∈ failure <;>
        simp only [hs, hq, hb, hf, ite_true, ite_false] <;> linarith [hweight ω]
  simpa only [eventMass, Finset.sum_sub_distrib] using
    Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)

/-- Removing a subevent subtracts its mass exactly. -/
theorem eventMass_sdiff (weight : Outcome → ℝ) (event collision : Finset Outcome)
    (hsubset : collision ⊆ event) :
    eventMass weight (event \ collision) =
      eventMass weight event - eventMass weight collision := by
  classical
  rw [eventMass, eventMass, eventMass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hc : ω ∈ collision
  · simp [hc, hsubset hc]
  · simp [hc]

/-- An independent uniformly selected observer avoids an outcome-dependent
excluded label with the exact factor (N-1)/N. This is a finite product sum,
not a union bound that loses an extra 1/N. -/
theorem uniform_observer_exclusion [Nonempty Agent]
    (weight : Outcome → ℝ) (event : Finset Outcome) (excluded : Outcome → Agent) :
    (∑ ω, ∑ i, if ω ∈ event ∧ i ≠ excluded ω then
      weight ω / (Fintype.card Agent : ℝ) else 0) =
      (1 - 1 / (Fintype.card Agent : ℝ)) * eventMass weight event := by
  classical
  have hn : (Fintype.card Agent : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [eventMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ event
  · simp only [hω, true_and, ite_true]
    have hid (i : Agent) :
        (if i ≠ excluded ω then weight ω / (Fintype.card Agent : ℝ) else 0) =
          weight ω / (Fintype.card Agent : ℝ) -
            (if i = excluded ω then weight ω / (Fintype.card Agent : ℝ) else 0) := by
      by_cases hi : i = excluded ω <;> simp [hi]
    simp_rw [hid]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
  · simp [hω]

/-- The finite success/collision ledger retains the multiplicative observer
factor. The collision bound is relative to successful tapes. -/
theorem eligible_observer_mass_lower [Nonempty Agent]
    (weight : Outcome → ℝ) (success collision : Finset Outcome)
    (excluded : Outcome → Agent) (s c : ℝ)
    (hcollision : collision ⊆ success)
    (hsuccess : s ≤ eventMass weight success)
    (hbound : eventMass weight collision ≤ c * eventMass weight success)
    (hc : c ≤ 1) :
    (1 - 1 / (Fintype.card Agent : ℝ)) * (1 - c) * s ≤
      ∑ ω, ∑ i, if ω ∈ success \ collision ∧ i ≠ excluded ω then
        weight ω / (Fintype.card Agent : ℝ) else 0 := by
  classical
  rw [uniform_observer_exclusion, eventMass_sdiff weight success collision hcollision]
  have hn : (1 : ℝ) ≤ Fintype.card Agent := by
    exact_mod_cast Fintype.card_pos
  have hfactor : 0 ≤ 1 - 1 / (Fintype.card Agent : ℝ) := by
    have hdiv : 1 / (Fintype.card Agent : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).mpr hn
    linarith
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hfactor
  have hmul := mul_le_mul_of_nonneg_left hsuccess (sub_nonneg.mpr hc)
  nlinarith

end FiniteEvents

noncomputable def queryLower (n δ w : ℝ) : ℝ :=
  (n / w) * ((1 - δ) * (1 - 1 / n) * (1 - 1 / (2 * n * w)) - δ)

noncomputable def optimizedWindow (n : ℝ) : ℝ := 2 * (n - 1) / (n * (n - 2))

noncomputable def optimizedConstant (n : ℝ) : ℝ := n * (n - 2) ^ 2 / (12 * (n - 1))

/-- The proposed window is legal in the circular coupling for N >= 6. -/
theorem optimized_window_legal (n : ℝ) (hn : 6 ≤ n) :
    0 < optimizedWindow n ∧ optimizedWindow n ≤ 1 / 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 < n - 2 := by linarith
  constructor
  · exact div_pos (by positivity) (mul_pos hn0 hn2)
  · apply (div_le_iff₀ (mul_pos hn0 hn2)).mpr
    nlinarith [mul_nonneg (le_of_lt hn0) (show 0 ≤ n - 6 by linarith)]

theorem optimized_value (n : ℝ) (hn : 2 < n) :
    queryLower n (1 / 3) (optimizedWindow n) = optimizedConstant n := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n - 1 ≠ 0 := by linarith
  have hn2 : n - 2 ≠ 0 := by linarith
  unfold queryLower optimizedWindow optimizedConstant
  field_simp
  ring

/-- Completing the square proves optimality, rather than merely evaluating a
convenient choice of the continuous window parameter. -/
theorem optimized_square_identity (n w : ℝ) (hn : 2 < n) (hw : 0 < w) :
    optimizedConstant n - queryLower n (1 / 3) w =
      (n * (n - 2) * w - 2 * (n - 1)) ^ 2 / (12 * n * (n - 1) * w ^ 2) := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n - 1 ≠ 0 := by linarith
  unfold optimizedConstant queryLower
  field_simp
  ring

theorem optimized_dominates (n w : ℝ) (hn : 2 < n) (hw : 0 < w) :
    queryLower n (1 / 3) w ≤ optimizedConstant n := by
  apply sub_nonneg.mp
  rw [optimized_square_identity n w hn hw]
  apply div_nonneg (sq_nonneg _)
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  positivity

/-- An explicit quadratic consequence, with no asymptotic notation. -/
theorem optimized_constant_quadratic (n : ℝ) (hn : 6 ≤ n) :
    n ^ 2 / 27 ≤ optimizedConstant n := by
  have hn1 : 0 < 12 * (n - 1) := by linarith
  apply (le_div_iff₀ hn1).mpr
  have hratio : (2 / 3 : ℝ) * n ≤ n - 2 := by linarith
  have hn0 : 0 < n := by linarith
  have hsq : (4 / 9 : ℝ) * n ^ 2 ≤ (n - 2) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hn0), sq_nonneg n]

/-- The arbitrary boundary-error allowance may be taken to zero at the level
of real inequalities. Its availability for every positive allowance is a
separate continuous dominated-convergence argument. -/
theorem remove_arbitrary_boundary_loss (signal failure loss : ℝ)
    (h : ∀ η : ℝ, 0 < η → signal - loss - η ≤ failure) :
    signal - failure ≤ loss := by
  by_contra hn
  have hpos : 0 < (signal - failure - loss) / 2 := by linarith
  have hh := h ((signal - failure - loss) / 2) hpos
  linarith

/-- The last expectation/truncation contradiction is pure arithmetic; proving
the cap-return bound and the Markov premise for a given execution is external. -/
theorem uniform_expected_budget_contradiction (B H returned δ : ℝ)
    (hH : 0 < H) (hlarge : 2 * B < H)
    (hmarkov : 1 - B / H ≤ returned)
    (hobstruction : returned ≤ δ) (hδ : δ < 1 / 2) : False := by
  have hratio : B / H < 1 / 2 := (div_lt_iff₀ hH).mpr (by linarith)
  linarith

end EnvyFreeResearch.SubmissionMonteCarlo

#print axioms EnvyFreeResearch.SubmissionMonteCarlo.eventMass_nonnegative
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.failure_mass_after_two_exceptions
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.eventMass_sdiff
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.uniform_observer_exclusion
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.eligible_observer_mass_lower
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.optimized_window_legal
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.optimized_value
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.optimized_square_identity
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.optimized_dominates
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.optimized_constant_quadratic
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.remove_arbitrary_boundary_loss
#print axioms EnvyFreeResearch.SubmissionMonteCarlo.uniform_expected_budget_contradiction
