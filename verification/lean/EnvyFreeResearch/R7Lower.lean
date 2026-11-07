import EnvyFreeResearch.R6Lower

/-!
# Round 7 finite robust-allocation certificates and counting

The dual inequalities are checked against actual nonnegative cell masses and
actual ownership comparisons. Strong LP duality, interval completion, oracle
replay, and probability over arbitrary tapes are not assumed or formalized.
-/

namespace EnvyFreeResearch.R7Lower

open scoped BigOperators

section RobustCertificate

variable {Cell EqRow LeRow Agent : Type*}

theorem robust_linear_certificate [Fintype Cell] [Fintype EqRow] [Fintype LeRow]
    (A : EqRow → Cell → ℝ) (H : LeRow → Cell → ℝ)
    (b : EqRow → ℝ) (d : LeRow → ℝ) (z comparison : Cell → ℝ)
    (y : EqRow → ℝ) (γ : LeRow → ℝ)
    (hz : ∀ c, 0 ≤ z c) (hγ : ∀ r, 0 ≤ γ r)
    (hequalities : ∀ r, ∑ c, A r c * z c = b r)
    (hinequalities : ∀ r, ∑ c, H r c * z c ≤ d r)
    (hdual : ∀ c, comparison c ≤ (∑ r, A r c * y r) + ∑ r, H r c * γ r)
    (hbudget : (∑ r, b r * y r) + ∑ r, d r * γ r ≤ 0) :
    (∑ c, comparison c * z c) ≤ 0 := by
  have hpoint : (∑ c, comparison c * z c) ≤
      ∑ c, ((∑ r, A r c * y r) + ∑ r, H r c * γ r) * z c := by
    apply Finset.sum_le_sum
    intro c _
    exact mul_le_mul_of_nonneg_right (hdual c) (hz c)
  have heqpart : (∑ c, (∑ r, A r c * y r) * z c) = ∑ r, b r * y r := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    calc
      (∑ c, A r c * y r * z c) = (∑ c, A r c * z c) * y r := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = b r * y r := by rw [hequalities r]
  have hlepart : (∑ c, (∑ r, H r c * γ r) * z c) ≤ ∑ r, d r * γ r := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro r _
    calc
      (∑ c, H r c * γ r * z c) = (∑ c, H r c * z c) * γ r := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ ≤ d r * γ r := mul_le_mul_of_nonneg_right (hinequalities r) (hγ r)
  simp_rw [add_mul, Finset.sum_add_distrib] at hpoint
  rw [heqpart] at hpoint
  linarith

theorem robust_equality_certificate [Fintype Cell] [Fintype EqRow]
    (A : EqRow → Cell → ℝ) (b : EqRow → ℝ) (z comparison : Cell → ℝ)
    (y : EqRow → ℝ) (hz : ∀ c, 0 ≤ z c)
    (hequalities : ∀ r, ∑ c, A r c * z c = b r)
    (hdual : ∀ c, comparison c ≤ ∑ r, A r c * y r)
    (hbudget : (∑ r, b r * y r) ≤ 0) :
    (∑ c, comparison c * z c) ≤ 0 := by
  exact robust_linear_certificate A (fun _ : Fin 0 => 0) b (fun _ : Fin 0 => 0) z comparison y
    (fun _ : Fin 0 => 0) hz (by simp) hequalities (by simp)
    (by simpa using hdual) (by simpa using hbudget)

def allocatedValue [Fintype Cell] [DecidableEq Agent]
    (z : Cell → ℝ) (owner : Cell → Agent) (recipient : Agent) : ℝ :=
  ∑ c, if owner c = recipient then z c else 0

def ownershipComparison [DecidableEq Agent] (owner : Cell → Agent) (own other : Agent)
    (c : Cell) : ℝ :=
  (if owner c = other then 1 else 0) - (if owner c = own then 1 else 0)

theorem ownership_comparison_sum [Fintype Cell] [DecidableEq Agent]
    (z : Cell → ℝ) (owner : Cell → Agent) (own other : Agent) :
    (∑ c, ownershipComparison owner own other c * z c) =
      allocatedValue z owner other - allocatedValue z owner own := by
  rw [allocatedValue, allocatedValue, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  unfold ownershipComparison
  split_ifs <;> ring

/-- The generic dual certifies an actual pair of recipient bundles, including
disconnected or empty bundles and inequality-recorded failed-query data. -/
theorem dual_certifies_actual_comparison [Fintype Cell] [Fintype EqRow] [Fintype LeRow]
    [DecidableEq Agent] (A : EqRow → Cell → ℝ) (H : LeRow → Cell → ℝ)
    (b : EqRow → ℝ) (d : LeRow → ℝ) (z : Cell → ℝ) (owner : Cell → Agent)
    (own other : Agent) (y : EqRow → ℝ) (γ : LeRow → ℝ)
    (hz : ∀ c, 0 ≤ z c) (hγ : ∀ r, 0 ≤ γ r)
    (hequalities : ∀ r, ∑ c, A r c * z c = b r)
    (hinequalities : ∀ r, ∑ c, H r c * z c ≤ d r)
    (hdual : ∀ c, ownershipComparison owner own other c ≤
      (∑ r, A r c * y r) + ∑ r, H r c * γ r)
    (hbudget : (∑ r, b r * y r) + ∑ r, d r * γ r ≤ 0) :
    allocatedValue z owner other ≤ allocatedValue z owner own := by
  have h := robust_linear_certificate A H b d z (ownershipComparison owner own other)
    y γ hz hγ hequalities hinequalities hdual hbudget
  rw [ownership_comparison_sum] at h
  linarith

end RobustCertificate

section EfficiencyCounting

variable {Candidate Outcome : Type*} [DecidableEq Candidate]

/-- One unchanged output succeeds on at most one unhit candidate. The finite
bound uses real candidate sets and permits their overlap. -/
theorem success_count_bound (candidates success hit unchanged : Finset Candidate)
    (q : ℕ) (hcomplete : success ⊆ candidates) (hcover : success ⊆ hit ∪ unchanged)
    (hhit : hit.card ≤ 4 * q) (hunchanged : unchanged.card ≤ 1) :
    success.card ≤ min candidates.card (4 * q + 1) := by
  apply le_min (Finset.card_le_card hcomplete)
  have hsub := Finset.card_le_card hcover
  have hunion := Finset.card_union_le hit unchanged
  omega

omit [DecidableEq Candidate] in
/-- Summing the actual candidate count against finite nonnegative weights
gives the average cost bound. Normalization is a caller's separate premise. -/
theorem weighted_success_fraction_bound [Fintype Outcome]
    (weight : Outcome → ℝ) (queries : Outcome → ℕ)
    (success : Outcome → Finset Candidate) (N : ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω) (hN : 0 < N)
    (hcount : ∀ ω, (success ω).card ≤ 4 * queries ω + 1) :
    (∑ ω, weight ω * ((success ω).card : ℝ)) / N ≤
      (4 * (∑ ω, weight ω * (queries ω : ℝ)) + ∑ ω, weight ω) / N := by
  apply div_le_div_of_nonneg_right _ (le_of_lt hN)
  calc
    (∑ ω, weight ω * ((success ω).card : ℝ)) ≤
        ∑ ω, weight ω * (4 * (queries ω : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (hweight ω)
      exact_mod_cast hcount ω
    _ = 4 * (∑ ω, weight ω * (queries ω : ℝ)) + ∑ ω, weight ω := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      ring

omit [DecidableEq Candidate] in
/-- The clipped finite bound is suitable for a later dominated-convergence
argument, but this statement does not formalize an arbitrary tape law. -/
theorem weighted_clipped_success_fraction [Fintype Outcome]
    (weight : Outcome → ℝ) (queries : Outcome → ℕ)
    (success : Outcome → Finset Candidate) (N : ℕ) (hN : 0 < N)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hcount : ∀ ω, (success ω).card ≤ min N (4 * queries ω + 1)) :
    (∑ ω, weight ω * ((success ω).card : ℝ)) / (N : ℝ) ≤
      ∑ ω, weight ω * min 1 ((4 * (queries ω : ℝ) + 1) / (N : ℝ)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ω _
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (hweight ω)
  apply le_min
  · apply (div_le_one hNreal).mpr
    exact_mod_cast (hcount ω).trans (min_le_left _ _)
  · apply div_le_div_of_nonneg_right _ (le_of_lt hNreal)
    exact_mod_cast (hcount ω).trans (min_le_right _ _)

theorem two_disjoint_successes_half (p r : ℝ) (hfirst : p ≤ r) (hsecond : p ≤ 1 - r) :
    p ≤ 1 / 2 := by linarith

end EfficiencyCounting

end EnvyFreeResearch.R7Lower

#print axioms EnvyFreeResearch.R7Lower.robust_linear_certificate
#print axioms EnvyFreeResearch.R7Lower.robust_equality_certificate
#print axioms EnvyFreeResearch.R7Lower.ownership_comparison_sum
#print axioms EnvyFreeResearch.R7Lower.dual_certifies_actual_comparison
#print axioms EnvyFreeResearch.R7Lower.success_count_bound
#print axioms EnvyFreeResearch.R7Lower.weighted_success_fraction_bound
#print axioms EnvyFreeResearch.R7Lower.weighted_clipped_success_fraction
#print axioms EnvyFreeResearch.R7Lower.two_disjoint_successes_half
