import EnvyFreeResearch.Full.UpperRepairParametersProbability
import EnvyFreeResearch.Full.UpperRepairParametersPopulation

/-! Exact manuscript constants instantiate every numerical Repair guard and
success allowance, uniformly as the active population decreases. -/
noncomputable section
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperRepairParameters
open UpperRepairJobs UpperLogicalIsolation

structure ArithmeticFacts (k s ell : ℕ) : Prop where
  scale_large : (2^42 : ℝ) ≤ s
  logarithm_positive : (1 : ℝ) ≤ ell
  representative_budget : 2 * (jobCount k * repetitions s ell) < coarseCount s ell + 1
  logical_grid_budget : k * coarseCount s ell + 1 ≤ samples s ell
  correction_cut_budget : 2 * k ≤ samples s ell
  normalized_cell_cap : cellCap (coarseCount s ell) (reserveMark scale_large logarithm_positive) ≤ fineCap s ell
  total_target_budget : (k : ℝ) * targetBudget k (coarseCount s ell) (repetitions s ell)
    (reserveMark scale_large logarithm_positive) (oldError s ell) (multiplier s) < 1 / 16
  correction_extra : (k : ℝ) * multiplier s * fineCap s ell < 1 / 16
  correction_spending : (k : ℝ) * targetBudget k (coarseCount s ell) (repetitions s ell)
    (reserveMark scale_large logarithm_positive) (oldError s ell) (multiplier s) +
      k * multiplier s * fineCap s ell < 1 / 8
  seed_spending : (jobCount k : ℝ) * repetitions s ell / ((coarseCount s ell : ℝ) + 1) < 1 / 8
  rounding_margin : (k : ℝ)^2 ≤ multiplier s / 2
  interpolation_margin : interpolationBudget s ell * retainedCap s ell ≤ multiplier s / 4
  rejection_budget : totalFailure k s ell < 1 / 64

theorem arithmetic_facts {k s ell : ℕ} (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell)
    (hk : (2^40 : ℝ) * k ≤ s) (hkpos : 2 ≤ k) (hlog : Real.log (2 * (k : ℝ)) ≤ ell) :
    ArithmeticFacts k s ell where
  scale_large := hs
  logarithm_positive := hell
  representative_budget := representatives_fit hs hell hk
  logical_grid_budget := (grid_fits hs hell hk (by omega)).1
  correction_cut_budget := (grid_fits hs hell hk (by omega)).2
  normalized_cell_cap := actual_cellCap_le hs hell
  total_target_budget := target_total_small hs hell hk
  correction_extra := payment_extra_small hs hell hk
  correction_spending := correction_spending_small hs hell hk
  seed_spending := seed_fraction_small hs hell hk
  rounding_margin := square_budget hs hk
  interpolation_margin := interpolation_allowance hs hell
  rejection_budget := totalFailure_small hs hell hk hkpos hlog

/-- The actual scales depend only on the original population and remain
valid for every later active population between two and the original size. -/
theorem original_population_facts (n k : ℕ) (hkpos : 2 ≤ k) (hk : k ≤ n) :
    ArithmeticFacts k (scale n) (logarithm (scale n)) := by
  apply arithmetic_facts (scale_large n)
  · exact_mod_cast logarithm_positive (scale_large n)
  · exact active_scale n k hk
  · exact hkpos
  · exact logarithm_dominates_log (scale_large n) (by omega) (active_scale n k hk)

theorem original_population_failure (n k : ℕ) (hkpos : 2 ≤ k) (hk : k ≤ n) :
    ENNReal.ofReal (totalFailure k (scale n) (logarithm (scale n))) < 1 / 64 := by
  have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 64)).mpr
    (original_population_facts n k hkpos hk).rejection_budget
  have h64 : ENNReal.ofReal (1 / 64 : ℝ) = (1 / 64 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [h64] at h
  exact h

end EnvyFreeResearch.Full.UpperRepairParameters
