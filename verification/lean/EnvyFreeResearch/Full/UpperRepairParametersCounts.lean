import EnvyFreeResearch.Full.UpperRepairParametersScale

/-! Integer coarse/sample/representative budgets at the exact scales. -/
noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperRepairParameters
open UpperRepairJobs UpperLogicalIsolation
variable {s ell k : ℕ} (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell)
include hs hell

theorem coarse_positive : (0 : ℝ) < coarseCount s ell := by
  rw [coarseCount_cast]
  positivity [s_positive hs, ell_positive hell]

theorem samples_positive : (0 : ℝ) < samples s ell := by
  rw [samples_cast]
  positivity [s_positive hs, ell_positive hell]

theorem repetitions_positive : (0 : ℝ) < repetitions s ell := by
  rw [repetitions_cast]
  positivity [s_positive hs, ell_positive hell]

theorem coarse_one : 1 ≤ coarseCount s ell := by
  have h := coarse_positive hs hell
  exact_mod_cast h

omit hs hell in
theorem samples_eq_scale_coarse : samples s ell = s * coarseCount s ell := by
  simp only [samples, coarseCount]
  ring

theorem coarse_denominator_bound : 1 / ((coarseCount s ell : ℝ) + 1) ≤ coarseCap s ell := by
  unfold coarseCap
  rw [← coarseCount_cast]
  exact one_div_le_one_div_of_le (coarse_positive hs hell) (by linarith)

theorem actual_cellCap_le : cellCap (coarseCount s ell) (reserveMark hs hell) ≤ fineCap s ell := by
  have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (mul_pos (reserve_positive hs hell) (coarse_positive hs hell))
    (mul_le_mul_of_nonneg_left (show (coarseCount s ell : ℝ) ≤ (coarseCount s ell : ℝ) + 1 by linarith)
      (reserve_positive hs hell).le)
  change 2 / (reserveProbability s ell * ((coarseCount s ell : ℝ) + 1)) ≤ _
  apply h.trans_eq
  rw [reserveProbability, coarseCount_cast, fineCap]
  field_simp [(s_positive hs).ne', (ell_positive hell).ne']

theorem seed_fraction_le_ratio :
    (jobCount k : ℝ) * repetitions s ell / ((coarseCount s ell : ℝ) + 1) ≤ populationRatio k s ^ 3 := by
  have hnum : (jobCount k : ℝ) * repetitions s ell ≤ (k : ℝ)^3 * repetitions s ell :=
    mul_le_mul_of_nonneg_right (jobCount_le_cube k) (repetitions_positive hs hell).le
  calc
    _ ≤ (k : ℝ)^3 * repetitions s ell / (coarseCount s ell : ℝ) :=
      div_le_div₀ (by positivity) hnum (coarse_positive hs hell) (by linarith)
    _ = populationRatio k s ^ 3 / ((s : ℝ)^9 * ell) := by
      rw [repetitions_cast, coarseCount_cast, populationRatio]
      field_simp [(s_positive hs).ne', (ell_positive hell).ne']
    _ ≤ populationRatio k s ^ 3 := by
      exact div_le_self (by positivity [populationRatio_nonnegative (s := s) k])
        (by simpa only [pow_one] using denominator_ge_one hs hell 9 1)

theorem seed_fraction_small (hk : (2^40 : ℝ) * k ≤ s) :
    (jobCount k : ℝ) * repetitions s ell / ((coarseCount s ell : ℝ) + 1) < 1 / 8 := by
  have h := pow_le_pow_left₀ (populationRatio_nonnegative (s := s) k) (populationRatio_le hs hk) 3
  exact (seed_fraction_le_ratio hs hell).trans_lt (h.trans_lt (by norm_num))

theorem representatives_fit (hk : (2^40 : ℝ) * k ≤ s) :
    2 * (jobCount k * repetitions s ell) < coarseCount s ell + 1 := by
  have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < (coarseCount s ell : ℝ) + 1)).mp (seed_fraction_small hs hell hk)
  have hc := coarse_positive hs hell
  have hr : 2 * ((jobCount k : ℝ) * repetitions s ell) < (coarseCount s ell : ℝ) + 1 := by linarith
  exact_mod_cast hr

theorem grid_fits (hk : (2^40 : ℝ) * k ≤ s) (hkpos : 0 < k) :
    k * coarseCount s ell + 1 ≤ samples s ell ∧ 2 * k ≤ samples s ell := by
  have htworeal : 2 * (k : ℝ) ≤ s := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have htwo : 2 * k ≤ s := by exact_mod_cast htworeal
  have hks : k + 1 ≤ s := by omega
  have hq := coarse_one hs hell
  rw [samples_eq_scale_coarse]
  constructor <;> nlinarith

end EnvyFreeResearch.Full.UpperRepairParameters
