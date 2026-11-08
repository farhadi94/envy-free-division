import EnvyFreeResearch.Full.UpperRepairParametersDeterministic

/-! Exact grouped rejection budgets for the original randomized trial. -/
noncomputable section
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperRepairParameters
open UpperLogicalIsolation UpperRepairJobs

def massFailure (k s ell : ℕ) : ℝ := 4 * k / (reserveProbability s ell * ((coarseCount s ell : ℝ) + 1))
def countFailure (s ell : ℕ) : ℝ := 2 * reserveProbability s ell * samples s ell / retainedCap s ell
def parentFailure (k s ell : ℕ) : ℝ := 2 * ((jobCount k : ℝ) * repetitions s ell) * reserveProbability s ell
def cycleFailure (k s ell : ℕ) : ℝ := isolationBound k (repetitions s ell) (multiplier s)
def estimateFailure (k s ell : ℕ) : ℝ := 8 * k * fineCap s ell * retainedCap s ell / multiplier s
def interpolationFailure (k s ell : ℕ) : ℝ :=
  16 * k * (k - 1 : ℝ) * (1 + interpolationBudget s ell) /
    (reserveProbability s ell * interpolationBudget s ell * ((samples s ell : ℝ) + 1))
def totalFailure (k s ell : ℕ) : ℝ := massFailure k s ell + countFailure s ell + parentFailure k s ell +
  cycleFailure k s ell + (interpolationFailure k s ell + estimateFailure k s ell)

variable {s ell k : ℕ} (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell)
  (hk : (2^40 : ℝ) * k ≤ s) (hkpos : 2 ≤ k) (hlog : Real.log (2 * (k : ℝ)) ≤ ell)
include hs hell

theorem massFailure_le : massFailure k s ell ≤ 4 * populationRatio k s := by
  unfold massFailure
  calc
    _ ≤ 4 * k / (reserveProbability s ell * coarseCount s ell) :=
      div_le_div_of_nonneg_left (by positivity)
        (mul_pos (reserve_positive hs hell) (coarse_positive hs hell))
        (mul_le_mul_of_nonneg_left (by linarith) (reserve_positive hs hell).le)
    _ = 4 * populationRatio k s / ((s : ℝ)^8 * ell) := by
      rw [reserveProbability, coarseCount_cast, populationRatio]
      field_simp [(s_positive hs).ne', (ell_positive hell).ne']
    _ ≤ 4 * populationRatio k s := div_le_self (by positivity [populationRatio_nonnegative (s := s) k])
      (by simpa only [pow_one] using denominator_ge_one hs hell 8 1)

theorem countFailure_exact : countFailure s ell = 1 / 512 := by
  unfold countFailure reserveProbability retainedCap
  rw [samples_cast]
  field_simp [(s_positive hs).ne', (ell_positive hell).ne']
  ring

theorem parentFailure_le : parentFailure k s ell ≤ populationRatio k s ^ 3 := by
  have he : parentFailure k s ell = (k : ℝ)^2 * (k - 1) / (s : ℝ)^3 := by
    unfold parentFailure reserveProbability jobCount
    rw [repetitions_cast, Nat.cast_mul, Nat.cast_choose_two]
    field_simp [(s_positive hs).ne', (ell_positive hell).ne']
  rw [he, populationRatio, div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg (k : ℝ)]

include hkpos hlog in
theorem cycleFailure_le : cycleFailure k s ell ≤ (3 / 2 : ℝ) * populationRatio k s ^ 3 +
    (k : ℝ)^3 / ((s : ℝ)^5 * ell) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hfactor : 0 ≤ 12 * multiplier s * Real.log (2 * (k : ℝ)) + 1 := by
    have hl : 0 ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
    positivity [multiplier_positive hs]
  have hnum : (k : ℝ)^2 * (k - 1) * (12 * multiplier s * Real.log (2 * (k : ℝ)) + 1) ≤
      (k : ℝ)^3 * (12 * multiplier s * ell + 1) := by
    apply mul_le_mul
    · nlinarith [sq_nonneg (k : ℝ)]
    · nlinarith [multiplier_positive hs]
    · exact hfactor
    · positivity
  unfold cycleFailure isolationBound
  calc
    _ ≤ (k : ℝ)^3 * (12 * multiplier s * ell + 1) / repetitions s ell :=
      div_le_div₀ (by positivity [multiplier_positive hs]) hnum (repetitions_positive hs hell) (by norm_cast; omega)
    _ = _ := by
      rw [repetitions_cast, multiplier, populationRatio]
      field_simp [(s_positive hs).ne', (ell_positive hell).ne']
      ring

include hkpos hlog in
theorem cycleFailure_le_ratio : cycleFailure k s ell ≤ (5 / 2 : ℝ) * populationRatio k s ^ 3 := by
  have he : (k : ℝ)^3 / ((s : ℝ)^5 * ell) = populationRatio k s ^ 3 / ((s : ℝ)^2 * ell) := by
    unfold populationRatio
    field_simp [(s_positive hs).ne', (ell_positive hell).ne']
  have hrem : (k : ℝ)^3 / ((s : ℝ)^5 * ell) ≤ populationRatio k s ^ 3 := by
    rw [he]
    exact div_le_self (by positivity [populationRatio_nonnegative (s := s) k])
      (by simpa only [pow_one] using denominator_ge_one hs hell 2 1)
  linarith [cycleFailure_le hs hell hkpos hlog]

theorem estimateFailure_exact : estimateFailure k s ell = 2^17 * populationRatio k s := by
  unfold estimateFailure fineCap retainedCap multiplier populationRatio
  field_simp [(s_positive hs).ne', (ell_positive hell).ne']
  ring

include hkpos in
theorem interpolationFailure_le : interpolationFailure k s ell ≤ 2^20 * populationRatio k s ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hn : 16 * (k : ℝ) * (k - 1) * (1 + interpolationBudget s ell) ≤ 32 * (k : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left (interpolation_le_one hs hell)
      (show 0 ≤ 16 * (k : ℝ) * (k - 1) by positivity)
    nlinarith
  unfold interpolationFailure
  calc
    _ ≤ 32 * (k : ℝ)^2 / (reserveProbability s ell * interpolationBudget s ell * samples s ell) :=
      div_le_div₀ (by positivity) hn
        (by positivity [reserve_positive hs hell, interpolation_positive hs hell, samples_positive hs hell])
        (by nlinarith [reserve_positive hs hell, interpolation_positive hs hell])
    _ = _ := by
      rw [(identities hs hell).2.1, populationRatio]
      field_simp
      ring

include hk hkpos hlog in
theorem grouped_failure_bounds :
    massFailure k s ell < 1 / 512 ∧ countFailure s ell = 1 / 512 ∧
    parentFailure k s ell < 1 / 512 ∧ cycleFailure k s ell < 1 / 512 ∧
    interpolationFailure k s ell + estimateFailure k s ell < 1 / 512 := by
  have hratio := populationRatio_le hs hk
  have hsq := pow_le_pow_left₀ (populationRatio_nonnegative (s := s) k) hratio 2
  have hcube := pow_le_pow_left₀ (populationRatio_nonnegative (s := s) k) hratio 3
  refine ⟨?_, countFailure_exact hs hell, ?_, ?_, ?_⟩
  · exact (massFailure_le hs hell).trans_lt
      ((mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4)).trans_lt (by norm_num))
  · exact (parentFailure_le hs hell).trans_lt (hcube.trans_lt (by norm_num))
  · exact (cycleFailure_le_ratio hs hell hkpos hlog).trans_lt
      ((mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 5 / 2)).trans_lt (by norm_num))
  · rw [estimateFailure_exact hs hell]
    have hi := interpolationFailure_le hs hell hkpos
    have h1 := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2^20)
    have h2 := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2^17)
    linarith

include hk hkpos hlog in
theorem totalFailure_small : totalFailure k s ell < 1 / 64 := by
  obtain ⟨hm, hc, hp, hi, hpay⟩ := grouped_failure_bounds hs hell hk hkpos hlog
  unfold totalFailure
  linarith

include hkpos in
theorem rejection_nonnegative :
    0 ≤ massFailure k s ell ∧ 0 ≤ countFailure s ell ∧ 0 ≤ parentFailure k s ell ∧
    0 ≤ cycleFailure k s ell ∧ 0 ≤ interpolationFailure k s ell ∧ 0 ≤ estimateFailure k s ell := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkm : (0 : ℝ) ≤ (k : ℝ) - 1 := sub_nonneg.mpr hk1
  have hlog : 0 ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  unfold massFailure countFailure parentFailure cycleFailure isolationBound interpolationFailure estimateFailure
  exact ⟨by positivity [reserve_positive hs hell],
    by positivity [reserve_positive hs hell, retainedCap_positive hs hell],
    by positivity [reserve_positive hs hell],
    by positivity [multiplier_positive hs],
    by positivity [reserve_positive hs hell, interpolation_positive hs hell],
    by positivity [fineCap_positive hs hell, retainedCap_positive hs hell, multiplier_positive hs]⟩

include hk hkpos hlog in
/-- This is the exact three-term ENNReal union-bound expression supplied by
the actual preparation guard, isolation, and correction theorems. -/
theorem original_failure_sum_small :
    ENNReal.ofReal (UpperLogicalPreparationGuard.failureBudget (Agent := Fin k)
      (coarseCount s ell) (samples s ell) (jobCount k * repetitions s ell)
      (reserveMark hs hell) (retainedCap s ell)) +
    ENNReal.ofReal (isolationBound k (repetitions s ell) (multiplier s)) +
    ENNReal.ofReal (8 * k * fineCap s ell * retainedCap s ell / multiplier s +
      16 * k * (k - 1 : ℝ) * (1 + interpolationBudget s ell) /
        (reserveProbability s ell * interpolationBudget s ell * ((samples s ell : ℝ) + 1))) < 1 / 64 := by
  have he : UpperLogicalPreparationGuard.failureBudget (Agent := Fin k)
      (coarseCount s ell) (samples s ell) (jobCount k * repetitions s ell)
      (reserveMark hs hell) (retainedCap s ell) =
        massFailure k s ell + countFailure s ell + parentFailure k s ell := by
    simp only [UpperLogicalPreparationGuard.failureBudget, massFailure, countFailure, parentFailure,
      Fintype.card_fin, reserveMark, Nat.cast_mul]
  obtain ⟨hm, hc, hp, hcy, hi, he'⟩ := rejection_nonnegative hs hell hkpos
  rw [he]
  change ENNReal.ofReal (massFailure k s ell + countFailure s ell + parentFailure k s ell) +
    ENNReal.ofReal (cycleFailure k s ell) + ENNReal.ofReal (estimateFailure k s ell + interpolationFailure k s ell) < _
  rw [← ENNReal.ofReal_add (add_nonneg (add_nonneg hm hc) hp) hcy,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg hm hc) hp) hcy) (add_nonneg he' hi)]
  have htotal := totalFailure_small hs hell hk hkpos hlog
  have hreal : massFailure k s ell + countFailure s ell + parentFailure k s ell + cycleFailure k s ell +
      (estimateFailure k s ell + interpolationFailure k s ell) < 1 / 64 := by
    simpa only [totalFailure, add_comm (estimateFailure k s ell) (interpolationFailure k s ell)] using htotal
  have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 64)).mpr hreal
  have h64 : ENNReal.ofReal (1 / 64 : ℝ) = (1 / 64 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [h64] at h
  exact h

end EnvyFreeResearch.Full.UpperRepairParameters
