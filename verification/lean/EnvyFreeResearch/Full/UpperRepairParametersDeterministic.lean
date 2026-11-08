import EnvyFreeResearch.Full.UpperRepairParametersCounts

/-! Concrete deterministic target, supply, and spending allowances. -/
noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperRepairParameters
open UpperLogicalIsolation
variable {s ell k : ℕ} (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell)
  (hk : (2^40 : ℝ) * k ≤ s)
include hs hell hk

omit hell in
theorem square_budget : (k : ℝ)^2 ≤ multiplier s / 2 := by
  have hfour : 4 * (k : ℝ) ≤ s := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 * k) hfour 2
  unfold multiplier
  nlinarith

omit hell in
theorem ratio_square_small : populationRatio k s ^ 2 < 1 / 16 := by
  have h := pow_le_pow_left₀ (populationRatio_nonnegative (s := s) k) (populationRatio_le hs hk) 2
  exact h.trans_lt (by norm_num)

theorem batch_allowance : (k.choose 2 : ℝ) * repetitions s ell * fineCap s ell ≤ 1 / (4 * (s : ℝ)^2) := by
  have hc : (k.choose 2 : ℝ) ≤ (k : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]
  have hs0 := s_positive hs
  have hr := square_budget hs hk
  unfold multiplier at hr
  have hL := (identities hs hell).2.2.2.2.1
  rw [mul_assoc, hL]
  apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (s : ℝ)^2)).mpr
  have he : (k : ℝ)^2 * (2 / (s : ℝ)^4) * (4 * (s : ℝ)^2) = 8 * (k : ℝ)^2 / (s : ℝ)^2 := by
    field_simp [hs0.ne']
    ring
  rw [he]
  apply (div_le_one (by positivity : (0 : ℝ) < (s : ℝ)^2)).mpr
  linarith

omit hk in
theorem edge_allowance : 2 * multiplier s * fineCap s ell ≤ 1 / (4 * (s : ℝ)^2) := by
  rw [(identities hs hell).2.2.2.2.2]
  apply one_div_le_one_div_of_le (by positivity [s_positive hs])
  have hpow : (s : ℝ)^2 ≤ (s : ℝ)^7 := pow_le_pow_right₀ (s_one hs) (by norm_num)
  have hpow5 : 2 ≤ (s : ℝ)^5 := (s_two hs).trans (le_self_pow₀ (s_one hs) (by norm_num))
  have h : 2 ≤ (s : ℝ)^5 * ell := by nlinarith
  have hp := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * (s : ℝ)^2)
  nlinarith [show (s : ℝ)^2 * (s : ℝ)^5 = (s : ℝ)^7 by ring]

theorem actual_near_budget : nearBudget k (coarseCount s ell) (repetitions s ell)
    (reserveMark hs hell) (oldError s ell) ≤ 3 / (4 * (s : ℝ)^2) := by
  have hcap := actual_cellCap_le hs hell
  have hb := (mul_le_mul_of_nonneg_left hcap (by positivity : (0 : ℝ) ≤ (k.choose 2 : ℝ) * repetitions s ell)).trans
    (batch_allowance hs hell hk)
  unfold nearBudget
  change 2 * oldError s ell / reserveProbability s ell + _ ≤ _
  rw [(identities hs hell).2.2.2.1]
  calc
    _ ≤ 1 / (2 * (s : ℝ)^2) + 1 / (4 * (s : ℝ)^2) := add_le_add le_rfl hb
    _ = _ := by ring

theorem actual_target_budget : targetBudget k (coarseCount s ell) (repetitions s ell)
    (reserveMark hs hell) (oldError s ell) (multiplier s) ≤ (k : ℝ) / (s : ℝ)^2 := by
  have hn := actual_near_budget hs hell hk
  have he := (mul_le_mul_of_nonneg_left (actual_cellCap_le hs hell)
    (by positivity [multiplier_positive hs] : (0 : ℝ) ≤ 2 * multiplier s)).trans (edge_allowance hs hell)
  have hn' := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) k)
  have he' := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α := ℝ) (k - 1))
  have hk' : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hlast := mul_le_mul_of_nonneg_right hk' (by positivity [s_positive hs] : (0 : ℝ) ≤ 1 / (4 * (s : ℝ)^2))
  unfold targetBudget
  calc
    _ ≤ (k : ℝ) * (3 / (4 * (s : ℝ)^2)) + k * (1 / (4 * (s : ℝ)^2)) :=
      add_le_add hn' (he'.trans hlast)
    _ = _ := by ring

theorem target_total_small : (k : ℝ) * targetBudget k (coarseCount s ell) (repetitions s ell)
    (reserveMark hs hell) (oldError s ell) (multiplier s) < 1 / 16 := by
  have h := mul_le_mul_of_nonneg_left (actual_target_budget hs hell hk) (Nat.cast_nonneg (α := ℝ) k)
  have he : (k : ℝ) * ((k : ℝ) / (s : ℝ)^2) = populationRatio k s ^ 2 := by
    unfold populationRatio
    field_simp
  rw [he] at h
  exact h.trans_lt (ratio_square_small hs hk)

theorem payment_extra_small : (k : ℝ) * multiplier s * fineCap s ell < 1 / 16 := by
  have he : (k : ℝ) * multiplier s * fineCap s ell = populationRatio k s / (4 * (s : ℝ)^6 * ell) := by
    unfold multiplier fineCap populationRatio
    field_simp [(s_positive hs).ne', (ell_positive hell).ne']
    ring
  rw [he]
  have hd : (1 : ℝ) ≤ 4 * (s : ℝ)^6 * ell := by
    have h := denominator_ge_one hs hell 6 1
    simp only [pow_one] at h
    nlinarith
  exact (div_le_self (populationRatio_nonnegative k) hd).trans_lt
    ((populationRatio_le hs hk).trans_lt (by norm_num))

theorem correction_spending_small :
    (k : ℝ) * targetBudget k (coarseCount s ell) (repetitions s ell)
      (reserveMark hs hell) (oldError s ell) (multiplier s) +
      k * multiplier s * fineCap s ell < 1 / 8 := by
  linarith [target_total_small hs hell hk, payment_extra_small hs hell hk]

omit hk in
theorem interpolation_allowance : interpolationBudget s ell * retainedCap s ell ≤ multiplier s / 4 :=
  (identities hs hell).2.2.1.le

end EnvyFreeResearch.Full.UpperRepairParameters
