import EnvyFreeResearch.Full.RefinedUpperParameterCounts

/-! Numerical allowances for the revised rejection analysis. These lemmas
are used only after the physical probability bounds have been established. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperRejectionParameters
open RefinedUpperParameterCounts

theorem envelope_allowance {s ell : ℕ} (hs : 0 < s) (he : 0 < ell) (hd : 128 ∣ s) :
    8 * fineCap s ell * (2 * (samples s ell : ℝ)) / (s : ℝ) = 1 / 4 := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have he0 : (ell : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt he
  rw [samples_cast hd]
  unfold fineCap
  field_simp
  <;> ring

theorem endpoint_allowance {k : ℝ} (hk : 0 < k) :
    (32 * k / 7) * (1 / (32768 * k^2)) = 1 / (7168 * k) := by
  field_simp
  <;> ring

theorem first_bad_allowance {k : ℝ} (hk : 0 < k) :
    k * ((4 / 3 : ℝ) * (1 / (7168 * k))) = 1 / 5376 := by
  field_simp
  <;> ring

theorem first_bad_fixed_point (a : ℝ) : a + ((4 / 3 : ℝ) * a) * (1 / 4) = (4 / 3 : ℝ) * a := by ring

theorem four_failures_small {x y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 256)
    (hy : y ≤ 1 / 1024) :
    2^23 * x^5 + 13 * x^3 + (1 / 5376 : ℝ) + y < 1 / 64 := by
  have h5 := pow_le_pow_left₀ hx0 hx 5
  have h3 := pow_le_pow_left₀ hx0 hx 3
  norm_num at h5 h3
  nlinarith

/-- The geometric failure allowance with continuation probability 1/4. -/
theorem exhaustion_allowance {s : ℝ} (hs : 0 < s) (ell : ℕ)
    (hlog : 2*s ≤ (2 : ℝ)^ell) :
    (1/4 : ℝ)^ell ≤ 1 / (4*s^2) := by
  have hpow : 4*s^2 ≤ (4 : ℝ)^ell := by
    have heq : ((2 : ℝ)^ell)^2 = (4 : ℝ)^ell := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    nlinarith [sq_nonneg ((2 : ℝ)^ell - 2*s)]
  rw [div_pow, one_pow]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow

end EnvyFreeResearch.Full.RefinedUpperRejectionParameters
