import EnvyFreeResearch.Full.UpperRepairParametersScale

/-! The actual original-population scale and integer logarithm. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperRepairParameters

theorem scale_large (n : ℕ) : (2^42 : ℝ) ≤ scale n := by
  have h := le_max_left 4 n
  have hc : (4 : ℝ) ≤ max 4 n := by exact_mod_cast h
  simp only [scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  norm_num
  simp only [Nat.cast_max, Nat.cast_ofNat] at hc
  nlinarith

theorem active_scale (n k : ℕ) (hk : k ≤ n) : (2^40 : ℝ) * k ≤ scale n := by
  have hc : (k : ℝ) ≤ max 4 n := by exact_mod_cast hk.trans (le_max_right 4 n)
  simp only [scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left hc (by norm_num)

theorem logarithm_positive {s : ℕ} (hs : (2^42 : ℝ) ≤ s) : 1 ≤ logarithm s := by
  apply Nat.succ_le_of_lt
  apply Nat.ceil_pos.mpr
  apply div_pos
  · apply Real.log_pos
    linarith [s_two hs]
  · exact Real.log_pos (by norm_num)

theorem logarithm_dominates_log {s k : ℕ} (hs : (2^42 : ℝ) ≤ s)
    (hkpos : 0 < k) (hk : (2^40 : ℝ) * k ≤ s) : Real.log (2 * (k : ℝ)) ≤ logarithm s := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hks : (k : ℝ) ≤ s := by nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2one : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hn : 0 ≤ Real.log (2 * (s : ℝ)) := Real.log_nonneg (by linarith [s_two hs])
  calc
    _ ≤ Real.log (2 * (s : ℝ)) := Real.log_le_log (by positivity) (by linarith)
    _ ≤ Real.log (2 * (s : ℝ)) / Real.log 2 := le_div_self hn hlog2 hlog2one
    _ ≤ logarithm s := Nat.le_ceil _

theorem two_mul_le_two_pow (s : ℕ) (hs : 1 ≤ s) : 2 * s ≤ 2^s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    nlinarith

theorem logarithm_le_scale {s : ℕ} (hs : (2^42 : ℝ) ≤ s) : logarithm s ≤ s := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  have hsp : 1 ≤ s := by exact_mod_cast s_one hs
  have hp : 2 * (s : ℝ) ≤ (2 : ℝ)^s := by exact_mod_cast two_mul_le_two_pow s hsp
  have h := Real.log_le_log (by positivity [s_positive hs]) hp
  simpa only [Real.log_pow] using h

/-- An explicit logarithmic upper bound for the actual integer logarithm;
the additive constant comes from the fixed factor in the manuscript scale. -/
theorem logarithm_bound (n : ℕ) (hn : 1 ≤ n) :
    (logarithm (scale n) : ℝ) ≤ 44 + Real.log (2 * (n : ℝ)) / Real.log 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : (max 4 n : ℝ) ≤ 4 * n := by
    apply max_le
    · nlinarith [(show (1 : ℝ) ≤ n by exact_mod_cast hn)]
    · nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := scale_large n
  have harg : 0 ≤ Real.log (2 * (scale n : ℝ)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith [s_two hs])) hlog2.le
  have hceil := Nat.ceil_lt_add_one harg
  have hlarge : 2 * (scale n : ℝ) ≤ (2 : ℝ)^42 * (2 * n) := by
    simp only [scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_max]
    norm_num
    nlinarith
  have hlog := Real.log_le_log (by positivity [s_positive hs]) hlarge
  rw [Real.log_mul (by positivity : (2 : ℝ)^42 ≠ 0) (by positivity : (2 * (n : ℝ)) ≠ 0), Real.log_pow] at hlog
  have hdivide := (div_le_div_iff_of_pos_right hlog2).mpr hlog
  have heq : (42 * Real.log 2 + Real.log (2 * (n : ℝ))) / Real.log 2 =
      42 + Real.log (2 * (n : ℝ)) / Real.log 2 := by field_simp
  norm_num only [Nat.cast_ofNat] at hdivide
  rw [heq] at hdivide
  change (logarithm (scale n) : ℝ) < _ at hceil
  linarith

theorem scale_linear (n : ℕ) (hn : 1 ≤ n) : (scale n : ℝ) ≤ 2^42 * n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : max (4 : ℝ) n ≤ 4 * n := max_le (by linarith) (by linarith)
  simp only [scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_max]
  nlinarith

/-- A multiplicative logarithmic bound, with an absolute explicit constant. -/
theorem logarithm_linear_log (n : ℕ) (hn : 1 ≤ n) :
    (logarithm (scale n) : ℝ) ≤ 45 * (Real.log (2 * (n : ℝ)) / Real.log 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ 2 * n by linarith)
  have hone : (1 : ℝ) ≤ Real.log (2 * (n : ℝ)) / Real.log 2 := (le_div_iff₀ hp).mpr (by simpa using hl)
  linarith [logarithm_bound n hn]

/-- The exact sample count has the advertised polynomial-logarithmic scale. -/
theorem samples_polynomial (n : ℕ) (hn : 1 ≤ n) :
    (samples (scale n) (logarithm (scale n)) : ℝ) ≤
      ((2^42 : ℝ)^18 * 45^2) * (n : ℝ)^18 * (Real.log (2 * (n : ℝ)) / Real.log 2)^2 := by
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (scale n)) (scale_linear n hn) 18
  have he := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (logarithm (scale n))) (logarithm_linear_log n hn) 2
  rw [samples_cast]
  calc
    _ ≤ ((2^42 : ℝ) * n)^18 * (45 * (Real.log (2 * (n : ℝ)) / Real.log 2))^2 :=
      mul_le_mul hs he (by positivity) (by positivity)
    _ = _ := by ring

end EnvyFreeResearch.Full.UpperRepairParameters
