import EnvyFreeResearch.Full.UpperShrinkRepair

noncomputable section
namespace EnvyFreeResearch.Full.UpperShrink
open UpperRepairParameters

theorem nearError_positive (n : ℕ) : 0 < UpperRepair.nearError n :=
  oldError_positive (scale_large n) (by exact_mod_cast logarithm_positive (scale_large n))

theorem population_nearError_le_two (n k : ℕ) (hkn : k ≤ n) :
    (k : ℝ) * UpperRepair.nearError n ≤ 2 := by
  have hs := scale_large n
  have he : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have hk := active_scale n k hkn
  have hks : (k : ℝ) ≤ scale n := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hp : (scale n : ℝ) ≤ (scale n : ℝ)^10 :=
    le_self_pow₀ (s_one hs) (by norm_num)
  have hmul : (scale n : ℝ)^10 ≤ (scale n : ℝ)^10 * logarithm (scale n) := by
    exact le_mul_of_one_le_right (by positivity) he
  unfold UpperRepair.nearError oldError
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity [s_positive hs, ell_positive he])).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) (scale n)]

end EnvyFreeResearch.Full.UpperShrink
