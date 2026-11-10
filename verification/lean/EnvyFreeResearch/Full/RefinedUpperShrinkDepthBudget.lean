import EnvyFreeResearch.Full.RefinedUpperShrinkDepth

noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperShrinkPrecision
open UpperRepairParameters (scale logarithm scale_large logarithm_positive active_scale logarithm_le_scale)
open RefinedUpperParameterCounts

theorem actual_precision (n k : ℕ) (hk : 3  ≤  k) (hkn : k  ≤  n)
    (G : ℝ) (hG : 0  <  G)
    (hmax : G  ≤  (2 / theta n) * (8 / RefinedUpperRepair.nearError n)^(k-1)) :
    (k : ℝ)^2 / (2 : ℝ)^(depth n k)  ≤  UpperShrink.error (RefinedUpperRepair.nearError n) G := by
  have hs := scale_large n
  have he : (1 : ℝ)  ≤  logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have hkR : (k : ℝ)  ≤  scale n := by
    have ha := active_scale n k hkn
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hks : k  ≤  scale n := by exact_mod_cast hkR
  exact geometric_precision hs he (logarithm_le_scale hs) hks hk
    (scale_le_binary_logarithm hs) G hG hmax

theorem actual_cut_budget (n k : ℕ) (hkn : k  ≤  n) :
    k^3*depth n k  ≤  RefinedUpperRepair.fine n := by
  have hs := scale_large n
  have hs4096 : 4096  ≤  scale n := by
    exact_mod_cast (show (4096 : ℝ)  ≤  scale n from (by norm_num : (4096 : ℝ) ≤ 2^42).trans hs)
  have hks : k  ≤  scale n := by
    have ha := active_scale n k hkn
    exact_mod_cast (show (k : ℝ) ≤ scale n by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  have hp : 4096*k^4  ≤  (scale n)^9 := by
    calc
      _  ≤  scale n*(scale n)^4 := by gcongr
      _ = (scale n)^5 := by ring
      _  ≤  _ := Nat.pow_le_pow_right (by omega) (by omega)
  unfold depth RefinedUpperRepair.fine samples
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 128)).mpr
  calc
    _ = (4096*k^4)*logarithm (scale n) := by ring
    _  ≤  _ := Nat.mul_le_mul_right _ hp

end EnvyFreeResearch.Full.RefinedUpperShrinkPrecision
