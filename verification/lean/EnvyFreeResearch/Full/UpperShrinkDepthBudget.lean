import EnvyFreeResearch.Full.UpperShrinkDepth

noncomputable section
namespace EnvyFreeResearch.Full.UpperShrinkPrecision
open UpperRepairParameters

theorem actual_precision (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n)
    (G : ℝ) (hG : 0 < G)
    (hmax : G ≤ (2 / theta n) * (8 / UpperRepair.nearError n)^(k-1)) :
    (k : ℝ)^2 / (2 : ℝ)^(depth n k) ≤ UpperShrink.error (UpperRepair.nearError n) G := by
  have hs := scale_large n
  have he : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have hkR : (k : ℝ) ≤ scale n := by
    have ha := active_scale n k hkn
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hks : k ≤ scale n := by exact_mod_cast hkR
  exact geometric_precision hs he (logarithm_le_scale hs) hks hk
    (scale_le_binary_logarithm hs) G hG hmax

theorem actual_cut_budget (n k : ℕ) (hkn : k ≤ n) :
    k^3 * depth n k ≤ UpperRepair.fine n := by
  have hs := scale_large n
  have hs32 : 32 ≤ scale n := by
    have : (32 : ℝ) ≤ scale n := by norm_num at hs ⊢; linarith
    exact_mod_cast this
  have hks : k ≤ scale n := by
    have ha := active_scale n k hkn
    have : (k : ℝ) ≤ scale n := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    exact_mod_cast this
  have he := logarithm_positive hs
  have hp : 32*k^4 ≤ (scale n)^5 := by
    calc
      _ ≤ scale n * (scale n)^4 := by gcongr
      _ = _ := by ring
  have hpow : (scale n)^5 ≤ (scale n)^18 := Nat.pow_le_pow_right (by omega) (by omega)
  have hell : logarithm (scale n) ≤ (logarithm (scale n))^2 := by nlinarith
  unfold depth UpperRepair.fine samples
  calc
    k^3 * (32*k*logarithm (scale n)) = (32*k^4)*logarithm (scale n) := by ring
    _ ≤ (scale n)^18 * (logarithm (scale n))^2 := Nat.mul_le_mul (hp.trans hpow) hell

end EnvyFreeResearch.Full.UpperShrinkPrecision
