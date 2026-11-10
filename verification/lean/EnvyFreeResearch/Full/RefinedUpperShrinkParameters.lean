import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.UpperShrinkCarved

/-! Positivity and population bounds for the revised near-equality tolerance. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperShrink
open UpperRepairParameters (scale scale_large active_scale s_positive s_one)
open RefinedUpperParameterCounts

theorem nearError_positive (n : ℕ) : 0  <  RefinedUpperRepair.nearError n := by
  unfold RefinedUpperRepair.nearError oldError
  positivity [s_positive (scale_large n)]

theorem population_nearError_le_two (n k : ℕ) (hkn : k  ≤  n) :
    (k : ℝ)*RefinedUpperRepair.nearError n  ≤  2 := by
  have hs := scale_large n
  have hk := active_scale n k hkn
  have hks : (k : ℝ)  ≤  scale n := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hsp := s_positive hs
  have hs1 := s_one hs
  unfold RefinedUpperRepair.nearError oldError
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*(scale n : ℝ)^2)).mpr
  nlinarith

end EnvyFreeResearch.Full.RefinedUpperShrink
