import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallParameters

/-! Concrete interpolation tolerances for every active subpopulation. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRepairParameters

theorem small_configured_tolerances {n k : ℕ} (hk : 0<k) (hkn : k ≤ n) :
    1/(scale n:ℝ)^2 ≤ (1:ℝ)/2 ∧
    1/(scale n:ℝ)^2 ≤ 3/(64*(k:ℝ)) ∧ UpperRepair.nearError n ≤ 4 := by
  have hs := scale_large n
  have hsp := s_positive hs
  have hs2 := s_two hs
  have hs1 := s_one hs
  have hactive := active_scale n k hkn
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  have h64 : 64*(k:ℝ) ≤ scale n := by
    norm_num at hactive
    nlinarith
  have hsq : 0<(scale n:ℝ)^2 := sq_pos_of_pos hsp
  refine ⟨?_,?_,?_⟩
  · apply (div_le_iff₀ hsq).mpr
    nlinarith [sq_nonneg ((scale n:ℝ)-2)]
  · apply (div_le_div_iff₀ hsq (by positivity : (0:ℝ)<64*k)).mpr
    nlinarith [sq_nonneg ((scale n:ℝ)-1)]
  · have hell : (1:ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
    have hden := denominator_ge_one hs hell 10 1
    simp only [pow_one] at hden
    change 1/(4*(scale n:ℝ)^10*(logarithm (scale n):ℝ)) ≤ 4
    apply (div_le_iff₀ (by positivity [hsp,ell_positive hell])).mpr
    nlinarith

end EnvyFreeResearch.Full.UpperSnapshotProtocol
