import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolLaw
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallReadyParameters
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallParameters

/-! Concrete interpolation tolerances for every active subpopulation. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRepairParameters

theorem small_configured_tolerances {n k : ℕ} (hk : 0<k) (hkn : k ≤ n) :
    1/(scale n:ℝ)^2 ≤ (1:ℝ)/2 ∧
    1/(scale n:ℝ)^2 ≤ 3/(64*(k:ℝ)) ∧ RefinedUpperRepair.nearError n ≤ 4 := by
  have h := UpperSnapshotProtocol.small_configured_tolerances hk hkn
  refine ⟨h.1,h.2.1,?_⟩
  have hs := s_one (scale_large n)
  change 1/(4*(scale n:ℝ)^2) ≤ 4
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(scale n:ℝ)^2)).mpr
  nlinarith
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
