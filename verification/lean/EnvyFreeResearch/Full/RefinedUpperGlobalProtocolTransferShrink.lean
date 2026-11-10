import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferFactors

namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer

/-- The accepted first shrink converts the safe scaled alternatives into
small-own-loss or large-comparison bounds in the new residue units. -/
theorem shrink_dichotomy {d r rho G tau : ℝ} (hr : 0 < r) (hG : 0 < G)
    (htau : 0 ≤ tau) (hlow : 3*r/(8*G) ≤ rho) (hupp : rho ≤ r/G)
    (hsafe : G*(d/r) ≤ 3*tau/8 ∨ 2 ≤ G*(d/r)) :
    d ≤ tau*rho ∨ 2*rho ≤ d := by
  have hl : 3*r ≤ rho*(8*G) := (div_le_iff₀ (by positivity)).mp hlow
  have hu : rho*G ≤ r := (le_div_iff₀ hG).mp hupp
  rcases hsafe with hs | hs
  · left
    have hs' : G*d ≤ (3*tau/8)*r := (div_le_iff₀ hr).mp (by simpa only [mul_div_assoc] using hs)
    have hh := mul_le_mul_of_nonneg_left hl htau
    nlinarith
  · right
    have hs' : 2*r ≤ G*d := (le_div_iff₀ hr).mp (by simpa only [mul_div_assoc] using hs)
    nlinarith

theorem factor_lower {theta tau : ℝ} (htheta : 0 < theta) (htau : 0 < tau)
    (htau1 : tau ≤ 1) (e : ℕ) : 2/theta ≤ factor theta tau e := by
  have hb : 1 ≤ 8/tau := (le_div_iff₀ htau).mpr (by linarith)
  have hp := one_le_pow₀ hb (n := e)
  unfold factor
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (show 0 ≤ 2/theta by positivity)

theorem certificate_row_large {theta tau x : ℝ} (htheta : 0 < theta)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (hx : theta ≤ x) (e : ℕ) :
    2 ≤ factor theta tau e*x := by
  have hscale : (2/theta)*theta=2 := div_mul_cancel₀ 2 (ne_of_gt htheta)
  have hh := mul_le_mul (factor_lower htheta htau htau1 e) hx htheta.le
    (factor_pos htheta htau e).le
  simpa only [hscale] using hh

end EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer
