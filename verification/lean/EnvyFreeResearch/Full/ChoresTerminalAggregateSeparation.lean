import EnvyFreeResearch.Full.ChoresTerminalAggregateResidue

/-! Converting actual atomic extraction and full-residue estimates into
the separation factors required by the constructive two-group finisher. -/
namespace EnvyFreeResearch.Full.Chores.Terminal

theorem atomic_large_separation (n J : ℕ) (H K r x u : ℝ)
    (hH : 0 < H) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H) (hscale : 2*K ≤ H)
    (hx : H*r ≤ x) (hu : u ≤ (1+(J : ℝ)*(n : ℝ)^2/H)*r) : K*u ≤ x := by
  have hj : (J : ℝ)*(n : ℝ)^2/H ≤ 1 := (div_le_iff₀ hH).mpr (by simpa using hreserve)
  have hu' : u ≤ 2*r := hu.trans (mul_le_mul_of_nonneg_right (by linarith) hr)
  calc
    K*u ≤ K*(2*r) := mul_le_mul_of_nonneg_left hu' hK
    _ = (2*K)*r := by ring
    _ ≤ H*r := mul_le_mul_of_nonneg_right hscale hr
    _ ≤ x := hx

theorem atomic_small_separation (n : ℕ) (H K r x u : ℝ)
    (hH : 0 < H) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hscale : K*(n : ℝ)^2 ≤ H)
    (hx : x ≤ (n : ℝ)^2*r/H) (hu : r ≤ u) : K*x ≤ u := by
  calc
    K*x ≤ K*((n : ℝ)^2*r/H) := mul_le_mul_of_nonneg_left hx hK
    _ = (K*(n : ℝ)^2)*r/H := by ring
    _ ≤ r := (div_le_iff₀ hH).mpr (by nlinarith [mul_le_mul_of_nonneg_right hscale hr])
    _ ≤ u := hu

end EnvyFreeResearch.Full.Chores.Terminal
