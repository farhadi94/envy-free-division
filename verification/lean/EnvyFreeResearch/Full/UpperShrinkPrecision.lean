import EnvyFreeResearch.Full.UpperShrinkParameters

/-! Canonical prescribed margin and deterministic carving depth. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperShrinkPrecision
open UpperRepairParameters

def theta (n : ℕ) : ℝ := UpperRepair.nearError n / (768 * UpperRepair.fine n)
def depth (n k : ℕ) : ℕ := 32 * k * logarithm (scale n)

theorem theta_positive (n : ℕ) : 0 < theta n := by
  unfold theta
  exact div_pos (UpperShrink.nearError_positive n)
    (mul_pos (by norm_num) (samples_positive (scale_large n)
      (by exact_mod_cast logarithm_positive (scale_large n))))

theorem fraction_range {k : ℕ} (hk : 0 < k) {G : ℝ} (hG : 1 ≤ G) :
    0 ≤ UpperShrink.fraction k G ∧ UpperShrink.fraction k G ≤ 1 / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hg : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hi : 1 / (2 * G) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  unfold UpperShrink.fraction
  exact ⟨div_nonneg (by linarith) hkR.le,
    div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) hkR.le⟩

theorem reciprocal_scales {s ell : ℕ} (hs : (2^42 : ℝ) ≤ s)
    (hell : (1 : ℝ) ≤ ell) (hells : ell ≤ s) :
    8 / oldError s ell ≤ (s : ℝ)^12 ∧
      2 / (oldError s ell / (768 * samples s ell)) ≤ (s : ℝ)^32 := by
  have hsp := s_positive hs
  have hep := ell_positive hell
  have hel : (ell : ℝ) ≤ s := by exact_mod_cast hells
  have h32 : (32 : ℝ) ≤ s := by norm_num at hs ⊢; linarith
  have h6144 : (6144 : ℝ) ≤ s := by norm_num at hs ⊢; linarith
  constructor
  · have heq : 8 / oldError s ell = 32 * (s : ℝ)^10 * ell := by
      unfold oldError
      field_simp
      norm_num
    rw [heq]
    calc
      _ ≤ (s : ℝ) * (s : ℝ)^10 * s := by gcongr
      _ = _ := by ring
  · have heq : 2 / (oldError s ell / (768 * samples s ell)) =
        6144 * (s : ℝ)^28 * (ell : ℝ)^3 := by
      rw [oldError, samples_cast]
      field_simp
      ring
    rw [heq]
    calc
      _ ≤ (s : ℝ) * (s : ℝ)^28 * (s : ℝ)^3 := by gcongr
      _ = _ := by ring

end EnvyFreeResearch.Full.UpperShrinkPrecision
