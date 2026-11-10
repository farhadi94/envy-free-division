import EnvyFreeResearch.Full.RefinedUpperShrinkParameters
import EnvyFreeResearch.Full.UpperShrinkPrecision

/-! Revised margin with the original prescribed median-refinement depth. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperShrinkPrecision
open UpperRepairParameters (scale logarithm scale_large logarithm_positive s_positive s_one ell_positive)
open RefinedUpperParameterCounts

def theta (n : ℕ) : ℝ := RefinedUpperRepair.nearError n/(768*RefinedUpperRepair.fine n)
def depth (n k : ℕ) : ℕ := 32*k*logarithm (scale n)

theorem theta_positive (n : ℕ) : 0  <  theta n := by
  have hs : 256  ≤  scale n := by
    exact_mod_cast (show (256 : ℝ)  ≤  scale n from (by norm_num : (256 : ℝ) ≤ 2^42).trans (scale_large n))
  have hm := samples_positive hs (logarithm_positive (scale_large n))
  unfold theta RefinedUpperRepair.fine
  exact div_pos (RefinedUpperShrink.nearError_positive n) (by exact_mod_cast (show 0 < 768*samples (scale n) (logarithm (scale n)) by omega))

theorem fraction_range {k : ℕ} (hk : 0  <  k) {G : ℝ} (hG : 1  ≤  G) :
    0  ≤  UpperShrink.fraction k G ∧ UpperShrink.fraction k G  ≤  1/k :=
  UpperShrinkPrecision.fraction_range hk hG

theorem reciprocal_scales {s ell : ℕ} (hs : (2^42 : ℝ) ≤ s)
    (hell : (1 : ℝ) ≤ ell) (hells : ell ≤ s) :
    8/oldError s  ≤  (s : ℝ)^12 ∧
      2/(oldError s/(768*samples s ell))  ≤  (s : ℝ)^32 := by
  have hsp := s_positive hs
  have hs1 := s_one hs
  have hel : (ell : ℝ) ≤ s := by exact_mod_cast hells
  have h32 : (32 : ℝ) ≤ s := by norm_num at hs ⊢; linarith
  have h6144 : (6144 : ℝ) ≤ s := by norm_num at hs ⊢; linarith
  have hsn : 256 ≤ s := by exact_mod_cast (show (256 : ℝ) ≤ s by linarith)
  have hen : 1 ≤ ell := by exact_mod_cast hell
  have hmpos : (0 : ℝ) < samples s ell := by exact_mod_cast samples_positive hsn hen
  have hm : (samples s ell : ℝ) ≤ (s:ℝ)^9*ell := by
    exact_mod_cast (show samples s ell ≤ s^9*ell from Nat.div_le_self _ _)
  constructor
  · have heq : 8/oldError s=32*(s:ℝ)^2 := by unfold oldError; field_simp; ring
    rw [heq]
    calc
      _  ≤  (s:ℝ)*(s:ℝ)^2 := by gcongr
      _ = (s:ℝ)^3 := by ring
      _  ≤  _ := pow_le_pow_right₀ hs1 (by omega)
  · have heq : 2/(oldError s/(768*samples s ell))=6144*(s:ℝ)^2*samples s ell := by
      unfold oldError
      field_simp
      ring
    rw [heq]
    calc
      _  ≤  (s:ℝ)*(s:ℝ)^2*((s:ℝ)^9*s) := by
        gcongr
        exact hm.trans (mul_le_mul_of_nonneg_left hel (by positivity))
      _ = (s:ℝ)^13 := by ring
      _  ≤  _ := pow_le_pow_right₀ hs1 (by omega)

end EnvyFreeResearch.Full.RefinedUpperShrinkPrecision
