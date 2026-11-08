import EnvyFreeResearch.Full.UpperRepairParametersScale
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The manuscript's Snapshot endpoint and interpolation constants. -/
noncomputable section
open scoped BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate

def snapshotAccuracy (s : ℕ) : ℝ := 1 / (s : ℝ)^2

theorem candidate_endpoint_count (k : ℕ) (hk : 2 ≤ k) : 16*k*(k+2) ≤ 32*k^2 := by
  nlinarith

theorem candidate_endpoint_budget (k : ℕ) (hk : 2 ≤ k) :
    (16*k*(k+2) : ℝ) * (2*k^2) ≤ 64*k^4 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h : (k : ℝ)+2 ≤ 2*k := by linarith
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 32*(k : ℝ)^3)
  nlinarith

theorem snapshot_accuracy_positive {s : ℕ} (hs : 0 < s) : 0 < snapshotAccuracy s := by
  unfold snapshotAccuracy
  positivity

theorem snapshot_failure_small {s ell k : ℕ}
    (hs : (4 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hk : (k : ℝ) ≤ s) :
    128 * (k : ℝ)^5 * (1 + snapshotAccuracy s) /
      (snapshotAccuracy s * ((UpperRepairParameters.samples s ell : ℝ) + 1)) < 1/64 := by
  have hsp : (0 : ℝ) < s := by linarith
  have hep : (0 : ℝ) < ell := by linarith
  have hs2 : (1 : ℝ) ≤ (s : ℝ)^2 := one_le_pow₀ (by linarith)
  have he2 : (1 : ℝ) ≤ (ell : ℝ)^2 := one_le_pow₀ hell
  have heps : snapshotAccuracy s ≤ 1 := by
    unfold snapshotAccuracy
    exact (div_le_one (by positivity : (0 : ℝ) < (s : ℝ)^2)).mpr hs2
  have hepspos : 0 < snapshotAccuracy s := by unfold snapshotAccuracy; positivity
  have hden : snapshotAccuracy s * (UpperRepairParameters.samples s ell : ℝ) =
      (s : ℝ)^16 * (ell : ℝ)^2 := by
    rw [UpperRepairParameters.samples_cast, snapshotAccuracy]
    field_simp
  have hfirst : 128 * (k : ℝ)^5 * (1 + snapshotAccuracy s) /
        (snapshotAccuracy s * ((UpperRepairParameters.samples s ell : ℝ) + 1)) ≤
        256 * (k : ℝ)^5 / ((s : ℝ)^16 * (ell : ℝ)^2) := by
    apply div_le_div₀
    · positivity
    · nlinarith [pow_nonneg (show (0 : ℝ) ≤ k by positivity) 5]
    · positivity
    · rw [mul_add, hden]
      linarith
  have hk5 : (k : ℝ)^5 ≤ (s : ℝ)^5 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk 5
  have hsecond : 256 * (k : ℝ)^5 / ((s : ℝ)^16 * (ell : ℝ)^2) ≤ 256 / (s : ℝ)^11 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_right hk5 (by positivity : 0 ≤ (s : ℝ)^11)
    have hp : (s : ℝ)^5 * (s : ℝ)^11 = (s : ℝ)^16 := by ring
    rw [hp] at h
    have he := mul_le_mul_of_nonneg_left he2 (by positivity : 0 ≤ (s : ℝ)^16)
    nlinarith
  have hs11 : (4 : ℝ)^11 ≤ (s : ℝ)^11 := pow_le_pow_left₀ (by norm_num) hs 11
  have hlast : 256 / (s : ℝ)^11 < 1/64 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (s : ℝ)^11)).mpr
    norm_num at hs11
    linarith
  exact hfirst.trans_lt (hsecond.trans_lt hlast)

theorem snapshot_full_budget_failure_small {s ell k : ℕ}
    (hs : (4 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hk : (k : ℝ) ≤ s) :
    ENNReal.ofReal (2 * ((k : ℝ) - 1) * (64 * (k : ℝ)^4) * (1 + snapshotAccuracy s) /
      (snapshotAccuracy s * (UpperRepairParameters.samples s ell + 1 : ℕ))) < 1/64 := by
  have hep : 0 < snapshotAccuracy s := by
    unfold snapshotAccuracy
    have hsp : (0 : ℝ) < s := by linarith
    positivity
  have hn : 2 * ((k : ℝ) - 1) * (64 * (k : ℝ)^4) ≤ 128 * (k : ℝ)^5 := by
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ k by positivity) 4]
  have hm := mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ 1 + snapshotAccuracy s)
  have hb := div_le_div_of_nonneg_right hm
    (show 0 ≤ snapshotAccuracy s * (UpperRepairParameters.samples s ell + 1 : ℕ) by positivity)
  have hreal : 2 * ((k : ℝ) - 1) * (64 * (k : ℝ)^4) * (1 + snapshotAccuracy s) /
      (snapshotAccuracy s * (UpperRepairParameters.samples s ell + 1 : ℕ)) < 1/64 := by
    exact hb.trans_lt (by exact_mod_cast snapshot_failure_small hs hell hk)
  have he := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1/64)).mpr hreal
  have h64 : ENNReal.ofReal (1/64 : ℝ) = (1/64 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [h64] at he
  exact he

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
