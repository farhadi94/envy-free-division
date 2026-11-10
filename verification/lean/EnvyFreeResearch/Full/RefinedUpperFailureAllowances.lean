import EnvyFreeResearch.Full.RefinedUpperRejectionParameters
import EnvyFreeResearch.Full.RefinedUpperStabilityChargeBudget

/-! The four numerical failure allowances for the actual refined Repair. -/
noncomputable section
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperFailureAllowances
open RefinedUpperParameterCounts RefinedUpperRejectionParameters

def badThreshold (k : ℕ) : ℝ := 1/(32768*(k : ℝ)^2)
def endpointAllowance (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1/(7168*(k : ℝ)))
def retryAllowance : ℝ≥0∞ := ENNReal.ofReal (1/4 : ℝ)
def firstBadAllowance (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((4/3 : ℝ)*(1/(7168*(k : ℝ))))

theorem endpoint_bound {k : ℕ} (hk : 0 < k) :
    ENNReal.ofReal (32*(k : ℝ)/7)*ENNReal.ofReal (badThreshold k) = endpointAllowance k := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact congrArg ENNReal.ofReal (endpoint_allowance (by exact_mod_cast hk))

theorem first_bad_fixed (k : ℕ) :
    endpointAllowance k + firstBadAllowance k*retryAllowance = firstBadAllowance k := by
  unfold endpointAllowance firstBadAllowance retryAllowance
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact congrArg ENNReal.ofReal (first_bad_fixed_point _)

theorem retry_total {k s ell : ℕ} (hk : 0 < k) (hs : 0 < s)
    (hlog : 2*(s : ℝ) ≤ (2 : ℝ)^ell) :
    (k : ℝ≥0∞)*(firstBadAllowance k+retryAllowance^ell) ≤
      ENNReal.ofReal (1/5376+(k : ℝ)/(4*(s : ℝ)^2)) := by
  have hkr : (0 : ℝ)<k := by exact_mod_cast hk
  have hsr : (0 : ℝ)<s := by exact_mod_cast hs
  have he := exhaustion_allowance hsr ell hlog
  have hreal : (k : ℝ)*((4/3 : ℝ)*(1/(7168*(k : ℝ)))+(1/4 : ℝ)^ell) ≤
      1/5376+(k : ℝ)/(4*(s : ℝ)^2) := by
    rw [mul_add,first_bad_allowance hkr]
    simpa only [mul_one_div] using add_le_add le_rfl (mul_le_mul_of_nonneg_left he hkr.le)
  calc
    _ = ENNReal.ofReal ((k : ℝ)*((4/3 : ℝ)*(1/(7168*(k : ℝ)))+(1/4 : ℝ)^ell)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg k),ENNReal.ofReal_natCast,
        ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_pow (by norm_num)]
      rfl
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

theorem isolation_bound {k s ell : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s) (he : 1 ≤ ell)
    (hlog : Real.log (2*(k : ℝ)) ≤ ell) :
    UpperLogicalIsolation.isolationBound k (repetitions s ell) (multiplier s) ≤
      13*((k : ℝ)/s)^3 := by
  have hkr : (1 : ℝ)≤k := by exact_mod_cast hk
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have her : (1 : ℝ)≤ell := by exact_mod_cast he
  have hsp : (0 : ℝ)<s := by linarith
  have hep : (0 : ℝ)<ell := by linarith
  have hlog0 : 0 ≤ Real.log (2*(k : ℝ)) := Real.log_nonneg (by linarith)
  have hfactor : (k : ℝ)^2*((k : ℝ)-1) ≤ (k : ℝ)^3 := by nlinarith [sq_nonneg (k : ℝ)]
  have hlogfactor : 12*(s : ℝ)*Real.log (2*(k : ℝ))+1 ≤ 13*(s : ℝ)*ell := by
    have hm := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 12*(s : ℝ))
    have hse : (1 : ℝ) ≤ (s : ℝ)*ell := by
      calc
        1 = 1*1 := by ring
        _ ≤ _ := mul_le_mul hsr her (by norm_num) (by linarith)
    nlinarith
  unfold UpperLogicalIsolation.isolationBound multiplier
  calc
    _ ≤ ((k : ℝ)^3*(13*(s : ℝ)*ell))/((s : ℝ)^4*ell) := by
      apply div_le_div₀
      · positivity
      · exact mul_le_mul hfactor hlogfactor (by positivity) (by positivity)
      · positivity
      · rw [Nat.cast_add,Nat.cast_one,repetitions_cast]
        linarith
    _ = _ := by field_simp [hsp.ne',hep.ne'] <;> ring

theorem logarithm_power {s : ℕ} (hs : 0 < s) :
    2*(s : ℝ) ≤ (2 : ℝ)^(UpperRepairParameters.logarithm s) := by
  have hsp : (0 : ℝ)<s := by exact_mod_cast hs
  have hlog2 : (0 : ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_pow]
  exact (div_le_iff₀ hlog2).mp (Nat.le_ceil (Real.log (2*(s : ℝ))/Real.log 2))

end EnvyFreeResearch.Full.RefinedUpperFailureAllowances
