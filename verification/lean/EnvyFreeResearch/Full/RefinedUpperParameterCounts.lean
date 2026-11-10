import EnvyFreeResearch.Full.UpperRepairParametersPopulation
import EnvyFreeResearch.Full.UpperRecordedQuantiles

/-! Integral counts for the revised randomized construction. These arithmetic
facts are used by physical adapters; they do not assert an oracle protocol. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperParameterCounts
open UpperRepairParameters (scale logarithm)

def coarseCount (s ell : ℕ) : ℕ := s^8*ell
def samples (s ell : ℕ) : ℕ := s^9*ell/128
def repetitions (s ell : ℕ) : ℕ := s^4*ell
def coarseCap (s ell : ℕ) : ℝ := 1/((s:ℝ)^8*ell)
def fineCap (s ell : ℕ) : ℝ := 2/((s:ℝ)^8*ell)
def oldError (s : ℕ) : ℝ := 1/(4*(s:ℝ)^2)
def multiplier (s : ℕ) : ℝ := s

theorem scale_divisible (n : ℕ) : 128 ∣ scale n := by
  unfold scale
  apply dvd_mul_of_dvd_left
  norm_num

theorem samples_cast {s ell : ℕ} (hd : 128 ∣ s) :
    (samples s ell : ℝ) = (s:ℝ)^9*ell/128 := by
  have hpow : s ∣ s^9 := dvd_pow_self s (by norm_num)
  have hdiv : 128 ∣ s^9*ell := dvd_mul_of_dvd_left (hd.trans hpow) ell
  rw [samples, Nat.cast_div hdiv (by norm_num : (128:ℝ)≠0)]
  push_cast
  rfl

theorem coarseCount_cast (s ell : ℕ) : (coarseCount s ell : ℝ)=(s:ℝ)^8*ell := by
  simp [coarseCount]
theorem repetitions_cast (s ell : ℕ) : (repetitions s ell : ℝ)=(s:ℝ)^4*ell := by
  simp [repetitions]

theorem coarse_positive {s ell : ℕ} (hs : 1 ≤ s) (he : 1 ≤ ell) : 1 ≤ coarseCount s ell := by
  unfold coarseCount
  exact Nat.mul_pos (pow_pos (by omega) _) (by omega)

theorem samples_ge_square {s ell : ℕ} (hs : 256 ≤ s) (he : 1 ≤ ell) :
    s^2 ≤ samples s ell := by
  unfold samples
  apply (Nat.le_div_iff_mul_le (by norm_num : 0<128)).mpr
  have hpow : 128 ≤ s^7 := by
    have hh : s ≤ s^7 := Nat.le_self_pow (by norm_num) s
    omega
  have hp := Nat.mul_le_mul_left (s^2) hpow
  have he' : s^9 ≤ s^9*ell := by simpa using Nat.mul_le_mul_left (s^9) he
  nlinarith [show s^2*s^7=s^9 by ring]

theorem samples_positive {s ell : ℕ} (hs : 256 ≤ s) (he : 1 ≤ ell) : 1 ≤ samples s ell := by
  have hh := samples_ge_square hs he
  have hs1 : 1 ≤ s := by omega
  have hs2 : 1 ≤ s^2 := one_le_pow₀ hs1
  omega

theorem grid_fits {s ell k : ℕ} (hs : 256 ≤ s) (he : 1 ≤ ell)
    (hk : 256*k ≤ s) (hk0 : 1 ≤ k) :
    k*coarseCount s ell+1 ≤ samples s ell ∧ 2*k ≤ samples s ell := by
  have hq : 1 ≤ coarseCount s ell := coarse_positive (by omega) he
  have hfirst : k*coarseCount s ell+1 ≤ samples s ell := by
    unfold samples
    apply (Nat.le_div_iff_mul_le (by norm_num : 0<128)).mpr
    have hks := Nat.mul_le_mul_right (coarseCount s ell) hk
    have hprod : 1 ≤ k*coarseCount s ell := by nlinarith
    have heq : s*coarseCount s ell=s^9*ell := by unfold coarseCount; ring
    nlinarith
  have hsecond : 2*k ≤ samples s ell := by
    have h2 := samples_ge_square hs he
    nlinarith
  exact ⟨hfirst,hsecond⟩

theorem cell_count {s ell k : ℕ} (hs : 256 ≤ s) (he : 1 ≤ ell)
    (hk : 256*k ≤ s) (hk0 : 1 ≤ k) :
    UpperRecordedQuantiles.count (Agent := Fin k) (coarseCount s ell)+samples s ell+1 ≤
      2*samples s ell := by
  have h := (grid_fits hs he hk hk0).1
  simp only [UpperRecordedQuantiles.count, Fintype.card_prod, Fintype.card_fin]
  omega

theorem candidate_queries_fit {s ell k : ℕ} (hs : 256 ≤ s) (he : 1 ≤ ell)
    (hk : 256*k ≤ s) (hk2 : 2 ≤ k) : (16*k)*(k+2) ≤ samples s ell := by
  have hm := samples_ge_square hs he
  have hsquare : (256*k)^2 ≤ s^2 := Nat.pow_le_pow_left hk 2
  nlinarith

/-- Fresh retries may spend two cuts per recipient per attempt. -/
theorem correction_retries_fit {s ell k : ℕ} (hs : 1 ≤ s) (hk : 256*k ≤ s) :
    2*k*ell ≤ samples s ell := by
  unfold samples
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 128)).mpr
  have hpow : s ≤ s^9 := Nat.le_self_pow (by norm_num) s
  have hprod := Nat.mul_le_mul_right ell (hk.trans hpow)
  nlinarith

/-- Retaining the old conservative Shrink depth costs no exponent. -/
theorem shrink_rounds_fit {s ell k : ℕ} (hs : 256 ≤ s) (hk : k ≤ s) :
    k^3*(32*k*ell) ≤ samples s ell := by
  unfold samples
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 128)).mpr
  have hk4 : k^4 ≤ s^4 := Nat.pow_le_pow_left hk 4
  have hs5 : 4096 ≤ s^5 := by
    have hpow := Nat.pow_le_pow_left hs 5
    norm_num at hpow
    omega
  have hprod := Nat.mul_le_mul hk4 hs5
  have hid : s^4*s^5=s^9 := by ring
  rw [hid] at hprod
  have hmore := Nat.mul_le_mul_right ell hprod
  nlinarith

theorem original_count_facts (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    k*coarseCount (scale n) (logarithm (scale n))+1 ≤ samples (scale n) (logarithm (scale n)) ∧
      2*k ≤ samples (scale n) (logarithm (scale n)) := by
  have hs : 256 ≤ scale n := by
    have h := UpperRepairParameters.scale_large n
    exact_mod_cast (show (256:ℝ) ≤ scale n by norm_num at h ⊢; linarith)
  have he := UpperRepairParameters.logarithm_positive (UpperRepairParameters.scale_large n)
  have hk : 256*k ≤ scale n := by
    have h := UpperRepairParameters.active_scale n k hkn
    exact_mod_cast (show (256:ℝ)*k ≤ scale n by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  exact grid_fits hs he hk (by omega)

theorem samples_polynomial (n : ℕ) (hn : 1 ≤ n) :
    (samples (scale n) (logarithm (scale n)) : ℝ) ≤
      ((2^42:ℝ)^9*45/128)*(n:ℝ)^9*(Real.log (2*(n:ℝ))/Real.log 2) := by
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (scale n))
    (UpperRepairParameters.scale_linear n hn) 9
  have he := UpperRepairParameters.logarithm_linear_log n hn
  rw [samples_cast (scale_divisible n)]
  calc
    _ ≤ (((2^42:ℝ)*n)^9*(45*(Real.log (2*(n:ℝ))/Real.log 2)))/128 :=
      div_le_div_of_nonneg_right (mul_le_mul hs he (by positivity) (by positivity)) (by norm_num)
    _ = _ := by ring

end EnvyFreeResearch.Full.RefinedUpperParameterCounts
