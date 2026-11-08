import Mathlib

/-! Explicit finite amplification constants for the small-candidate loop. -/
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition

theorem geometric_times_linear (x : ℝ) (hx : 0 ≤ x) (hxone : x ≤ 1) (m : ℕ) :
    (1-x)^m * (1+(m:ℝ)*x) ≤ 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hp : 0 ≤ (1-x)^m := pow_nonneg (by linarith) _
    have hs : 0 ≤ ((m:ℝ)+1)*x*x := by positivity
    have hlocal : (1-x)*(1+((m:ℝ)+1)*x) ≤ 1+(m:ℝ)*x := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hlocal hp
    rw [pow_succ,Nat.cast_succ]
    nlinarith

theorem sixteen_trials_quarter (k : ℕ) (hk : 1 ≤ k) :
    (1-1/(8*(k:ℝ)))^(16*k) ≤ (1:ℝ)/4 := by
  have hkpos : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hx : 0 ≤ 1/(8*(k:ℝ)) := by positivity
  have hxone : 1/(8*(k:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by norm_cast; omega)
  have h := geometric_times_linear (1/(8*(k:ℝ))) hx hxone (8*k)
  have he : (8*k:ℕ)=8*k := rfl
  have hscale : (8*k:ℕ)*(1/(8*(k:ℝ)))=1 := by
    push_cast
    field_simp
  rw [hscale] at h
  have hn : 0 ≤ (1-1/(8*(k:ℝ)))^(8*k) := pow_nonneg (by linarith) _
  have hhalf : (1-1/(8*(k:ℝ)))^(8*k) ≤ 1/2 := by linarith
  have hexp : 16*k=(8*k)*2 := by omega
  rw [hexp,pow_mul,pow_two]
  nlinarith

end EnvyFreeResearch.Full.UpperSnapshotRepetition
