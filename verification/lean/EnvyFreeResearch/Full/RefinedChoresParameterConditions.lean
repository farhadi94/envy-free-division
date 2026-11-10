import EnvyFreeResearch.Full.RefinedChoresParameters

/-! The concrete root-local scale satisfies every physical terminal and
clearance separation hypothesis used by the completion programs. -/
namespace EnvyFreeResearch.Full.RefinedChoresParameters

theorem scale_lower {n : ℕ} (hn : 2 ≤ n) : 2*n ≤ scale n := by
  have hj : 1 ≤ roots n := roots_pos n
  have hn1 : 1 ≤ n := by omega
  have hn3 : n ≤ n^3 := by simpa using Nat.pow_le_pow_right hn1 (show 1 ≤ 3 by decide)
  have hp : 2 ≤ 2^(n+5) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) (show 1 ≤ n+5 by omega)
    simpa only [pow_one] using h
  have h := Nat.mul_le_mul (Nat.mul_le_mul hp hj) hn3
  simpa only [mul_one,scale] using h

theorem reserve_scale {n : ℕ} (hn : 1 ≤ n) : roots n*n^2 ≤ scale n := by
  have hn2 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn (by decide)
  have hp : roots n ≤ 2^(n+5)*roots n := by
    simpa only [one_mul] using Nat.mul_le_mul_right (roots n) (Nat.one_le_two_pow (n := n+5))
  exact Nat.mul_le_mul hp hn2

theorem small_scale {n : ℕ} (hn : 1 ≤ n) : 2^(n+2)*n^2 ≤ scale n := by
  have hj : 1 ≤ roots n := roots_pos n
  have hp := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) (show n+2 ≤ n+5 by omega)
  have hm : 2^(n+2) ≤ 2^(n+5)*roots n := by simpa only [mul_one] using Nat.mul_le_mul hp hj
  exact Nat.mul_le_mul hm (Nat.pow_le_pow_right hn (show 2 ≤ 3 by decide))

theorem large_scale {n : ℕ} (hn : 1 ≤ n) : 2*2^(n+2) ≤ scale n := by
  have hp : 2*2^(n+2) ≤ 2^(n+5) := by
    rw [mul_comm,← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hj : 1 ≤ roots n*n^3 := Nat.mul_le_mul (roots_pos n) (Nat.one_le_pow 3 n hn)
  have h := Nat.mul_le_mul hp hj
  simpa only [mul_one,mul_assoc,scale] using h

theorem real_conditions {n : ℕ} (hn : 3 ≤ n) :
    (n-1 : ℕ) < (scale n : ℝ) ∧ 1 < (scale n : ℝ) ∧
    (n : ℝ) < (scale n : ℝ)*(scale n : ℝ) ∧
    (roots n : ℝ)*(n : ℝ)^2 ≤ scale n ∧
    2*(2 : ℝ)^(n+2) ≤ scale n ∧
    (2 : ℝ)^(n+2)*(n : ℝ)^2 ≤ scale n ∧ (n : ℝ)+2 ≤ scale n := by
  have hs : 2*(n:ℝ) ≤ scale n := by exact_mod_cast scale_lower (by omega : 2 ≤ n)
  have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hpred : ((n-1:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  refine ⟨by linarith,by linarith,by nlinarith,?_,?_,?_,by linarith⟩
  · exact_mod_cast reserve_scale (by omega : 1 ≤ n)
  · exact_mod_cast large_scale (by omega : 1 ≤ n)
  · exact_mod_cast small_scale (by omega : 1 ≤ n)

end EnvyFreeResearch.Full.RefinedChoresParameters
#print axioms EnvyFreeResearch.Full.RefinedChoresParameters.real_conditions
