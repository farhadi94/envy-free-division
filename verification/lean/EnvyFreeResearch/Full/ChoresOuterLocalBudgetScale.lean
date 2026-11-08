import EnvyFreeResearch.Full.ChoresOuterLocalBudget

/-! The literal terminal separation/dominance hypotheses at the actual
integer scale, transported to real-valued costs without asymptotic notation. -/
namespace EnvyFreeResearch.Full.Chores.Outer
open Parameters

theorem scale_factor (n : ℕ) : scale n=8*2^(n+2)*roots n*n^3 := by
  unfold scale
  rw [show n+5=(n+2)+3 by omega,pow_add]
  norm_num only [show (2:ℕ)^3=8 by decide]
  ring

theorem terminal_scale_nat {n : ℕ} (hn : 3 ≤ n) :
    roots n*n^2 ≤ scale n ∧ 2*2^(n+2) ≤ scale n ∧
      2^(n+2)*n^2 ≤ scale n ∧ n+2 ≤ scale n := by
  have hj : 1 ≤ roots n := roots_pos n
  have hn1 : 1 ≤ n := by omega
  have hn2 : 1 ≤ n^2 := Nat.one_le_pow _ _ hn1
  have h23 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn1 (by decide)
  have hp : 1 ≤ (2:ℕ)^(n+2) := Nat.one_le_two_pow
  have hbase : 8*2^(n+2)*roots n*n^2 ≤ scale n := by
    rw [scale_factor]
    exact Nat.mul_le_mul_left _ h23
  have hcoef : 8 ≤ 8*2^(n+2)*roots n := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hp) hj
    simpa using h
  have h8 : 8*n^2 ≤ scale n :=
    (Nat.mul_le_mul_right _ hcoef).trans hbase
  constructor
  · have hc : 1 ≤ 8*2^(n+2) := by omega
    have hh := Nat.mul_le_mul_right (roots n*n^2) hc
    nlinarith
  constructor
  · have hh : 1 ≤ roots n*n^2 := Nat.mul_le_mul hj hn2
    have hh' := Nat.mul_le_mul_left (8*2^(n+2)) hh
    nlinarith
  constructor
  · have hc : 1 ≤ 8*roots n := by omega
    have hh := Nat.mul_le_mul_left (2^(n+2)*n^2) hc
    nlinarith
  · nlinarith

theorem terminal_scale_real {n : ℕ} (hn : 3 ≤ n) :
    (roots n : ℝ)*(n : ℝ)^2 ≤ (scale n : ℝ) ∧
      2*(2:ℝ)^(n+2) ≤ (scale n : ℝ) ∧
      (2:ℝ)^(n+2)*(n : ℝ)^2 ≤ (scale n : ℝ) ∧
      (n : ℝ)+2 ≤ (scale n : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := terminal_scale_nat hn
  exact ⟨by exact_mod_cast ha,by exact_mod_cast hb,by exact_mod_cast hc,by exact_mod_cast hd⟩

end EnvyFreeResearch.Full.Chores.Outer
