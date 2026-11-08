import EnvyFreeResearch.Full.ChoresComponentBudgetGlobal
import EnvyFreeResearch.Full.ChoresComponentPopulationGroups

/-! Exact residual child allowances in the proper-population recurrence. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Population Parameters

def childQueries (n : ℕ) : ℕ := (totalCapacity n).queries-nativeLocalQueries n
def childCuts (n : ℕ) : ℕ := (totalCapacity n).cuts-nativeLocalCuts n

theorem local_child_queries {n : ℕ} (hn : 0 < n) :
    nativeLocalQueries n+childQueries n=(totalCapacity n).queries := by
  exact Nat.add_sub_of_le (capacity_local nativeLocalQueries nativeLocalCuts hn).1

theorem local_child_cuts {n : ℕ} (hn : 0 < n) :
    nativeLocalCuts n+childCuts n=(totalCapacity n).cuts := by
  exact Nat.add_sub_of_le (capacity_local nativeLocalQueries nativeLocalCuts hn).2

theorem child_allowance_one {n k : ℕ} (hk : k < n) :
    (totalCapacity k).queries+n*(totalCapacity k).cuts ≤ childQueries n ∧
      (totalCapacity k).cuts ≤ childCuts n := by
  have h := capacity_one nativeLocalQueries nativeLocalCuts hk
  constructor
  · apply Nat.le_sub_of_add_le
    simpa only [totalCapacity,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.1
  · apply Nat.le_sub_of_add_le
    simpa only [totalCapacity,Nat.add_comm] using h.2

theorem child_allowance_two {n b d : ℕ} (hb : 0 < b) (hd : 0 < d) (hs : b+d=n) :
    (totalCapacity b).queries+n*(totalCapacity b).cuts+
      ((totalCapacity d).queries+n*(totalCapacity d).cuts) ≤ childQueries n ∧
    (totalCapacity b).cuts+(totalCapacity d).cuts ≤ childCuts n := by
  have h := capacity_two nativeLocalQueries nativeLocalCuts hb hd hs
  constructor
  · apply Nat.le_sub_of_add_le
    simpa only [totalCapacity,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.1
  · apply Nat.le_sub_of_add_le
    simpa only [totalCapacity,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2

theorem selected_le_roots {n : ℕ} (hn : 2 ≤ n) : selected n ≤ roots n := by
  have hp := selected_pos n
  have hn' : 1 ≤ n-1 := by omega
  have hmul := Nat.mul_le_mul_left (selected n-1) hn'
  unfold roots
  omega

theorem scale_lower {n : ℕ} (hn : 3 ≤ n) : n < scale n := by
  have hj := roots_pos n
  have hnpos : 1 ≤ n := by omega
  have hn3 : n ≤ n^3 := by
    calc
      n = n*1*1 := by omega
      _ ≤ n*n*n := Nat.mul_le_mul (Nat.mul_le_mul_left n hnpos) hnpos
      _ = n^3 := by ring
  have hp : 2 ≤ 2^(n+5) := by
    rw [show n+5=(n+4)+1 by omega, pow_succ]
    have : 1 ≤ (2:ℕ)^(n+4) := Nat.one_le_two_pow
    omega
  have h := Nat.mul_le_mul hp hj
  have h' := Nat.mul_le_mul_right (n^3) h
  unfold scale
  nlinarith

theorem scale_conditions {n : ℕ} (hn : 3 ≤ n) :
    (n-1 : ℕ) < (scale n : ℝ) ∧ 1 < (scale n : ℝ) ∧
      (n : ℝ) < (scale n : ℝ)*(scale n : ℝ) := by
  have hs : (n : ℝ) < (scale n : ℝ) := by exact_mod_cast scale_lower hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpred : ((n-1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  constructor
  · linarith
  constructor <;> nlinarith

end EnvyFreeResearch.Full.Chores.Outer
