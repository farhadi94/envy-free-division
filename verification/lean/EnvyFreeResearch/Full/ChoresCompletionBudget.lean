import EnvyFreeResearch.Full.ChoresCompletionSplit

/-! The manuscript's 19·2^k preparation bound follows from the actual
near-equal splitting and whole-piece augmentation query ledgers. -/

namespace EnvyFreeResearch.Full.Chores.Completion

theorem square_pow_bound (k : ℕ) : 8*k^2 ≤ 9*2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases hk : k < 3
    · interval_cases k <;> norm_num
    · have hstep : (k+1)^2 ≤ 2*k^2 := by
        have hmul : 3*k ≤ k*k := Nat.mul_le_mul_right k (by omega : 3 ≤ k)
        nlinarith
      calc
        8*(k+1)^2 ≤ 2*(8*k^2) := by nlinarith
        _ ≤ 2*(9*2^k) := Nat.mul_le_mul_left 2 ih
        _ = 9*2^(k+1) := by rw [pow_succ]; ring

theorem sum_powers_bound (b c : ℕ) (hb : 0 < b) (hc : 0 < c) : 2^b+2^c ≤ (2 : ℕ)^(b+c) := by
  have hb2 : 2 ≤ (2 : ℕ)^b := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hb
  have hc2 : 2 ≤ (2 : ℕ)^c := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hc
  have hprod : ((2 : ℕ)^b-2)*((2 : ℕ)^c-2) ≥ 0 := Nat.zero_le _
  rw [pow_add]
  have hx : (2 : ℕ)^b-2+2=2^b := Nat.sub_add_cancel hb2
  have hy : (2 : ℕ)^c-2+2=2^c := Nat.sub_add_cancel hc2
  nlinarith

theorem split_budget_envelope (b k : ℕ) : splitBudget b k ≤ 8*b^2*2^k+2^k := by
  unfold splitBudget countPieces
  have hsub1 : 4*b*2^(k+1)-1 ≤ 4*b*2^(k+1) := Nat.sub_le _ _
  have hsub2 : 2^k-1 ≤ (2 : ℕ)^k := Nat.sub_le _ _
  calc
    b*(4*b*2^(k+1)-1)+(2^k-1) ≤ b*(4*b*2^(k+1))+2^k :=
      Nat.add_le_add (Nat.mul_le_mul_left b hsub1) hsub2
    _ = 8*b^2*2^k+2^k := by rw [pow_succ]; ring

theorem two_group_budget (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    splitBudget b c+splitBudget c b ≤ 19*2^(b+c) := by
  have h1 := Nat.mul_le_mul_right (2^c) (square_pow_bound b)
  have h2 := Nat.mul_le_mul_right (2^b) (square_pow_bound c)
  have hp := sum_powers_bound b c hb hc
  have hbudget := Nat.add_le_add (split_budget_envelope b c) (split_budget_envelope c b)
  rw [pow_add] at hp ⊢
  nlinarith

end EnvyFreeResearch.Full.Chores.Completion
