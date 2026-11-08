import EnvyFreeResearch.Full.ChoresComponentBudgetAsymptotic

namespace EnvyFreeResearch.Full.Chores.Parameters

theorem sharpFactor_mono : Monotone sharpFactor := by
  intro a b hab
  unfold sharpFactor
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (by decide) hab
  · exact (Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 3 hab))

theorem sharpLocal_mono : Monotone sharpLocal := by
  intro a b hab
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab _)) (sharpFactor_mono hab)

theorem sharpLocal_large {n : ℕ} (hn : 1 ≤ n) : 2 ≤ sharpLocal n := by
  have h1 : 1 ≤ n^12 := Nat.one_le_pow _ _ hn
  have h2 : 1 ≤ sharpFactor n := by
    unfold sharpFactor
    exact Nat.mul_le_mul (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by omega))
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 4096 h1) h2
  unfold sharpLocal
  omega

theorem uniform_local_sharp {n : ℕ} (hn : 3 ≤ n) :
    (∀ k, 0 < k → k ≤ n → nativeLocalQueries k ≤ sharpLocal n) ∧
    (∀ k, 0 < k → k ≤ n → nativeLocalCuts k ≤ sharpLocal n) := by
  have hlarge := sharpLocal_large (show 1 ≤ n by omega)
  constructor
  · intro k hk hkn
    by_cases hs : k ≤ 2
    · simpa only [nativeLocalQueries, ite_eq_left hs] using hlarge
    · rw [nativeLocalQueries, ite_eq_right hs]
      exact (local_sharp (by omega : 3 ≤ k)).1.trans (sharpLocal_mono hkn)
  · intro k hk hkn
    by_cases hs : k ≤ 2
    · simp only [nativeLocalCuts, ite_eq_left hs]; omega
    · rw [nativeLocalCuts, ite_eq_right hs]
      exact (local_sharp (by omega : 3 ≤ k)).2.trans (sharpLocal_mono hkn)

theorem total_capacity_sharp_polynomial {n : ℕ} (hn : 3 ≤ n) :
    n+(totalCapacity n).queries ≤ 32768*n^15*sharpFactor n ∧
    (totalCapacity n).cuts ≤ 32768*n^15*sharpFactor n := by
  obtain ⟨hQ,hC⟩ := uniform_local_sharp hn
  obtain ⟨hq,hc⟩ := Population.capacity_envelope nativeLocalQueries nativeLocalCuts n
    (sharpLocal n) (sharpLocal n) hQ hC
  change (totalCapacity n).queries ≤ _ at hq
  change (totalCapacity n).cuts ≤ _ at hc
  have hn1 : 1 ≤ n := by omega
  have hsub : 2*n-1 ≤ 2*n := Nat.sub_le _ _
  have hsq : 1 ≤ n^2 := Nat.one_le_pow _ _ hn1
  have h15 : n ≤ n^15 := Nat.le_self_pow (by decide) n
  have hf : 1 ≤ sharpFactor n := by
    unfold sharpFactor
    exact Nat.mul_le_mul (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by omega))
  have hnF : n ≤ n^15*sharpFactor n := h15.trans (by simpa using Nat.mul_le_mul_left (n^15) hf)
  have hq' := hq.trans (Nat.mul_le_mul_right _ hsub)
  have hc' := hc.trans (Nat.mul_le_mul_right _ hsub)
  have hp := Nat.mul_le_mul_right (8192*n^13*sharpFactor n) hsq
  unfold sharpLocal at hq' hc'
  constructor <;> nlinarith

theorem sharpFactor_le {n : ℕ} (hn : 1 ≤ n) :
    sharpFactor n ≤ n^(3*n)*2^(7*n) := by
  have hnext : n+1 ≤ 2*n := by omega
  calc
    sharpFactor n ≤ 16^n*(2*n)^(3*n) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnext _)
    _ = n^(3*n)*2^(7*n) := by
      rw [mul_pow, show (16:ℕ)=2^4 by norm_num, ← pow_mul]
      rw [show 7*n=4*n+3*n by ring, pow_add]
      ring

theorem sharp_polynomial_le {n : ℕ} (hn : 3 ≤ n) :
    32768*n^15*sharpFactor n ≤ n^(3*n)*2^(27*n) := by
  have hnpow : n ≤ 2^n := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ 32768*(2^n)^15*(n^(3*n)*2^(7*n)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnpow _)) (sharpFactor_le (by omega))
    _ = n^(3*n)*2^(22*n+15) := by
      rw [← pow_mul, show (32768:ℕ)=2^15 by norm_num]
      rw [show 22*n+15=15+n*15+7*n by ring, pow_add, pow_add]
      ring
    _ ≤ n^(3*n)*2^(27*n) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (by omega))

/-- Separate query/Cut budgets, including initial Evals, with sharp leading
coefficient 3. This is a scalar capacity statement, not an execution theorem. -/
theorem total_capacity_leading_exponent {n : ℕ} (hn : 3 ≤ n) :
    n+(totalCapacity n).queries ≤ n^(3*n)*2^(27*n) ∧
    (totalCapacity n).cuts ≤ n^(3*n)*2^(27*n) := by
  exact ⟨(total_capacity_sharp_polynomial hn).1.trans (sharp_polynomial_le hn),
    (total_capacity_sharp_polynomial hn).2.trans (sharp_polynomial_le hn)⟩

end EnvyFreeResearch.Full.Chores.Parameters
