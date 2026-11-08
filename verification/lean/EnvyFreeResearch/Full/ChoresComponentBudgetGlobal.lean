import EnvyFreeResearch.Full.ChoresComponentBudgetLocal
import EnvyFreeResearch.Full.ChoresComponentPopulationCapacity

/-! The explicit 2^(14*n*(ceil(log₂ n)+1)) envelope absorbs actual physical
snapshot/compensation costs, proper-population recursion and all ancestor
recording, plus n initial whole-domain Evals. This is the scalar recurrence
bound; the unfinished outer driver must instantiate its local call counts. -/

namespace EnvyFreeResearch.Full.Chores.Parameters

def nativeLocalQueries (n : ℕ) : ℕ := if n ≤ 2 then 2 else localQueries n
def nativeLocalCuts (n : ℕ) : ℕ := if n ≤ 2 then 1 else localCuts n
noncomputable def totalCapacity (n : ℕ) : Population.Capacity :=
  Population.capacity nativeLocalQueries nativeLocalCuts n

theorem uniform_local_binary {n : ℕ} (hn : 3 ≤ n) :
    (∀ k, 0 < k → k ≤ n → nativeLocalQueries k ≤ 5*n*2^(12*weight n)) ∧
      (∀ k, 0 < k → k ≤ n → nativeLocalCuts k ≤ 2*2^(12*weight n)) := by
  have hpow : 1 ≤ 2^(12*weight n) := Nat.one_le_two_pow
  constructor
  · intro k hk hkn
    by_cases hsmall : k ≤ 2
    · rw [nativeLocalQueries, ite_eq_left hsmall]
      have hh := Nat.mul_le_mul_left (5*n) hpow
      omega
    · rw [nativeLocalQueries, ite_eq_right hsmall]
      exact (actual_queries_binary (by omega : 3 ≤ k)).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left 5 hkn)
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 12 (weight_mono hkn))))
  · intro k hk hkn
    by_cases hsmall : k ≤ 2
    · rw [nativeLocalCuts, ite_eq_left hsmall]
      omega
    · rw [nativeLocalCuts, ite_eq_right hsmall]
      exact (actual_cuts_binary (by omega : 3 ≤ k)).trans
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_left 12 (weight_mono hkn))))

theorem total_capacity_binary {n : ℕ} (hn : 3 ≤ n) :
    (totalCapacity n).queries ≤ (2*n-1)*(5*n+2*n^2)*2^(12*weight n) ∧
      (totalCapacity n).cuts ≤ (2*n-1)*2*2^(12*weight n) := by
  obtain ⟨hQ, hC⟩ := uniform_local_binary hn
  obtain ⟨hq, hc⟩ := Population.capacity_envelope nativeLocalQueries nativeLocalCuts n
    (5*n*2^(12*weight n)) (2*2^(12*weight n)) hQ hC
  exact ⟨by simpa only [totalCapacity] using hq.trans_eq (by ring),
    by simpa only [totalCapacity] using hc.trans_eq (by ring)⟩

theorem population_prefactor {n : ℕ} (hn : 3 ≤ n) :
    (2*n-1)*(5*n+2*n^2)+n ≤ 2^(2*weight n) := by
  have hn1 : 1 ≤ n := by omega
  have hn3 : n ≤ n^3 := by simpa using Nat.pow_le_pow_right hn1 (show 1 ≤ 3 by decide)
  have hn2 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn1 (by decide)
  have hprod := Nat.mul_le_mul_right (5*n+2*n^2) (Nat.sub_le (2*n) 1)
  have hpoly : (2*n-1)*(5*n+2*n^2)+n ≤ 16*n^3 := by nlinarith
  have hnpow : n ≤ 2^n := Nat.le_of_lt Nat.lt_two_pow_self
  have hw := weight_lower hn
  calc
    _ ≤ 16*n^3 := hpoly
    _ ≤ 16*(2^n)^3 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hnpow 3)
    _ = 2^(4+n*3) := by rw [← pow_mul]; simp only [pow_add]; norm_num
    _ ≤ 2^(2*weight n) := Nat.pow_le_pow_right (by decide) (by omega)

/-- The initial n whole-domain Evals are included in the explicit envelope. -/
theorem total_with_initial_evals {n : ℕ} (hn : 3 ≤ n) :
    n+(totalCapacity n).queries ≤ 2^(14*weight n) := by
  have hq := (total_capacity_binary hn).1
  have hpow : 1 ≤ 2^(12*weight n) := Nat.one_le_two_pow
  have hnrecord : n ≤ n*2^(12*weight n) := by simpa using Nat.mul_le_mul_left n hpow
  calc
    n+(totalCapacity n).queries ≤ n*2^(12*weight n)+(2*n-1)*(5*n+2*n^2)*2^(12*weight n) :=
      Nat.add_le_add hnrecord hq
    _ = ((2*n-1)*(5*n+2*n^2)+n)*2^(12*weight n) := by ring
    _ ≤ 2^(2*weight n)*2^(12*weight n) := Nat.mul_le_mul_right _ (population_prefactor hn)
    _ = 2^(14*weight n) := by rw [← pow_add]; congr 1; ring

end EnvyFreeResearch.Full.Chores.Parameters
