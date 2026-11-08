import EnvyFreeResearch.Full.ChoresComponentBudgetGlobal

/-! Leading-exponent envelope for the actual scalar recurrence.
Execution and local call-count obligations are separate. -/
namespace EnvyFreeResearch.Full.Chores.Parameters

def sharpFactor (n : ℕ) : ℕ := 16^n*(n+1)^(3*n)
def sharpLocal (n : ℕ) : ℕ := 4096*n^12*sharpFactor n

theorem snapshots_polynomial {n : ℕ} (hn : 3 ≤ n) :
    snapshots n ≤ 58*roots n*n^6 := by
  have hn1 : 1 ≤ n := by omega
  have h23 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn1 (by decide)
  have hell : ell n+1 ≤ 2*n := by have := ell_le n; omega
  have hweight : weight n ≤ 2*n^2 := by unfold weight; nlinarith
  have hp : 1 ≤ n^6 := Nat.one_le_pow _ _ hn1
  have ha := Nat.mul_le_mul h23 (Nat.le_refl (14*n*weight n))
  have hb := Nat.mul_le_mul_left (28*n^4) hweight
  unfold snapshots tracked length
  nlinarith [Nat.mul_le_mul_left (roots n) hp, Nat.mul_le_mul_left (roots n) hb,
    Nat.mul_le_mul_left (roots n) ha]

theorem roots_polynomial {n : ℕ} (hn : 1 ≤ n) :
    roots n ≤ 4*n^2*4^n*(n+1)^(3*n) := by
  calc
    roots n ≤ n*selected n := roots_le hn
    _ ≤ n*((4*n*4^n)*(n+1)^(3*n)) := by
      unfold selected
      gcongr
      · exact classes_base_le hn
      · unfold exponent; omega
    _ = _ := by ring

theorem reference_sharp {n : ℕ} (hn : 3 ≤ n) :
    referenceBudget n ≤ 512*n^11*sharpFactor n := by
  have hn1 : 1 ≤ n := by omega
  have h4 : 4^n*4^n=16^n := by rw [← mul_pow]; norm_num
  have h2 : 2^n ≤ 4^n := Nat.pow_le_pow_left (by decide) _
  have h16 : 2^n ≤ 16^n := Nat.pow_le_pow_left (by decide) _
  have hpre : snapshots n*IntervalCore.queryBudget n ≤ 464*n^11*sharpFactor n := by
    calc
      _ ≤ (58*(4*n^2*4^n*(n+1)^(3*n))*n^6)*(2*n^3*4^n) :=
        Nat.mul_le_mul ((snapshots_polynomial hn).trans (by gcongr; exact roots_polynomial hn1))
          (core_polynomial hn1)
      _ = _ := by unfold sharpFactor; calc
        _ = 464*n^11*(4^n*4^n)*(n+1)^(3*n) := by ring
        _ = _ := by rw [h4]; ring
  have hgroup : roots n*(n*2^(n+1)) ≤ 8*n^11*sharpFactor n := by
    calc
      _ ≤ (4*n^2*4^n*(n+1)^(3*n))*(n*(2*4^n)) := by
        gcongr
        · exact roots_polynomial hn1
        · simpa only [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 h2
      _ = 8*n^3*(4^n*4^n)*(n+1)^(3*n) := by ring
      _ ≤ 8*n^11*sharpFactor n := by
        rw [h4]
        have hh := Nat.mul_le_mul_right (8*16^n*(n+1)^(3*n))
          (Nat.pow_le_pow_right hn1 (show 3 ≤ 11 by decide))
        unfold sharpFactor
        nlinarith
  have hcomplete : 19*n*2^n ≤ 19*n^11*sharpFactor n := by
    calc
      _ ≤ 19*n^11*16^n := by gcongr; exact Nat.le_self_pow (by decide) n
      _ ≤ 19*n^11*sharpFactor n := by
        unfold sharpFactor
        have hh := Nat.one_le_pow (3*n) (n+1) (by omega)
        have hh2 := Nat.mul_le_mul_left (19*n^11*16^n) hh
        nlinarith
  unfold referenceBudget
  nlinarith

theorem local_sharp {n : ℕ} (hn : 3 ≤ n) :
    localQueries n ≤ sharpLocal n ∧ localCuts n ≤ sharpLocal n := by
  have hq := (actual_queries_reference hn).trans (Nat.mul_le_mul_left (5*n) (reference_sharp hn))
  have hc := (actual_cuts_reference hn).trans (Nat.mul_le_mul_left 2 (reference_sharp hn))
  have hp : n^11 ≤ n^12 := Nat.pow_le_pow_right (by omega) (by decide)
  constructor
  · unfold sharpLocal; nlinarith
  · unfold sharpLocal; nlinarith [Nat.mul_le_mul_right (sharpFactor n) hp]

end EnvyFreeResearch.Full.Chores.Parameters
