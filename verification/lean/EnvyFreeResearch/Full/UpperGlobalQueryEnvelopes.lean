import EnvyFreeResearch.Full.UpperRepair

/-! Scalar envelopes include paid initialization and every reached
normalization, as well as the all-attempt randomized ledger. These arithmetic
lemmas do not replace the execution and expected-count proofs. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalBounds

theorem stages_le_square (n : ℕ) (hn : 1 ≤ n) : n*(n-1)+1 ≤ n^2 := by
  have he : n*(n-1)+n = n*n := by
    calc
      _ = n*((n-1)+1) := by ring
      _ = n*n := by rw [Nat.sub_add_cancel hn]
  nlinarith

theorem normalization_queries (n : ℕ) (hn : 1 ≤ n) :
    (n*(n-1)+1)*(n+1)+2*n ≤ 4*n^3 := by
  have hstage := stages_le_square n hn
  have hn3 : n ≤ n^3 := by
    calc
      n = n*1*1 := by ring
      _ ≤ n*n*n := Nat.mul_le_mul (Nat.mul_le_mul_left n hn) hn
      _ = n^3 := by ring
  calc
    _ ≤ n^2*(2*n)+2*n^3 := Nat.add_le_add
      (Nat.mul_le_mul hstage (by omega)) (Nat.mul_le_mul_left 2 hn3)
    _ = _ := by ring

theorem query_ledger (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    96*n*n*(n-1)*m + (n*(n-1)+1)*(n+1)+2*n ≤ 100*n^3*m := by
  have hpaid : 96*n*n*(n-1)*m ≤ 96*n^3*m := by
    calc
      _ ≤ 96*n*n*n*m := Nat.mul_le_mul_right m
        (Nat.mul_le_mul_left (96*n*n) (Nat.sub_le n 1))
      _ = _ := by ring
  have hnorm := normalization_queries n hn
  have hm' : 4*n^3 ≤ 4*n^3*m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4*n^3) hm
  calc
    _ = 96*n*n*(n-1)*m + ((n*(n-1)+1)*(n+1)+2*n) := by omega
    _ ≤ 96*n^3*m + 4*n^3*m := Nat.add_le_add hpaid (hnorm.trans hm')
    _ = _ := by ring

theorem cut_ledger (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    48*n*(n-1)*m + (n*(n-1)+1) ≤ 49*n^2*m := by
  have hpaid : 48*n*(n-1)*m ≤ 48*n^2*m := by
    calc
      _ ≤ 48*n*n*m := Nat.mul_le_mul_right m
        (Nat.mul_le_mul_left (48*n) (Nat.sub_le n 1))
      _ = _ := by ring
  have hnorm : n*(n-1)+1 ≤ n^2*m := (stages_le_square n hn).trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n^2) hm)
  calc
    _ ≤ 48*n^2*m + n^2*m := Nat.add_le_add hpaid hnorm
    _ = _ := by ring

def sampleConstant : ℝ := (2^42 : ℝ)^18 * 45^2

theorem query_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ((100*n^3*UpperRepair.fine n : ℕ) : ℝ) ≤
      (100*sampleConstant)*(n : ℝ)^21*(Real.log (2*(n : ℝ))/Real.log 2)^2 := by
  have hs := UpperRepairParameters.samples_polynomial n hn
  have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 100*(n : ℝ)^3)
  push_cast
  change 100*(n : ℝ)^3*(UpperRepairParameters.samples
    (UpperRepairParameters.scale n) (UpperRepairParameters.logarithm (UpperRepairParameters.scale n)) : ℝ) ≤ _
  calc
    _ ≤ 100*(n : ℝ)^3 * (((2^42 : ℝ)^18*45^2)*(n : ℝ)^18*
      (Real.log (2*(n : ℝ))/Real.log 2)^2) := h
    _ = _ := by unfold sampleConstant; ring

theorem cut_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ((49*n^2*UpperRepair.fine n : ℕ) : ℝ) ≤
      (49*sampleConstant)*(n : ℝ)^20*(Real.log (2*(n : ℝ))/Real.log 2)^2 := by
  have hs := UpperRepairParameters.samples_polynomial n hn
  have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 49*(n : ℝ)^2)
  push_cast
  change 49*(n : ℝ)^2*(UpperRepairParameters.samples
    (UpperRepairParameters.scale n) (UpperRepairParameters.logarithm (UpperRepairParameters.scale n)) : ℝ) ≤ _
  calc
    _ ≤ 49*(n : ℝ)^2 * (((2^42 : ℝ)^18*45^2)*(n : ℝ)^18*
      (Real.log (2*(n : ℝ))/Real.log 2)^2) := h
    _ = _ := by unfold sampleConstant; ring

end EnvyFreeResearch.Full.UpperGlobalBounds
