import EnvyFreeResearch.Full.RefinedUpperParameterCounts
import EnvyFreeResearch.Full.UpperGlobalQueryEnvelopes

/-! Convert the existing generic all-attempt ledger to the new integral
sample count. These are adapters for a physical execution ledger, not a
standalone existence claim for the revised global protocol. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalBudgetAdapter
open RefinedUpperParameterCounts
open UpperRepairParameters (scale logarithm)
open scoped ENNReal

def fine (n : ℕ) : ℕ := samples (scale n) (logarithm (scale n))
def sampleConstant : ℝ := (2^42:ℝ)^9*45/128

theorem fine_positive (n : ℕ) : 1 ≤ fine n := by
  have hs : 256 ≤ scale n := by
    have h := UpperRepairParameters.scale_large n
    exact_mod_cast (show (256:ℝ) ≤ scale n by norm_num at h ⊢; linarith)
  exact samples_positive hs (UpperRepairParameters.logarithm_positive (UpperRepairParameters.scale_large n))

theorem query_ledger (n : ℕ) (hn : 1 ≤ n) :
    96*n*n*(n-1)*fine n+(n*(n-1)+1)*(n+1)+2*n ≤ 100*n^3*fine n :=
  UpperGlobalBounds.query_ledger n (fine n) hn (fine_positive n)

theorem cut_ledger (n : ℕ) (hn : 1 ≤ n) :
    48*n*(n-1)*fine n+(n*(n-1)+1) ≤ 49*n^2*fine n :=
  UpperGlobalBounds.cut_ledger n (fine n) hn (fine_positive n)

theorem query_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ((100*n^3*fine n:ℕ):ℝ) ≤
      (100*sampleConstant)*(n:ℝ)^12*(Real.log (2*(n:ℝ))/Real.log 2) := by
  have hs := samples_polynomial n hn
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤100*(n:ℝ)^3)
  push_cast
  change 100*(n:ℝ)^3*(samples (scale n) (logarithm (scale n)):ℝ) ≤ _
  calc
    _ ≤ 100*(n:ℝ)^3*(((2^42:ℝ)^9*45/128)*(n:ℝ)^9*(Real.log (2*(n:ℝ))/Real.log 2)) := hh
    _ = _ := by unfold sampleConstant; ring

theorem cut_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ((49*n^2*fine n:ℕ):ℝ) ≤
      (49*sampleConstant)*(n:ℝ)^11*(Real.log (2*(n:ℝ))/Real.log 2) := by
  have hs := samples_polynomial n hn
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤49*(n:ℝ)^2)
  push_cast
  change 49*(n:ℝ)^2*(samples (scale n) (logarithm (scale n)):ℝ) ≤ _
  calc
    _ ≤ 49*(n:ℝ)^2*(((2^42:ℝ)^9*45/128)*(n:ℝ)^9*(Real.log (2*(n:ℝ))/Real.log 2)) := hh
    _ = _ := by unfold sampleConstant; ring

/-- Only the all-attempt ledger enters this final arithmetic conversion. -/
theorem query_from_ledger {q : ℝ≥0∞} (n : ℕ) (hn : 1 ≤ n)
    (hq : q ≤ ((96*n*n*(n-1)*fine n+(n*(n-1)+1)*(n+1)+2*n:ℕ):ℝ≥0∞)) :
    q ≤ ENNReal.ofReal ((100*sampleConstant)*(n:ℝ)^12*(Real.log (2*(n:ℝ))/Real.log 2)) := by
  have hnat : ((96*n*n*(n-1)*fine n+(n*(n-1)+1)*(n+1)+2*n:ℕ):ℝ≥0∞) ≤
      ((100*n^3*fine n:ℕ):ℝ≥0∞) := by exact_mod_cast query_ledger n hn
  have hpoly := ENNReal.ofReal_le_ofReal (query_polynomial n hn)
  rw [ENNReal.ofReal_natCast] at hpoly
  exact hq.trans (hnat.trans hpoly)

theorem cut_from_ledger {c : ℝ≥0∞} (n : ℕ) (hn : 1 ≤ n)
    (hc : c ≤ ((48*n*(n-1)*fine n+(n*(n-1)+1):ℕ):ℝ≥0∞)) :
    c ≤ ENNReal.ofReal ((49*sampleConstant)*(n:ℝ)^11*(Real.log (2*(n:ℝ))/Real.log 2)) := by
  have hnat : ((48*n*(n-1)*fine n+(n*(n-1)+1):ℕ):ℝ≥0∞) ≤
      ((49*n^2*fine n:ℕ):ℝ≥0∞) := by exact_mod_cast cut_ledger n hn
  have hpoly := ENNReal.ofReal_le_ofReal (cut_polynomial n hn)
  rw [ENNReal.ofReal_natCast] at hpoly
  exact hc.trans (hnat.trans hpoly)

end EnvyFreeResearch.Full.RefinedUpperGlobalBudgetAdapter
