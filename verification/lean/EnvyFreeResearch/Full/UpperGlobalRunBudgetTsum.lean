import EnvyFreeResearch.Full.UpperGlobalRunBudgetPrefix
import EnvyFreeResearch.Full.UpperExpectedRuntime

/-! Pathwise infinite-stream budgets for the actual successful calls. The
finite-prefix proofs pass to ENNReal sums without a termination assumption. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalRunBudget
open UpperGlobalPhysical UpperCircularStage UpperGlobalTape UpperExpectedRuntime
variable {n : ℕ}

theorem success_indicator_cast (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (kind : Kind) (t : ℕ) (omega : Stream (Universal n)) :
    (successIndicator policy chores kind (Phase.run policy fallback chores initial t omega) (omega t) : ℝ≥0∞)=
      (successEvent policy fallback chores initial kind t).indicator (fun _ => (1 : ℝ≥0∞)) omega := by
  unfold successIndicator successEvent
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq]
  split_ifs <;> norm_num

theorem success_prefix_cast (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (kind : Kind) (omega : Stream (Universal n)) (T : ℕ) :
    (∑ t ∈ Finset.range T,
      (successEvent policy fallback chores initial kind t).indicator (fun _ => (1 : ℝ≥0∞)) omega)=
      (prefixSuccess policy fallback chores initial omega kind T : ℝ≥0∞) := by
  simp_rw [← success_indicator_cast]
  simp only [prefixSuccess,Nat.cast_sum]

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
  (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy) (fallback : Fin n)
  (a : Anchor n) (ha : (Phase.normalize a).Valid μ chores whole)
  (omega : Stream (Universal n))
include ha hp

theorem snapshot_success_count :
    attempts (successEvent policy fallback chores (.normalize a) .snapshot) omega ≤ (n*(n-1) : ℕ) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro T
  rw [success_prefix_cast]
  exact_mod_cast (prefix_normalized_counts μ whole chores policy hp fallback omega a ha T).1

theorem other_success_count :
    attempts (successEvent policy fallback chores (.normalize a) .shrink) omega+
      attempts (successEvent policy fallback chores (.normalize a) .repair) omega ≤ (3*(n*(n-1)) : ℕ) := by
  unfold attempts
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_of_sum_range_le
  intro T
  rw [Finset.sum_add_distrib,success_prefix_cast,success_prefix_cast,← Nat.cast_add]
  exact_mod_cast (prefix_normalized_counts μ whole chores policy hp fallback omega a ha T).2.1

theorem repair_success_count :
    attempts (successEvent policy fallback chores (.normalize a) .repair) omega ≤ (n*(n-1) : ℕ) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro T
  rw [success_prefix_cast]
  exact_mod_cast (prefix_normalized_counts μ whole chores policy hp fallback omega a ha T).2.2.1

theorem normalization_count :
    (∑' t, (normalizeToken (Phase.run policy fallback chores (.normalize a) t omega) : ℝ≥0∞)) ≤
      (n*(n-1)+1 : ℕ) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro T
  rw [← Nat.cast_sum]
  exact_mod_cast (prefix_normalized_counts μ whole chores policy hp fallback omega a ha T).2.2.2

end EnvyFreeResearch.Full.UpperGlobalRunBudget
