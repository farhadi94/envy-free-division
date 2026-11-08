import EnvyFreeResearch.Full.UpperGlobalRunCostBounds
import EnvyFreeResearch.Full.UpperGlobalRunBudgetTsum

/-! Exact operational costs are integrated after the concrete pathwise
normalization budget. The paid-call mean is supplied by the actual fresh-tape
success analysis; it is kept explicit in this accounting adapter. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape UpperGlobalRunBudget IntervalOracle
variable {n : ℕ}
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
  (a : Anchor n) (ha : (Phase.normalize a).Valid μ chores whole)
  (oracle : AdaptiveOracle.Policy (Query n) ℝ)
  (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
  (fallback : Fin n)
include ha horacle

theorem actual_query_ledger (omega : Stream (Universal n)) :
    totalQueries (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega ≤
      (12*n*UpperRepair.fine n : ℕ)*paidCount (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega +
      ((n+1)*(n*(n-1)+1) : ℕ) := by
  have hnorm := normalization_count μ whole chores (AdaptiveOracle.answer oracle)
    (UpperQueryLegality.answer_admissible _ oracle horacle) fallback a ha omega
  have h := actual_query_tokens μ whole chores (.normalize a) ha oracle horacle fallback omega
  apply h.trans
  push_cast at hnorm ⊢
  gcongr

theorem actual_cut_ledger (omega : Stream (Universal n)) :
    totalCuts (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega ≤
      (6*UpperRepair.fine n : ℕ)*paidCount (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega +
      (n*(n-1)+1 : ℕ) := by
  have hnorm := normalization_count μ whole chores (AdaptiveOracle.answer oracle)
    (UpperQueryLegality.answer_admissible _ oracle horacle) fallback a ha omega
  apply (actual_cut_tokens μ whole chores (.normalize a) ha oracle horacle fallback omega).trans
  gcongr

theorem expected_actual_costs (law : Measure (Stream (Universal n))) [IsProbabilityMeasure law]
    (hpaid : Measurable (paidCount (AdaptiveOracle.answer oracle) fallback chores (.normalize a)))
    (hmean : (∫⁻ omega, paidCount (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega ∂law) ≤
      (8*(n*(n-1)) : ℕ)) :
    (∫⁻ omega, totalQueries (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega ∂law) ≤
      (96*n*n*(n-1)*UpperRepair.fine n + (n+1)*(n*(n-1)+1) : ℕ) ∧
    (∫⁻ omega, totalCuts (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega ∂law) ≤
      (48*n*(n-1)*UpperRepair.fine n + (n*(n-1)+1) : ℕ) := by
  constructor
  · calc
      _ ≤ ∫⁻ omega, (12*n*UpperRepair.fine n : ℕ)*
          paidCount (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega +
          ((n+1)*(n*(n-1)+1) : ℕ) ∂law :=
        lintegral_mono (actual_query_ledger μ whole chores a ha oracle horacle fallback)
      _ = (12*n*UpperRepair.fine n : ℕ)*
          (∫⁻ omega, paidCount (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega ∂law) +
          ((n+1)*(n*(n-1)+1) : ℕ) := by
        rw [lintegral_add_right _ measurable_const,lintegral_const_mul _ hpaid]
        simp
      _ ≤ (12*n*UpperRepair.fine n : ℕ)*(8*(n*(n-1)) : ℕ) +
          ((n+1)*(n*(n-1)+1) : ℕ) :=
        by gcongr
      _ = _ := by push_cast; ring
  · calc
      _ ≤ ∫⁻ omega, (6*UpperRepair.fine n : ℕ)*
          paidCount (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega +
          (n*(n-1)+1 : ℕ) ∂law :=
        lintegral_mono (actual_cut_ledger μ whole chores a ha oracle horacle fallback)
      _ = (6*UpperRepair.fine n : ℕ)*
          (∫⁻ omega, paidCount (AdaptiveOracle.answer oracle) fallback chores (.normalize a) omega ∂law) +
          (n*(n-1)+1 : ℕ) := by
        rw [lintegral_add_right _ measurable_const,lintegral_const_mul _ hpaid]
        simp
      _ ≤ (6*UpperRepair.fine n : ℕ)*(8*(n*(n-1)) : ℕ) + (n*(n-1)+1 : ℕ) :=
        by gcongr
      _ = _ := by push_cast; ring

end EnvyFreeResearch.Full.UpperGlobalPhysical
