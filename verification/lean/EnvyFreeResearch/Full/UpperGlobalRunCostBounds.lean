import EnvyFreeResearch.Full.UpperGlobalProtocolCostLedger
import EnvyFreeResearch.Full.UpperGlobalRunTerminationCounts
import EnvyFreeResearch.Full.UpperGlobalRunBudgetTokens

/-! Actual query and Cut totals, including rejected attempts, are charged to
the actual paid-call count and actual normalization count. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape UpperExpectedRuntime UpperGlobalRunBudget IntervalOracle
variable {n : ℕ}

def paidToken : Phase n → ℕ
  | .normalize _ | .done _ => 0
  | _ => 1

theorem queryCap_tokens (phase : Phase n) :
    phase.queryCap ≤ (12*n*UpperRepair.fine n)*paidToken phase + (n+1)*normalizeToken phase := by
  cases phase <;> simp only [Phase.queryCap,paidToken,normalizeToken,Nat.mul_zero,
    Nat.mul_one,Nat.zero_add,Nat.add_zero] <;> nlinarith

theorem cutCap_tokens (phase : Phase n) :
    phase.cutCap ≤ (6*UpperRepair.fine n)*paidToken phase + normalizeToken phase := by
  cases phase <;> simp only [Phase.cutCap,paidToken,normalizeToken,Nat.mul_zero,
    Nat.mul_one,Nat.zero_add,Nat.add_zero] <;> omega

theorem paidCount_eq_tokens (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n)) :
    paidCount policy fallback chores initial omega =
      ∑' t, (paidToken (Phase.run policy fallback chores initial t omega) : ℝ≥0∞) := by
  unfold paidCount attempts
  calc
    _ = ∑' kind, ∑' t,
        (paidEvent policy fallback chores initial kind t).indicator (fun _ => (1:ℝ≥0∞)) omega :=
      (tsum_fintype _).symm
    _ = ∑' t, ∑' kind,
        (paidEvent policy fallback chores initial kind t).indicator (fun _ => (1:ℝ≥0∞)) omega :=
      ENNReal.tsum_comm
    _ = _ := by
      congr 1
      funext t
      rw [tsum_fintype]
      rw [show (Finset.univ : Finset Kind)={.snapshot,.shrink,.repair} from rfl]
      cases hs : Phase.run policy fallback chores initial t omega <;>
        simp [paidEvent,hs,Phase.paidKind,paidToken]

theorem queryCap_sum_le (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n)) :
    (∑' t, ((Phase.run policy fallback chores initial t omega).queryCap : ℝ≥0∞)) ≤
      (12*n*UpperRepair.fine n : ℕ)*paidCount policy fallback chores initial omega +
      (n+1 : ℕ)*(∑' t, (normalizeToken (Phase.run policy fallback chores initial t omega) : ℝ≥0∞)) := by
  rw [paidCount_eq_tokens,← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_left,← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro t
  exact_mod_cast queryCap_tokens (Phase.run policy fallback chores initial t omega)

theorem cutCap_sum_le (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n)) :
    (∑' t, ((Phase.run policy fallback chores initial t omega).cutCap : ℝ≥0∞)) ≤
      (6*UpperRepair.fine n : ℕ)*paidCount policy fallback chores initial omega +
      (∑' t, (normalizeToken (Phase.run policy fallback chores initial t omega) : ℝ≥0∞)) := by
  rw [paidCount_eq_tokens,← ENNReal.tsum_mul_left,← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro t
  exact_mod_cast cutCap_tokens (Phase.run policy fallback chores initial t omega)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
    (initial : Phase n) (hinit : initial.Valid μ chores whole)
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (fallback : Fin n) (omega : Stream (Universal n))
include hinit horacle

theorem actual_query_tokens :
    totalQueries (AdaptiveOracle.answer oracle) fallback chores initial omega ≤
      (12*n*UpperRepair.fine n : ℕ)*paidCount (AdaptiveOracle.answer oracle) fallback chores initial omega +
      (n+1 : ℕ)*(∑' t, (normalizeToken (Phase.run (AdaptiveOracle.answer oracle)
        fallback chores initial t omega) : ℝ≥0∞)) :=
  (actual_total_queries_le μ whole chores initial hinit oracle horacle fallback omega).trans
    (queryCap_sum_le _ _ _ _ _)

theorem actual_cut_tokens :
    totalCuts (AdaptiveOracle.answer oracle) fallback chores initial omega ≤
      (6*UpperRepair.fine n : ℕ)*paidCount (AdaptiveOracle.answer oracle) fallback chores initial omega +
      (∑' t, (normalizeToken (Phase.run (AdaptiveOracle.answer oracle)
        fallback chores initial t omega) : ℝ≥0∞)) :=
  (actual_total_cuts_le μ whole chores initial hinit oracle horacle fallback omega).trans
    (cutCap_sum_le _ _ _ _ _)

end EnvyFreeResearch.Full.UpperGlobalPhysical
