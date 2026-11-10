import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunBudgetRemaining
import EnvyFreeResearch.Full.RefinedUpperGlobalRunBudgetTokens

/-! Finite-prefix call bounds for the actual dispatcher on every original
tape. Reachability invariants are obtained from the compiled concrete run. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
open RefinedUpperGlobalPhysical UpperCircularStage RefinedUpperGlobalTape
variable {n : ℕ}

def prefixSuccess (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) (kind : Kind) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, successIndicator policy chores kind
    (Phase.run policy fallback chores initial t omega) (omega t)

def prefixNormalizations (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, normalizeToken (Phase.run policy fallback chores initial t omega)

theorem prefix_success_succ (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) (kind : Kind) (T : ℕ) :
    prefixSuccess policy fallback chores initial omega kind (T+1)=
      prefixSuccess policy fallback chores initial omega kind T+
      successIndicator policy chores kind (Phase.run policy fallback chores initial T omega) (omega T) := by
  exact Finset.sum_range_succ _ _

theorem prefix_normalizations_succ (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) (T : ℕ) :
    prefixNormalizations policy fallback chores initial omega (T+1)=
      prefixNormalizations policy fallback chores initial omega T+
      normalizeToken (Phase.run policy fallback chores initial T omega) := by
  exact Finset.sum_range_succ _ _

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
  (initial : Phase n) (hinit : initial.Valid μ chores whole)
  (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy) (fallback : Fin n)
  (omega : Stream (Universal n))
include hinit hp

theorem prefix_snapshot_credit (T : ℕ) :
    credit chores initial+prefixSuccess policy fallback chores initial omega .snapshot T ≤
      credit chores (Phase.run policy fallback chores initial T omega) := by
  induction T with
  | zero => simp [prefixSuccess,phaseRun_zero]
  | succ T ih =>
    rw [prefix_success_succ]
    have hs := step_credit μ whole chores policy hp fallback
      (Phase.run policy fallback chores initial T omega)
      (run_valid μ whole chores initial hinit policy hp fallback T omega) (omega T)
    rw [← phaseRun_succ] at hs
    omega

theorem prefix_snapshot_bound (T : ℕ) :
    prefixSuccess policy fallback chores initial omega .snapshot T ≤ n*(n-1) := by
  have h1 := prefix_snapshot_credit μ whole chores initial hinit policy hp fallback omega T
  have h2 := valid_credit_le μ chores whole (Phase.run policy fallback chores initial T omega)
    (run_valid μ whole chores initial hinit policy hp fallback T omega)
  omega

theorem prefix_remaining_balance (T : ℕ) :
    prefixSuccess policy fallback chores initial omega .shrink T+
      prefixSuccess policy fallback chores initial omega .repair T+
      remainingCalls (Phase.run policy fallback chores initial T omega) ≤
      3*prefixSuccess policy fallback chores initial omega .snapshot T+remainingCalls initial := by
  induction T with
  | zero => simp [prefixSuccess,phaseRun_zero]
  | succ T ih =>
    rw [prefix_success_succ,prefix_success_succ,prefix_success_succ]
    have hs := step_remaining_calls μ whole chores policy hp fallback
      (Phase.run policy fallback chores initial T omega)
      (run_valid μ whole chores initial hinit policy hp fallback T omega) (omega T)
    rw [← phaseRun_succ] at hs
    omega

omit hinit hp in
theorem prefix_repair_balance (T : ℕ) :
    prefixSuccess policy fallback chores initial omega .repair T+
      pendingCredit (Phase.run policy fallback chores initial T omega) ≤
      prefixSuccess policy fallback chores initial omega .snapshot T+pendingCredit initial := by
  induction T with
  | zero => simp [prefixSuccess,phaseRun_zero]
  | succ T ih =>
    rw [prefix_success_succ,prefix_success_succ]
    have hs := step_pending_balance policy fallback chores
      (Phase.run policy fallback chores initial T omega) (omega T)
    rw [← phaseRun_succ] at hs
    omega

omit hinit hp in
theorem prefix_normalization_balance (T : ℕ) :
    prefixNormalizations policy fallback chores initial omega T+
      normalizeToken (Phase.run policy fallback chores initial T omega)=
      prefixSuccess policy fallback chores initial omega .repair T+normalizeToken initial := by
  induction T with
  | zero => simp [prefixNormalizations,prefixSuccess,phaseRun_zero]
  | succ T ih =>
    rw [prefix_normalizations_succ,prefix_success_succ]
    have hs := step_normalizeToken policy fallback chores
      (Phase.run policy fallback chores initial T omega) (omega T)
    rw [← phaseRun_succ] at hs
    omega

omit hinit in
theorem prefix_normalized_counts (a : Anchor n)
    (ha : (Phase.normalize a).Valid μ chores whole) (T : ℕ) :
    prefixSuccess policy fallback chores (.normalize a) omega .snapshot T ≤ n*(n-1) ∧
    prefixSuccess policy fallback chores (.normalize a) omega .shrink T+
      prefixSuccess policy fallback chores (.normalize a) omega .repair T ≤ 3*(n*(n-1)) ∧
    prefixSuccess policy fallback chores (.normalize a) omega .repair T ≤ n*(n-1) ∧
    prefixNormalizations policy fallback chores (.normalize a) omega T ≤ n*(n-1)+1 := by
  have hs := prefix_snapshot_bound μ whole chores (.normalize a) ha policy hp fallback omega T
  have ho := prefix_remaining_balance μ whole chores (.normalize a) ha policy hp fallback omega T
  have hr := prefix_repair_balance chores (.normalize a) policy fallback omega T
  have hn := prefix_normalization_balance chores (.normalize a) policy fallback omega T
  simp only [pendingCredit,remainingCalls,normalizeToken] at ho hr hn
  omega

end EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
