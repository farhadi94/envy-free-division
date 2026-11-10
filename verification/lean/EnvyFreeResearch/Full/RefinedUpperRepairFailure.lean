import EnvyFreeResearch.Full.RefinedUpperRepairProbability
import EnvyFreeResearch.Full.RefinedUpperFailureAllowances
import EnvyFreeResearch.Full.RefinedUpperRepair

/-! The actual finite Repair rejects with probability below 1/64 at the
revised original-population parameters, for both cake and chores. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperRepairProbability
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  RefinedUpperParameterCounts RefinedUpperRepairParameters RefinedUpperFailureAllowances
  RefinedUpperRepairLaw RefinedUpperRepairEvents RefinedUpperActualCorrectionBound
open UpperRepairParameters (scale logarithm scale_large logarithm_positive active_scale)

theorem failure_sum_small {k s ell : ℕ} (hkpos : 0 < k) (hs : (2^42 : ℝ) ≤ s)
    (he : 1 ≤ ell) (hk : (2^40 : ℝ)*k ≤ s)
    (hlog : Real.log (2*(k : ℝ)) ≤ ell) (hpow : 2*(s : ℝ) ≤ (2 : ℝ)^ell) :
    ENNReal.ofReal ((((4*(UpperLogicalIsolation.requests k (repetitions s ell)).length+
      4*(finalJobs k).length : ℕ) : ℝ)/(samples s ell+1 : ℕ))/badThreshold k) +
      ENNReal.ofReal (UpperLogicalIsolation.isolationBound k (repetitions s ell) (multiplier s)) +
      (k : ℝ≥0∞)*(firstBadAllowance k+retryAllowance^ell) < 1/64 := by
  have hs256 : (256 : ℝ) ≤ s := (by norm_num : (256 : ℝ)≤2^42).trans hs
  have hsp : (0 : ℝ)<s := by linarith
  have hs2 : 2 ≤ s := by exact_mod_cast (show (2 : ℝ) ≤ s by linarith)
  have hk0 : (0 : ℝ)≤k := Nat.cast_nonneg k
  have hk256 : (256 : ℝ)*k ≤ s := by nlinarith
  have hks : (k : ℝ) ≤ s := by nlinarith
  have hx : (k : ℝ)/s ≤ 1/256 := (div_le_iff₀ hsp).mpr (by linarith)
  have hy : (k : ℝ)/(4*(s : ℝ)^2) ≤ 1/1024 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*(s : ℝ)^2)).mpr
    nlinarith [mul_nonneg (hsp.le) (sub_nonneg.mpr hs256)]
  have hreal := RefinedUpperRejectionParameters.four_failures_small
    (div_nonneg hk0 hsp.le) hx hy
  have hg := ENNReal.ofReal_le_ofReal
    (RefinedUpperStabilityChargeBudget.numerical_markov_bound k s ell hs2 he)
  have hg' : ENNReal.ofReal ((((4*(UpperLogicalIsolation.requests k (repetitions s ell)).length+
      4*(finalJobs k).length : ℕ) : ℝ)/(samples s ell+1 : ℕ))/badThreshold k) ≤
        ENNReal.ofReal ((2 : ℝ)^23*((k : ℝ)/s)^5) := by
    simpa only [RefinedUpperStabilityChargeBudget.endpointCharge,finalJobs,badThreshold,
      Nat.cast_add,Nat.cast_one] using hg
  have hc := ENNReal.ofReal_le_ofReal (isolation_bound (by omega : 1 ≤ k) (by omega : 1 ≤ s) he hlog)
  have hf := retry_total hkpos (by omega : 0 < s) hpow
  apply (add_le_add (add_le_add hg' hc) hf).trans_lt
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ)<1/64)).mpr
    (show (2 : ℝ)^23*((k : ℝ)/s)^5+13*((k : ℝ)/s)^3+
      (1/5376+(k : ℝ)/(4*(s : ℝ)^2))<1/64 by linarith)
  have h64 : ENNReal.ofReal (1/64 : ℝ) = (1/64 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [h64] at hlt
  exact hlt

variable {n k : ℕ} [Nonempty (Fin k)]
theorem original_population_failure_lt
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : UpperRepairPreparationChecks.Near chores μ active origin old (oldError (scale n))) :
    trialLaw k (samples (scale n) (logarithm (scale n)))
      (repetitions (scale n) (logarithm (scale n))) (logarithm (scale n))
      (failed policy hk chores active origin old (coarseCount (scale n) (logarithm (scale n)))
        (fineCap (scale n) (logarithm (scale n))) (multiplier (scale n))) < 1/64 := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hs := scale_large n
  have he := logarithm_positive hs
  have her : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast he
  have ha := active_scale n k hkn
  have hs256 : 256 ≤ scale n := by exact_mod_cast ((by norm_num : (256 : ℝ)≤2^42).trans hs)
  have hk256 : 256*k ≤ scale n := by
    exact_mod_cast (show (256 : ℝ)*k ≤ scale n by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  have hsize : 16*(k : ℝ) ≤ multiplier (scale n) := by
    unfold multiplier
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have henvelope : ENNReal.ofReal
      (8*fineCap (scale n) (logarithm (scale n))*(2*(samples (scale n) (logarithm (scale n)) : ℝ))/
        multiplier (scale n)) ≤ retryAllowance := by
    rw [multiplier,RefinedUpperRejectionParameters.envelope_allowance
      (by omega : 0 < scale n) (by omega : 0 < logarithm (scale n)) (scale_divisible n)]
    exact le_rfl
  have h := probability_le (m := samples (scale n) (logarithm (scale n)))
    (L := repetitions (scale n) (logarithm (scale n))) (r := logarithm (scale n))
    μ policy hp hm hk chores active hinj origin hgood hpositive old hold
    (coarseCount (scale n) (logarithm (scale n))) (parent_budget hs her ha)
    (oldError (scale n)) (fineCap (scale n) (logarithm (scale n))) (multiplier (scale n))
    (2*(samples (scale n) (logarithm (scale n)) : ℝ))
    (by unfold oldError; positivity) (by unfold fineCap; positivity)
    (by unfold multiplier; positivity) (by positivity) hnear (cell_cap hs her) (target_total hs her ha)
    (by exact_mod_cast cell_count hs256 he hk256 (by omega)) hsize (correction_spending hs her ha)
    (badThreshold k) (by unfold badThreshold; positivity)
    (endpointAllowance k) retryAllowance (firstBadAllowance k) (endpoint_bound (by omega)).le
    henvelope (first_bad_fixed k).le
  exact h.trans_lt (failure_sum_small (by omega) hs he ha
    (UpperRepairParameters.logarithm_dominates_log hs (by omega) ha)
    (logarithm_power (by omega)))

end EnvyFreeResearch.Full.RefinedUpperRepairProbability

namespace EnvyFreeResearch.Full.RefinedUpperRepair
open MeasureTheory UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
variable {n k : ℕ} [Nonempty (Fin k)]

theorem failure_lt
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : UpperRepairPreparationChecks.Near chores μ active origin old (nearError n)) :
    law n k {p | (execute policy hk chores active origin old p).2.2 = true} < 1/64 :=
  RefinedUpperRepairProbability.original_population_failure_lt μ policy hp hm hk chores active hinj
    origin hgood hpositive old hold hnear

end EnvyFreeResearch.Full.RefinedUpperRepair
#print axioms EnvyFreeResearch.Full.RefinedUpperRepair.failure_lt
