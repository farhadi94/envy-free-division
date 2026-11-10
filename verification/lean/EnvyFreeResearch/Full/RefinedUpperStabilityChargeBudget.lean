import EnvyFreeResearch.Full.RefinedUpperActualBadGrid
import EnvyFreeResearch.Full.RefinedUpperParameterCounts
import EnvyFreeResearch.Full.UpperLogicalIsolationData

/-! Exact endpoint charges and their numerical failure bound under the
 actual iid grid sampler. Integer division costs no factor when m+1 is kept. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperStabilityChargeBudget
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
open RefinedUpperParameterCounts RefinedUpperStability

def endpointCharge (k L : ℕ) : ℕ :=
  4*(UpperLogicalIsolation.requests k L).length +
    4*(Finset.univ.toList : List (Fin k × Fin k)).length

theorem endpointCharge_exact (k L : ℕ) :
    (endpointCharge k L : ℝ) = 2*(k:ℝ)^2*((k:ℝ)-1)*L+4*(k:ℝ)^2 := by
  simp only [endpointCharge,UpperLogicalIsolation.requests_length,Finset.length_toList,
    Finset.card_univ,Fintype.card_prod,Fintype.card_fin,UpperRepairJobs.jobCount,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_choose_two]
  ring

theorem endpointCharge_le (k L : ℕ) (hL : 2 ≤ L) :
    (endpointCharge k L : ℝ) ≤ 2*(k:ℝ)^3*L := by
  rw [endpointCharge_exact]
  have hLr : (2:ℝ) ≤ L := by exact_mod_cast hL
  nlinarith [mul_nonneg (sq_nonneg (k:ℝ)) (sub_nonneg.mpr hLr)]

theorem repetitions_ge_two {s ell : ℕ} (hs : 2 ≤ s) (he : 1 ≤ ell) :
    2 ≤ repetitions s ell := by
  have hp : 2 ≤ s^4 := hs.trans (Nat.le_self_pow (by norm_num) s)
  unfold repetitions
  exact hp.trans (by simpa using Nat.mul_le_mul_left (s^4) he)

theorem samples_denominator (s ell : ℕ) :
    (s:ℝ)^9*ell/128 ≤ (samples s ell : ℝ)+1 := by
  have h := Nat.lt_mul_div_succ (s^9*ell) (by norm_num : 0 < 128)
  have hr : (s:ℝ)^9*ell < 128*((samples s ell : ℝ)+1) := by
    exact_mod_cast h
  exact (div_le_iff₀ (by norm_num : (0:ℝ)<128)).mpr (by linarith)

theorem numerical_markov_bound (k s ell : ℕ) (hs : 2 ≤ s) (he : 1 ≤ ell) :
    ((endpointCharge k (repetitions s ell) : ℝ)/((samples s ell : ℝ)+1))/(1/(32768*(k:ℝ)^2)) ≤
      (2:ℝ)^23*((k:ℝ)/s)^5 := by
  have hsp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have hep : (0:ℝ)<ell := by exact_mod_cast (show 0<ell by omega)
  have hc := endpointCharge_le k (repetitions s ell) (repetitions_ge_two hs he)
  rw [repetitions_cast] at hc
  calc
    _ = ((endpointCharge k (repetitions s ell) : ℝ)/((samples s ell : ℝ)+1)) * (32768*(k:ℝ)^2) := by
      simp only [div_eq_mul_inv,one_mul,inv_inv]
    _ ≤ (2*(k:ℝ)^3*((s:ℝ)^4*ell)/((s:ℝ)^9*ell/128))*(32768*(k:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply div_le_div₀ (by positivity) hc (by positivity)
      exact samples_denominator s ell
    _ = (2:ℝ)^23*((k:ℝ)/s)^5 := by
      field_simp [ne_of_gt hsp,ne_of_gt hep]
      <;> ring

variable {n k : ℕ} [Nonempty (Fin k)]

theorem actual_numerical_grid_failure
    (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (active : Fin k → Fin n)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (s ell : ℕ) (hs : 2 ≤ s) (he : 1 ≤ ell) :
    let law := UpperMixtureSampling.mixture μ active origin.cells
    UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) (samples s ell)
      {draw | 1/(32768*(k:ℝ)^2) ≤ law.real
        (physicalBad μ policy active origin (coarseCount s ell)
          (UpperLogicalIsolation.requests k (repetitions s ell)) Finset.univ.toList
          (UpperGridMerge.prepare policy active origin (coarseCount s ell) (samples s ell) draw).1
          (UpperGridMerge.prepare policy active origin (coarseCount s ell) (samples s ell) draw).2.1)} ≤
      ENNReal.ofReal ((2:ℝ)^23*((k:ℝ)/s)^5) := by
  have hk : 0<k := by simpa only [Fintype.card_fin] using (Fintype.card_pos (α := Fin k))
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have h := actual_bad_grid_probability μ policy hp hm active origin hgood hpositive
    (m := samples s ell) (coarseCount s ell) (UpperLogicalIsolation.requests k (repetitions s ell))
    (Finset.univ.toList : List (Fin k × Fin k)) (1/(32768*(k:ℝ)^2)) (by positivity)
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  simpa only [endpointCharge,Nat.cast_add,Nat.cast_one] using numerical_markov_bound k s ell hs he

end EnvyFreeResearch.Full.RefinedUpperStabilityChargeBudget
#print axioms EnvyFreeResearch.Full.RefinedUpperStabilityChargeBudget.actual_numerical_grid_failure
