import EnvyFreeResearch.Full.RefinedUpperRepairPreparationChecks
import EnvyFreeResearch.Full.RefinedUpperParameterCounts
import EnvyFreeResearch.Full.UpperRepairParametersDeterministic

/-! Numerical physical-preparation checks at the revised integral parameters.
These inequalities instantiate actual recorded Repair, not an abstract
successful-subroutine assumption. -/
noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperRepairParameters
open RefinedUpperParameterCounts RefinedUpperRepairPreparationChecks UpperRepairJobs
open UpperRepairParameters (populationRatio populationRatio_nonnegative populationRatio_le
  s_positive ell_positive s_one)
open UpperLogicalIsolation (jobCount_le_cube)
variable {s ell k : ℕ} (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell)
  (hk : (2^40 : ℝ)*k ≤ s)
include hs hell

lemma coarse_positive : (0 : ℝ) < coarseCount s ell := by
  rw [coarseCount_cast]
  positivity [s_positive hs,ell_positive hell]

lemma cell_cap : 2/((coarseCount s ell : ℝ)+1) ≤ fineCap s ell := by
  unfold fineCap
  rw [← coarseCount_cast]
  exact div_le_div_of_nonneg_left (by norm_num) (coarse_positive hs hell) (by linarith)

lemma repetitions_cap : (repetitions s ell : ℝ)*fineCap s ell=2/(s : ℝ)^4 := by
  rw [repetitions_cast]
  unfold fineCap
  field_simp [(s_positive hs).ne',(ell_positive hell).ne'] <;> ring

lemma seed_fraction_le_ratio :
    (jobCount k : ℝ)*repetitions s ell/((coarseCount s ell : ℝ)+1) ≤ populationRatio k s^3 := by
  have hnum := mul_le_mul_of_nonneg_right (jobCount_le_cube k)
    (Nat.cast_nonneg (α := ℝ) (repetitions s ell))
  calc
    _ ≤ (k : ℝ)^3*repetitions s ell/(coarseCount s ell : ℝ) :=
      div_le_div₀ (by positivity) hnum (coarse_positive hs hell) (by linarith)
    _ = populationRatio k s^3/(s : ℝ) := by
      rw [repetitions_cast,coarseCount_cast,populationRatio]
      field_simp [(s_positive hs).ne',(ell_positive hell).ne'] <;> ring
    _ ≤ populationRatio k s^3 := div_le_self (by positivity [populationRatio_nonnegative (s := s) k]) (s_one hs)

include hk in
lemma seed_spending :
    (jobCount k : ℝ)*repetitions s ell/((coarseCount s ell : ℝ)+1) < 1/8 := by
  have h := pow_le_pow_left₀ (populationRatio_nonnegative (s := s) k) (populationRatio_le hs hk) 3
  exact (seed_fraction_le_ratio hs hell).trans_lt (h.trans_lt (by norm_num))

include hk in
lemma parent_budget : 4*(jobCount k*repetitions s ell) ≤ coarseCount s ell+1 := by
  have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < (coarseCount s ell : ℝ)+1)).mp (seed_spending hs hell hk)
  have hp := coarse_positive hs hell
  have hr : 4*((jobCount k : ℝ)*repetitions s ell) ≤ (coarseCount s ell : ℝ)+1 := by linarith
  exact_mod_cast hr

include hk in
lemma batch_allowance : (k.choose 2 : ℝ)*repetitions s ell*fineCap s ell ≤ 1/(4*(s : ℝ)^2) := by
  have h := UpperRepairParameters.batch_allowance hs hell hk
  rw [mul_assoc,repetitions_cap hs hell]
  have hid : (UpperRepairParameters.repetitions s ell : ℝ)*UpperRepairParameters.fineCap s ell=2/(s : ℝ)^4 := by
    rw [UpperRepairParameters.repetitions_cast]
    unfold UpperRepairParameters.fineCap
    field_simp [(s_positive hs).ne',(ell_positive hell).ne'] <;> ring
  rwa [mul_assoc,hid] at h

lemma edge_allowance : 2*multiplier s*fineCap s ell ≤ 1/(4*(s : ℝ)^2) := by
  have hpow : (16 : ℝ) ≤ (s : ℝ)^5 := by
    have h := le_self_pow₀ (s_one hs) (by norm_num : 5≠0)
    exact (show (16 : ℝ) ≤ (s : ℝ) from (by norm_num : (16 : ℝ) ≤ 2^42).trans hs).trans h
  have he : (16 : ℝ) ≤ (s : ℝ)^5*ell := by nlinarith
  unfold multiplier fineCap
  apply (le_div_iff₀ (by positivity [s_positive hs] : (0 : ℝ) < 4*(s : ℝ)^2)).mpr
  have hid : (2*(s : ℝ)*(2/((s : ℝ)^8*ell)))*(4*(s : ℝ)^2)=16/((s : ℝ)^5*ell) := by
    field_simp [(s_positive hs).ne',(ell_positive hell).ne'] <;> ring
  rw [hid]
  exact (div_le_one (by positivity [s_positive hs,ell_positive hell])).mpr he

include hk in
lemma near_budget : nearBudget k (coarseCount s ell) (repetitions s ell) (oldError s) ≤ 3/(4*(s : ℝ)^2) := by
  have hb := (mul_le_mul_of_nonneg_left (cell_cap hs hell)
    (by positivity : (0 : ℝ) ≤ (k.choose 2 : ℝ)*repetitions s ell)).trans (batch_allowance hs hell hk)
  unfold nearBudget oldError
  calc
    _ ≤ 2*(1/(4*(s : ℝ)^2))+1/(4*(s : ℝ)^2) := add_le_add le_rfl hb
    _ = _ := by ring

include hk in
lemma target_budget : targetBudget k (coarseCount s ell) (repetitions s ell)
    (oldError s) (fineCap s ell) (multiplier s) ≤ (k : ℝ)/(s : ℝ)^2 := by
  have hn := mul_le_mul_of_nonneg_left (near_budget hs hell hk) (Nat.cast_nonneg (α := ℝ) k)
  have he := mul_le_mul_of_nonneg_left (edge_allowance hs hell) (Nat.cast_nonneg (α := ℝ) (k-1))
  have hlast := mul_le_mul_of_nonneg_right (show ((k-1 : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.sub_le k 1)
    (by positivity [s_positive hs] : (0 : ℝ) ≤ 1/(4*(s : ℝ)^2))
  unfold targetBudget
  calc
    _ ≤ (k : ℝ)*(3/(4*(s : ℝ)^2))+k*(1/(4*(s : ℝ)^2)) := add_le_add hn (he.trans hlast)
    _ = _ := by ring

include hk in
lemma target_total : (k : ℝ)*targetBudget k (coarseCount s ell) (repetitions s ell)
    (oldError s) (fineCap s ell) (multiplier s) < 1/16 := by
  have h := mul_le_mul_of_nonneg_left (target_budget hs hell hk) (Nat.cast_nonneg (α := ℝ) k)
  have hid : (k : ℝ)*((k : ℝ)/(s : ℝ)^2)=populationRatio k s^2 := by unfold populationRatio; field_simp
  rw [hid] at h
  exact h.trans_lt (UpperRepairParameters.ratio_square_small hs hk)

include hk in
lemma correction_spending : (k : ℝ)*multiplier s*fineCap s ell < 1/16 := by
  have h := mul_le_mul_of_nonneg_left (edge_allowance hs hell) (Nat.cast_nonneg (α := ℝ) k)
  have hk1 : (k : ℝ) ≤ s := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hlarge : (8 : ℝ) < s := (by norm_num : (8 : ℝ) < 2^42).trans_le hs
  have hsmall : (k : ℝ)/(4*(s : ℝ)^2) < 1/8 := by
    apply (div_lt_iff₀ (by positivity [s_positive hs] : (0 : ℝ) < 4*(s : ℝ)^2)).mpr
    nlinarith
  have hr : (k : ℝ)*(1/(4*(s : ℝ)^2)) < 1/8 := by simpa only [mul_one_div] using hsmall
  nlinarith

omit hell in
include hk in
lemma linear_margin : 4*(k : ℝ) ≤ multiplier s := by
  unfold multiplier
  nlinarith [Nat.cast_nonneg (α := ℝ) k]


open MeasureTheory UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
open scoped unitInterval

include hs hell hk in
theorem physical_checks {n : ℕ} [Nonempty (Fin k)]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (hk2 : 2 ≤ k) (chores : Bool) (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : UpperRepairPreparationChecks.Near chores μ active origin old (oldError s))
    (draw : Fin (samples s ell) → Fin k × I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k-1+1) → Fin (repetitions s ell+1)) :
    let data := UpperGridMerge.prepare policy active origin (coarseCount s ell) (samples s ell) draw
    let prepared := RefinedUpperPreparationProgram.finish hk2 chores active origin old data (repetitions s ell) pi threshold
    UpperPreparedEnvelopeMean.Checks μ active prepared.2.1 (UpperGridData.cuts data)
      (RefinedUpperRepairTargets.targets chores active prepared (fineCap s ell) (multiplier s))
      (fineCap s ell) (RefinedUpperRepairSeedIndices.reserved active origin data (repetitions s ell))
      (2*(samples s ell : ℝ)) := by
  have hs256 : 256 ≤ s := by exact_mod_cast (show (256 : ℝ) ≤ s by exact (by norm_num : (256 : ℝ) ≤ 2^42).trans hs)
  have he1 : 1 ≤ ell := by exact_mod_cast hell
  have hk256 : 256*k ≤ s := by exact_mod_cast (show (256 : ℝ)*k ≤ s by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  exact actual_checks μ policy hpolicy active origin hgood hpositive hk2 chores old hold
    (coarseCount s ell) (samples s ell) (repetitions s ell) draw (parent_budget hs hell hk)
    (oldError s) (fineCap s ell) (multiplier s) (2*(samples s ell : ℝ))
    (by unfold oldError; positivity) hnear (by unfold multiplier; positivity)
    (cell_cap hs hell) (target_total hs hell hk)
    (by exact_mod_cast cell_count hs256 he1 hk256 (by omega)) pi threshold

end EnvyFreeResearch.Full.RefinedUpperRepairParameters
