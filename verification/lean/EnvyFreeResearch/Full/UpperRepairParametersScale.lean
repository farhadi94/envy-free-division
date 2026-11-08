import EnvyFreeResearch.Full.UpperLogicalIsolation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

/-! The manuscript's exact Repair scales. Coarse counts and reserve marking
probability are distinct named quantities. No constants are asymptotic. -/
noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperRepairParameters

def coarseCount (s ell : ℕ) : ℕ := s^17 * ell^2
def samples (s ell : ℕ) : ℕ := s^18 * ell^2
def repetitions (s ell : ℕ) : ℕ := s^5 * ell

def reserveProbability (s ell : ℕ) : ℝ := 1 / ((s : ℝ)^8 * ell)
def fineCap (s ell : ℕ) : ℝ := 2 / ((s : ℝ)^9 * ell)
def multiplier (s : ℕ) : ℝ := (s : ℝ)^2 / 8
def retainedCap (s ell : ℕ) : ℝ := 1024 * (s : ℝ)^10 * ell
def interpolationBudget (s ell : ℕ) : ℝ := 1 / (32768 * (s : ℝ)^8 * ell)
def oldError (s ell : ℕ) : ℝ := 1 / (4 * (s : ℝ)^10 * ell)
def coarseCap (s ell : ℕ) : ℝ := 1 / ((s : ℝ)^17 * ell^2)
def populationRatio (k s : ℕ) : ℝ := k / s

def scale (n : ℕ) : ℕ := 2^40 * max 4 n
def logarithm (s : ℕ) : ℕ := ⌈Real.log (2 * (s : ℝ)) / Real.log 2⌉₊

theorem coarseCount_cast (s ell : ℕ) : (coarseCount s ell : ℝ) = (s : ℝ)^17 * ell^2 := by
  simp only [coarseCount, Nat.cast_mul, Nat.cast_pow]
theorem samples_cast (s ell : ℕ) : (samples s ell : ℝ) = (s : ℝ)^18 * ell^2 := by
  simp only [samples, Nat.cast_mul, Nat.cast_pow]
theorem repetitions_cast (s ell : ℕ) : (repetitions s ell : ℝ) = (s : ℝ)^5 * ell := by
  simp only [repetitions, Nat.cast_mul, Nat.cast_pow]

variable {s ell k : ℕ}

theorem s_two (hs : (2^42 : ℝ) ≤ s) : (2 : ℝ) ≤ s := by norm_num at hs ⊢; linarith
theorem s_positive (hs : (2^42 : ℝ) ≤ s) : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) (s_two hs)
theorem s_one (hs : (2^42 : ℝ) ≤ s) : (1 : ℝ) ≤ s := by linarith [s_two hs]
theorem ell_positive (hell : (1 : ℝ) ≤ ell) : (0 : ℝ) < ell := lt_of_lt_of_le zero_lt_one hell

section Bounds
variable (hs : (2^42 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell)
include hs hell

theorem denominator_ge_one (a b : ℕ) : (1 : ℝ) ≤ (s : ℝ)^a * (ell : ℝ)^b :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (s_one hs)) (one_le_pow₀ hell)

theorem reserve_positive : 0 < reserveProbability s ell := by
  unfold reserveProbability
  positivity [s_positive hs, ell_positive hell]

theorem reserve_le_one : reserveProbability s ell ≤ 1 := by
  unfold reserveProbability
  apply (div_le_one (by positivity [s_positive hs, ell_positive hell])).mpr
  simpa only [pow_one] using denominator_ge_one hs hell 8 1

def reserveMark : unitInterval := ⟨reserveProbability s ell, (reserve_positive hs hell).le, reserve_le_one hs hell⟩

theorem fineCap_positive : 0 < fineCap s ell := by
  unfold fineCap
  positivity [s_positive hs, ell_positive hell]

omit hell in
theorem multiplier_positive : 0 < multiplier s := by
  unfold multiplier
  positivity [s_positive hs]

theorem retainedCap_positive : 0 < retainedCap s ell := by
  unfold retainedCap
  positivity [s_positive hs, ell_positive hell]

theorem interpolation_positive : 0 < interpolationBudget s ell := by
  unfold interpolationBudget
  positivity [s_positive hs, ell_positive hell]

theorem interpolation_le_one : interpolationBudget s ell ≤ 1 := by
  unfold interpolationBudget
  apply (div_le_one (by positivity [s_positive hs, ell_positive hell])).mpr
  have h := denominator_ge_one hs hell 8 1
  simp only [pow_one] at h
  nlinarith

theorem oldError_positive : 0 < oldError s ell := by
  unfold oldError
  positivity [s_positive hs, ell_positive hell]

omit hs hell in
theorem populationRatio_nonnegative (k : ℕ) : 0 ≤ populationRatio k s := by
  unfold populationRatio
  positivity

omit hell in
theorem populationRatio_le (hk : (2^40 : ℝ) * k ≤ s) : populationRatio k s ≤ 1 / 2^40 := by
  unfold populationRatio
  apply (div_le_iff₀ (s_positive hs)).mpr
  linarith

omit hell in
theorem populationRatio_le_one (hk : (2^40 : ℝ) * k ≤ s) : populationRatio k s ≤ 1 := by
  exact (populationRatio_le hs hk).trans (by norm_num)

/-- The display identities hold exactly for the integral counts. -/
theorem identities :
    coarseCap s ell * samples s ell = s ∧
    reserveProbability s ell * interpolationBudget s ell * samples s ell = (s : ℝ)^2 / 32768 ∧
    interpolationBudget s ell * retainedCap s ell = multiplier s / 4 ∧
    2 * oldError s ell / reserveProbability s ell = 1 / (2 * (s : ℝ)^2) ∧
    repetitions s ell * fineCap s ell = 2 / (s : ℝ)^4 ∧
    2 * multiplier s * fineCap s ell = 1 / (2 * (s : ℝ)^7 * ell) := by
  have hsn := (s_positive hs).ne'
  have hen := (ell_positive hell).ne'
  simp only [coarseCap, samples_cast, repetitions_cast, reserveProbability, interpolationBudget,
    retainedCap, multiplier, oldError, fineCap]
  constructor
  · field_simp [hsn, hen]
  constructor
  · field_simp [hsn, hen]
  constructor
  · field_simp [hsn, hen]; ring
  constructor
  · field_simp [hsn, hen]; ring
  constructor
  · field_simp [hsn, hen]
  · field_simp [hsn, hen]; ring

end Bounds
end EnvyFreeResearch.Full.UpperRepairParameters
