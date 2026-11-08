import EnvyFreeResearch.Full.ChoresRecords
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic

/-!
# A concrete continuous realization of finite prefix records

A finite strictly increasing prefix-value table is extended by a finite sum
of clipped linear ramps. This gives a continuous strictly increasing function
on the abstract parent interval and agrees exactly with every stored record.
No endpoint of the original physical parent is modified.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores

open Set
open scoped BigOperators

/-- The unit ramp occupying abstract cell `[j,j+1]`. -/
def unitRamp (j : ℕ) (x : ℝ) : ℝ := min 1 (max 0 (x - j))

theorem unitRamp_continuous (j : ℕ) : Continuous (unitRamp j) := by
  unfold unitRamp
  fun_prop

theorem unitRamp_monotone (j : ℕ) : Monotone (unitRamp j) := by
  intro x y hxy
  exact min_le_min_left _ (max_le_max_left _ (sub_le_sub_right hxy _))

@[simp] theorem unitRamp_of_le {j : ℕ} {x : ℝ} (hx : x ≤ j) : unitRamp j x = 0 := by
  simp [unitRamp, max_eq_left (sub_nonpos.mpr hx)]

@[simp] theorem unitRamp_of_add_one_le {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) + 1 ≤ x) : unitRamp j x = 1 := by
  have h0 : 0 ≤ x - j := by linarith
  have h1 : 1 ≤ x - j := by linarith
  simp [unitRamp, max_eq_right h0, min_eq_left h1]

/-- Clipped unit ramps sum to the identity on the whole abstract parent. -/
theorem sum_unitRamp (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    ∑ j ∈ Finset.range n, unitRamp j x = x := by
  induction n with
  | zero =>
    have hx : x = 0 := le_antisymm (by simpa using hxn) hx0
    simp [hx]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : x ≤ n
    · rw [ih hn, unitRamp_of_le hn, add_zero]
    · have hnx : (n : ℝ) < x := lt_of_not_ge hn
      have hfull : ∀ j ∈ Finset.range n, unitRamp j x = 1 := by
        intro j hj
        apply unitRamp_of_add_one_le
        have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
        have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
        linarith
      rw [Finset.sum_congr rfl hfull]
      have h0 : 0 ≤ x - n := by linarith
      have h1 : x - n ≤ 1 := by
        have hxn' : x ≤ (n : ℝ) + 1 := by simpa using hxn
        linarith
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [unitRamp, max_eq_right h0, min_eq_right h1]
      ring

/-- Explicit piecewise-linear interpolation of the stored values. -/
def prefixInterpolation (n : ℕ) (v : ℕ → ℝ) (x : ℝ) : ℝ :=
  v 0 + ∑ j ∈ Finset.range n, (v (j + 1) - v j) * unitRamp j x

theorem prefixInterpolation_continuous (n : ℕ) (v : ℕ → ℝ) :
    Continuous (prefixInterpolation n v) := by
  unfold prefixInterpolation unitRamp
  fun_prop

/-- Every positive cell increment makes the complete interpolation strictly
increasing, including when two arguments belong to different cells. -/
theorem prefixInterpolation_strictMonoOn (n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ j < n, v j < v (j + 1)) :
    StrictMonoOn (prefixInterpolation n v) (Icc 0 n) := by
  intro x hx y hy hxy
  have hle : ∀ j ∈ Finset.range n, unitRamp j x ≤ unitRamp j y := by
    intro j _
    exact unitRamp_monotone j hxy.le
  have hex : ∃ j ∈ Finset.range n, unitRamp j x < unitRamp j y := by
    by_contra! hnone
    have heq : ∀ j ∈ Finset.range n, unitRamp j x = unitRamp j y := by
      intro j hj
      exact le_antisymm (hle j hj) (hnone j hj)
    have hs := Finset.sum_congr rfl heq
    rw [sum_unitRamp n hx.1 hx.2, sum_unitRamp n hy.1 hy.2] at hs
    exact (ne_of_lt hxy) hs
  unfold prefixInterpolation
  apply add_lt_add_right
  apply Finset.sum_lt_sum
  · intro j hj
    exact mul_le_mul_of_nonneg_left (hle j hj)
      (sub_nonneg.mpr (hv j (Finset.mem_range.mp hj)).le)
  · obtain ⟨j, hj, hlt⟩ := hex
    exact ⟨j, hj, mul_lt_mul_of_pos_left hlt
      (sub_pos.mpr (hv j (Finset.mem_range.mp hj)))⟩

/-- Every stored knot has exactly its prescribed prefix value. -/
theorem prefixInterpolation_at_record (n : ℕ) (v : ℕ → ℝ) (k : ℕ) (hk : k ≤ n) :
    prefixInterpolation n v k = v k := by
  have hramp : ∀ j : ℕ, unitRamp j k = if j < k then 1 else 0 := by
    intro j
    split_ifs with hj
    · apply unitRamp_of_add_one_le
      exact_mod_cast (Nat.succ_le_iff.mpr hj)
    · apply unitRamp_of_le
      exact_mod_cast (Nat.le_of_not_gt hj)
  have hf : (Finset.range n).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hs : (∑ j ∈ Finset.range n, (v (j + 1) - v j) * unitRamp j k) =
      ∑ j ∈ Finset.range k, (v (j + 1) - v j) := by
    simp_rw [hramp, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, hf]
  have htel : ∀ m, (∑ j ∈ Finset.range m, (v (j + 1) - v j)) = v m - v 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  unfold prefixInterpolation
  rw [hs, htel]
  ring

/-- A concrete continuous hungry prefix function realizes every entry of a
finite strictly increasing real table, with zero empty-prefix value. -/
theorem continuous_strict_realization (n : ℕ) (v : ℕ → ℝ)
    (hzero : v 0 = 0) (hinc : ∀ j < n, v j < v (j + 1)) :
    ∃ f : ℝ → ℝ, Continuous f ∧ StrictMonoOn f (Icc 0 n) ∧
      f 0 = 0 ∧ (∀ k ≤ n, f k = v k) := by
  refine ⟨prefixInterpolation n v, prefixInterpolation_continuous n v,
    prefixInterpolation_strictMonoOn n v hinc, ?_, ?_⟩
  · simpa [hzero] using prefixInterpolation_at_record n v 0 (Nat.zero_le n)
  · exact prefixInterpolation_at_record n v

/-- Positive table increments also make the extension monotone on all of ℝ. -/
theorem prefixInterpolation_monotone (n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ j < n, v j ≤ v (j + 1)) : Monotone (prefixInterpolation n v) := by
  intro x y hxy
  unfold prefixInterpolation
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (unitRamp_monotone j hxy)
    (sub_nonneg.mpr (hv j (Finset.mem_range.mp hj)))

/-- The interpolation, bundled to construct an actual Borel measure. -/
def prefixStieltjes (n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ j < n, v j ≤ v (j + 1)) : StieltjesFunction ℝ where
  toFun := prefixInterpolation n v
  mono' := prefixInterpolation_monotone n v hv
  right_continuous' := fun _ => (prefixInterpolation_continuous n v).continuousAt.continuousWithinAt

/-- Continuous interpolation gives a nonatomic physical measure. -/
theorem prefixStieltjes_noAtoms (n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ j < n, v j ≤ v (j + 1)) :
    MeasureTheory.NullSingletonClass (prefixStieltjes n v hv).measure := by
  constructor
  intro x
  rw [StieltjesFunction.measure_singleton]
  have hleft : Function.leftLim (prefixStieltjes n v hv) x = prefixStieltjes n v hv x :=
    (prefixInterpolation_continuous n v).continuousAt.continuousWithinAt.leftLim_eq
  rw [hleft, sub_self, ENNReal.ofReal_zero]

/-- Bounds on ramps make the constructed measure finite. -/
theorem prefixStieltjes_finite (n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ j < n, v j ≤ v (j + 1)) (hzero : v 0 = 0) :
    MeasureTheory.IsFiniteMeasure (prefixStieltjes n v hv).measure := by
  apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le (C := v n)
  intro x
  change |prefixInterpolation n v x| ≤ v n
  have hnonneg : 0 ≤ prefixInterpolation n v x := by
    unfold prefixInterpolation
    rw [hzero, zero_add]
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (sub_nonneg.mpr (hv j (Finset.mem_range.mp hj)))
    exact le_min (by norm_num) (le_max_left _ _)
  rw [abs_of_nonneg hnonneg, ← prefixInterpolation_at_record n v n le_rfl]
  unfold prefixInterpolation
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hv j (Finset.mem_range.mp hj)))
  have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Finset.mem_range.mp hj)
  rw [unitRamp_of_add_one_le hjn]
  exact min_le_left _ _

/-- The constructed measure has exactly the recorded real prefix values. -/
theorem prefixStieltjes_record_value (n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ j < n, v j ≤ v (j + 1)) (hzero : v 0 = 0)
    (k : ℕ) (hk : k ≤ n) :
    (prefixStieltjes n v hv).measure.real (Icc 0 k) = v k := by
  have hleft : Function.leftLim (prefixStieltjes n v hv) 0 = prefixStieltjes n v hv 0 :=
    (prefixInterpolation_continuous n v).continuousAt.continuousWithinAt.leftLim_eq
  rw [MeasureTheory.measureReal_def, StieltjesFunction.measure_Icc, hleft]
  change (ENNReal.ofReal (prefixInterpolation n v k - prefixInterpolation n v 0)).toReal = v k
  have hstart : prefixInterpolation n v 0 = 0 := by
    simpa [hzero] using prefixInterpolation_at_record n v 0 (Nat.zero_le n)
  rw [prefixInterpolation_at_record n v k hk, hstart, sub_zero]
  apply ENNReal.toReal_ofReal
  have hmono := prefixInterpolation_monotone n v hv (show (0 : ℝ) ≤ k by positivity)
  simpa only [hstart, prefixInterpolation_at_record n v k hk] using hmono

/-- Every nondegenerate interval inside the abstract parent has positive cost. -/
theorem prefixStieltjes_hungry (n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ j < n, v j < v (j + 1)) {a b : ℝ}
    (ha : a ∈ Icc 0 (n : ℝ)) (hb : b ∈ Icc 0 (n : ℝ)) (hab : a < b) :
    0 < (prefixStieltjes n v (fun j hj => (hv j hj).le)).measure (Ioc a b) := by
  rw [StieltjesFunction.measure_Ioc]
  apply ENNReal.ofReal_pos.mpr
  exact sub_pos.mpr (prefixInterpolation_strictMonoOn n v hv ha hb hab)

end EnvyFreeResearch.Full.Chores
