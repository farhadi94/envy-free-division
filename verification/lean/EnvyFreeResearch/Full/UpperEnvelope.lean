import EnvyFreeResearch.Full.UpperPayments
import EnvyFreeResearch.Full.UpperCorrectionStage

/-!
# The maximum-cell correction envelope

For each recipient, take the largest normalized cell disagreement across
observers, including zero as a candidate. The positive measure obtained by
spreading this height uniformly in each sampled cell dominates every
interpolated signed correction. Its total mass is at most the cell count,
so one Markov event controls all observers without an extra observer factor.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal

namespace EnvyFreeResearch.Full.UpperEnvelope

open UpperPayments

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def ratio (a : Agent → Cell → ℝ) (i j : Agent) (e : Cell) : ℝ :=
  if 0 < cellGap a i j then |a i e - a j e| / cellGap a i j else 0

def height (a : Agent → Cell → ℝ) (j : Agent) (e : Cell) : ℝ :=
  (Finset.univ : Finset (Option Agent)).sup' ⟨none, Finset.mem_univ none⟩
    (fun c => c.elim 0 (fun i => ratio a i j e))

omit [Fintype Agent] in
theorem ratio_nonneg (a : Agent → Cell → ℝ) (i j : Agent) (e : Cell) : 0 ≤ ratio a i j e := by
  unfold ratio
  split_ifs with h
  · exact div_nonneg (abs_nonneg _) h.le
  · exact le_rfl

omit [Fintype Agent] in
theorem ratio_le_one (a : Agent → Cell → ℝ) (i j : Agent) (e : Cell) : ratio a i j e ≤ 1 := by
  unfold ratio
  split_ifs with h
  · exact (div_le_one h).mpr (difference_le_cellGap a i j e)
  · norm_num

theorem height_nonneg (a : Agent → Cell → ℝ) (j : Agent) (e : Cell) : 0 ≤ height a j e :=
  Finset.le_sup' (fun c : Option Agent => c.elim 0 (fun i => ratio a i j e)) (Finset.mem_univ none)

theorem height_le_one (a : Agent → Cell → ℝ) (j : Agent) (e : Cell) : height a j e ≤ 1 := by
  apply Finset.sup'_le
  intro c _
  cases c with
  | none => norm_num
  | some i => exact ratio_le_one a i j e

theorem ratio_le_height (a : Agent → Cell → ℝ) (i j : Agent) (e : Cell) :
    ratio a i j e ≤ height a j e :=
  Finset.le_sup' (fun c : Option Agent => c.elim 0 (fun i => ratio a i j e)) (Finset.mem_univ (some i))

theorem difference_le_height (a : Agent → Cell → ℝ) (i j : Agent) (e : Cell) :
    |a i e - a j e| ≤ cellGap a i j * height a j e := by
  by_cases hpos : 0 < cellGap a i j
  · have hr := ratio_le_height a i j e
    rw [ratio, ite_eq_left hpos] at hr
    have h := (div_le_iff₀ hpos).mp hr
    simpa only [mul_comm] using h
  · have hz : cellGap a i j = 0 := le_antisymm (le_of_not_gt hpos) (cellGap_nonneg a i j)
    simpa only [hz, zero_mul] using difference_le_cellGap a i j e

def envelope (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ) (j : Agent) : Measure ℝ :=
  ∑ e, ENNReal.ofReal (height a j e) • rho e

instance envelope_finite (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsFiniteMeasure (rho e)] (j : Agent) : IsFiniteMeasure (envelope a rho j) := by
  constructor
  simp only [envelope, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.sum_lt_top.mpr (fun e _ =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top (rho e) univ))

def estimate (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    (i j : Agent) (C : Set ℝ) : ℝ := ∑ e, (a i e - a j e) * (rho e).real C

theorem envelope_real (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsFiniteMeasure (rho e)] (j : Agent) (C : Set ℝ) :
    (envelope a rho j).real C = ∑ e, height a j e * (rho e).real C := by
  simp only [envelope, Measure.real, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun e _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (rho e) C))]
  apply Finset.sum_congr rfl
  intro e _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (height_nonneg a j e)]

/-- The bound uses a maximum over observers, so its mass costs only one
unit per sampled cell. It remains valid for zero-measure virtual cells. -/
theorem envelope_mass_le (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsZeroOrProbabilityMeasure (rho e)] (j : Agent) (C : Set ℝ) :
    (envelope a rho j).real C ≤ Fintype.card Cell := by
  rw [envelope_real]
  calc
    _ ≤ ∑ _e : Cell, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact (mul_le_mul (height_le_one a j e) measureReal_le_one measureReal_nonneg (by norm_num)).trans_eq
        (one_mul 1)
    _ = _ := by simp

/-- Every interpolated observer difference is bounded by the same positive
recipient envelope, including pairs with zero maximum disagreement. -/
theorem estimate_abs_le (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsFiniteMeasure (rho e)] (i j : Agent) (C : Set ℝ) :
    |estimate a rho i j C| ≤ cellGap a i j * (envelope a rho j).real C := by
  unfold estimate
  calc
    _ ≤ ∑ e, |(a i e - a j e) * (rho e).real C| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, cellGap a i j * (height a j e * (rho e).real C) := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul, abs_of_nonneg measureReal_nonneg]
      have h := mul_le_mul_of_nonneg_right (difference_le_height a i j e)
        (show 0 ≤ (rho e).real C from measureReal_nonneg)
      simpa only [mul_assoc] using h
    _ = _ := by rw [← Finset.mul_sum, envelope_real]

theorem zero_gap_estimate (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsFiniteMeasure (rho e)] (i j : Agent) (hzero : cellGap a i j = 0) (C : Set ℝ) :
    estimate a rho i j C = 0 := by
  have h := estimate_abs_le a rho i j C
  rw [hzero, zero_mul] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- One envelope threshold covers every observer's estimated-error test. -/
theorem estimated_exceed_implies_envelope (a : Agent → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsFiniteMeasure (rho e)] (j : Agent) (C : Set ℝ) (lam : ℝ)
    (hbad : ∃ i, lam * cellGap a i j / 4 < |estimate a rho i j C|) :
    lam / 4 < (envelope a rho j).real C := by
  obtain ⟨i, hi⟩ := hbad
  have hpos : 0 < cellGap a i j := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (cellGap_nonneg a i j)
    rw [hz, mul_zero, zero_div, zero_gap_estimate a rho i j hz C, abs_zero] at hi
    exact lt_irrefl _ hi
  have hbound := estimate_abs_le a rho i j C
  nlinarith

def uniformCells (cells : Cell → Set ℝ) (e : Cell) : Measure ℝ := cond volume (cells e)

instance uniformCells_zeroOrProbability (cells : Cell → Set ℝ) (e : Cell) :
    IsZeroOrProbabilityMeasure (uniformCells cells e) := inferInstanceAs (IsZeroOrProbabilityMeasure (cond volume (cells e)))

omit [Fintype Cell] in
/-- On literal interval cells this is precisely the piecewise-constant
interpolation formula. Conditional normalization also defines the empty or
degenerate cell as the zero measure. -/
theorem uniformCell_real (cells : Cell → Set ℝ) (hmeas : ∀ e, MeasurableSet (cells e))
    (e : Cell) (C : Set ℝ) : (uniformCells cells e).real C =
      volume.real (cells e ∩ C) / volume.real (cells e) := by
  rw [uniformCells, measureReal_def, cond_apply (hmeas e), ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [measureReal_def, div_eq_mul_inv, mul_comm]

omit [Fintype Agent] in
theorem uniform_estimate_formula (a : Agent → Cell → ℝ) (cells : Cell → Set ℝ)
    (hmeas : ∀ e, MeasurableSet (cells e)) (i j : Agent) (C : Set ℝ) :
    estimate a (uniformCells cells) i j C =
      ∑ e, (a i e - a j e) * (volume.real (cells e ∩ C) / volume.real (cells e)) := by
  simp only [estimate, uniformCell_real cells hmeas]

end EnvyFreeResearch.Full.UpperEnvelope
