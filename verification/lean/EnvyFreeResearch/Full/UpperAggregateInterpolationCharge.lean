import EnvyFreeResearch.Full.UpperGridInterpolationEnvelope
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# One common charge for all cumulative interpolation errors

The scalar comparison includes zero disagreement and zero endpoint errors.
A single charge threshold controls every pair simultaneously; there is no
union bound over the pairs.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

variable {Index Pair Ω : Type*} [Fintype Index]

/-- The endpoint fractions dominate the fraction of the total error. -/
theorem total_error_fraction_le (D : ℝ) (hD : 0 ≤ D) (e : Index → ℝ)
    (he : ∀ i, 0 ≤ e i) :
    (∑ i, e i) / (D + ∑ i, e i) ≤ ∑ i, e i / (D + e i) := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : e i = 0
  · simp [hi]
  · have hip : 0 < e i := lt_of_le_of_ne (he i) (Ne.symm hi)
    have hisum : e i ≤ ∑ j, e j := Finset.single_le_sum (fun j _ => he j) (Finset.mem_univ i)
    exact div_le_div_of_nonneg_left (he i) (by linarith) (by linarith)

/-- Crossing the desired error budget forces a strictly positive common
charge, also when the disagreement `D` vanishes. -/
theorem fraction_threshold (D E b : ℝ) (hD : 0 ≤ D) (hb : 0 < b)
    (hE : b * D < E) : b / (1 + b) < E / (D + E) := by
  have hEpos : 0 < E := lt_of_le_of_lt (mul_nonneg hb.le hD) hE
  apply (div_lt_div_iff₀ (by linarith : 0 < 1 + b) (by linarith : 0 < D + E)).mpr
  nlinarith

/-- A zero-disagreement pair with nonzero aggregate error costs at least
one unit of the common charge. This is derived from the same fractions. -/
theorem zero_disagreement_charge (e : Index → ℝ) (he : ∀ i, 0 ≤ e i)
    (hE : 0 < ∑ i, e i) : 1 ≤ ∑ i, e i / e i := by
  have h := total_error_fraction_le 0 (by norm_num) e he
  simpa [hE.ne'] using h

/-- Any collection of endpoint charges that bounds every pairwise fraction
simultaneously controls every total pair error. -/
theorem total_error_fraction_le_common (D : Pair → ℝ) (hD : ∀ p, 0 ≤ D p)
    (e : Pair → Index → ℝ) (he : ∀ p i, 0 ≤ e p i) (u : Index → ℝ)
    (hu : ∀ p i, e p i / (D p + e p i) ≤ u i) (p : Pair) :
    (∑ i, e p i) / (D p + ∑ i, e p i) ≤ ∑ i, u i :=
  (total_error_fraction_le (D p) (hD p) (e p) (he p)).trans
    (Finset.sum_le_sum (fun i _ => hu p i))

theorem any_error_implies_charge (D : Pair → ℝ) (hD : ∀ p, 0 ≤ D p)
    (e : Pair → Index → ℝ) (he : ∀ p i, 0 ≤ e p i) (u : Index → ℝ)
    (hu : ∀ p i, e p i / (D p + e p i) ≤ u i) (b : ℝ) (hb : 0 < b)
    (hbad : ∃ p, b * D p < ∑ i, e p i) : b / (1 + b) < ∑ i, u i := by
  obtain ⟨p, hp⟩ := hbad
  exact (fraction_threshold (D p) (∑ i, e p i) b (hD p) hb hp).trans_le
    (total_error_fraction_le_common D hD e he u hu p)

/-- One Markov inequality for the common charge. The failure set need not
be a finite or countable union of pair-indexed events. -/
theorem common_charge_probability [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (charge : Ω → ℝ) (hcharge : Integrable charge μ)
    (hnonneg : ∀ ω, 0 ≤ charge ω) (bad : Set Ω) (b C : ℝ) (hb : 0 < b)
    (hmean : ∫ ω, charge ω ∂μ ≤ C)
    (hbad : ∀ ω ∈ bad, b / (1 + b) < charge ω) :
    μ bad ≤ ENNReal.ofReal (C * (1 + b) / b) := by
  have ht : 0 < b / (1 + b) := div_pos hb (by linarith)
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hnonneg) hcharge (b / (1 + b))
  have hbound : μ.real {ω | b / (1 + b) ≤ charge ω} ≤ C / (b / (1 + b)) := by
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm] using hm.trans hmean
  calc
    μ bad ≤ μ {ω | b / (1 + b) ≤ charge ω} := measure_mono (fun ω hω => (hbad ω hω).le)
    _ = ENNReal.ofReal (μ.real {ω | b / (1 + b) ≤ charge ω}) :=
      (ofReal_measureReal (by finiteness)).symm
    _ ≤ ENNReal.ofReal (C / (b / (1 + b))) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := by congr 1; field_simp

end EnvyFreeResearch.Full.UpperAggregateInterpolation
