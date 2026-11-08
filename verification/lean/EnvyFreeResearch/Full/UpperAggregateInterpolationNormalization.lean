import EnvyFreeResearch.Full.UpperAggregateInterpolationLoop
import EnvyFreeResearch.Full.UpperMixtureSampling

/-!
# Raw remaining supply and the fixed normalized mixture budget

Original oracle measures remain unchanged. The raw lower supply converts the
two-endpoint allowance to `(8/q)` times the original buffer's normalized row.
Distinct recipients are charged at most once against the fixed mixture.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperRecordedDomain

theorem two_endpoint_allowance_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (B : Set ℝ)
    (hpositive : 0 < μ.real B) (q : ℝ) (hq : 0 < q) :
    (2 * ENNReal.ofReal (1 / ((q / 4) * μ.real B))) • μ.restrict B =
      ENNReal.ofReal (8 / q) • cond μ B := by
  have hi : (μ B)⁻¹ = ENNReal.ofReal ((μ.real B)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hpositive, ofReal_measureReal (measure_ne_top μ B)]
  rw [ProbabilityTheory.cond, smul_smul, hi]
  congr 1
  have hq8 : 0 ≤ 8 / q := div_nonneg (by norm_num) hq.le
  have hscalar : 2 * (1 / ((q / 4) * μ.real B)) = (8 / q) * (μ.real B)⁻¹ := by
    field_simp
    norm_num
  calc
    (2 : ℝ≥0∞) * ENNReal.ofReal (1 / ((q / 4) * μ.real B)) =
        ENNReal.ofReal (2 * (1 / ((q / 4) * μ.real B))) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ = _ := by rw [hscalar, ENNReal.ofReal_mul hq8]

/-- A finite sublist with distinct recipient labels has no larger allowance
than the whole active population. -/
theorem distinct_recipient_budget {Job Agent : Type*} [Fintype Job] [Fintype Agent] [Nonempty Agent]
    (row : Agent → Measure ℝ) (recipient : Job → Agent) (hinj : Function.Injective recipient)
    (c : ℝ≥0∞) :
    (∑ j, c • row (recipient j)) ≤
      (c * Fintype.card Agent) • ((Fintype.card Agent : ℝ≥0∞)⁻¹ • ∑ a, row a) := by
  have hsum : (∑ j, row (recipient j)) ≤ ∑ a, row a := by
    classical
    exact Finset.sum_le_sum_of_injOn recipient hinj.injOn (Finset.subset_univ _)
      (fun _ _ => le_rfl) (fun _ _ _ => bot_le)
  have hcard : (Fintype.card Agent : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have heq : (c * Fintype.card Agent) * (Fintype.card Agent : ℝ≥0∞)⁻¹ = c := by
    rw [mul_assoc, ENNReal.mul_inv_cancel hcard (by finiteness), mul_one]
  rw [← Finset.smul_sum, smul_smul, heq]
  exact smul_le_smul_left c hsum

/-- The manuscript's exact fixed mixture is used; permanent component joins
and the actual oracle profile play no role in this finite recipient sum. -/
theorem mixture_budget {n : ℕ} {Agent Job : Type*} [Fintype Agent] [Nonempty Agent] [Fintype Job]
    (μ : Fin n → Measure ℝ) (active : Agent → Fin n) (cs : List Component)
    (recipient : Job → Agent) (hinj : Function.Injective recipient) (q : ℝ) :
    (∑ j, ENNReal.ofReal (8 / q) • cond (μ (active (recipient j))) (domain cs)) ≤
      (ENNReal.ofReal (8 / q) * Fintype.card Agent) • UpperMixtureSampling.mixture μ active cs :=
  distinct_recipient_budget (fun a => cond (μ (active a)) (domain cs)) recipient hinj _

end EnvyFreeResearch.Full.UpperAggregateInterpolation
