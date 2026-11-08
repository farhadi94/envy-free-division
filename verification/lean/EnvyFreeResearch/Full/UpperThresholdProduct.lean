import EnvyFreeResearch.Full.UpperIsolationMean
import Mathlib.MeasureTheory.Integral.Pi

/-! Independent seed thresholds and the actual coordinate-fiber integral.
The product law is fixed before an assignment is chosen. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace EnvyFreeResearch.Full.UpperThresholdProduct

open UpperSeeds UpperSeedProbability UpperIsolationMean

def tapeLaw (M L : ℕ) : Measure (Fin M → Fin (L + 1)) :=
  Measure.pi (fun _ => thresholdLaw)

instance tapeLaw_probability (M L : ℕ) : IsProbabilityMeasure (tapeLaw M L) := by
  unfold tapeLaw
  infer_instance

/-- Splitting any one coordinate gives its fresh uniform threshold and the
unchanged independent law of all remaining coordinates. -/
theorem coordinate_integral {M L : ℕ} (i : Fin (M + 1))
    (f : (Fin (M + 1) → Fin (L + 1)) → ℝ) :
    (∫ draw, f draw ∂tapeLaw (M + 1) L) =
      ∫ rest, ∫ t, f (Fin.insertNth i t rest) ∂thresholdLaw ∂tapeLaw M L := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (M + 1) => (thresholdLaw : Measure (Fin (L + 1)))) i).symm
  have heq := hp.integral_comp' f
  unfold tapeLaw
  rw [← heq, integral_prod_symm _ (Integrable.of_finite)]
  rfl

theorem coordinate_integral_le {M L : ℕ} (i : Fin (M + 1))
    (f : (Fin (M + 1) → Fin (L + 1)) → ℝ) (bound : ℝ)
    (hfiber : ∀ rest, (∫ t, f (Fin.insertNth i t rest) ∂thresholdLaw) ≤ bound) :
    (∫ draw, f draw ∂tapeLaw (M + 1) L) ≤ bound := by
  rw [coordinate_integral i f]
  calc
    _ ≤ ∫ _rest, bound ∂tapeLaw M L :=
      integral_mono Integrable.of_finite (integrable_const bound) hfiber
    _ = bound := by simp

/-- A separated seed coordinate controls the full product expectation even
when its fixed offset is an arbitrary function of all other thresholds. -/
theorem product_truncated_charge_expectation {M L : ℕ} (i : Fin (M + 1))
    (gamma : Fin L → ℝ) (A lam a : ℝ)
    (score : (Fin (M + 1) → Fin (L + 1)) → ℝ)
    (offset : (Fin M → Fin (L + 1)) → ℝ)
    (hscore : ∀ rest t, score (Fin.insertNth i t rest) = offset rest + value gamma t)
    (hA : 0 < A) (hlam : 0 ≤ lam) (ha : 0 < a) (haone : a ≤ 1)
    (hgap : ∀ j, A / 3 ≤ |gamma j|) :
    (∫ draw, max (charge A lam (score draw) - a) 0 ∂tapeLaw (M + 1) L) ≤
      (12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ) := by
  apply coordinate_integral_le i
  intro rest
  simp_rw [hscore]
  exact truncated_charge_expectation gamma A lam (offset rest) a hA hlam ha haone hgap

end EnvyFreeResearch.Full.UpperThresholdProduct
