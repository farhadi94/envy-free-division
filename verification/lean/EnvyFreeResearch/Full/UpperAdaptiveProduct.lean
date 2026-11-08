import EnvyFreeResearch.Full.UpperEnvelopeStage
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Unconditional finite fresh-tape composition

An actual failure event can depend on preceding starts and can disappear
after early rejection. Bounding its fresh-coordinate fibers before
averaging gives a bound on the whole product law. Summing these unconditioned
events includes the first rejecting correction and never conditions on
having reached or passed a correction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAdaptiveProduct

variable {Draw : Type*} [MeasurableSpace Draw]

def tapeLaw (rho : Measure Draw) (m : ℕ) : Measure (Fin m → Draw) := Measure.pi (fun _ => rho)

instance tapeLaw_probability (rho : Measure Draw) [IsProbabilityMeasure rho] (m : ℕ) :
    IsProbabilityMeasure (tapeLaw rho m) := by unfold tapeLaw; infer_instance

/-- The fiber may retain every other tape coordinate. In a sequential
implementation the reached state ignores future coordinates; only the
fresh coordinate is averaged here. -/
theorem event_of_fiber_bound (rho : Measure Draw) [IsProbabilityMeasure rho]
    {m : ℕ} (j : Fin (m + 1)) (bad : Set (Fin (m + 1) → Draw)) (hbad : MeasurableSet bad)
    (bound : ℝ≥0∞)
    (hfiber : ∀ rest : Fin m → Draw, rho {draw | Fin.insertNth j draw rest ∈ bad} ≤ bound) :
    tapeLaw rho (m + 1) bad ≤ bound := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => rho) j).symm
  have hpre := hbad.preimage hp.measurable
  unfold tapeLaw
  rw [← hp.measure_preimage hbad.nullMeasurableSet, Measure.prod_apply_symm hpre]
  change (∫⁻ rest : Fin m → Draw, rho {draw | Fin.insertNth j draw rest ∈ bad}
    ∂tapeLaw rho m) ≤ bound
  calc
    _ ≤ ∫⁻ _rest : Fin m → Draw, bound ∂tapeLaw rho m := lintegral_mono hfiber
    _ = _ := by simp

/-- A finite union of reached-failure events, measured on the original
fresh tape. No successful-prefix conditional distribution occurs. -/
theorem any_failure_probability (rho : Measure Draw) [IsProbabilityMeasure rho]
    {m : ℕ} (bad : Fin (m + 1) → Set (Fin (m + 1) → Draw))
    (hbad : ∀ j, MeasurableSet (bad j)) (bound : Fin (m + 1) → ℝ≥0∞)
    (hfiber : ∀ j (rest : Fin m → Draw),
      rho {draw | Fin.insertNth j draw rest ∈ bad j} ≤ bound j) :
    tapeLaw rho (m + 1) (⋃ j, bad j) ≤ ∑ j, bound j := by
  calc
    _ ≤ ∑ j, tapeLaw rho (m + 1) (bad j) := measure_iUnion_fintype_le (tapeLaw rho (m + 1)) bad
    _ ≤ _ := Finset.sum_le_sum (fun j _ => event_of_fiber_bound rho j (bad j) (hbad j) (bound j) (hfiber j))

/-- Deficits are fixed before correction starts. Their pathwise budget
controls all reached estimated failures on the complete independent tape. -/
theorem deficit_budget_probability (rho : Measure Draw) [IsProbabilityMeasure rho]
    {m : ℕ} (bad : Fin (m + 1) → Set (Fin (m + 1) → Draw))
    (hbad : ∀ j, MeasurableSet (bad j)) (eps : Fin (m + 1) → ℝ)
    (heps : ∀ j, 0 ≤ eps j) (N lam budget : ℝ) (hN : 0 ≤ N) (hlam : 0 < lam)
    (hbudget : (∑ j, eps j) ≤ budget)
    (hfiber : ∀ j (rest : Fin m → Draw),
      rho {draw | Fin.insertNth j draw rest ∈ bad j} ≤ ENNReal.ofReal (8 * eps j * N / lam)) :
    tapeLaw rho (m + 1) (⋃ j, bad j) ≤ ENNReal.ofReal (8 * budget * N / lam) := by
  have hs := any_failure_probability rho bad hbad (fun j => ENNReal.ofReal (8 * eps j * N / lam)) hfiber
  have hnonneg (j : Fin (m + 1)) : 0 ≤ 8 * eps j * N / lam :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (heps j)) hN) hlam.le
  have heq : (∑ j, 8 * eps j * N / lam) = 8 * (∑ j, eps j) * N / lam := by
    rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ j, ENNReal.ofReal (8 * eps j * N / lam) := hs
    _ = ENNReal.ofReal (∑ j, 8 * eps j * N / lam) :=
      (ENNReal.ofReal_sum_of_nonneg (fun j _ => hnonneg j)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by rw [heq]; gcongr)

/-- Averaging over the preceding preparation history keeps the same
uniform bound, and includes preparation branches whose failure event is
empty. This is a direct product-law calculation. -/
theorem preparation_average {History : Type*} [MeasurableSpace History]
    (mu : Measure History) (rho : Measure Draw) [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
    (m : ℕ) (bad : Set (History × (Fin m → Draw))) (hbad : MeasurableSet bad)
    (bound : ℝ≥0∞) (hfiber : ∀ history, tapeLaw rho m {draw | (history, draw) ∈ bad} ≤ bound) :
    (mu.prod (tapeLaw rho m)) bad ≤ bound := by
  rw [Measure.prod_apply hbad]
  calc
    _ ≤ ∫⁻ _history, bound ∂mu := lintegral_mono hfiber
    _ = _ := by simp

end EnvyFreeResearch.Full.UpperAdaptiveProduct
