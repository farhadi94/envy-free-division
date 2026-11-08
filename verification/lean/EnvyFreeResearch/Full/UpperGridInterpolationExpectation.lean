import EnvyFreeResearch.Full.UpperGridInterpolationSamples

/-!
# Exchangeable grid averaging

The actual iid product law is invariant under coordinate swaps. Finite
symmetry of the computed scores and their pathwise deletion bound yield the
factor `1 / (m+1)`. Product disintegration then gives the independent-test
sample integral.
-/

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

variable {Row : Type*} [Fintype Row] [Nonempty Row] {b n : ℕ}

theorem sampleScore_integral_eq (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (permanent : Fin b → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (i j : Fin n) :
    (∫ samples, sampleScore F L permanent samples i ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ samples, sampleScore F L permanent samples j ∂Measure.pi (fun _ : Fin n => μ) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Equiv.swap i j)
  have he (samples : Fin n → ℝ) : e samples = samples ∘ Equiv.swap i j := by
    funext k
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) (Equiv.swap i j) samples (Equiv.swap i j k)
    simpa [e] using h
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => μ) (Equiv.swap i j)
  calc
    _ = ∫ samples, sampleScore F L permanent (e samples) i ∂Measure.pi (fun _ : Fin n => μ) :=
      (hp.integral_comp' (fun samples => sampleScore F L permanent samples i)).symm
    _ = _ := integral_congr_ae (ae_of_all _ (fun samples => by
      change sampleScore F L permanent (e samples) i = _
      rw [he, sampleScore_swap]))

/-- The exchangeability step with all expectations taken over the actual
finite iid product measure, rather than an assumed equal-expectation law. -/
theorem sampleScore_expectation_le (F : Row → ℝ → ℝ) (hF : ∀ i, Measurable (F i))
    (L : ℝ → ℝ) (hL : Monotone L) (hLm : Measurable L) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : Fin n) :
    (∫ samples, sampleScore F L permanent samples i ∂Measure.pi (fun _ : Fin n => μ)) ≤
      2 * ((Fintype.card Row : ℝ) - 1) / n := by
  have hint (j : Fin n) := sampleScore_integrable F hF L hL hLm permanent μ j
  have hsum : (∑ j : Fin n, ∫ samples, sampleScore F L permanent samples j
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ 2 * ((Fintype.card Row : ℝ) - 1) := calc
    _ = ∫ samples, ∑ j : Fin n, sampleScore F L permanent samples j
        ∂Measure.pi (fun _ : Fin n => μ) := (integral_finsetSum _ (fun j _ => hint j)).symm
    _ ≤ ∫ _samples : Fin n → ℝ, 2 * ((Fintype.card Row : ℝ) - 1)
        ∂Measure.pi (fun _ : Fin n => μ) :=
      integral_mono (integrable_finsetSum _ (fun j _ => hint j)) (integrable_const _)
        (sum_sampleScore F L hL permanent)
    _ = _ := by simp
  have heq (j : Fin n) := sampleScore_integral_eq F L permanent μ j i
  simp_rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  exact (le_div_iff₀ hn).mpr (by nlinarith)

/-- The test coordinate is adjoined to the original samples and its own
interior coordinate is deleted in the actual sorted augmented grid. -/
def interpolationKernel {m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin m → ℝ) (test : ℝ) : ℝ :=
  sampleScore F L permanent (Fin.cons test samples) 0

/-- Integrated immutable-grid interpolation estimate. Repeated sample or
permanent coordinates are allowed by the total finite score definition.
At unique test coordinates this is the ordinary normalized interpolation
error, as certified by the coarsening and cumulative-error theorems. -/
theorem integrated_interpolation_le {m : ℕ} (F : Row → ℝ → ℝ)
    (hF : ∀ i, Measurable (F i)) (L : ℝ → ℝ) (hL : Monotone L) (hLm : Measurable L)
    (permanent : Fin b → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ samples : Fin m → ℝ, ∫ test, interpolationKernel F L permanent samples test ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ 2 * ((Fintype.card Row : ℝ) - 1) / (m + 1 : ℕ) := by
  let score := fun samples : Fin (m + 1) → ℝ => sampleScore F L permanent samples 0
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
  have he (z : ℝ × (Fin m → ℝ)) : e z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv ]
  have hint : Integrable (score ∘ e) (μ.prod (Measure.pi (fun _ : Fin m => μ))) :=
    hp.integrable_comp_of_integrable (sampleScore_integrable F hF L hL hLm permanent μ 0)
  have heq : (∫ samples : Fin m → ℝ, ∫ test, interpolationKernel F L permanent samples test ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) =
      ∫ samples, score samples ∂Measure.pi (fun _ : Fin (m + 1) => μ) := by
    calc
      _ = ∫ z : ℝ × (Fin m → ℝ), score (e z) ∂μ.prod (Measure.pi (fun _ : Fin m => μ)) := by
        simpa only [Function.comp_def, he, score, interpolationKernel] using
          (integral_prod_symm (score ∘ e) hint).symm
      _ = _ := hp.integral_comp' score
  rw [heq]
  exact sampleScore_expectation_le F hF L hL hLm permanent μ 0

end EnvyFreeResearch.Full.UpperGridInterpolation
