import EnvyFreeResearch.Full.UpperGridInterpolationKernel

/-!
# Immutable-grid interpolation estimate on the original grid

The final integrand is the ordinary cumulative interpolation sum on the
original sorted grid. The atomless independent test sample avoids that grid's
finitely many coordinates. Exchangeability was proved for the explicit iid
product experiment, with its permanent grid fixed before sampling.
-/

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperSortedGrid

variable {Row : Type*} [Fintype Row] [Nonempty Row]

theorem interpolationKernel_ae_eq_linear {b m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (hflat : FlatCompatible F L) (permanent : Fin b → ℝ) (samples : Fin m → ℝ)
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hsupport : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) :
    (fun test => interpolationKernel F L permanent samples test) =ᵐ[μ]
      (fun test => linearMaximum F L (sorted (augmented permanent samples)) test) := by
  have hnew : ∀ᵐ test ∂μ, ∀ j, augmented permanent samples j ≠ test := by
    apply ae_all_iff.mpr
    intro j
    exact (μ.ae_ne (augmented permanent samples j)).mono (fun _ h => Ne.symm h)
  filter_upwards [hnew, hsupport, μ.ae_ne 0, μ.ae_ne 1] with test hnew hbound hzero hone
  apply interpolationKernel_eq_linear F L hflat permanent samples test _ hnew
  exact ⟨lt_of_le_of_ne hbound.1 (Ne.symm hzero), lt_of_le_of_ne hbound.2 hone⟩

/-- The integrated interpolation bound for an immutable permanent logical
grid, any finite number of iid samples, and an independent atomless test.
The only flat-cell premise is the concrete compatibility of cumulative row
values with the interpolation coordinate; finite physical unions satisfy it
without requiring absolute continuity. -/
theorem integrated_linear_interpolation_le {b m : ℕ} (F : Row → ℝ → ℝ)
    (hF : ∀ i, Measurable (F i)) (L : ℝ → ℝ) (hL : Monotone L) (hLm : Measurable L)
    (hflat : FlatCompatible F L) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupport : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ samples : Fin m → ℝ, ∫ test,
      linearMaximum F L (sorted (augmented permanent samples)) test ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ 2 * ((Fintype.card Row : ℝ) - 1) / (m + 1 : ℕ) := by
  calc
    _ = ∫ samples : Fin m → ℝ, ∫ test, interpolationKernel F L permanent samples test ∂μ
        ∂Measure.pi (fun _ : Fin m => μ) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun samples => (integral_congr_ae
        (interpolationKernel_ae_eq_linear F L hflat permanent samples μ hsupport)).symm)
    _ ≤ _ := integrated_interpolation_le F hF L hL hLm permanent μ

end EnvyFreeResearch.Full.UpperGridInterpolation
