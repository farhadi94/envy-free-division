import EnvyFreeResearch.Full.UpperAggregateInterpolationBoundary
import EnvyFreeResearch.Full.UpperAggregateInterpolationPredictable

/-! The proved immutable-grid estimate in lower-integral form, ready for
adaptive endpoint charging and one Markov inequality. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperGridInterpolation UpperGridSensitivity UpperSortedGrid

theorem error_fraction_mem_unit (D e : ℝ) (hD : 0 ≤ D) (he : 0 ≤ e) :
    0 ≤ e / (D + e) ∧ e / (D + e) ≤ 1 := by
  refine ⟨div_nonneg he (add_nonneg hD he), ?_⟩
  by_cases hd : D + e = 0
  · simp [hd]
  · exact (div_le_one (lt_of_le_of_ne (add_nonneg hD he) (Ne.symm hd))).mpr (by linarith)

variable {Row : Type*} [Fintype Row] [Nonempty Row]

theorem linearMaximum_mem_unit {n : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (cuts : Fin (n + 1) → ℝ) (z : ℝ) :
    0 ≤ linearMaximum F L cuts z ∧ linearMaximum F L cuts z ≤ 1 := by
  have hpair (ij : Row × Row) := error_fraction_mem_unit
    (distance (linearRows F cuts) ij.1 ij.2) (linearError F L cuts z ij.1 ij.2)
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (abs_nonneg _)
  constructor
  · obtain ⟨i⟩ := ‹Nonempty Row›
    exact (hpair (i, i)).1.trans
      (Finset.le_sup' (fun ij : Row × Row => linearError F L cuts z ij.1 ij.2 /
        (distance (linearRows F cuts) ij.1 ij.2 + linearError F L cuts z ij.1 ij.2))
          (Finset.mem_univ (i, i)))
  · exact Finset.sup'_le _ _ (fun ij _ => (hpair ij).2)

def immutableCharge {b m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin m → ℝ) (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (linearMaximum F L (sorted (augmented permanent samples)) z)

theorem immutableCharge_measurable {b m : ℕ} (F : Row → ℝ → ℝ) (hF : ∀ i, Measurable (F i))
    (L : ℝ → ℝ) (hL : Measurable L) (permanent : Fin b → ℝ) :
    Measurable (fun p : (Fin m → ℝ) × ℝ => immutableCharge F L permanent p.1 p.2) := by
  apply Measurable.ennreal_ofReal
  exact linearMaximum_measurable F hF L hL _
    (fun e => ((measurable_pi_apply e).comp (sorted_measurable (augmented permanent) (augmented_measurable permanent))).comp measurable_fst)
    _ measurable_snd

/-- No aggregate expectation is assumed: this is the already constructed
MST/deletion/exchangeability bound converted to nonnegative integration. -/
theorem immutableCharge_integrated_bound {b m : ℕ} (F : Row → ℝ → ℝ)
    (hF : ∀ i, Measurable (F i)) (L : ℝ → ℝ) (hL : Monotone L) (hLm : Measurable L)
    (hflat : FlatCompatible F L) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupport : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1) :
    (∫⁻ samples : Fin m → ℝ, ∫⁻ z, immutableCharge F L permanent samples z ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) ≤
      ENNReal.ofReal (2 * ((Fintype.card Row : ℝ) - 1) / (m + 1 : ℕ)) := by
  let f (p : (Fin m → ℝ) × ℝ) := linearMaximum F L (sorted (augmented permanent p.1)) p.2
  have hf : Measurable f := linearMaximum_measurable F hF L hLm _
    (fun e => ((measurable_pi_apply e).comp (sorted_measurable (augmented permanent) (augmented_measurable permanent))).comp measurable_fst)
    _ measurable_snd
  have hint : Integrable f ((Measure.pi (fun _ : Fin m => μ)).prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    apply ae_of_all
    intro p
    change ‖linearMaximum F L (sorted (augmented permanent p.1)) p.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (linearMaximum_mem_unit _ _ _ _).1]
    exact (linearMaximum_mem_unit _ _ _ _).2
  have hinner (samples : Fin m → ℝ) : Integrable (fun z => f (samples, z)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    apply ae_of_all
    intro z
    change ‖linearMaximum F L (sorted (augmented permanent samples)) z‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (linearMaximum_mem_unit _ _ _ _).1]
    exact (linearMaximum_mem_unit _ _ _ _).2
  have hin (samples : Fin m → ℝ) :
      (∫⁻ z, immutableCharge F L permanent samples z ∂μ) = ENNReal.ofReal (∫ z, f (samples, z) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hinner samples)
      (ae_of_all _ (fun z => (linearMaximum_mem_unit _ _ _ _).1))).symm
  simp_rw [hin]
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integral_prod_left
    (ae_of_all _ (fun samples => integral_nonneg (fun z => (linearMaximum_mem_unit _ _ _ _).1)))]
  exact ENNReal.ofReal_le_ofReal
    (integrated_linear_interpolation_le F hF L hL hLm hflat permanent μ hsupport)

/-- A single lower-integral Markov bound, useful before converting finite
endpoint totals back to real-valued error budgets. -/
theorem common_lintegral_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (charge : Ω → ℝ≥0∞) (hcharge : AEMeasurable charge μ) (bad : Set Ω)
    (C b : ℝ) (hb : 0 < b) (hmean : (∫⁻ ω, charge ω ∂μ) ≤ ENNReal.ofReal C)
    (hbad : ∀ ω ∈ bad, ENNReal.ofReal (b / (1 + b)) ≤ charge ω) :
    μ bad ≤ ENNReal.ofReal (C * (1 + b) / b) := by
  have ht : 0 < b / (1 + b) := div_pos hb (by linarith)
  calc
    μ bad ≤ μ {ω | ENNReal.ofReal (b / (1 + b)) ≤ charge ω} := measure_mono hbad
    _ ≤ (∫⁻ ω, charge ω ∂μ) / ENNReal.ofReal (b / (1 + b)) :=
      meas_ge_le_lintegral_div hcharge (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal (b / (1 + b)) := by gcongr
    _ = ENNReal.ofReal (C / (b / (1 + b))) := (ENNReal.ofReal_div_of_pos ht).symm
    _ = _ := by congr 1; field_simp

end EnvyFreeResearch.Full.UpperAggregateInterpolation
