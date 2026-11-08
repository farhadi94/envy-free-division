import EnvyFreeResearch.Full.ChoresTwoAgent
import EnvyFreeResearch.Full.UpperCircularStage

/-!
# Measure-profile adapter for the physical randomized primitive

The oracle cumulative profile is constructed from actual finite atomless Borel
measures using the physical prefix construction. The CDF equation and unit total
needed by the circular stage are derived from normalization and support.
This is a primitive theorem, not the full randomized envy-free upper bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperProfiles

open Chores UpperCircular UpperCircularStage

abbrev Circle := UpperCircular.Circle

theorem prefixCost_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1) :
    prefixCost μ 0 = cdf μ := by
  funext x
  rw [cdf_eq_real]
  apply measureReal_congr
  filter_upwards [hsupport] with y hy
  simp only [mem_Icc, mem_Iic, hy.1, true_and]

theorem measureProfile_cdf {Agent : Type*} (μ : Agent → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (cutter : Agent) [IsProbabilityMeasure (μ cutter)]
    (hsupport : ∀ᵐ x ∂μ cutter, x ∈ Icc (0 : ℝ) 1) :
    (measureProfile μ).cumulative cutter = cdf (μ cutter) :=
  prefixCost_eq_cdf (μ cutter) hsupport

theorem measureProfile_total {Agent : Type*} (μ : Agent → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (cutter : Agent) [IsProbabilityMeasure (μ cutter)]
    (hsupport : ∀ᵐ x ∂μ cutter, x ∈ Icc (0 : ℝ) 1) :
    (measureProfile μ).cumulative cutter 1 = 1 := by
  change (μ cutter).real (Icc 0 1) = 1
  calc
    _ = (μ cutter).real univ := by
      apply measureReal_congr
      filter_upwards [hsupport] with x hx
      simp [hx]
    _ = 1 := probReal_univ

/-- A concrete probabilistic and physical primitive with its actual ordinary
query trace. All observer measures are supplied as actual measures. The policy
may choose each root using the entire earlier answered history. The only
probabilistic input is a fresh uniform circular start, itself realized from an
ordinary uniform real draw by `project_preserves_volume`.

The result proves exact own mass and actual unconditional query accounting;
the expected foreign-mass law is for every finite or sigma-finite foreign
measure, without an absolute-continuity assumption. -/
theorem circular_stage_primitive {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (cutter : Fin n) [IsProbabilityMeasure (μ cutter)]
    (hsupport : ∀ᵐ x ∂μ cutter, x ∈ Icc (0 : ℝ) 1)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (history : History n) (amount : I)
    (hfirstMeas : Measurable (firstEndpoint policy history cutter))
    (hlastMeas : Measurable (lastEndpoint policy history cutter amount))
    (foreign : Measure ℝ) [SFinite foreign] :
    (∀ start, (μ cutter).real (output policy history cutter amount start) = (amount : ℝ)) ∧
    (∀ start, (finalHistory policy history cutter amount start).length =
      history.length + 2 * (n + 1)) ∧
    (∀ start, ((finalHistory policy history cutter amount start).map Prod.fst).countP isCut =
      (history.map Prod.fst).countP isCut + 2) ∧
    ((∫⁻ start, foreign (output policy history cutter amount start)
      ∂(volume : Measure Circle)) = ENNReal.ofReal (amount : ℝ) * foreign (Icc 0 1)) := by
  have htotal := measureProfile_total μ cutter hsupport
  have hCDF := measureProfile_cdf μ cutter hsupport
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro start
    exact output_exact_cutter_mass (measureProfile μ) policy hpolicy history cutter htotal
      (μ cutter) hCDF hsupport amount start
  · exact stage_query_count policy history cutter amount
  · exact stage_cut_count policy history cutter amount
  · exact output_foreign_mass_expectation (measureProfile μ) policy hpolicy history cutter htotal
      (μ cutter) hCDF amount hfirstMeas hlastMeas foreign

/-- The physical stage can be driven by an ordinary uniform real draw on
`[0,1]`; the circle is a deterministic representation of that draw. -/
theorem uniform_real_stage_foreign_expectation {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (cutter : Fin n) [IsProbabilityMeasure (μ cutter)]
    (hsupport : ∀ᵐ x ∂μ cutter, x ∈ Icc (0 : ℝ) 1)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (history : History n) (amount : I)
    (hfirstMeas : Measurable (firstEndpoint policy history cutter))
    (hlastMeas : Measurable (lastEndpoint policy history cutter amount))
    (foreign : Measure ℝ) [SFinite foreign] :
    (∫⁻ draw, foreign (output policy history cutter amount (project draw))
      ∂(volume : Measure I)) = ENNReal.ofReal (amount : ℝ) * foreign (Icc 0 1) := by
  have hcharge : Measurable (fun start => foreign (output policy history cutter amount start)) :=
    measurable_measure_prodMk_left
      (UpperPhysical.measurable_physical_membership (Icc 0 1) measurableSet_Icc amount
        _ _ hfirstMeas hlastMeas)
  rw [project_preserves_volume.lintegral_comp hcharge]
  exact (circular_stage_primitive μ cutter hsupport policy hpolicy history amount
    hfirstMeas hlastMeas foreign).2.2.2

end EnvyFreeResearch.Full.UpperProfiles
