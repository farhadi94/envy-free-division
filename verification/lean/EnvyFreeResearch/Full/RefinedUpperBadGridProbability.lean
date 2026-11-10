import EnvyFreeResearch.Full.RefinedUpperStability

/-! The actual protected endpoint event has an integrable random mass.
Markov's inequality gives the grid failure probability used by Repair. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperStability
variable {b m K : ℕ}

theorem protectedMass_integrable
    (procedure : (Fin (b+(m+1)+2) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => procedure s k)) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun samples : Fin m → ℝ => μ.real (protectedBad procedure permanent samples))
      (Measure.pi (fun _ : Fin m => μ)) := by
  let join (z : (Fin m → ℝ) × ℝ) : Fin (m+1) → ℝ := Fin.cons z.2 z.1
  have hj : Measurable join := by
    apply Measurable.of_eval
    intro i
    refine Fin.cases measurable_snd (fun j => (measurable_pi_apply j).comp measurable_fst) i
  let event := fun z : (Fin m → ℝ) × ℝ => coincidence procedure permanent (join z) 0
  have he : Measurable event := (coincidence_measurable procedure hp permanent 0).comp hj
  have hi := integrable_bounded_nonneg ((Measure.pi (fun _ : Fin m => μ)).prod μ)
    event he 1 (fun z => coincidence_nonneg _ _ _ _) (fun z => coincidence_le_one _ _ _ _)
  have hh := hi.integral_prod_left
  simpa only [event, join, coincidence_integral_eq_measure procedure hp] using hh

theorem physical_bad_grid_probability {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (rows : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (rows i)]
    (policy : UpperCircularStage.Policy n) (active : Agent → Fin n)
    (origin : UpperCorrectionExecution.State n) (q : ℕ)
    (jobs finalJobs : List (Agent × Agent)) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi (fun _ : Fin m => μ))
      {samples | δ ≤ μ.real (physicalBad rows policy active origin q jobs finalJobs permanent samples)} ≤
      ENNReal.ofReal ((((4*jobs.length+4*finalJobs.length : ℕ) : ℝ)/(m+1 : ℕ))/δ) := by
  let cost := fun samples : Fin m → ℝ =>
    μ.real (physicalBad rows policy active origin q jobs finalJobs permanent samples)
  have hint : Integrable cost (Measure.pi (fun _ : Fin m => μ)) :=
    protectedMass_integrable _ (RefinedUpperPeeling.endpointProcedure_measurable _
      (RefinedUpperPeeling.physicalCumulative_measurable rows active origin) _ jobs finalJobs) permanent μ
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (Measure.pi (fun _ : Fin m => μ)) (fun _ => measureReal_nonneg)) hint δ
  have he := physical_expected_bad_measure_le (m := m) rows policy active origin q jobs finalJobs permanent μ
  have hb : (Measure.pi (fun _ : Fin m => μ)).real {samples | δ ≤ cost samples} ≤
      (((4*jobs.length+4*finalJobs.length : ℕ) : ℝ)/(m+1 : ℕ))/δ := by
    apply (le_div_iff₀ hδ).mpr
    simpa only [mul_comm] using hm.trans he
  rw [← ofReal_measureReal (μ := Measure.pi (fun _ : Fin m => μ))]
  exact ENNReal.ofReal_le_ofReal hb

end EnvyFreeResearch.Full.RefinedUpperStability
