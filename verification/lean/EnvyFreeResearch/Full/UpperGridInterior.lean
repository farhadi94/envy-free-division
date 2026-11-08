import EnvyFreeResearch.Full.UpperGridMerge

/-! The common quantile grid has a unique zero boundary. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperGridInterior

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperQuantileExecution
  UpperStageMeasurable UpperUnionSampling UpperCommonGrid Chores

theorem normalized_cdf_zero (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (cells : List Component) (hpositive : 0 < μ.real (domain cells)) :
    cdf (cond μ (domain cells)) 0 = 0 := by
  have hs : domain cells ∩ Iic (0 : ℝ) ⊆ {0} := by
    intro x hx
    exact le_antisymm hx.2 (domain_subset_unit cells hx.1).1
  have hz : μ (domain cells ∩ Iic (0 : ℝ)) = 0 := measure_mono_null hs (measure_singleton 0)
  rw [normalized_cdf μ (domain cells) hpositive]
  simp only [measureReal_def, hz, ENNReal.toReal_zero, zero_div]

theorem raw_zero_only {m : ℕ} (endpoints : Fin m → ℝ) (hpos : ∀ i, 0 < endpoints i)
    (i : Fin (m + 2)) (hi : raw endpoints i = 0) : i = 0 := by
  revert hi
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro h
    simp [raw] at h
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      rfl
    · intro h
      rw [raw_endpoint] at h
      exact ((hpos j).ne' h).elim

theorem grid_zero_only {m : ℕ} (endpoints : Fin m → ℝ) (hpos : ∀ i, 0 < endpoints i)
    (hbound : ∀ i, endpoints i ∈ Icc (0 : ℝ) 1) (i : Fin (m + 2)) (hi : grid endpoints i = 0) : i = 0 := by
  have h0 := grid_first endpoints hbound
  have hp := raw_zero_only endpoints hpos (UpperSortedGrid.select (raw endpoints) i) hi
  have hp0 := raw_zero_only endpoints hpos (UpperSortedGrid.select (raw endpoints) 0) h0
  exact (UpperSortedGrid.select (raw endpoints)).injective (hp.trans hp0.symm)

variable {n : ℕ} {Agent : Type*} [Fintype Agent]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem quantile_endpoints_positive (q : ℕ) (i : Fin (UpperRecordedQuantiles.count (Agent := Agent) q)) :
    0 < (UpperRecordedQuantiles.run policy active origin q).1 i := by
  have heq : (UpperRecordedQuantiles.run policy active origin q).1 =
      (execution μ policy active (fun a => values origin (active a)) origin.cells q origin.history).1 := by
    unfold UpperRecordedQuantiles.run UpperRecordedGrid.execute
    dsimp only
    rw [UpperRecordedGrid.samples_eq_mixture μ policy active origin hgood]
    rfl
  rw [heq]
  let job := (Fintype.equivFin (Agent × Fin q)).symm i
  have hr := roots_spec μ policy hpolicy active (fun a => values origin (active a)) origin.cells
    hgood.1 hgood.2.1 (fun a => values_correct μ origin hgood (active a)) hpositive q origin.history job.1 job.2
  have hidx : jobIndex job.1 job.2 = i := by simp only [jobIndex, Prod.mk.eta, job, Equiv.apply_symm_apply]
  have hv : 0 ≤ (execution μ policy active (fun a => values origin (active a)) origin.cells q origin.history).1 i := by
    simpa only [root, hidx] using hr.1.1
  have hneq : (execution μ policy active (fun a => values origin (active a)) origin.cells q origin.history).1 i ≠ 0 := by
    intro hz
    have hc := hr.2
    simp only [root, hidx, hz, normalized_cdf_zero _ origin.cells (hpositive job.1)] at hc
    have hp : 0 < ((job.2.val : ℝ) + 1) / (q + 1) :=
      div_pos (by positivity) (by positivity)
    linarith
  exact lt_of_le_of_ne hv (Ne.symm hneq)

/-- Permanent quantile boundaries are strictly away from zero except the
adjoined resource boundary, so the first logical cell's literal endpoint is
assigned consistently under later sampled refinement. -/
theorem coarse_zero_only (q : ℕ) (i : Fin (UpperRecordedQuantiles.count (Agent := Agent) q + 2))
    (hi : UpperRecordedQuantiles.cuts policy active origin q i = 0) : i = 0 :=
  grid_zero_only _ (quantile_endpoints_positive μ policy hpolicy active origin hgood hpositive q)
    (UpperGridMerge.coarse_endpoints μ policy hpolicy active origin hgood hpositive q) i hi

end EnvyFreeResearch.Full.UpperGridInterior
