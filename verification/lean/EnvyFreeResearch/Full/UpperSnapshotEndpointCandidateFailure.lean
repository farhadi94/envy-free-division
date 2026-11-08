import EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailureMeasurable

/-! Original-tape probability of exhausting all16k actual small candidates.
The sampler is not conditioned on its selected branch or interpolation event. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailure
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperSnapshotRepetition UpperSnapshotEndpointAggregate Chores
variable {n k : ℕ}

theorem actual_original_exhaustion_quarter
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (hk : 2 ≤ k) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (q m : ℕ) (tau : ℝ) (htau : 0 < tau) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m).prod
      (law (volume.prod volume : Measure (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle)) (16*k)))
      {p | smallBranch hk policy active origin cutter q m tau p.1 ∧
        (packetResult hk policy active origin cutter q m tau p).2 = none} ≤ 1/4 := by
  letI : Nonempty (Fin k) := ⟨cutter⟩
  rw [Measure.prod_apply (exhaustion_measurableSet hk policy hmeas active origin cutter q m tau)]
  calc
    _ ≤ ∫⁻ _ : GridSeed k m, ENNReal.ofReal ((1 : ℝ)/4)
        ∂UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m := by
      apply lintegral_mono
      intro draw
      by_cases hb : smallBranch hk policy active origin cutter q m tau draw
      · simp only [Set.preimage_setOf_eq, hb, true_and]
        exact actual_original_fiber_failure μ policy hpolicy hmeas active hk origin hgood hpositive
          cutter q m tau htau draw hb
      · simp only [Set.preimage_setOf_eq, hb, false_and, Set.setOf_false, measure_empty]
        exact bot_le
    _ = 1/4 := by
      simp only [lintegral_const, measure_univ, mul_one]
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

end EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailure
