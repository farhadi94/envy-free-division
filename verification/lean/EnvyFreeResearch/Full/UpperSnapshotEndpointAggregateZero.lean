import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateGrid
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateCircle
import EnvyFreeResearch.Full.UpperSnapshotProtocolZeroInterpolation

/-! Actual original-grid / complete-history probability bound for the zero
Snapshot branch. Agreement of cached cell rows alone is insufficient; the
common physical interpolation event discharges the inside-cell obstruction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperAggregateInterpolation UpperGridInterpolation UpperSortedGrid UpperSnapshotSmall Chores
variable {n k q m : ℕ} [Nonempty (Fin k)]

def zeroPoints (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m : ℕ) (cutter : Fin k)
    (p : (Fin m → Fin k × I) × UpperSnapshotSmall.Circle) : Fin k → ℝ :=
  (partitionRun policy (UpperGridCache.aligned policy active origin q m p.1)
    (active cutter) (equalTargets k) p.2).1

set_option maxHeartbeats 1200000 in
theorem zeroPoints_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (q m : ℕ) (cutter : Fin k) (j : Fin k) :
    Measurable (fun p => zeroPoints policy active origin q m cutter p j) := by
  have hstate : Measurable (fun p : (Fin m → Fin k × I) × UpperSnapshotSmall.Circle =>
      UpperGridCache.aligned policy active origin q m p.1) :=
    UpperLogicalPreparationGuard.fixed_origin_projection_measurable
      (fun p : State n × (Fin m → Fin k × I) => UpperGridCache.aligned policy active p.1 q m p.2)
      (UpperGridCache.aligned_measurable policy hmeas active q m) origin
  exact (measurable_pi_apply j).comp (measurable_fst.comp
    (execute_measurable policy hmeas _ (active cutter) (fun _ => shifts (equalTargets k)) Prod.snd
      hstate (fun _ => measurable_const) measurable_snd))

theorem actual_zero_interpolation_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (b : ℝ) (hb : 0 < b) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m).prod
      (volume : Measure UpperSnapshotSmall.Circle))
      {p | BadSupportedRecordedUnion (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
        (UpperGridMerge.cuts policy active origin q m p.1)
        (zeroPoints policy active origin q m cutter p) b} ≤
      ENNReal.ofReal (2 * ((k : ℝ) - 1) * (k : ℝ)^2 * (1 + b) /
        (b * (m + 1 : ℕ))) := by
  apply (original_grid_supported_probability μ active policy hpolicy hmeas origin hgood hpositive
    (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
    (volume : Measure UpperSnapshotSmall.Circle) (zeroPoints policy active origin q m cutter)
    (zeroPoints_measurable policy hmeas active origin q m cutter) ((k : ℝ)^2) b (sq_nonneg _) hb ?_).trans_eq
  · simp only [Fintype.card_fin]
  · apply ae_of_all
    intro draw u hu hu0
    have hw := UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw
    have hd := UpperGridCache.aligned_domain policy active origin q m draw
    have h := circle_charge_le_mixture μ active origin.cells cutter (hpositive cutter) policy hpolicy hmeas
      (UpperGridCache.aligned policy active origin q m draw) hw
      (by rw [hd]) 1 zero_lt_one (by rw [hd]; simp) (shifts (equalTargets k)) u hu
    change (∫⁻ start, ∑ j, u (zeroPoints policy active origin q m cutter (draw,start) j)
      ∂(volume : Measure UpperSnapshotSmall.Circle)) ≤ _ at h
    convert h using 1
    simp [ENNReal.ofReal_pow, pow_two]

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
