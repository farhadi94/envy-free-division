import EnvyFreeResearch.Full.RefinedUpperStabilityProtectedEvent
import EnvyFreeResearch.Full.RefinedUpperStabilityPointwise
import EnvyFreeResearch.Full.RefinedUpperStabilityRecordedProcedure

/-!
# Stability of maximum-determinant physical preparation

The analytical bad set is the concrete Borel protected-endpoint event. Its
expectation is bounded under the actual iid law. `point_unprotected_control`
proves both partial discrepancies on its complement using the actual peeling
and final witness choices. `pointRun_recorded` identifies those computations
with the physically queried grid cache.

All row cumulatives are normalized by the ORIGINAL buffer. The bad set does
not depend on the retained-domain normalizers: these are arbitrary real
coefficients in `point_unprotected_control`. Coarse endpoints and the buffer
are fixed before the iid grid draw; all statements can therefore be applied
conditional on the complete preceding history.
-/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperStability
open MeasureTheory RefinedUpperPeeling UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable Chores
open scoped Classical unitInterval
variable {n b m : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

/-- The explicit bad set for the actual recorded coarse grid and physical
row measures. It is defined before any retained-domain renormalization. -/
def physicalBad (rows : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (origin : State n) (q : ℕ) (jobs finalJobs : List (Agent × Agent))
    (permanent : Fin b → ℝ) (samples : Fin m → ℝ) : Set ℝ :=
  protectedBad (endpointProcedure (physicalCumulative rows active origin)
    (UpperRecordedQuantiles.cuts policy active origin q) jobs finalJobs) permanent samples

theorem physicalBad_measurable (rows : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (rows i)]
    (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ)
    (jobs finalJobs : List (Agent × Agent)) (permanent : Fin b → ℝ) (samples : Fin m → ℝ) :
    MeasurableSet (physicalBad rows policy active origin q jobs finalJobs permanent samples) :=
  protectedBad_measurable _ (endpointProcedure_measurable _
    (physicalCumulative_measurable rows active origin) _ jobs finalJobs) permanent samples

/-- Actual physical preparation has expected bad mass at most four endpoint
charges per peeling slot and final row-pair witness, divided by `m+1`.
The reference sampling law may be any atomless probability measure. -/
theorem physical_expected_bad_measure_le
    (rows : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (rows i)]
    (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ)
    (jobs finalJobs : List (Agent × Agent)) (permanent : Fin b → ℝ)
    (samplingLaw : Measure ℝ) [IsProbabilityMeasure samplingLaw] [NullSingletonClass samplingLaw] :
    (∫ samples : Fin m → ℝ,
      samplingLaw.real (physicalBad rows policy active origin q jobs finalJobs permanent samples)
      ∂Measure.pi (fun _ : Fin m => samplingLaw)) ≤
      ((4*jobs.length+4*finalJobs.length : ℕ) : ℝ)/(m+1 : ℕ) :=
  expected_protectedBad_measure_le (physicalCumulative rows active origin)
    (physicalCumulative_measurable rows active origin)
    (UpperRecordedQuantiles.cuts policy active origin q) jobs finalJobs permanent samplingLaw

end EnvyFreeResearch.Full.RefinedUpperStability
