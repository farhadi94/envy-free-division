import EnvyFreeResearch.Full.UpperSnapshotProtocolProbabilityFiber
import EnvyFreeResearch.Full.UpperSnapshotProtocolProbabilityGlue
import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurableExecute

/-! Unconditional success probability of the complete actual Snapshot trial,
on the original random tape and after any fixed complete preceding history.
The proof counts failed candidate attempts and does not condition on a good
sample grid or on successful inner preparation. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
variable {n k : ℕ} [Nonempty (Fin k)]

theorem snapshot_acceptance_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (cutter : Fin k) :
    (1:ℝ)/4 < (law n k).real
      {p | (snapshotExecute policy hk chores active origin cutter p).2.2=false} := by
  let success : Set (Tape n k) := {p | (snapshotExecute policy hk chores active origin cutter p).2.2=false}
  have hrun := snapshotExecute_measurable policy hmeas hk chores active (fun _ : Tape n k => origin) cutter id
    measurable_const measurable_id
  have hs : MeasurableSet success := measurableSet_eq_fun
    (measurable_snd.comp (measurable_snd.comp hrun)) measurable_const
  let joined : Set (PreparationTape n k × UpperRepair.Tape n k) := joinTape ⁻¹' success
  have hj : MeasurableSet joined := hs.preimage (joinTape_measurePreserving n k).measurable
  obtain ⟨hz,hc,hi⟩ := preparation_bad_bounds μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive cutter
  have hprob := three_exception_product_bound (preparationLaw n k) (UpperRepair.law n k) joined hj
    (preparationBadZero policy hk chores active origin cutter)
    (preparationBadCandidates policy hk active origin cutter)
    (preparationBadInterpolation μ policy hk active origin cutter) hz hc hi
    (fun p hpz hpc hpi => prepared_fiber_chance μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive cutter p hpz hpc hpi)
  have heq : ((preparationLaw n k).prod (UpperRepair.law n k)) joined = law n k success :=
    (joinTape_measurePreserving n k).measure_preimage hs.nullMeasurableSet
  change 1/4 < (law n k success).toReal
  change 1/4 < (((preparationLaw n k).prod (UpperRepair.law n k)) joined).toReal at hprob
  rwa [heq] at hprob
end EnvyFreeResearch.Full.UpperSnapshotProtocol
