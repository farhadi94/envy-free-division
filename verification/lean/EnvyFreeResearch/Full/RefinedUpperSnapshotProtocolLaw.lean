import EnvyFreeResearch.Full.RefinedUpperRepair
import EnvyFreeResearch.Full.RefinedUpperSnapshotParameters
import EnvyFreeResearch.Full.UpperSnapshotRepetitionProbability

/-! Full fresh Snapshot tape. Every branch has its randomness allocated in
advance, and the final Repair tape is independent of the whole candidate
history. Unused branch coordinates are ignored by the actual program. -/
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
def margin (n : ℕ) : ℝ := RefinedUpperSnapshotParameters.margin
  (UpperRepairParameters.scale n) (UpperRepairParameters.logarithm (UpperRepairParameters.scale n))

abbrev CandidateTape (k : ℕ) :=
  UpperSnapshotRepetition.Tape (UpperCircular.Circle × UpperCircular.Circle) (16*k)
abbrev Tape (n k : ℕ) := (Fin (RefinedUpperRepair.fine n) → Fin k × I) ×
  (UpperCircular.Circle × (CandidateTape k × RefinedUpperRepair.Tape n k))
def candidateLaw (k : ℕ) : Measure (CandidateTape k) :=
  UpperSnapshotRepetition.law (volume.prod volume) (16*k)
def law (n k : ℕ) : Measure (Tape n k) :=
  (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) (RefinedUpperRepair.fine n)).prod
    (volume.prod ((candidateLaw k).prod (RefinedUpperRepair.law n k)))
instance candidateLaw_probability (k : ℕ) : IsProbabilityMeasure (candidateLaw k) := by
  unfold candidateLaw
  infer_instance
instance law_probability {n k : ℕ} [Nonempty (Fin k)] : IsProbabilityMeasure (law n k) := by
  unfold law
  infer_instance
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
