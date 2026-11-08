import EnvyFreeResearch.Full.UpperRepair
import EnvyFreeResearch.Full.UpperSnapshotRepetitionProbability

/-! Full fresh Snapshot tape. Every branch has its randomness allocated in
advance, and the final Repair tape is independent of the whole candidate
history. Unused branch coordinates are ignored by the actual program. -/
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
abbrev CandidateTape (k : ℕ) :=
  UpperSnapshotRepetition.Tape (UpperCircular.Circle × UpperCircular.Circle) (16*k)
abbrev Tape (n k : ℕ) := (Fin (UpperRepair.fine n) → Fin k × I) ×
  (UpperCircular.Circle × (CandidateTape k × UpperRepair.Tape n k))
def candidateLaw (k : ℕ) : Measure (CandidateTape k) :=
  UpperSnapshotRepetition.law (volume.prod volume) (16*k)
def law (n k : ℕ) : Measure (Tape n k) :=
  (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) (UpperRepair.fine n)).prod
    (volume.prod ((candidateLaw k).prod (UpperRepair.law n k)))
instance candidateLaw_probability (k : ℕ) : IsProbabilityMeasure (candidateLaw k) := by
  unfold candidateLaw
  infer_instance
instance law_probability {n k : ℕ} [Nonempty (Fin k)] : IsProbabilityMeasure (law n k) := by
  unfold law
  infer_instance
end EnvyFreeResearch.Full.UpperSnapshotProtocol
