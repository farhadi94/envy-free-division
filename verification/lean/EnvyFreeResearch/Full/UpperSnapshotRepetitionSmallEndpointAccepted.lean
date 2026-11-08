import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpointVector
import EnvyFreeResearch.Full.UpperSnapshotRepetitionEndpointAccepted
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallPacketAccepted

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
variable {n m J : ℕ}

theorem accepted_small_endpoints_supported (hJ : 2≤J) (policy : Policy n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (score : Fin (m+1) → ℝ) (U : Set ℝ) (t : ℝ)
    (origin : State n) (tape : Tape (Circle × Circle) (16*J)) (p : SmallPacket n J)
    (hp : (run (packetStep (smallStep policy cutter cuts (positiveIndices score) t
      (interpolationCheck hJ cutter cuts score U t))) (drawList tape) origin).2=some p) :
    (∀ j : Fin 2, ∃ e, smallEndpointVector hJ policy cutter cuts score U t origin tape e =
      (firstRun policy p.1 cutter cuts (positiveIndices score) t p.2.1.1).1 j) ∧
    (∀ j : Fin J, ∃ e, smallEndpointVector hJ policy cutter cuts score U t origin tape e =
      (secondRun (J:=J) policy p.1 cutter cuts (positiveIndices score) t p.2.1.1 p.2.1.2).1 j) := by
  have h := packet_endpoint_supported
    (smallStep policy cutter cuts (positiveIndices score) t (interpolationCheck hJ cutter cuts score U t))
    (smallEndpoints (J:=J) policy cutter cuts (positiveIndices score) t) (16*J) origin tape p hp
  constructor
  · intro j
    simpa only [smallEndpointVector,smallEndpoints,Fin.append_left] using h (Fin.castAdd J j)
  · intro j
    simpa only [smallEndpointVector,smallEndpoints,Fin.append_right] using h (Fin.natAdd 2 j)

end EnvyFreeResearch.Full.UpperSnapshotRepetition
