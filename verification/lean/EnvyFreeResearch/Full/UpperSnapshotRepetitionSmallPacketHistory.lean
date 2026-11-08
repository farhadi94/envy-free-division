import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallPacketAccepted

/-! Pure history correspondence for the accepted payload, independent of
physical validity, the response policy, and the tape law. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
variable {n m J : ℕ}

theorem small_packet_allocation_history (hJ : 0 < J) (policy : Policy n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ)
    (check : State n → Circle × Circle → ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Bool)
    (draws : List (Circle × Circle)) (origin : State n) (p : SmallPacket n J)
    (hp : (run (packetStep (smallStep policy cutter cuts selected t check)) draws origin).2=some p) :
    (∀ j, ((smallPacketAllocation hJ cutter cuts selected t p).1 j).history =
      (run (packetStep (smallStep policy cutter cuts selected t check)) draws origin).1.history) ∧
    (smallPacketAllocation hJ cutter cuts selected t p).2.1.history =
      (run (packetStep (smallStep policy cutter cuts selected t check)) draws origin).1.history ∧
    (smallPacketAllocation hJ cutter cuts selected t p).2.2.history =
      (run (packetStep (smallStep policy cutter cuts selected t check)) draws origin).1.history := by
  obtain ⟨_,he⟩ := packet_run_provenance (smallStep policy cutter cuts selected t check)
    (fun _ => True) (fun _ _ _ => trivial) draws origin trivial p hp
  have hstate := (small_step_accepted policy cutter cuts selected t check p.1 p.2.1 _ p.2.2 he).2.2
  rw [hstate]
  exact allocationFrom_history hJ p.1 cutter cuts selected t p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

end EnvyFreeResearch.Full.UpperSnapshotRepetition
