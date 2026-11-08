import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallPacketAccepted
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationPartition
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationValues
import EnvyFreeResearch.Full.UpperSnapshotProtocolBranchFacts

/-! Every selected actual repeated candidate has a complete physical
partition, even on tapes outside the interpolation good event. The cached
safety guard therefore suffices to call Repair safely on every tape. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall UpperSnapshotRepetition UpperDomainDifference UpperGridRecords
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem small_packet_physical
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (hgood : WellFormed μ origin) (cutter : Fin k)
    (hpositive : 0 < (μ (active cutter)).real (domain origin.cells))
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells) (score : Fin (m+1) → ℝ)
    (t : ℝ) (ht : 0<t) (hhalf : t≤1/2) (hfit : (k:ℝ)*t<1)
    (draws : List (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle)) (packet : SmallPacket n k)
    (hp : (run (packetStep (smallStep policy (active cutter) cuts (positiveIndices score) t
      (interpolationCheck hk (active cutter) cuts score (domain origin.cells) t))) draws origin).2 = some packet) :
    let candidate := smallPacketAllocation (by omega) (active cutter) cuts (positiveIndices score) t packet
    (∀ j, WellFormed μ (candidate.1 j)) ∧ WellFormed μ candidate.2.1 ∧
    Pairwise (fun i j => Disjoint (domain (candidate.1 i).cells) (domain (candidate.1 j).cells)) ∧
    (∀ j, Disjoint (domain (candidate.1 j).cells) (domain candidate.2.1.cells)) ∧
    ((⋃ j, domain (candidate.1 j).cells) ∪ domain candidate.2.1.cells = domain origin.cells) ∧
    (∀ j, (candidate.1 j).history = candidate.2.1.history) := by
  have hv : smallValid μ (domain origin.cells) cuts origin := ⟨hgood,rfl,hsep⟩
  obtain ⟨hvalid,hraw,_,_⟩ := actual_small_packet_accepted μ policy hpolicy (active cutter)
    (domain origin.cells) hpositive cuts hzero hmono score t ht hhalf hk origin hv draws packet hp
  have hpPos : 0 < (μ (active cutter)).real (domain packet.1.cells) := by rw [hvalid.2.1]; exact hpositive
  have ht1 : t<1 := by linarith
  dsimp only
  rw [smallPacketAllocation_actual (by omega) policy (active cutter) cuts (positiveIndices score) t packet hraw]
  have hw := actual_allocation_wellFormed (J:=k) μ policy hpolicy packet.1 hvalid.1 (active cutter) hpPos cuts
    hzero hmono hvalid.2.2 (positiveIndices score) t ht ht1 (by omega) packet.2.1.1 packet.2.1.2
  refine ⟨hw.1,hw.2.1,?_,?_,?_,?_⟩
  · exact actual_shares_disjoint μ policy hpolicy packet.1 hvalid.1 (active cutter) hpPos cuts
      hzero hmono hvalid.2.2 (positiveIndices score) t ht ht1 (by omega) hfit packet.2.1.1 packet.2.1.2
  · exact actual_share_buffer_disjoint μ policy hpolicy packet.1 hvalid.1 (active cutter) hpPos cuts
      hzero hmono hvalid.2.2 (positiveIndices score) t ht ht1 (by omega) hfit packet.2.1.1 packet.2.1.2
  · exact (actual_allocation_cover μ policy hpolicy packet.1 hvalid.1 (active cutter) hpPos cuts
      hzero hmono hvalid.2.2 (positiveIndices score) t ht ht1 (by omega) hfit packet.2.1.1 packet.2.1.2).trans hvalid.2.1
  · intro j
    have hh := allocationFrom_history (J:=k) (by omega) packet.1 (active cutter) cuts (positiveIndices score) t
      packet.2.1.1 packet.2.1.2
      (firstRun policy packet.1 (active cutter) cuts (positiveIndices score) t packet.2.1.1)
      (secondRun (J:=k) policy packet.1 (active cutter) cuts (positiveIndices score) t packet.2.1.1 packet.2.1.2)
    exact (hh.1 j).trans hh.2.1.symm
end EnvyFreeResearch.Full.UpperSnapshotProtocol
