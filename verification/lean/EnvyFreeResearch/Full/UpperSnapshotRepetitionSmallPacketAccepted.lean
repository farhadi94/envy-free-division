import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallChance
import EnvyFreeResearch.Full.UpperSnapshotRepetitionPacket
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocation

/-! Every returned small-candidate packet has an actual reached originating
state, its two random starts, and the raw records required by pure assembly. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells UpperStageMeasurable Chores
variable {n m J : ℕ}

abbrev SmallPacket (n J : ℕ) := Packet (State n) (Circle × Circle) (SmallRaw n J)

def smallPacketAllocation (hJ : 0 < J) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (p : SmallPacket n J) :=
  allocationFrom hJ p.1 cutter cuts selected t p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

theorem small_step_accepted (policy : Policy n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ)
    (check : State n → Circle × Circle → ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Bool)
    (origin : State n) (z : Circle × Circle) (final : State n) (raw : SmallRaw n J)
    (h : smallStep policy cutter cuts selected t check origin z = (final,some raw)) :
    raw = (firstRun policy origin cutter cuts selected t z.1,
      secondRun (J:=J) policy origin cutter cuts selected t z.1 z.2) ∧
    check origin z raw.1 raw.2 = true ∧
    final = secondRestoredFrom origin raw.1 raw.2 := by
  have ho := congrArg Prod.snd h
  simp only [smallStep,smallPost] at ho
  split_ifs at ho with hc
  · have hh := Option.some.inj ho
    subst raw
    exact ⟨rfl,hc,(congrArg Prod.fst h).symm⟩

theorem actual_small_packet_accepted
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (cutter : Fin n) (U : Set ℝ) (hpositive : 0 < (μ cutter).real U)
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (score : Fin (m+1) → ℝ) (t : ℝ) (ht : 0<t) (hhalf : t≤1/2) (hJ : 2≤J)
    (origin : State n) (hs : smallValid μ U cuts origin) (draws : List (Circle × Circle))
    (p : SmallPacket n J)
    (hp : (run (packetStep (smallStep policy cutter cuts (positiveIndices score) t
      (interpolationCheck hJ cutter cuts score U t))) draws origin).2 = some p) :
    smallValid μ U cuts p.1 ∧
    p.2.2 = (firstRun policy p.1 cutter cuts (positiveIndices score) t p.2.1.1,
      secondRun (J:=J) policy p.1 cutter cuts (positiveIndices score) t p.2.1.1 p.2.1.2) ∧
    interpolationCheck hJ cutter cuts score U t p.1 p.2.1 p.2.2.1 p.2.2.2 = true ∧
    (run (packetStep (smallStep policy cutter cuts (positiveIndices score) t
      (interpolationCheck hJ cutter cuts score U t))) draws origin).1 =
      secondRestoredFrom p.1 p.2.2.1 p.2.2.2 := by
  obtain ⟨hv,he⟩ := packet_run_provenance
    (smallStep policy cutter cuts (positiveIndices score) t (interpolationCheck hJ cutter cuts score U t))
    (smallValid μ U cuts)
    (fun state z hv => small_valid_preserved μ policy hpolicy cutter U hpositive cuts hzero hmono score t ht hhalf hJ state hv z)
    draws origin hs p hp
  exact ⟨hv,small_step_accepted policy cutter cuts (positiveIndices score) t
    (interpolationCheck hJ cutter cuts score U t) p.1 p.2.1 _ p.2.2 he⟩

theorem smallPacketAllocation_actual (hJ : 0 < J) (policy : Policy n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (p : SmallPacket n J)
    (hraw : p.2.2 = (firstRun policy p.1 cutter cuts selected t p.2.1.1,
      secondRun (J:=J) policy p.1 cutter cuts selected t p.2.1.1 p.2.1.2)) :
    smallPacketAllocation hJ cutter cuts selected t p =
      actualAllocation hJ policy p.1 cutter cuts selected t p.2.1.1 p.2.1.2 := by
  simp only [smallPacketAllocation,actualAllocation,hraw]

end EnvyFreeResearch.Full.UpperSnapshotRepetition
