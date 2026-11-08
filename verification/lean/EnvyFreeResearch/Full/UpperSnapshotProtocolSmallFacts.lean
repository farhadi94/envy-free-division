import EnvyFreeResearch.Full.UpperSnapshotProtocolSmallPhysical
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallParameters

/-! All accepted outputs of the actual small Snapshot branch satisfy the
physical contract, including on randomness where interpolation estimates fail.
The explicit cached safety guard protects the fresh Repair preconditions. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall UpperDomainDifference UpperGridRecords UpperRepairParameters
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem small_snapshot_facts
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin k)
    (hpositive : 0 < (μ (active cutter)).real (domain origin.cells))
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells) (score : Fin (m+1) → ℝ)
    (D : ℝ) (hD : 0<D) (hsmall : D<UpperRepair.nearError n/16)
    (tape : CandidateTape k) (fresh : UpperRepair.Tape n k)
    (hs : (smallExecute policy hk chores active origin cutter cuts score D tape fresh).2.2=false) :
    SnapshotSuccessFacts μ chores active origin
      (smallExecute policy hk chores active origin cutter cuts score D tape fresh) := by
  let t := smallAmount n k D
  let selected := positiveIndices score
  let check := UpperSnapshotRepetition.interpolationCheck hk (active cutter) cuts score (domain origin.cells) t
  let result := UpperSnapshotRepetition.run
    (UpperSnapshotRepetition.packetStep (UpperSnapshotRepetition.smallStep policy (active cutter) cuts selected t check))
    (UpperSnapshotRepetition.drawList tape) origin
  let output := fun result : State n × Option (UpperSnapshotRepetition.SmallPacket n k) =>
    match result.2 with
    | none => rejectWhole (k:=k) origin result.1.history
    | some packet =>
      let candidate := UpperSnapshotRepetition.smallPacketAllocation (by omega) (active cutter) cuts selected t packet
      if candidateSafe chores active candidate.1 candidate.2.1 then
        restoreRejected origin (execute policy hk chores active (margin n) candidate.2.1 candidate.1 fresh)
      else rejectWhole origin result.1.history
  have hout : smallExecute policy hk chores active origin cutter cuts score D tape fresh = output result := rfl
  rw [hout] at hs ⊢
  cases hp : result.2 with
  | none => simp only [output,hp,rejectWhole,Bool.true_eq_false] at hs
  | some packet =>
    let candidate := UpperSnapshotRepetition.smallPacketAllocation (by omega) (active cutter) cuts selected t packet
    have he : output result = if candidateSafe chores active candidate.1 candidate.2.1 then
        restoreRejected origin (execute policy hk chores active (margin n) candidate.2.1 candidate.1 fresh)
      else rejectWhole origin result.1.history := by simp only [output,hp]; rfl
    rw [he] at hs ⊢
    by_cases hsafe : candidateSafe chores active candidate.1 candidate.2.1 = true
    · simp only [hsafe,ite_true] at hs ⊢
      have htau : 0 < UpperRepair.nearError n := oldError_positive (scale_large n)
        (by exact_mod_cast logarithm_positive (scale_large n))
      have htcheck := small_amount_checks (UpperRepair.nearError n) D (k:ℝ) htau hD hsmall (by exact_mod_cast hk)
      have ht : 0<t := htcheck.1
      have hhalf : t≤1/2 := htcheck.2.1
      have hfit : (k:ℝ)*t<1 := htcheck.2.2.2.1
      obtain ⟨hold,hbuffer,hpair,hdisj,hcover,hhist⟩ := small_packet_physical μ policy hpolicy hk active origin hgood cutter
        hpositive cuts hzero hmono hsep score t ht hhalf hfit (UpperSnapshotRepetition.drawList tape) packet hp
      obtain ⟨hpositive',hnear⟩ := (candidateSafe_physical μ chores active candidate.1 hold candidate.2.1 hbuffer).mp hsafe
      exact repaired_snapshot_facts μ policy hpolicy hk chores active hinj origin candidate.2.1 hbuffer hpositive'
        candidate.1 hold hnear hpair hdisj (fun j => by rw [hhist j]) hcover fresh hs
    · simp [hsafe,rejectWhole] at hs
end EnvyFreeResearch.Full.UpperSnapshotProtocol
