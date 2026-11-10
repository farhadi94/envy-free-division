import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolSmallFacts
import EnvyFreeResearch.Full.RefinedUpperRepairHistory

/-! Truthful histories for every small-branch tape, including rejected
candidate attempts and failed cached checks. No interpolation event is used. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall UpperDomainDifference UpperGridRecords UpperRepairParameters
  UpperEndpointCache UpperRepairPreparationChecks
open UpperSnapshotProtocol (small_packet_physical)
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem repaired_history_truthful
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (gamma : ℝ) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n)) (p : RefinedUpperRepair.Tape n k) :
    Truthful μ (execute policy hk chores active gamma origin old p).2.1.history := by
  unfold execute
  dsimp only [finish]
  rw [finish_history]
  exact RefinedUpperRepairHistory.original_history_truthful μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear p

theorem small_history_truthful
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin k)
    (hpositive : 0 < (μ (active cutter)).real (domain origin.cells))
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells) (score : Fin (m+1) → ℝ)
    (D : ℝ) (hD : 0<D) (hsmall : D<RefinedUpperRepair.nearError n/16)
    (tape : CandidateTape k) (fresh : RefinedUpperRepair.Tape n k) :
    Truthful μ (smallExecute policy hk chores active origin cutter cuts score D tape fresh).2.1.history := by
  let t := smallAmount n k D
  let selected := positiveIndices score
  let check := UpperSnapshotRepetition.interpolationCheck hk (active cutter) cuts score (domain origin.cells) t
  let step := UpperSnapshotRepetition.smallStep policy (active cutter) cuts selected t check
  let result := UpperSnapshotRepetition.run (UpperSnapshotRepetition.packetStep step)
    (UpperSnapshotRepetition.drawList tape) origin
  have htau : 0 < RefinedUpperRepair.nearError n := by
        unfold RefinedUpperRepair.nearError RefinedUpperParameterCounts.oldError
        positivity [UpperRepairParameters.s_positive (scale_large n)]
  have htcheck := UpperSnapshotProtocol.small_amount_checks (RefinedUpperRepair.nearError n) D (k:ℝ) htau hD hsmall (by exact_mod_cast hk)
  have ht : 0<t := htcheck.1
  have hhalf : t≤1/2 := htcheck.2.1
  have hfit : (k:ℝ)*t<1 := htcheck.2.2.2.1
  have hresult : UpperSnapshotRepetition.smallValid μ (domain origin.cells) cuts result.1 :=
    UpperSnapshotRepetition.run_preserves (UpperSnapshotRepetition.packetStep step)
      (UpperSnapshotRepetition.smallValid μ (domain origin.cells) cuts)
      (fun s z hs => UpperSnapshotRepetition.small_valid_preserved μ policy hpolicy (active cutter)
        (domain origin.cells) hpositive cuts hzero hmono score t ht hhalf hk s hs z)
      (UpperSnapshotRepetition.drawList tape) origin ⟨hgood,rfl,hsep⟩
  let output := fun result : State n × Option (UpperSnapshotRepetition.SmallPacket n k) =>
    match result.2 with
    | none => rejectWhole (k:=k) origin result.1.history
    | some packet =>
      let candidate := UpperSnapshotRepetition.smallPacketAllocation (by omega) (active cutter) cuts selected t packet
      if candidateSafe chores active candidate.1 candidate.2.1 then
        restoreRejected origin (execute policy hk chores active (margin n) candidate.2.1 candidate.1 fresh)
      else rejectWhole origin result.1.history
  have hout : smallExecute policy hk chores active origin cutter cuts score D tape fresh = output result := rfl
  rw [hout]
  cases hp : result.2 with
  | none =>
    simp only [output,hp,rejectWhole]
    exact hresult.1.2.2.1
  | some packet =>
    let candidate := UpperSnapshotRepetition.smallPacketAllocation (by omega) (active cutter) cuts selected t packet
    have he : output result = if candidateSafe chores active candidate.1 candidate.2.1 then
        restoreRejected origin (execute policy hk chores active (margin n) candidate.2.1 candidate.1 fresh)
      else rejectWhole origin result.1.history := by simp only [output,hp]; rfl
    rw [he]
    by_cases hsafe : candidateSafe chores active candidate.1 candidate.2.1 = true
    · simp only [hsafe,ite_true,restoreRejected_history]
      obtain ⟨hold,hbuffer,_,_,_,_⟩ := small_packet_physical μ policy hpolicy hk active origin hgood cutter
        hpositive cuts hzero hmono hsep score t ht hhalf hfit (UpperSnapshotRepetition.drawList tape) packet hp
      obtain ⟨hpositive',hnear⟩ := (candidateSafe_physical μ chores active candidate.1 hold candidate.2.1 hbuffer).mp hsafe
      exact repaired_history_truthful μ policy hpolicy hk chores active hinj (margin n) candidate.2.1 hbuffer hpositive'
        candidate.1 hold hnear fresh
    · simp only [hsafe,ite_false,rejectWhole]
      exact hresult.1.2.2.1

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
