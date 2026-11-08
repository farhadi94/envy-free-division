import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallReadySafety
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallReadyParameters
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpointAccepted

/-! A packet actually accepted by the finite repeated candidate program passes
the concrete guard and admits the fresh checked-Repair probability bound.
The interpolation event covers the endpoints of every attempted candidate. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity UpperSnapshotSmall
  UpperStageMeasurable UpperRepairPreparationChecks UpperRepairParameters UpperSnapshotRepetition
variable {n m k : ℕ} [Nonempty (Fin k)]

theorem accepted_small_packet_ready
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter foreign : Fin k) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (rows : Fin k → Fin (m+1) → ℝ)
    (hrows : rows=physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts)
    (score : Fin (m+1) → ℝ) (hscore : ∀ e, score e=rows foreign e-rows cutter e)
    (D t : ℝ) (hD : 0<D) (hsmall : D < UpperRepair.nearError n/16)
    (htdef : t=smallAmount n k D)
    (hmax : ∀ i, distance rows i cutter ≤ D) (hforeign : distance rows foreign cutter=D)
    (tape : UpperSnapshotRepetition.Tape (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle) (16*k)) (p : SmallPacket n k)
    (hp : (run (packetStep (smallStep policy (active cutter) cuts (positiveIndices score) t
      (interpolationCheck hk (active cutter) cuts score (domain origin.cells) t))) (drawList tape) origin).2=some p)
    (hinterp : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts
      (smallEndpointVector hk policy (active cutter) cuts score (domain origin.cells) t origin tape)
      (1/(scale n:ℝ)^2)) :
    let candidate := smallPacketAllocation (by omega : 0<k) (active cutter) cuts (positiveIndices score) t p
    candidateSafe chores active candidate.1 candidate.2.1=true ∧
      31/64 < (UpperRepair.law n k).real
        {q | (execute policy hk chores active (margin n) candidate.2.1 candidate.1 q).2.2=false} := by
  have htau : 0 < UpperRepair.nearError n := oldError_positive (scale_large n)
    (by exact_mod_cast logarithm_positive (scale_large n))
  have hkreal : (2:ℝ) ≤ k := by exact_mod_cast hk
  have htcheck := small_amount_checks (UpperRepair.nearError n) D (k:ℝ) htau hD hsmall hkreal
  change t=(1-(8/UpperRepair.nearError n)*D)/(k:ℝ) at htdef
  rw [← htdef] at htcheck
  obtain ⟨ht,hhalf,ht1,hfit,_,_⟩ := htcheck
  obtain ⟨hvalid,hraw,hcheck,_⟩ := actual_small_packet_accepted μ policy hpolicy (active cutter)
    (domain origin.cells) (hpositive cutter) cuts hzero hmono score t ht hhalf hk origin ⟨hgood,rfl,hsep⟩
    (drawList tape) p hp
  have hpos (i : Fin k) : 0 < (μ (active i)).real (domain p.1.cells) := by
    rw [hvalid.2.1]
    exact hpositive i
  have hrowp : physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain p.1.cells)) p.1.cells cuts=rows := by
    rw [hrows]
    funext i e
    change (μ (active i)).real (cell (domain p.1.cells) cuts e)/(μ (active i)).real (domain p.1.cells)=_
    rw [hvalid.2.1]
    rfl
  have hgoodp : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain p.1.cells)) p.1.cells cuts
      (smallEndpointVector hk policy (active cutter) cuts score (domain origin.cells) t origin tape)
      (1/(scale n:ℝ)^2) := by
    unfold BadSupportedRecordedUnion
    rw [hrowp]
    simpa only [BadSupportedRecordedUnion,← hrows,hvalid.2.1] using hinterp
  have hend := accepted_small_endpoints_supported hk policy (active cutter) cuts score (domain origin.cells) t origin tape p hp
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hscalar := small_configured_tolerances (by omega : 0<k) hkn
  have hscorefun : score=fun e => rows foreign e-rows cutter e := funext hscore
  have hsour := firstSource_positive μ p.1 hvalid.1 (active cutter) (hpos cutter) cuts
    (positiveIndices score) t ht ht1
  have hfirstwf := (first_partition μ policy hpolicy p.1 hvalid.1 (active cutter) cuts
    (positiveIndices score) t hsour p.2.1.1).1
  have hsecondwf := second_piece_wellFormed μ policy hpolicy p.1 hvalid.1 (active cutter) (hpos cutter)
    cuts hzero hmono hvalid.2.2 (positiveIndices score) t ht ht1 (by omega : 0<k) p.2.1.1 p.2.1.2 ⟨0,by omega⟩
  rw [hraw] at hcheck
  rw [interpolationCheck_actual hk policy p.1 (active cutter) cuts score (domain origin.cells) t p.2.1
    hfirstwf.2.1 hsecondwf.2.1] at hcheck
  have hwitness := of_decide_eq_true hcheck
  have hsum : (∑ e, |score e|)=D := by simpa only [hscorefun,distance] using hforeign
  rw [hsum] at hwitness
  have hwitness' : D/(8*(k:ℝ)) ≤ candidateContrast hk policy p.1 (active cutter) cuts
      (positiveIndices score) t (signedEstimate (fun e =>
        physicalRows (fun i => μ (active i)) (fun i => (μ (active i)).real (domain p.1.cells)) p.1.cells cuts foreign e-
        physicalRows (fun i => μ (active i)) (fun i => (μ (active i)).real (domain p.1.cells)) p.1.cells cuts cutter e)
        (cell (domain p.1.cells) cuts)) p.2.1 := by
    rw [hrowp,hvalid.2.1,← hscorefun]
    exact hwitness
  have hmaxp : ∀ i, distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain p.1.cells)) p.1.cells cuts) i cutter ≤ D := by
    simpa only [hrowp] using hmax
  have hforeignp : distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain p.1.cells)) p.1.cells cuts) foreign cutter=D := by
    simpa only [hrowp] using hforeign
  have hsafe := actual_small_candidate_safe μ policy hpolicy hk chores active p.1 hvalid.1 hpos cutter
    cuts hzero hone hmono hvalid.2.2 (positiveIndices score) D t hD hsmall htdef p.2.1.1 p.2.1.2
    _ hend.1 hend.2 (1/(scale n:ℝ)^2) hscalar.1 hscalar.2.2 hgoodp hmaxp
  have hprob := actual_small_candidate_probability μ policy hpolicy hmeas hk chores active hinj p.1 hvalid.1 hpos
    cutter foreign cuts hzero hone hmono hvalid.2.2 (positiveIndices score) D t hD hsmall htdef p.2.1.1 p.2.1.2
    _ hend.1 hend.2 (1/(scale n:ℝ)^2) hscalar.1 hscalar.2.1 hscalar.2.2 hgoodp hmaxp hforeignp hwitness'
  dsimp only
  rw [smallPacketAllocation_actual (by omega : 0<k) policy (active cutter) cuts (positiveIndices score) t p hraw]
  exact ⟨hsafe,hprob⟩

end EnvyFreeResearch.Full.UpperSnapshotProtocol
