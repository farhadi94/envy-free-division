import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolSmallOriginalExecute
import EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailureData

/-! Fixed-preparation success probability for the actual small Snapshot
branch. The original recorded grid supplies the true table and maximizing
row; the reached packet and the simultaneous endpoint event supply all
remaining checked-Repair hypotheses. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperSnapshotRepetition UpperSnapshotCandidates UpperSnapshotEndpointAggregate
  UpperSnapshotEndpointCandidateFailure UpperAggregateInterpolation UpperGridInterpolation
  UpperGridSensitivity UpperLogicalCells UpperRepairParameters UpperCommonGrid
variable {n k : ℕ} [Nonempty (Fin k)]

theorem fixed_small_original_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (q m : ℕ) (draw : GridSeed k m) (tape : CandidateTape k)
    (hbranch : smallBranch hk policy active origin cutter q m (RefinedUpperRepair.nearError n) draw)
    (hpacket : (packetResult hk policy active origin cutter q m (RefinedUpperRepair.nearError n) (draw,tape)).2≠none)
    (hinterp : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
      (UpperGridMerge.cuts policy active origin q m draw)
      (smallOriginalPoints hk policy active origin cutter q m (RefinedUpperRepair.nearError n) (draw,tape))
      (1/(scale n:ℝ)^2)) :
    31/64 < (RefinedUpperRepair.law n k).real
      {fresh | (smallExecute policy hk chores active (UpperGridCache.aligned policy active origin q m draw)
        cutter (UpperGridMerge.cuts policy active origin q m draw)
        (smallScore hk policy active origin cutter q m draw)
        (smallD hk policy active origin cutter q m draw) tape fresh).2.2=false} := by
  let initial := UpperGridCache.aligned policy active origin q m draw
  let cuts := UpperGridMerge.cuts policy active origin q m draw
  let rows := UpperGridCache.table policy active origin q m draw
  let foreign := selectedRow (by omega : 0<k) rows cutter
  let score := smallScore hk policy active origin cutter q m draw
  let D := smallD hk policy active origin cutter q m draw
  let t := smallTarget hk policy active origin cutter q m (RefinedUpperRepair.nearError n) draw
  have hv := actual_small_initial_valid μ policy hpolicy active origin hgood hpositive q m draw
  have hd : domain initial.cells=domain origin.cells := hv.2.1
  have hpos : ∀ i, 0 < (μ (active i)).real (domain initial.cells) := by simpa only [hd] using hpositive
  have hend := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
  have hrows : rows=physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain initial.cells)) initial.cells cuts := by
    funext i e
    change _=(μ (active i)).real (cell (domain initial.cells) cuts e)/(μ (active i)).real (domain initial.cells)
    rw [hd]
    exact UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive q m draw i e
  have hrows0 : physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts=rows := by
    funext i e
    exact (UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive q m draw i e).symm
  obtain ⟨packet,hpacketEq⟩ := Option.ne_none_iff_exists'.mp hpacket
  have hp : (run (packetStep (smallStep policy (active cutter) cuts (positiveIndices score) t
      (interpolationCheck hk (active cutter) cuts score (domain initial.cells) t))) (drawList tape) initial).2=some packet := by
    simpa only [packetResult,hd] using hpacketEq
  have hi : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain initial.cells)) initial.cells cuts
      (smallEndpointVector hk policy (active cutter) cuts score (domain initial.cells) t initial tape)
      (1/(scale n:ℝ)^2) := by
    have hepoints : smallOriginalPoints hk policy active origin cutter q m (RefinedUpperRepair.nearError n) (draw,tape)=
        smallEndpointVector hk policy (active cutter) cuts score (domain origin.cells) t initial tape := by
      simp only [smallOriginalPoints,hbranch,ite_true]
      rfl
    rw [hepoints] at hinterp
    unfold BadSupportedRecordedUnion at hinterp ⊢
    rw [← hrows]
    rw [hrows0] at hinterp
    simpa only [hd] using hinterp
  have hmax (i : Fin k) : distance rows i cutter ≤ D := selectedRow_spec (by omega) rows cutter i
  have hforeign : distance rows foreign cutter=D := rfl
  obtain ⟨hsafe,hprob⟩ := accepted_small_packet_ready μ policy hpolicy hmeas hk chores active hinj initial hv.1
    hpos cutter foreign cuts hend.1 hend.2 (grid_monotone _) hv.2.2 rows hrows score (fun _ => rfl)
    D t hbranch.1 hbranch.2 rfl hmax hforeign tape packet hp hi
  apply hprob.trans_le
  apply measureReal_mono _ (measure_ne_top _ _)
  intro fresh hfresh
  change (smallExecute policy hk chores active initial cutter cuts score D tape fresh).2.2=false
  rw [small_execute_of_packet policy hk chores active initial cutter cuts score D tape packet hp hsafe fresh]
  exact (restoreRejected_success initial _).mpr hfresh

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
