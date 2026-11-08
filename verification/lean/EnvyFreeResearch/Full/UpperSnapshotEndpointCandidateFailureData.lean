import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateSmallData
import EnvyFreeResearch.Full.UpperSnapshotSmallActualRows
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallPacketChance

/-! Actual immutable-grid scores and target checks for candidate exhaustion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailure
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotCandidates UpperSnapshotSmall UpperSnapshotRepetition UpperSnapshotEndpointAggregate
  UpperLogicalCells Chores
variable {n k q m : ℕ}

def packetResult (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (cutter : Fin k) (q m : ℕ) (tau : ℝ)
    (p : GridSeed k m × Tape (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle) (16*k)) :
    State n × Option (Packet (State n) (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle) (SmallRaw n k)) :=
  run (packetStep (smallStep policy (active cutter) (UpperGridMerge.cuts policy active origin q m p.1)
    (positiveIndices (smallScore hk policy active origin cutter q m p.1))
    (smallTarget hk policy active origin cutter q m tau p.1)
    (interpolationCheck hk (active cutter) (UpperGridMerge.cuts policy active origin q m p.1)
      (smallScore hk policy active origin cutter q m p.1) (domain origin.cells)
      (smallTarget hk policy active origin cutter q m tau p.1)))) (drawList p.2)
    (UpperGridCache.aligned policy active origin q m p.1)

theorem actual_score_facts
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (hk : 2 ≤ k) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (q m : ℕ) (draw : GridSeed k m) :
    (∑ e, smallScore hk policy active origin cutter q m draw e) = 0 ∧
    (∀ e, volume (cell (domain origin.cells) (UpperGridMerge.cuts policy active origin q m draw) e) = 0 →
      smallScore hk policy active origin cutter q m draw e = 0) ∧
    (∑ e, |smallScore hk policy active origin cutter q m draw e|) = smallD hk policy active origin cutter q m draw := by
  let selected := selectedRow (by omega : 0 < k) (UpperGridCache.table policy active origin q m draw) cutter
  have he := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
  have hscore : smallScore hk policy active origin cutter q m draw =
      fun e => (μ (active selected)).real (cell (domain origin.cells) (UpperGridMerge.cuts policy active origin q m draw) e) /
        (μ (active selected)).real (domain origin.cells) -
        (μ (active cutter)).real (cell (domain origin.cells) (UpperGridMerge.cuts policy active origin q m draw) e) /
        (μ (active cutter)).real (domain origin.cells) := by
    funext e
    unfold smallScore
    simp only [UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive]
    rfl
  have h := normalized_physical_scores (μ (active selected)) (μ (active cutter)) origin
    (UpperGridMerge.cuts policy active origin q m draw) he.1 he.2 (UpperCommonGrid.grid_monotone _)
    (hpositive selected) (hpositive cutter)
  refine ⟨?_, ?_, ?_⟩
  · rw [hscore]
    exact h.1
  · rw [hscore]
    exact h.2
  · rfl

theorem actual_original_fiber_failure
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (hk : 2 ≤ k) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (q m : ℕ) (tau : ℝ) (htau : 0 < tau) (draw : GridSeed k m)
    (hbranch : smallBranch hk policy active origin cutter q m tau draw) :
    law (volume.prod volume : Measure (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle)) (16*k)
      {tape | (packetResult hk policy active origin cutter q m tau (draw,tape)).2 = none} ≤
      ENNReal.ofReal ((1 : ℝ)/4) := by
  have he := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
  have hscore := actual_score_facts μ policy hpolicy active hk origin hgood hpositive cutter q m draw
  have ht := UpperSnapshotProtocol.small_amount_checks tau (smallD hk policy active origin cutter q m draw)
    k htau hbranch.1 hbranch.2 (by exact_mod_cast hk)
  exact actual_small_packet_failure_quarter μ policy hpolicy hmeas (active cutter)
    (domain origin.cells) (hpositive cutter) (UpperGridMerge.cuts policy active origin q m draw)
    he.1 he.2 (UpperCommonGrid.grid_monotone _) (smallScore hk policy active origin cutter q m draw)
    (smallTarget hk policy active origin cutter q m tau draw) ht.1 ht.2.1 hk ht.2.2.2.1 ht.2.2.2.2.1
    hscore.1 hscore.2.1 (by rw [hscore.2.2]; exact hbranch.1)
    (UpperGridCache.aligned policy active origin q m draw)
    (actual_small_initial_valid μ policy hpolicy active origin hgood hpositive q m draw)

end EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailure
