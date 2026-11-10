import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallContrast
import EnvyFreeResearch.Full.RefinedUpperSnapshotAcceptance
import EnvyFreeResearch.Full.RefinedUpperSnapshotReserve

/-! One fresh actual checked Repair accepts a verified small candidate with
probability greater than 31/64. All physical hypotheses here concern the
already constructed candidate, before any fresh Repair randomness. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotContrast RefinedUpperRepairSnapshot UpperDomainDifference
  UpperRepairPreparationChecks UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

theorem small_candidate_repair_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (buffer : State n) (hbuffer : WellFormed μ buffer)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain buffer.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : Near chores μ active buffer old (RefinedUpperRepair.nearError n))
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain buffer.cells))
    (holdHistory : ∀ j, (old j).history ⊆ buffer.history)
    (foreign cutter first second : Fin k) (U A B : ℝ) (hU : 0 < U) (hA : 0 < A) (hB : 0 < B)
    (hbufferupper : (μ (active foreign)).real (domain buffer.cells) ≤ B*U)
    (hforeign : A*U ≤ (μ (active foreign)).real (domain (old first).cells) -
      (μ (active foreign)).real (domain (old second).cells))
    (hcutter : (μ (active cutter)).real (domain (old first).cells) =
      (μ (active cutter)).real (domain (old second).cells)) :
    31/64 < (RefinedUpperRepair.law n k).real
      {p | (UpperSnapshotProtocol.finish (by omega) chores active ((2*A/(3*B))/8) buffer old
        (RefinedUpperRepair.execute policy hk chores active buffer old p)).2.2 = false} := by
  apply acceptance_probability μ policy hpolicy hmeas hk chores active hinj buffer hbuffer hpositive old hold hnear
    holdpair holdbuffer holdHistory (fun _ => ((foreign,cutter),(first,second))) measurable_const
    (2*A/(3*B)) (by positivity)
  intro p hp
  have hreserve := freshReserve_wellFormed μ policy hpolicy active buffer hbuffer hpositive (view p).1
  have hpos : 0 < (μ (active foreign)).real (domain (prepReserve policy active buffer (view p).1).cells) :=
    (mul_pos (by norm_num : (0 : ℝ)<1/2) (hpositive foreign)).trans_le
      (freshReserve_half μ policy hpolicy active buffer hbuffer hpositive hinj (view p).1 foreign)
  have hu : (μ (active foreign)).real (domain (prepReserve policy active buffer (view p).1).cells) ≤
      3*(1 : ℝ)/2*(B*U) := by
    have h := (measureReal_mono (μ := μ (active foreign))
      (freshReserve_subset μ policy hpolicy active buffer hbuffer hpositive (view p).1) (measure_ne_top _ _)).trans hbufferupper
    nlinarith
  have h := UpperSnapshotProtocol.equal_cutter_contrast μ active old hold (prepReserve policy active buffer (view p).1) hreserve
    foreign cutter first second U A B 1 hU hA.le hB (by norm_num) hpos hu hforeign hcutter
  simpa only [div_one,prepOld] using h
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
